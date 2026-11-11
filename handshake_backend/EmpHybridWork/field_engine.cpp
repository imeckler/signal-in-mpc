#define NO_MIXED_CIRCUITS
#include "Machines/minimal.hpp"
#ifdef EMP_HYBRID_SEMI_HONEST
// Explicit honest-but-curious build: additive shares, OT-based triples, no MACs.
#include "Machines/Semi.hpp"
#else
#include "Machines/SPDZ.hpp"
#endif
#include "Protocols/MascotPrep.hpp"
#include "Protocols/ProtocolSet.h"
#include "Protocols/ProtocolSetup.h"
#include "field_engine.h"
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <deque>
#include <filesystem>
#include <fstream>
#include <map>
#include <mutex>
#include <thread>
namespace emp_hybrid {
using F=gfp_<17,4>;
#ifdef EMP_HYBRID_SEMI_HONEST
#undef EMP_HYBRID_TEST_FAULTS
using S=SemiShare<F>;
#else
using S=Share<F>;
#endif
static std::atomic<uint64_t> next_owner{1};
static F canonical_element(const std::array<uint8_t,32>&bytes){
    bigint n;mpz_import(n.get_mpz_t(),32,-1,1,0,0,bytes.data());
    if(n>=(bigint(1)<<255)-19)throw std::invalid_argument("noncanonical field element");
    return F(n);
}
static std::array<uint8_t,32> element_bytes(const F&x){
    bigint n;to_bigint(n,x);std::array<uint8_t,32>bytes{};for(auto&b:bytes){b=mpz_get_ui(n.get_mpz_t())&255;n>>=8;}return bytes;
}
// The library samples the MAC key share and builds the OT setup whose receiver choice bits
// are that share's bits (OT/MascotMacKey.hpp, `read_or_generate`). This does the same for a
// SUPPLIED share, and writes nothing to disk. The library then finds the key already set.
static std::unique_ptr<ProtocolSetup<S>> make_setup(Player&P,const std::array<uint8_t,32>*key_share){
    const bigint prime=(bigint(1)<<255)-19;
    if(key_share){
#ifdef EMP_HYBRID_SEMI_HONEST
        throw std::invalid_argument("the semi-honest field engine has no MAC key");
#else
        F::init_field(prime);F::next::init_field(prime,false);
        // The triple generator works on the library's preprocessing share type, whose key
        // type is a second instance of the same field.
        using X=S::prep_type;using K=X::mac_key_type;
        bigint n;to_bigint(n,canonical_element(*key_share));K value(n);if(value.is_zero())throw std::invalid_argument("zero MAC key share");
        auto&key=S::TripleGenerator::get_mac_key();
        static_cast<K&>(key)=value;
        key.ot=OTTripleSetup(P,true);key.ot.base_receiver_inputs.set(key);
        auto ot_setup=BaseMachine::fresh_ot_setup(P);
        if(not OTExtensionWithMatrix(0).use_kos())P.fork("soft");
        for(int i:P.balanced_others())OTMultiplierBase::init(key,P,i,ot_setup);
        X::set_mac_key(key);
        // On a failed MAC check the library deletes its key-material file and asserts that
        // the deletion worked. Nothing is stored here, so give it an empty file to delete.
        auto filename=get_ot_secrets_filename<X>(P);X::set_secrets_filename(filename);
        std::filesystem::create_directories(std::filesystem::path(filename).parent_path());
        std::ofstream placeholder(filename,std::ios::trunc);if(!placeholder)throw std::runtime_error("field engine working directory");
#endif
    }
    return std::make_unique<ProtocolSetup<S>>(prime,P);
}
// Triples generated ahead of use. Triple generation does not depend on what is multiplied, so
// a second protocol instance of the SAME engine (same MAC key, its own connection between the
// same two parties) generates them in a background thread with the library's own generator
// and checks, and the engine's multiplication takes them from here instead of generating
// them when it runs out. Triples are used in the order they were made, each once, only by
// this engine, and are gone with it.
//
// Both parties must generate the same batches. Batch k is started when
// k*batch < requested + reserve, where `requested` counts the products asked for so far: the
// same number on both sides, reached at different moments. Each side announces a batch on
// the stock's connection when its own count allows it and the batch starts when both have;
// on shutdown a side announces the end instead, and both stop.
// With several generator lines, line j makes the batches k with k mod lines = j, each on its
// own connection, and batches are used in the order of k whichever finishes first.
// (The name is distinct from dyn_session.h's TripleStock on purpose: both end up in one program.)
struct FieldTripleStock {
    struct Line {
        CryptoPlayer player;ProtocolSet<S>set;std::thread thread;
        Line(const Names&names,const ProtocolSetup<S>&setup,unsigned index):player(names,"stock"+std::to_string(index)),set(player,setup){}
    };
    std::mutex m;std::condition_variable changed;std::deque<std::array<S,3>>ready;std::map<uint64_t,std::vector<std::array<S,3>>>finished;
    uint64_t requested=0,next=0;bool stopping=false,broken=false;size_t batch=0,reserve=0;double waited=0;
    DataPositions usage;std::vector<std::unique_ptr<Line>>lines;
    // What the multiplication protocol asks for triples.
    struct Source:Preprocessing<S>{
        FieldTripleStock&stock;
        Source(FieldTripleStock&s):Preprocessing<S>(s.usage),stock(s){}
        std::array<S,3> get_triple(int)override{
            std::lock_guard<std::mutex>lock(stock.m);
            if(stock.ready.empty())throw std::runtime_error("triple stock empty");   // `need` runs first
            auto triple=stock.ready.front();stock.ready.pop_front();return triple;
        }
    };
    Source source;
    FieldTripleStock(const Names&names,const ProtocolSetup<S>&setup,size_t batch_,size_t reserve_,unsigned count):batch(batch_),reserve(reserve_),usage(2),source(*this){
        // Connections are made here, in the same order by both parties.
        for(unsigned j=0;j<count;j++)lines.push_back(std::make_unique<Line>(names,setup,j));
        // A failure in the background (a failed check, a lost connection) fails the next multiplication.
        for(unsigned j=0;j<count;j++)lines[j]->thread=std::thread([this,j]{try{work(*lines[j],j);}catch(...){{std::lock_guard<std::mutex>lock(m);broken=true;}changed.notify_all();}});
    }
    void work(Line&line,uint64_t first){
        auto&player=line.player;const int me=player.my_num();
        for(uint64_t k=first;;k+=lines.size()){
            octet mine=0,peer=0;
            {std::unique_lock<std::mutex>lock(m);changed.wait(lock,[&]{return stopping||k*batch<requested+reserve;});mine=stopping?0:1;}
            octetStream out,in;out.append(&mine,1);
            if(me==0){player.send_to(1,out);player.receive_player(1,in);}
            else{player.receive_player(0,in);player.send_to(0,out);}
            if(in.get_length()!=1)throw std::runtime_error("triple stock announcement");
            in.consume(&peer,1);
            if(!mine||!peer)return;
            std::vector<std::array<S,3>>made(batch);
            for(auto&t:made)line.set.preprocessing.get_three(DATA_TRIPLE,t[0],t[1],t[2]);
            {
                std::lock_guard<std::mutex>lock(m);finished[k]=std::move(made);
                for(auto it=finished.find(next);it!=finished.end();it=finished.find(next)){for(auto&t:it->second)ready.push_back(t);finished.erase(it);next++;}
            }
            changed.notify_all();
        }
    }
    // Before a multiplication round of n products: count them, and wait until n triples are ready.
    void need(size_t n){
        const auto started=std::chrono::steady_clock::now();
        std::unique_lock<std::mutex>lock(m);requested+=n;changed.notify_all();
        changed.wait(lock,[&]{return ready.size()>=n||broken;});
        if(broken)throw std::runtime_error("triple stock failed");
        waited+=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
    }
    ~FieldTripleStock(){
        {std::lock_guard<std::mutex>lock(m);stopping=true;}
        changed.notify_all();
        for(auto&line:lines)if(line->thread.joinable())line->thread.join();
        lines.clear();
    }
    uint64_t sent()const{uint64_t n=0;for(auto&line:lines)n+=line->player.total_comm().sent;return n;}
};
// The library's ProtocolSet (Protocols/ProtocolSet.h) with a choice of its two opening protocols.
// Indirect (the library's default, and ours): party 1 sends its shares to party 0, which answers
// with the sums: two message delays per multiplication round or opening. Direct (the library's
// `--direct`): each party sends its shares to the other at once and adds: one message delay.
// The values opened and the MAC check on them are the same in both.
template<class T> struct EngineSet {
    DataPositions usage;std::unique_ptr<typename T::MAC_Check>owned;typename T::MAC_Check&output;typename T::LivePrep preprocessing;
    SubProcessor<T>processor;typename T::Protocol&protocol;typename T::Input&input;
    EngineSet(Player&P,const ProtocolSetup<T>&setup,bool direct):usage(P.num_players()),
        owned(direct?std::unique_ptr<typename T::MAC_Check>(new typename T::Direct_MC(setup.get_mac_key())):std::make_unique<typename T::MAC_Check>(setup.get_mac_key())),
        output(*owned),preprocessing(0,usage),processor(output,preprocessing,P),protocol(processor.protocol),input(processor.input){}
    void check(){protocol.check();output.Check(processor.P);}
};
struct FieldEngine::Impl {
    // Destruction order: values, protocol owners, setup, transport, names.
    Names names;CryptoPlayer player;std::unique_ptr<ProtocolSetup<S>> setup;std::unique_ptr<EngineSet<S>> set;std::unique_ptr<FieldTripleStock>stock;
    std::vector<S> values;uint64_t products=0,local_inputs=0,mul_rounds=0,openings=0,input_rounds=0;bool failed=false;const uint64_t owner=next_owner.fetch_add(1);
    Impl(unsigned p,unsigned port,const std::array<uint8_t,32>*key_share,unsigned batch,unsigned reserve,unsigned lines,const char*peer,bool direct):
        names(peer?Names(int(p),int(port),std::vector<std::string>{p==0?std::string("127.0.0.1"):std::string(peer),"127.0.0.1"}):Names(p,2,"127.0.0.1",port)),player(names),
        setup(make_setup(player,key_share)),set(std::make_unique<EngineSet<S>>(player,*setup,direct)){
        if(reserve){stock=std::make_unique<FieldTripleStock>(names,*setup,batch,reserve,lines);set->protocol.init(stock->source,set->output);}
    }
    void require(){if(failed)throw std::runtime_error("native engine poisoned");}
    const S&get(Handle h){require();if(!owner||h.owner!=owner||!h.index||h.index>values.size())throw std::invalid_argument("native handle owner/range");return values[h.index-1];}
    Handle put(S x){values.push_back(std::move(x));return Handle(owner,values.size());}
};
FieldEngine::Handle FieldEngine::import_share(const std::array<uint8_t,32>&value_share,const std::array<uint8_t,32>&mac_share){
    auto&p=*impl;p.require();
#ifdef EMP_HYBRID_SEMI_HONEST
    (void)mac_share;return p.put(S(canonical_element(value_share)));
#else
    return p.put(S(canonical_element(value_share),canonical_element(mac_share)));
#endif
}
std::pair<std::array<uint8_t,32>,std::array<uint8_t,32>> FieldEngine::export_share(Handle a){
    auto&p=*impl;const S&x=p.get(a);
#ifdef EMP_HYBRID_SEMI_HONEST
    return {element_bytes(F(x)),std::array<uint8_t,32>{}};
#else
    return {element_bytes(x.get_share()),element_bytes(x.get_mac())};
#endif
}
FieldEngine::FieldEngine(unsigned party,unsigned port,unsigned batch,const std::array<uint8_t,32>*mac_key_share,unsigned stock_reserve,unsigned stock_lines,const char*peer,bool direct){
    if(party>1||port>65000||batch<1||batch>1000000)throw std::invalid_argument("native identity/port");
    // Exact p, checked OT, no online/preprocessing reuse across owners.
    // In the MASCOT/Fp path MP-SPDZ reads this only as a minimum field-size
    // guard (Protocols/mac_key.hpp); 128 is the production profile.
#ifndef EMP_HYBRID_NATIVE_SECURITY
#define EMP_HYBRID_NATIVE_SECURITY 40
#endif
    OnlineOptions::singleton.security_parameter=EMP_HYBRID_NATIVE_SECURITY;
    OnlineOptions::singleton.use_security_parameter=true;
    OnlineOptions::singleton.verbose=true;
    ProtocolSetup<S>::set_batch_size(batch);
    if(stock_reserve>10000000||stock_lines<1||stock_lines>8)throw std::invalid_argument("triple stock reserve");
    impl=std::make_unique<Impl>(party,port,mac_key_share,batch,stock_reserve,stock_lines,peer,direct);
}
FieldEngine::~FieldEngine(){if(impl){
    // Finish protocol/preprocessing owners before sampling protocol traffic.
    impl->stock.reset();impl->set.reset();impl->setup.reset();
    std::cout<<"NATIVE_PROTOCOL_SENT bytes="<<impl->player.total_comm().sent<<"\n";
    std::cout<<"NATIVE_LOGICAL completed_products="<<impl->products<<" local_inputs="<<impl->local_inputs<<"\n";
}}
std::array<std::vector<FieldEngine::Handle>,2> FieldEngine::input_coins(const std::vector<uint64_t>&local){
    auto &p=*impl;p.require();try{
        p.input_rounds++;
        auto &in=p.set->input;in.reset_all(p.player);
        for(auto x:local)in.add_from_all(F(bigint(static_cast<unsigned long>(x))));
        in.exchange();std::array<std::vector<Handle>,2> out;
        for(size_t i=0;i<local.size();i++)for(unsigned owner=0;owner<2;owner++)out[owner].push_back(p.put(in.finalize(owner)));
        p.local_inputs+=local.size();return out;
    }catch(...){p.failed=true;throw;}
}
std::vector<FieldEngine::Handle> FieldEngine::mul(const std::vector<Handle>&a,const std::vector<Handle>&b){
    auto&p=*impl;p.require();if(a.size()!=b.size())throw std::invalid_argument("native multiply shape");
    try{
        if(p.stock)p.stock->need(a.size());
        p.mul_rounds++;
        auto &m=p.set->protocol;m.init_mul();
        for(size_t i=0;i<a.size();i++)m.prepare_mul(p.get(a[i]),p.get(b[i]));m.exchange();
        std::vector<Handle>out;for(size_t i=0;i<a.size();i++)out.push_back(p.put(m.finalize_mul()));p.products+=a.size();return out;
    }catch(...){p.failed=true;throw;}
}
FieldEngine::Handle FieldEngine::add(Handle a,Handle b){auto&p=*impl;return p.put(p.get(a)+p.get(b));}
FieldEngine::Handle FieldEngine::sub(Handle a,Handle b){auto&p=*impl;return p.put(p.get(a)-p.get(b));}
FieldEngine::Handle FieldEngine::constant(uint64_t v){auto&p=*impl;p.require();return p.put(S::constant(F(bigint(static_cast<unsigned long>(v))),p.player.my_num(),p.setup->get_mac_key()));}
FieldEngine::Handle FieldEngine::scale(Handle a,uint64_t c){auto&p=*impl;return p.put(p.get(a)*F(bigint(static_cast<unsigned long>(c))));}
FieldEngine::Handle FieldEngine::divide_public(Handle a,const std::array<uint8_t,32>&c){
    auto&p=*impl;F value=canonical_element(c);if(value.is_zero())throw std::invalid_argument("division by zero");
    return p.put(p.get(a)*value.invert());
}
FieldEngine::Handle FieldEngine::public_element(const std::array<uint8_t,32>&v){auto&p=*impl;p.require();return p.put(S::constant(canonical_element(v),p.player.my_num(),p.setup->get_mac_key()));}
std::array<std::vector<FieldEngine::Handle>,2> FieldEngine::input_elements(const std::vector<std::array<uint8_t,32>>&local){
    auto &p=*impl;p.require();try{
        p.input_rounds++;
        auto &in=p.set->input;in.reset_all(p.player);
        for(auto&x:local)in.add_from_all(canonical_element(x));
        in.exchange();std::array<std::vector<Handle>,2> out;
        for(size_t i=0;i<local.size();i++)for(unsigned owner=0;owner<2;owner++)out[owner].push_back(p.put(in.finalize(owner)));
        p.local_inputs+=local.size();return out;
    }catch(...){p.failed=true;throw;}
}
unsigned FieldEngine::party_id()const{return impl->player.my_num();}
uint64_t FieldEngine::sent_bytes()const{return impl->player.total_comm().sent+(impl->stock?impl->stock->sent():0);}
double FieldEngine::stock_waited()const{return impl->stock?impl->stock->waited:0;}
bool FieldEngine::stocked()const{return bool(impl->stock);}
uint64_t FieldEngine::products()const{return impl->products;}
std::array<uint64_t,3> FieldEngine::exchanges()const{return {impl->mul_rounds,impl->openings,impl->input_rounds};}
void FieldEngine::check(){auto&p=*impl;p.require();try{p.set->check();}catch(...){p.failed=true;throw;}}
std::vector<std::array<uint8_t,32>> FieldEngine::checked_open(const std::vector<Handle>&a){
    auto&p=*impl;p.require();try{
        p.openings++;
        p.set->check();auto&o=p.set->output;o.init_open(p.player);
        for(size_t i=0;i<a.size();i++) {
#ifdef EMP_HYBRID_TEST_FAULTS
            if(i==0&&p.player.my_num()==1&&std::getenv("EMP_TEST_NATIVE_OPEN_MAC")) {
                auto bad=p.get(a[i]);bad=S(bad.get_share(),bad.get_mac()+F(1));o.prepare_open(bad);
            }else
#endif
                o.prepare_open(p.get(a[i]));
        }
        o.exchange(p.player);
        std::vector<F> quarantine;for(size_t i=0;i<a.size();i++)quarantine.push_back(o.finalize_open());
        o.Check(p.player); // Never serialize/use an unchecked field opening.
        std::vector<std::array<uint8_t,32>>out;
        for(auto &x:quarantine){bigint n;to_bigint(n,x);std::array<uint8_t,32> bytes{};
            for(auto &b:bytes){b=mpz_get_ui(n.get_mpz_t())&255; n>>=8;}out.push_back(bytes);}
        return out;
    }catch(...){p.failed=true;throw;}
}
}
