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
#include <filesystem>
#include <fstream>
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
struct FieldEngine::Impl {
    // Destruction order: values, protocol owners, setup, transport, names.
    Names names;CryptoPlayer player;std::unique_ptr<ProtocolSetup<S>> setup;std::unique_ptr<ProtocolSet<S>> set;
    std::vector<S> values;uint64_t products=0,local_inputs=0;bool failed=false;const uint64_t owner=next_owner.fetch_add(1);
    Impl(unsigned p,unsigned port,const std::array<uint8_t,32>*key_share):names(p,2,"127.0.0.1",port),player(names),
        setup(make_setup(player,key_share)),set(std::make_unique<ProtocolSet<S>>(player,*setup)){}
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
FieldEngine::FieldEngine(unsigned party,unsigned port,unsigned batch,const std::array<uint8_t,32>*mac_key_share){
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
    impl=std::make_unique<Impl>(party,port,mac_key_share);
}
FieldEngine::~FieldEngine(){if(impl){
    // Finish protocol/preprocessing owners before sampling protocol traffic.
    impl->set.reset();impl->setup.reset();
    std::cout<<"NATIVE_PROTOCOL_SENT bytes="<<impl->player.total_comm().sent<<"\n";
    std::cout<<"NATIVE_LOGICAL completed_products="<<impl->products<<" local_inputs="<<impl->local_inputs<<"\n";
}}
std::array<std::vector<FieldEngine::Handle>,2> FieldEngine::input_coins(const std::vector<uint64_t>&local){
    auto &p=*impl;p.require();try{
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
        auto &in=p.set->input;in.reset_all(p.player);
        for(auto&x:local)in.add_from_all(canonical_element(x));
        in.exchange();std::array<std::vector<Handle>,2> out;
        for(size_t i=0;i<local.size();i++)for(unsigned owner=0;owner<2;owner++)out[owner].push_back(p.put(in.finalize(owner)));
        p.local_inputs+=local.size();return out;
    }catch(...){p.failed=true;throw;}
}
unsigned FieldEngine::party_id()const{return impl->player.my_num();}
uint64_t FieldEngine::sent_bytes()const{return impl->player.total_comm().sent;}
uint64_t FieldEngine::products()const{return impl->products;}
void FieldEngine::check(){auto&p=*impl;p.require();try{p.set->check();}catch(...){p.failed=true;throw;}}
std::vector<std::array<uint8_t,32>> FieldEngine::checked_open(const std::vector<Handle>&a){
    auto&p=*impl;p.require();try{
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
