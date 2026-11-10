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
namespace emp_hybrid {
using F=gfp_<17,4>;
#ifdef EMP_HYBRID_SEMI_HONEST
#undef EMP_HYBRID_TEST_FAULTS
using S=SemiShare<F>;
#else
using S=Share<F>;
#endif
static std::atomic<uint64_t> next_owner{1};
struct FieldEngine::Impl {
    // Destruction order: values, protocol owners, setup, transport, names.
    Names names;CryptoPlayer player;std::unique_ptr<ProtocolSetup<S>> setup;std::unique_ptr<ProtocolSet<S>> set;
    std::vector<S> values;uint64_t products=0,local_inputs=0;bool failed=false;const uint64_t owner=next_owner.fetch_add(1);
    Impl(unsigned p,unsigned port):names(p,2,"127.0.0.1",port),player(names),
        setup(std::make_unique<ProtocolSetup<S>>((bigint(1)<<255)-19,player)),set(std::make_unique<ProtocolSet<S>>(player,*setup)){}
    void require(){if(failed)throw std::runtime_error("native engine poisoned");}
    const S&get(Handle h){require();if(!owner||h.owner!=owner||!h.index||h.index>values.size())throw std::invalid_argument("native handle owner/range");return values[h.index-1];}
    Handle put(S x){values.push_back(std::move(x));return Handle(owner,values.size());}
};
FieldEngine::FieldEngine(unsigned party,unsigned port,unsigned batch){
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
    impl=std::make_unique<Impl>(party,port);
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
static F canonical_element(const std::array<uint8_t,32>&bytes){
    bigint n;mpz_import(n.get_mpz_t(),32,-1,1,0,0,bytes.data());
    if(n>=(bigint(1)<<255)-19)throw std::invalid_argument("noncanonical field element");
    return F(n);
}
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
