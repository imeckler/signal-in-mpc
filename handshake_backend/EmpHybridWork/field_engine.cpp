#define NO_MIXED_CIRCUITS
#include "Machines/minimal.hpp"
#include "Machines/SPDZ.hpp"
#include "Protocols/MascotPrep.hpp"
#include "Protocols/ProtocolSet.h"
#include "Protocols/ProtocolSetup.h"
#include "field_engine.h"
#include <atomic>
namespace emp_hybrid {
using F=gfp_<17,4>;
using S=Share<F>;
static std::atomic<uint64_t> next_owner{1};
struct FieldEngine::Impl {
    // Destruction order: values, protocol owners, setup, transport, names.
    Names names;CryptoPlayer player;ProtocolSetup<S> setup;ProtocolSet<S> set;
    std::vector<S> values;bool failed=false;const uint64_t owner=next_owner.fetch_add(1);
    Impl(unsigned p,unsigned port):names(p,2,"127.0.0.1",port),player(names),
        setup((bigint(1)<<255)-19,player),set(player,setup){}
    void require(){if(failed)throw std::runtime_error("native engine poisoned");}
    const S&get(Handle h){require();if(!owner||h.owner!=owner||!h.index||h.index>values.size())throw std::invalid_argument("native handle owner/range");return values[h.index-1];}
    Handle put(S x){values.push_back(std::move(x));return Handle(owner,values.size());}
};
FieldEngine::FieldEngine(unsigned party,unsigned port){
    if(party>1||port>65000)throw std::invalid_argument("native identity/port");
    // Exact p, checked OT, no online/preprocessing reuse across owners.
    OnlineOptions::singleton.security_parameter=40;
    OnlineOptions::singleton.use_security_parameter=true;
    ProtocolSetup<S>::set_batch_size(10000);
    impl=std::make_unique<Impl>(party,port);
}
FieldEngine::~FieldEngine(){if(impl)std::cout<<"NATIVE_PROTOCOL_SENT bytes="<<impl->player.total_comm().sent<<"\n";}
std::array<std::vector<FieldEngine::Handle>,2> FieldEngine::input_coins(const std::vector<uint64_t>&local){
    auto &p=*impl;p.require();try{
        auto &in=p.set.input;in.reset_all(p.player);
        for(auto x:local)in.add_from_all(F(bigint(static_cast<unsigned long>(x))));
        in.exchange();std::array<std::vector<Handle>,2> out;
        for(size_t i=0;i<local.size();i++)for(unsigned owner=0;owner<2;owner++)out[owner].push_back(p.put(in.finalize(owner)));
        return out;
    }catch(...){p.failed=true;throw;}
}
std::vector<FieldEngine::Handle> FieldEngine::mul(const std::vector<Handle>&a,const std::vector<Handle>&b){
    auto&p=*impl;p.require();if(a.size()!=b.size())throw std::invalid_argument("native multiply shape");
    try{
        auto &m=p.set.protocol;m.init_mul();
        for(size_t i=0;i<a.size();i++)m.prepare_mul(p.get(a[i]),p.get(b[i]));m.exchange();
        std::vector<Handle>out;for(size_t i=0;i<a.size();i++)out.push_back(p.put(m.finalize_mul()));return out;
    }catch(...){p.failed=true;throw;}
}
FieldEngine::Handle FieldEngine::add(Handle a,Handle b){auto&p=*impl;return p.put(p.get(a)+p.get(b));}
FieldEngine::Handle FieldEngine::sub(Handle a,Handle b){auto&p=*impl;return p.put(p.get(a)-p.get(b));}
FieldEngine::Handle FieldEngine::constant(uint64_t v){auto&p=*impl;p.require();return p.put(S::constant(F(bigint(static_cast<unsigned long>(v))),p.player.my_num(),p.setup.get_mac_key()));}
void FieldEngine::check(){auto&p=*impl;p.require();try{p.set.check();}catch(...){p.failed=true;throw;}}
std::vector<std::array<uint8_t,32>> FieldEngine::checked_open(const std::vector<Handle>&a){
    auto&p=*impl;p.require();try{
        p.set.check();auto&o=p.set.output;o.init_open(p.player);for(auto h:a)o.prepare_open(p.get(h));o.exchange(p.player);
        std::vector<F> quarantine;for(size_t i=0;i<a.size();i++)quarantine.push_back(o.finalize_open());
        o.Check(p.player); // Never serialize/use an unchecked field opening.
        std::vector<std::array<uint8_t,32>>out;
        for(auto &x:quarantine){bigint n;to_bigint(n,x);std::array<uint8_t,32> bytes{};
            for(auto &b:bytes){b=mpz_get_ui(n.get_mpz_t())&255; n>>=8;}out.push_back(bytes);}
        return out;
    }catch(...){p.failed=true;throw;}
}
}
