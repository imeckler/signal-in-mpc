#include "PrivateProviderRegistry.h"
#include <cassert>
#include <vector>
#include <iostream>
using Bits=std::vector<unsigned char>;
using Registry=tls_mpc_worker::PrivateProviderRegistry<Bits>;
static Bits bits(size_t bytes,unsigned char bit=0){return Bits(bytes*8,bit);}
struct Counts {unsigned upgrades=0,produced=0,acks=0,closed=0,terminal=0,checkpoints=0;};
struct Provider:Registry::Provider {
    Counts& count;bool reject=false;
    explicit Provider(Counts& count):count(count){}
    Registry::Upgrade upgrade(Bits nonce)override{assert(nonce.size()==128);++count.upgrades;return{bits(5),5};}
    void upgrade_complete()override{}
    Registry::Produced produce(Bits input,Bits time)override{
        assert(input.size()==8&&time.size()==64);++count.produced;
        auto out=bits(6);std::fill(out.begin(),out.begin()+8,reject?0:1);
        return{count.produced,std::move(out),bits(8),3};
    }
    void response_complete(uint64_t ticket)override{assert(ticket==count.produced);++count.acks;}
    void close()noexcept override{++count.closed;}
};
struct Harness {
    Counts count;uint64_t next=1;std::vector<Bits> retained;bool fail_checkpoint=false;
    Registry registry;
    Harness():registry({
      [&](Bits payload,Bits valid){assert(valid.size()==8);retained.push_back(valid);return next++;},
      [&](Bits payload,size_t capacity){assert(payload.size()==8*(capacity+3));retained.emplace_back(payload.begin(),payload.begin()+8);return next++;},
      [](Bits a,Bits b){bool accepted=std::all_of(a.begin(),a.end(),[](auto x){return x==1;})&&std::all_of(b.begin(),b.end(),[](auto x){return x==1;});return bits(1,accepted);},
      [](Bits id){assert(id.size()==64);},
      [&]{++count.checkpoints;if(fail_checkpoint)throw std::runtime_error("injected checkpoint failure");},
      [&]{++count.terminal;}}){}
    Provider* admit(unsigned char credentials=1,unsigned char state=1){auto p=std::make_unique<Provider>(count);auto raw=p.get();assert(registry.admit(std::move(p),bits(1,credentials),bits(1,state))==1);return raw;}
    void start(){auto r=registry.upgrade(1,bits(16));assert(r.handle==1&&r.capacity==5);registry.authenticated_upgrade_complete();}
    uint64_t input(unsigned char valid=1){return registry.admit_input(bits(1),bits(8),bits(1,valid));}
};
template<class F>static void rejected(F&& f){bool failed=false;try{f();}catch(const std::runtime_error&){failed=true;}assert(failed);}
int main(){
    unsigned checks=0;
    {Harness h;rejected([&]{h.registry.upgrade(1,bits(16));});assert(h.count.terminal==1);++checks;}
    {Harness h;h.admit();auto i=h.input();h.registry.upgrade(1,bits(16));rejected([&]{h.registry.produce(1,i);});assert(h.count.produced==0&&h.count.closed==1);++checks;}
    {Harness h;h.admit();h.start();auto i=h.input();auto r=h.registry.produce(1,i);assert(r.handle==2);h.registry.authenticated_response_complete();
      auto j=h.input();h.registry.produce(1,j);h.registry.authenticated_response_complete();assert(h.count.produced==2&&h.count.acks==2&&h.count.checkpoints==3);++checks;}
    {Harness h;h.admit();h.start();auto i=h.input(),j=h.input();h.registry.produce(1,i);rejected([&]{h.registry.produce(1,j);});assert(h.count.produced==1&&h.count.closed==1);++checks;}
    {Harness h;h.admit();h.start();auto i=h.input();h.registry.produce(1,i);h.registry.authenticated_response_complete();rejected([&]{h.registry.produce(1,i);});assert(h.count.produced==1);++checks;}
    {Harness h;h.admit();h.start();rejected([&]{h.registry.authenticated_response_complete();});assert(h.count.acks==0);++checks;}
    for(unsigned credential:{0,1})for(unsigned state:{0,1})for(unsigned upstream:{0,1})for(unsigned actual:{0,1}){
      Harness h;auto p=h.admit(credential,state);p->reject=!actual;h.start();h.registry.produce(1,h.input(upstream));
      assert(h.retained[0]==bits(1,credential));assert(h.retained[1]==bits(1,state&&upstream&&actual));++checks;}
    {Harness h;h.admit();h.start();h.fail_checkpoint=true;rejected([&]{h.registry.produce(1,h.input());});assert(h.count.produced==1&&h.count.acks==0&&h.count.closed==1&&h.count.terminal==1);++checks;}
    {Harness h;h.admit();h.start();auto i=h.input();h.registry.close();rejected([&]{h.registry.produce(1,i);});assert(h.count.produced==0);++checks;}
    std::cout<<checks<<" public provider-registry transitions passed; no native MPC claim\n";
}
