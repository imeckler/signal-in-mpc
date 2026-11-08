#include "PrivateMuxRegistry.h"
#include <vector>
#include <cassert>
using Bits=std::vector<unsigned char>;
struct Conversation {
    struct Produced{uint64_t ticket;Bits payload,request_id;size_t capacity;};
    bool active=false,pending=false,closed=false;uint64_t ticket=0;int calls=0;
    void authenticated_connection_ready(){assert(!active&&!closed);active=true;}
    Produced produce(Bits,Bits,Bits id){assert(active&&!pending&&!closed);pending=true;++calls;return{++ticket,Bits(32,255),std::move(id),1};}
    void authenticated_response_complete(uint64_t value){assert(pending&&value==ticket&&!closed);pending=false;}
    void close()noexcept{closed=true;}
};
using Registry=tls_mpc_worker::PrivateMuxRegistry<Bits,Conversation>;
struct Fixture {
    int burns=0,retained=0,checkpoints=0,terminal=0,expectations=0;bool reject=false;
    std::vector<size_t> slots;Registry registry;
    Fixture():registry({[&]{++burns;return Bits(64,static_cast<unsigned char>(burns));},
      [](Bits a,Bits b){assert(a.size()==8&&b.size()==8);for(size_t i=0;i<8;++i)a[i]&=b[i];return a;},
      [&](size_t slot,Bits id,Bits valid){assert(id.size()==64&&valid.size()==8);++expectations;slots.push_back(slot);if(reject)throw std::runtime_error("rejected computed flag");},
      [&](Bits payload,size_t capacity){assert(payload.size()==8*(capacity+3));return uint64_t(++retained);},
      [&]{++checkpoints;},[&]{++terminal;}},Bits(8,255)){}
    uint64_t add(){return registry.admit(std::make_unique<Conversation>(),Bits(8,255));}
    uint64_t input(uint64_t owner){return registry.admit_input(owner,Bits(8),Bits(64),Bits(8,255));}
};
template<class F>void rejects(F&& f){bool caught=false;try{f();}catch(const std::exception&){caught=true;}assert(caught);}
int main(){
    {Fixture f;auto a=f.add(),b=f.add();auto a1=f.input(a),a2=f.input(a),b1=f.input(b),b2=f.input(b);
     f.registry.authenticated_connection_ready();f.registry.produce(a,a1);f.registry.produce(b,b1);
     assert(f.slots==std::vector<size_t>({0,1}));assert(f.registry.authenticated_response_complete(1)==b);
     f.registry.produce(b,b2);assert(f.slots.back()==1);assert(f.registry.authenticated_response_complete(0)==a);
     f.registry.produce(a,a2);assert(f.registry.authenticated_response_complete(1)==b);assert(f.registry.authenticated_response_complete(0)==a);
     assert(f.burns==4&&f.retained==4&&f.checkpoints==4&&!f.terminal);}
    {Fixture f;auto a=f.add(),b=f.add();auto input=f.input(a);f.registry.authenticated_connection_ready();rejects([&]{f.registry.produce(b,input);});assert(!f.burns&&f.terminal==1);}
    {Fixture f;auto a=f.add();auto first=f.input(a),second=f.input(a);f.registry.authenticated_connection_ready();f.registry.produce(a,first);rejects([&]{f.registry.produce(a,second);});assert(f.burns==1&&f.retained==1&&f.terminal==1);}
    {Fixture f;auto a=f.add();auto input=f.input(a);f.registry.authenticated_connection_ready();f.registry.produce(a,input);f.registry.authenticated_response_complete(0);rejects([&]{f.registry.produce(a,input);});assert(f.burns==1&&f.terminal==1);}
    {Fixture f;auto a=f.add();auto input=f.input(a);f.registry.authenticated_connection_ready();f.reject=true;rejects([&]{f.registry.produce(a,input);});assert(f.burns==1&&!f.retained&&!f.checkpoints&&f.terminal==1);rejects([&]{f.registry.produce(a,input);});assert(f.burns==1);}
    {Fixture f;for(int i=0;i<4;++i)f.add();rejects([&]{f.add();});assert(f.terminal==1);}
    {Fixture f;auto a=f.add();auto input=f.input(a);rejects([&]{f.registry.produce(a,input);});assert(!f.burns&&f.terminal==1);}
    {Fixture f;f.add();f.registry.authenticated_connection_ready();rejects([&]{f.registry.authenticated_response_complete(0);});assert(f.terminal==1);}
    {Fixture f;std::vector<uint64_t> owners,inputs;for(int i=0;i<4;++i){auto owner=f.add();owners.push_back(owner);inputs.push_back(f.input(owner));}f.registry.authenticated_connection_ready();for(int i=0;i<4;++i)f.registry.produce(owners[i],inputs[i]);for(int i=3;i>=0;--i)assert(f.registry.authenticated_response_complete(i)==owners[i]);assert(f.burns==4&&f.retained==4);rejects([&]{f.registry.authenticated_response_complete(0);});}
}
