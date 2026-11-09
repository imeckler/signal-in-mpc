#include "PrivateMuxRegistry.h"
#include "PublicProtocol.h"
#include <cassert>
#include <vector>
using Bits=std::vector<unsigned char>;
struct Conversation {
 struct Produced{uint64_t ticket;Bits payload,request_id;size_t capacity;};
 struct BatchRequest{Conversation* conversation;Bits payload,timestamp,request_id;};
 inline static int evaluations=0;inline static bool fail_evaluate=false,bad_last=false;
 bool active=false,pending=false,closed=false;uint64_t ticket=0;
 void authenticated_connection_ready(){assert(!active&&!closed);active=true;}
 Produced produce(Bits,Bits,Bits id){assert(active&&!pending&&!closed);pending=true;return{++ticket,Bits(32,255),std::move(id),1};}
 static std::vector<Produced> produce_batch(std::vector<BatchRequest> requests){
  ++evaluations;if(fail_evaluate)throw std::runtime_error("fixed batch failure");std::vector<Produced> result;
  for(auto&r:requests)result.push_back(r.conversation->produce(std::move(r.payload),std::move(r.timestamp),std::move(r.request_id)));
  if(bad_last)result.back().payload.pop_back();return result;
 }
 void authenticated_response_complete(uint64_t value){assert(pending&&value==ticket&&!closed);pending=false;}
 void close()noexcept{closed=true;}
};
using Registry=tls_mpc_worker::PrivateMuxRegistry<Bits,Conversation>;
struct Fixture {
 int burns=0,retains=0,checks=0,terminal=0;bool reject=false,fail_checkpoint=false;
 std::vector<unsigned char> ids;std::vector<Conversation*> owners;Registry registry;
 Fixture():registry({[&]{++burns;return Bits(64,static_cast<unsigned char>(burns));},
 [](Bits a,Bits b){for(size_t i=0;i<a.size();++i)a[i]&=b[i];return a;},
 [&](size_t,Bits id,Bits valid){assert(valid.size()==8);ids.push_back(id[0]);if(reject)throw std::runtime_error("fixed validity failure");},
 [&](Bits payload,size_t cap){assert(payload.size()==8*(cap+3));return uint64_t(++retains);},
 [&]{++checks;if(fail_checkpoint)throw std::runtime_error("fixed barrier failure");},[&]{++terminal;}},Bits(8,255)){
 Conversation::evaluations=0;Conversation::fail_evaluate=Conversation::bad_last=false;
 }
 uint64_t add(){auto value=std::make_unique<Conversation>();owners.push_back(value.get());return registry.admit(std::move(value),Bits(8,255));}
 uint64_t input(uint64_t owner){return registry.admit_input(owner,Bits(8),Bits(64),Bits(8,255));}
};
template<class F>void rejects(F&& f){bool caught=false;try{f();}catch(const std::exception&){caught=true;}assert(caught);}
int main(){
 {using namespace tls_mpc_worker;Request request{9,Opcode::mux_produce_batch,{2,0,1}};auto wire=encode_request(request);auto decoded=decode_request(wire);assert(decoded.sequence==9&&decoded.operation==Opcode::mux_produce_batch&&decoded.payload==request.payload);wire[0]=27;rejects([&]{decode_request(wire);});wire=encode_request(request);wire.pop_back();rejects([&]{decode_request(wire);});}

 {Fixture f;auto a=f.add(),b=f.add();auto a1=f.input(a),b1=f.input(b),a2=f.input(a),b2=f.input(b);f.registry.authenticated_connection_ready();
 auto out=f.registry.produce_batch({{a,a1},{b,b1}});assert(out.size()==2&&f.burns==2&&f.retains==2&&f.checks==1&&Conversation::evaluations==1);assert((f.ids==std::vector<unsigned char>{1,2}));
 assert(f.registry.authenticated_response_complete(1)==b);f.registry.produce(b,b2);assert(f.registry.authenticated_response_complete(0)==a);f.registry.produce(a,a2);assert(f.registry.authenticated_response_complete(1)==b);assert(f.registry.authenticated_response_complete(0)==a);assert(f.burns==4&&!f.terminal);}
 {Fixture f;auto a=f.add();auto a1=f.input(a),a2=f.input(a);f.registry.authenticated_connection_ready();rejects([&]{f.registry.produce_batch({{a,a1},{a,a2}});});assert(!f.burns&&!Conversation::evaluations&&f.terminal==1);}
 {Fixture f;auto a=f.add(),b=f.add();auto a1=f.input(a);f.registry.authenticated_connection_ready();rejects([&]{f.registry.produce_batch({{a,a1},{b,a1}});});assert(!f.burns&&!Conversation::evaluations&&f.terminal==1);}
 for(int failure=0;failure<4;++failure){Fixture f;auto a=f.add(),b=f.add();auto a1=f.input(a),b1=f.input(b);f.registry.authenticated_connection_ready();
 Conversation::fail_evaluate=failure==0;Conversation::bad_last=failure==1;f.reject=failure==2;f.fail_checkpoint=failure==3;
 rejects([&]{f.registry.produce_batch({{a,a1},{b,b1}});});assert(f.burns==2&&f.terminal==1);if(failure<3)assert(f.retains==0);else assert(f.retains==2&&f.checks==1);
 rejects([&]{f.registry.produce_batch({{a,a1},{b,b1}});});assert(f.burns==2);}
 {Fixture f;std::vector<std::pair<uint64_t,uint64_t>> requests;for(int i=0;i<4;++i){auto owner=f.add();requests.push_back({owner,f.input(owner)});}f.registry.authenticated_connection_ready();auto out=f.registry.produce_batch(requests);assert(out.size()==4&&f.burns==4&&f.checks==1&&Conversation::evaluations==1);for(int i=3;i>=0;--i)assert(f.registry.authenticated_response_complete(i)==requests[i].first);rejects([&]{f.registry.authenticated_response_complete(0);});}
}
