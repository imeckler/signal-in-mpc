#include "PrivateRequestCursor.h"
#include "../WebSocketWork/PrivateMuxRegistry.h"
#include <vector>
#include <cassert>
#include <functional>
using Bits=std::vector<unsigned char>;
using Cursor=tls_mpc_worker::PrivateRequestCursor<Bits>;
Bits id(unsigned n){Bits b(64);b.back()=n;return b;}
template<class F>void rejects(F f){bool threw=false;try{f();}catch(...){threw=true;}assert(threw);}
auto next=[](Bits x){++x.back();return x;};
struct Conversation{
 struct Produced{uint64_t ticket;Bits payload,request_id;size_t capacity;};
 bool active=false,closed=false;uint64_t ticket=0;std::vector<unsigned>* released;std::function<void()> reserve;
 Conversation(std::vector<unsigned>& r,std::function<void()> reserve):released(&r),reserve(std::move(reserve)){}
 void authenticated_connection_ready(){active=true;}
 Produced produce(Bits,Bits,Bits request){assert(active&&!closed);reserve();released->push_back(request.back());return{++ticket,Bits(32,255),request,1};}
 void authenticated_response_complete(uint64_t t){assert(t==ticket&&!closed);}
 void close()noexcept{closed=true;}
};
using Registry=tls_mpc_worker::PrivateMuxRegistry<Bits,Conversation>;
struct Fixture{
 Cursor cursor;unsigned& disk;std::vector<unsigned>& released;bool fail_commit=false;int terminals=0;
 Registry registry;
 Fixture(unsigned& disk,std::vector<unsigned>& released):disk(disk),released(released),registry({
  [&]{return cursor.reserve(next);},
  [](Bits a,Bits b){for(size_t i=0;i<a.size();++i)a[i]&=b[i];return a;},
  [](size_t,Bits,Bits){},[](Bits,size_t){return uint64_t(1);},[]{},[&]{++terminals;}},Bits(8,255)){
  cursor.initialize(id(disk),true);
 }
 uint64_t add(){return registry.admit(std::make_unique<Conversation>(released,[&]{cursor.commit_pending([&](const Bits& old,const Bits& successor,uint64_t,size_t count){assert(old.back()==disk&&count==1);disk=successor.back();if(fail_commit)throw std::runtime_error("uncertain durable write");});}),Bits(8,255));}
 uint64_t input(uint64_t owner){return registry.admit_input(owner,Bits(8),Bits(64),Bits(8,255));}
};
int main(){
 {Cursor c;rejects([&]{c.reserve(next);});rejects([&]{c.initialize(id(1));});}
 {Cursor c;c.initialize(id(2));assert(c.reserve(next)==id(2));rejects([&]{c.initialize(id(2));});rejects([&]{c.reserve(next);});}
 {Cursor c;rejects([&]{c.initialize(Bits(63));});rejects([&]{c.initialize(id(2));});}
 {Cursor c;c.initialize(id(3));rejects([&]{c.reserve([](Bits){return Bits(63);});});rejects([&]{c.reserve(next);});}
 {Cursor c;c.initialize(id(3),true);c.reserve(next);rejects([&]{c.commit_pending([&](const Bits&,const Bits&,uint64_t,size_t){c.close();});});rejects([&]{c.reserve(next);});}
 {Cursor c;c.initialize(id(3),true);c.reserve(next);rejects([&]{c.commit_pending([&](const Bits&,const Bits&,uint64_t,size_t){rejects([&]{c.reserve(next);});});});}
 {Cursor c;c.initialize(id(20),true);assert(c.reserve(next)==id(20));assert(c.reserve(next)==id(21));assert(!c.committed());int commits=0;
  c.commit_pending([&](const Bits& current,const Bits& final,uint64_t lease,size_t count){assert(current==id(20)&&final==id(22)&&lease==1&&count==2);++commits;});assert(c.committed()&&commits==1);
  assert(c.reserve(next)==id(22));c.commit_pending([&](const Bits&,const Bits& final,uint64_t lease,size_t count){assert(final==id(23)&&lease==2&&count==1);});}
 // Real mux registry path: persist/burn before producer invocation; reordered
 // independent response slots don't roll back the connection-global cursor.
 unsigned disk=10;std::vector<unsigned> released;
 {Fixture f(disk,released);auto a=f.add(),b=f.add();auto ai=f.input(a),bi=f.input(b);f.registry.authenticated_connection_ready();
  f.registry.produce(a,ai);f.registry.produce(b,bi);assert(disk==12&&released==std::vector<unsigned>({10,11}));
  assert(f.registry.authenticated_response_complete(1)==b);assert(f.registry.authenticated_response_complete(0)==a);
  rejects([&]{f.registry.authenticated_response_complete(1);});assert(disk==12);}
 // Simulated restart from persisted cursor: unresolved old outbox IDs10/11 are
 // not reallocated, regardless of new transport or dropped host handles.
 {Fixture f(disk,released);auto a=f.add(),ai=f.input(a);f.registry.authenticated_connection_ready();f.registry.produce(a,ai);assert(disk==13&&released.back()==12);}
 {Fixture f(disk,released);auto a=f.add(),ai=f.input(a);f.registry.authenticated_connection_ready();f.fail_commit=true;
  rejects([&]{f.registry.produce(a,ai);});assert(disk==14&&released.back()==12&&f.terminals==1);
  rejects([&]{f.registry.produce(a,ai);});assert(disk==14);}
 {Fixture f(disk,released);auto a=f.add(),ai=f.input(a);f.registry.authenticated_connection_ready();f.registry.produce(a,ai);assert(disk==15&&released.back()==14);}
}
