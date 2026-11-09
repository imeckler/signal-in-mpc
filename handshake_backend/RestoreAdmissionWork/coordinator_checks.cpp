#include "CoordinatedConversation.h"
#include "PrivateRequestCursor.h"
#include "../WebSocketWork/PrivateMuxRegistry.h"
#include <cassert>
#include <filesystem>
using Bits=std::vector<unsigned char>;
Bits id(unsigned n){Bits b(64);b.back()=n;return b;}
template<class F>void rejects(F f){bool threw=false;try{f();}catch(...){threw=true;}assert(threw);}
struct Collective {void require_local_success(bool success){if(!success)throw std::runtime_error("local failure");}};
struct Session {
 tls_mpc_worker::PrivateRequestCursor<Bits> cursor;unsigned evals=0;
 template<class C>void commit_private_request_ids(C c){cursor.commit_pending(c);}
 Bits reserve(){return cursor.reserve([](Bits b){++b.back();return b;});}
 Bits evaluate_variable(const signal_mpc::VariableShape& s,Bits){assert(cursor.committed());++evals;return Bits(8*s.output_bytes(),255);}
 std::vector<Bits> evaluate_variable_batch(const std::vector<signal_mpc::VariableShape>& s,std::vector<Bits> in){assert(s.size()==in.size());std::vector<Bits> out;for(size_t i=0;i<s.size();++i)out.push_back(evaluate_variable(s[i],std::move(in[i])));return out;}
};
using Conversation=tls_mpc_worker::CoordinatedConversation<Bits,Session,Collective>;
using Registry=tls_mpc_worker::PrivateMuxRegistry<Bits,Conversation>;
struct Account:tls_mpc_worker::DurableConversationHooksT<Bits>{
 unsigned& disk;bool fail_after_reserve=false,closed=false;unsigned reserves=0,binds=0,commits=0,acks=0;
 std::vector<unsigned> frozen_ids,retained_outbox_ids;std::vector<Bits> states;
 explicit Account(unsigned& disk):disk(disk){}
 void reserve(const std::vector<size_t>& slots,const std::vector<signal_mpc::VariableShape>& shapes,const std::vector<Store::Staged>& staged,const Bits& current,const Bits& final,uint64_t lease)override{
  assert(!closed&&lease&&slots.size()==staged.size()&&shapes.size()==staged.size()&&current==id(disk));++reserves;
  for(auto& s:staged){assert(!s.input().empty());frozen_ids.push_back(s.request_id().back());}
  assert(final==id(disk+staged.size()));disk=final.back(); // Simulated whole-account Reserve certificate.
  if(fail_after_reserve)throw std::runtime_error("injected after certificate before cursor install");
 }
 std::vector<Bits> bind(const std::vector<size_t>& slots,const std::vector<signal_mpc::VariableShape>& shapes,std::vector<Bits> outputs)override{
  assert(!closed&&reserves>binds&&slots.size()==outputs.size()&&shapes.size()==outputs.size());++binds;return outputs;
 }
 void commit(const std::vector<size_t>& slots,const std::vector<signal_mpc::VariableShape>&,const std::vector<Store::Candidate>& candidates)override{
  assert(!closed&&binds>commits&&slots.size()==candidates.size());++commits;
  for(auto& c:candidates){states.push_back(c.next_state());retained_outbox_ids.push_back(c.request_id().back());}
 }
 void response_complete(size_t,uint64_t ticket)override{assert(!closed&&ticket);++acks;}
 void close()noexcept override{closed=true;}
};
struct Fixture{
 Session session;Collective collective;signal_mpc::VariableShape shape{260,0,false,false};std::shared_ptr<Account> account;
 std::filesystem::path dir;Registry registry;unsigned retained=0;std::vector<size_t> slots;
 Fixture(unsigned& disk,const std::filesystem::path& directory):account(std::make_shared<Account>(disk)),dir(directory),registry({
  [&]{return session.reserve();},[](Bits a,Bits b){for(size_t i=0;i<a.size();++i)a[i]&=b[i];return a;},
  [&](size_t slot,Bits,Bits){slots.push_back(slot);},[&](Bits,size_t){assert(account->commits&&session.cursor.committed());return uint64_t(++retained);},
  [&]{assert(session.cursor.committed());},[]{}},Bits(8,255)){session.cursor.initialize(id(disk),true);}
 uint64_t add(size_t slot){return registry.admit(std::make_unique<Conversation>(session,collective,shape,Bits(shape.input_bytes()*8), (dir/std::to_string(slot)).string(),account,slot),Bits(8,255));}
 uint64_t input(uint64_t owner){return registry.admit_input(owner,Bits(8),Bits(64),Bits(8,255));}
};
int main(int argc,char**argv){assert(argc==2);std::filesystem::path root(argv[1]);std::filesystem::create_directories(root);unsigned disk=30;std::vector<unsigned> old_outbox;
 {Fixture f(disk,root);auto a=f.add(0),b=f.add(1);auto ai=f.input(a),bi=f.input(b);f.registry.authenticated_connection_ready();auto receipts=f.registry.produce_batch({{a,ai},{b,bi}});
  assert(receipts.size()==2&&disk==32&&f.account->reserves==1&&f.account->binds==1&&f.account->commits==1&&f.session.evals==2);
  assert(f.account->frozen_ids==std::vector<unsigned>({30,31}));assert(f.registry.authenticated_response_complete(1)==b);assert(f.registry.authenticated_response_complete(0)==a);
  old_outbox=f.account->retained_outbox_ids;assert(old_outbox==std::vector<unsigned>({30,31}));rejects([&]{f.registry.authenticated_response_complete(0);});}
 auto second=root/"restart";std::filesystem::create_directories(second);
 {Fixture f(disk,second);auto a=f.add(0),b=f.add(1);auto ai=f.input(a),bi=f.input(b);f.registry.authenticated_connection_ready();f.account->fail_after_reserve=true;
  rejects([&]{f.registry.produce_batch({{a,ai},{b,bi}});});assert(disk==34&&f.session.evals==0&&f.retained==0&&f.account->closed);
  rejects([&]{f.registry.produce(a,ai);});assert(disk==34);}
 auto third=root/"restart2";std::filesystem::create_directories(third);
 {Fixture f(disk,third);auto a=f.add(0),ai=f.input(a);f.registry.authenticated_connection_ready();f.registry.produce(a,ai);
  assert(f.account->frozen_ids==std::vector<unsigned>({34})&&disk==35&&old_outbox==std::vector<unsigned>({30,31}));}
}
