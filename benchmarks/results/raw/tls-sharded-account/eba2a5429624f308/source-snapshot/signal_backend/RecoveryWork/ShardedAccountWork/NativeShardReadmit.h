#pragma once
#include "NativeShardCapture.h"
#include "NativeShardResume.h"
#include "NativeShardRoute.h"
#include "../ImportV2Work/RawFieldReadmitV2.h"
#include "../../../handshake_backend/SessionWork/NativeLifecycle.h"
#include "Protocols/Opener.h"
namespace signal_mpc::recovery::sharded {
// Checked active-working-set readmission, never a public/RPC share importer.
class NativeShardReadmit {
 using Bits=tls_mpc_worker::Bits;
 struct Completion {size_t& count;~Completion(){++count;}};
 struct Helper {Completion done;import_v2::RawFieldReadmitV2 input;Helper(size_t& count,Player& player):done{count},input(player){}};
 static Bits copy(const Bits& b){return{b.begin(),b.end()};}
 static Bits slice(const Bits& b,size_t offset,size_t count){require((offset+count)*8<=b.size(),"readmit shard slice");return{b.begin()+offset*8,b.begin()+(offset+count)*8};}
public:
 struct Raw {uint64_t key;NativeShardCapture::Quarantine quarantine;uint64_t send_generation;};
 struct Imported {Bits global,validity;std::map<size_t,Bits> conversations;std::map<size_t,NativeShardResume::Pending> pending;std::map<size_t,unsigned> routing;uint64_t import_host,retirement_host;size_t helpers_destroyed;};
 static Imported run(std::vector<Raw> raw,Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned){
  using tls_mpc_worker::ErasedHostCall;require(!ErasedHostCall::active()&&raw.size()>=2&&raw.size()<=5,"shard readmission host/working set");
  std::optional<Imported> result;size_t destroyed=0;uint64_t imported=0,retired=0;Bits flat;
  std::map<size_t,std::pair<Bits,Bits>> private_routes;
  bool success=ErasedHostCall::run([&]{imported=ErasedHostCall::generation();try{result.emplace();
   {Helper helper(destroyed,machine.get_player());
    for(size_t index=0;index<raw.size();++index){auto& item=raw[index];require((index==0?item.key==0:item.key>0)&&item.quarantine.values.bit_count()==(item.key?12611:8306)*8,"shard readmission dimensions");require(index==0||raw[index-1].key<item.key,"shard readmission canonical key order");flat.clear();flat.reserve(item.quarantine.values.bit_count());
     for(size_t offset=0;offset<item.quarantine.values.bit_count();offset+=4096){size_t count=std::min<size_t>(4096,item.quarantine.values.bit_count()-offset);SecretBytes local(count*16);std::memcpy(local.data(),item.quarantine.values.local_bytes().data()+offset*16,count*16);auto domain=item.quarantine.archive_domain;domain.bit_count=count;auto bits=helper.input.values_candidate(QuarantinedEvaluations(std::move(local)),domain,worker);flat.insert(flat.end(),std::make_move_iterator(bits.begin()),std::make_move_iterator(bits.end()));}
     item.quarantine.values=QuarantinedEvaluations(SecretBytes(0));if(item.key)require(result->conversations.emplace(item.key-1,std::move(flat)).second,"duplicate imported shard");else result->global=std::move(flat);
    }
   }
   require(destroyed==1,"shard import helper destruction");
   result->validity=NativeShardValidation::evaluate(false,copy(result->global),{},machine,worker,pinned);
   auto combine=[&](Bits flag){flag.insert(flag.end(),result->validity.begin(),result->validity.end());result->validity=worker.binary("tls-provider-validity",std::move(flag),8);};
   for(size_t i=1;i<raw.size();++i){auto slot=raw[i].key-1;auto& body=result->conversations.at(slot);combine(NativeShardValidation::evaluate(true,copy(result->global),body,machine,worker,pinned));
    std::vector<unsigned char> bytes(8);auto n=raw[i].send_generation;for(int k=7;k>=0;--k){bytes[k]=n&255;n>>=8;}auto generation=worker.allocate(64);for(size_t bit=0;bit<64;++bit)generation[bit][0]=tls_mpc_worker::Bit::constant((bytes[bit/8]>>(7-bit%8))&1,machine.get_player().my_num(),machine.get_bit_mac_key(),1);
    auto route=NativeShardRoute::evaluate(raw[i].send_generation?(raw[i].send_generation-1)%4:0,slice(body,7367,5240),slice(body,12607,4),generation,copy(result->validity),machine,worker,pinned);combine(copy(route.validity));private_routes.emplace(slot,std::make_pair(std::move(route.pending),std::move(route.blocked)));result->pending.emplace(slot,NativeShardResume::Pending{std::move(route.validity),std::move(route.typed_payload),std::move(route.expected_id)});
   }
   Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());opener.init_open();opener.prepare_open(result->validity.front()[0]);opener.exchange();bool valid=opener.finalize_open().get()==1;opener.Check();require(valid,"shard computed admission rejected");
   // Only after whole-account validity is authenticated do we disclose the
   // documented idle/pending/blocked routing metadata, never IDs or bodies.
   Opener<tls_mpc_worker::Bit> routes(machine.get_player(),machine.get_bit_mac_key());routes.init_open();for(auto& [slot,flags]:private_routes){routes.prepare_open(flags.first.front()[0]);routes.prepare_open(flags.second.front()[0]);}routes.exchange();for(auto& [slot,flags]:private_routes){bool pending=routes.finalize_open().get()==1,blocked=routes.finalize_open().get()==1;require(!(pending&&blocked),"inconsistent shard routing");result->routing.emplace(slot,blocked?2:pending?1:0);if(!pending)result->pending.erase(slot);}routes.Check();private_routes.clear();
  }catch(...){flat.clear();private_routes.clear();result.reset();raw.clear();throw;}});
  require(success&&result&&destroyed==1&&ErasedHostCall::completed(imported),"shard import completion failed");raw.clear();
  bool renewed=ErasedHostCall::run([&]{tls_mpc_worker::NativeLifecycle lifecycle(machine);lifecycle.renew_epoch();retired=ErasedHostCall::generation();require(!lifecycle.application_allowed(),"shard import retirement barrier bypass");});
  require(renewed&&retired>imported&&ErasedHostCall::completed(retired),"shard retirement completion failed");result->import_host=imported;result->retirement_host=retired;result->helpers_destroyed=destroyed;return std::move(*result);
 }
};
}
