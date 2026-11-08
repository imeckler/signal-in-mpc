// PUBLIC mock-bit host transaction ordering only. No crypto/MPC/durability claim.
#include "../VariableServiceWork/VariableSendStore.h"
#include <vector>
#include <iostream>
#include <filesystem>
#include <unistd.h>
using Bits=std::vector<unsigned char>;
int main(){char dir[]="/tmp/signal-checkpoint-XXXXXX";if(!mkdtemp(dir))return 1;unsigned checks=0;
 for(unsigned failure=0;failure<=3;++failure){signal_mpc::VariableShape shape(1,0,false,false);std::vector<unsigned> trace;
  signal_mpc::VariableSendStore<Bits> store(shape,Bits(shape.input_bytes()*8),std::string(dir)+"/slot"+std::to_string(failure));
  Bits id(64,1),timestamp(64,0),payload(8,0);bool returned=false;
  auto reserve=[&](uint64_t ticket,const Bits& call){trace.push_back(1);if(ticket!=1||call.size()!=shape.input_bytes()*8)throw std::runtime_error("bad intent");
   const auto at=shape.metadata_offset()+40;for(size_t i=0;i<64;++i)if(call[8*at+i]!=1)throw std::runtime_error("intent ID mismatch");if(failure==1)throw std::runtime_error("reserve failed");};
  auto eval=[&](const auto&,Bits call){trace.push_back(2);if(failure==2)throw std::runtime_error("eval failed");Bits out(shape.output_bytes()*8);out[0]=1;out[8*83]=1;return out;};
  auto commit=[&](uint64_t ticket,const Bits& next,const Bits& wire,const Bits& request){trace.push_back(3);
   if(ticket!=1||next.size()!=shape.input_bytes()*8||wire.size()!=8*(3+shape.frame_capacity())||request!=id||wire[0]!=1||wire[24]!=1)throw std::runtime_error("commit binding mismatch");
   if(failure==3)throw std::runtime_error("commit failed");};
  try{auto out=store.produce_with_checkpoint(payload,timestamp,id,eval,reserve,commit);returned=true;if(out.request_id!=id||out.payload[24]!=1)throw std::runtime_error("released wrong payload");}catch(const std::exception&){}
  if(returned!=(failure==0))throw std::runtime_error("transaction fail-open");++checks;
  std::vector<unsigned> expected=failure==1?std::vector<unsigned>{1}:failure==2?std::vector<unsigned>{1,2}:std::vector<unsigned>{1,2,3};
  if(trace!=expected)throw std::runtime_error("transaction ordering");++checks;
  bool second=false;try{store.produce_with_checkpoint(payload,timestamp,id,eval,reserve,commit);second=true;}catch(const std::exception&){}if(second)throw std::runtime_error("reuse after failure/pending");++checks;
 }
 std::filesystem::remove_all(dir);std::cout<<checks<<" private-store checkpoint ordering checks passed\n";
}
