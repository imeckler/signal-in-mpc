#include "EstablishedSendStore.h"
#include "PrivateGrpcRequest.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <sstream>
#include <vector>
using Bits=std::vector<bool>; // Public test bits only; production uses OwnedBits.
using Store=signal_mpc::EstablishedSendStore<Bits>;
Bits decode(const std::string& text){Bits b;for(size_t i=0;i<text.size();i+=2){auto c=std::stoul(text.substr(i,2),nullptr,16);for(int j=7;j>=0;--j)b.push_back((c>>j)&1);}return b;}
Bits sub(const Bits& x,size_t offset,size_t n){return Bits(x.begin()+offset*8,x.begin()+(offset+n)*8);}
void append(Bits& x,const Bits& y){x.insert(x.end(),y.begin(),y.end());}
template<class F>void rejects(F f){bool failed=false;try{f();}catch(const std::exception&){failed=true;}assert(failed);}
int main(int argc,char** argv){
 assert(argc==9);
 signal_mpc::SendShape shape(std::stoul(argv[1]),std::stoul(argv[2]),std::stoul(argv[3]),
  std::stoul(argv[4]),std::stoul(argv[5]),std::stoul(argv[6]),std::stoul(argv[7]),std::stoul(argv[8]));
 std::unique_ptr<Store> store;std::string line;size_t rows=0;
 Bits last_payload,last_state,last_addresses,last_output;
 while(std::getline(std::cin,line)){
  std::istringstream in(line);unsigned reuse;std::string raw_hex,out_hex;in>>reuse>>raw_hex>>out_hex;
  auto raw=decode(raw_hex),out=decode(out_hex);assert(raw.size()==shape.input_bytes()*8);assert(out.size()==shape.output_bytes()*8);
  last_output=out;
  const size_t chunk=shape.chunk_bytes();
  last_state=sub(raw,0,117);append(last_state,sub(raw,118+chunk,64));
  last_addresses=sub(raw,182+chunk+shape.plaintext_bytes(),shape.address_bytes());
  if(!reuse){
   auto state=sub(raw,0,117);append(state,sub(raw,118+chunk,64));
   store=std::make_unique<Store>(std::move(state),sub(raw,182+chunk+shape.plaintext_bytes(),shape.address_bytes()));
  }
  assert(store);
  auto payload=sub(raw,117,1+chunk);append(payload,sub(raw,182+chunk,shape.plaintext_bytes()));last_payload=payload;
  size_t calls=0;
  auto eval=[&](const signal_mpc::SendShape& requested,Bits assembled){
   ++calls;assert(requested.descriptor()==shape.descriptor());assert(assembled==raw);return out;
  };
  auto produced=store->produce(shape,payload,eval);assert(calls==1);assert(produced.wire==sub(out,73,shape.wire_bytes()));
  // Outstanding sends cannot derive again or release another wire.
  rejects([&]{store->produce(shape,payload,eval);});assert(calls==1);
  rejects([&]{store->transport_complete(produced.ticket+1);});
  store->transport_complete(produced.ticket);
  rejects([&]{store->transport_complete(produced.ticket);});
  ++rows;
 }
 assert(rows>0);
 // Runtime failure poisons the store and forbids reuse of the chain.
 size_t failures=0;
 auto broken=[&](const signal_mpc::SendShape&,Bits)->Bits{++failures;throw std::runtime_error("injected execution failure");};
 rejects([&]{store->produce(shape,last_payload,broken);});
 rejects([&]{store->produce(shape,last_payload,broken);});assert(failures==1);
 Store malformed(last_state,last_addresses);size_t bad_calls=0;
 auto short_output=[&](const signal_mpc::SendShape&,Bits)->Bits{++bad_calls;return {};};
 rejects([&]{malformed.produce(shape,last_payload,short_output);});
 rejects([&]{malformed.produce(shape,last_payload,short_output);});assert(bad_calls==1);
 Store mismatch(last_state,last_addresses);size_t mismatch_calls=0;
 auto unused=[&](const signal_mpc::SendShape&,Bits)->Bits{++mismatch_calls;return {};};
 rejects([&]{mismatch.produce(shape,{},unused);});assert(mismatch_calls==0);
 Store handoff(last_state,last_addresses);size_t retained=0;
 auto produce=[&](const signal_mpc::SendShape&,Bits){return last_output;};
 auto same=[](Bits b){return b;};
 auto retain=[&](Bits b)->uint64_t{++retained;assert(b==sub(last_output,73,shape.wire_bytes()));return 17;};
 assert(signal_mpc::produce_private_request(handoff,shape,last_payload,produce,same,same,retain)==17);
 assert(retained==1);
 Store failed_handoff(last_state,last_addresses);
 auto fail_retain=[](Bits)->uint64_t{throw std::runtime_error("injected TLS retain failure");};
 rejects([&]{signal_mpc::produce_private_request(failed_handoff,shape,last_payload,produce,same,same,fail_retain);});
 rejects([&]{failed_handoff.produce(shape,last_payload,produce);});
 rejects([]{signal_mpc::SendShape(1025,1,1,1,1,0,false,false);});
 rejects([]{signal_mpc::SendShape(0,1,1,1,1,1,false,false);});
 rejects([]{signal_mpc::SendShape(0,1,1,1,1,0,true,false);});
 std::cout<<rows<<" store transitions; pending/stale/failure checks passed\n";
}
