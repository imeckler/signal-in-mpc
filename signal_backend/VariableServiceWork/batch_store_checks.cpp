// PUBLIC mock bits: transaction ordering/ownership only, not cryptography.
#include "VariableSendBatch.h"
#include <filesystem>
#include <iostream>
#include <unistd.h>
using Bits=std::vector<unsigned char>;using Store=signal_mpc::VariableSendStore<Bits>;using Request=signal_mpc::BatchSendRequest<Bits>;
static void require(bool ok){if(!ok)throw std::runtime_error("batch store regression");}
template<class F>static void rejected(F f){bool ok=false;try{f();}catch(const std::exception&){ok=true;}require(ok);}
int main(){char dir[]="/tmp/signal-batch-store-XXXXXX";require(mkdtemp(dir));unsigned checks=0,slot=0;
 auto new_store=[&](const signal_mpc::VariableShape& shape,unsigned mark){Bits state(shape.input_bytes()*8,mark);return std::make_unique<Store>(shape,std::move(state),std::string(dir)+"/"+std::to_string(slot++));};
 for(size_t batch:{size_t(1),size_t(2),size_t(4),size_t(8)})for(unsigned failure=0;failure<7;++failure){
  signal_mpc::VariableShape shape(1,0,false,false);std::vector<std::unique_ptr<Store>> stores;std::vector<Request> requests;std::vector<unsigned> trace;
  for(size_t i=0;i<batch;++i){stores.push_back(new_store(shape,i+1));requests.push_back({stores.back().get(),Bits(8,11+i),Bits(64,31+i),Bits(64,71+i)});}
  auto reserve=[&](const auto& shapes,const std::vector<Store::Staged>& staged){trace.push_back(1);require(staged.size()==batch&&shapes.size()==batch);
   for(size_t i=0;i<batch;++i){require(staged[i].ticket()==1&&staged[i].request_id()==Bits(64,71+i));const auto& input=staged[i].input();require(input.size()==shape.input_bytes()*8&&input[0]==i+1&&input[8*(shape.metadata_offset()+40)]==71+i);rejected([&]{stores[i]->response_complete(1);});}
   if(failure==1)throw std::runtime_error("reserve failure");};
  auto evaluate=[&](const auto& shapes,std::vector<Bits> inputs){trace.push_back(2);require(inputs.size()==batch&&shapes.size()==batch);if(failure==2)throw std::runtime_error("eval failure");
   std::vector<Bits> outputs;for(size_t i=0;i<batch;++i){require(inputs[i][0]==i+1);Bits out(shape.output_bytes()*8,i+17);out[0]=255;outputs.push_back(std::move(out));}
   if(failure==3)outputs.pop_back();if(failure==4)outputs.back().pop_back();return outputs;};
  auto commit=[&](const auto& shapes,const std::vector<Store::Candidate>& candidates){trace.push_back(3);require(candidates.size()==batch&&shapes.size()==batch);
   for(size_t i=0;i<batch;++i){require(candidates[i].ticket()==1&&candidates[i].next_state().size()==shape.input_bytes()*8&&candidates[i].request_id()==Bits(64,71+i)&&candidates[i].payload()[0]==255&&candidates[i].payload()[24]==i+17);rejected([&]{stores[i]->response_complete(1);});}
   if(failure==5)throw std::runtime_error("commit failure");if(failure==6)stores.back()->close();};
  bool returned=false;std::vector<Store::Produced> result;
  try{result=signal_mpc::produce_batch_with_checkpoint(std::move(requests),reserve,evaluate,commit);returned=true;}catch(const std::exception&){}
  require(returned==(failure==0));++checks;
  require(trace==(failure==1?std::vector<unsigned>{1}:failure==2||failure==3||failure==4?std::vector<unsigned>{1,2}:std::vector<unsigned>{1,2,3}));++checks;
  if(returned){require(result.size()==batch);for(size_t i=0;i<batch;++i){require(result[i].ticket==1&&result[i].request_id==Bits(64,71+i));stores[i]->response_complete(1);}++checks;}
  else for(auto& store:stores){rejected([&]{store->stage(Bits(8),Bits(64),Bits(64));});++checks;}
 }
 signal_mpc::VariableShape shape(1,0,false,false);
 {auto store=new_store(shape,1);std::vector<Request> requests;requests.push_back({store.get(),Bits(8),Bits(64),Bits(64)});requests.push_back({store.get(),Bits(8),Bits(64),Bits(64)});
  rejected([&]{signal_mpc::produce_batch_with_checkpoint(std::move(requests),[](const auto&,const auto&){},[](const auto&,auto){return std::vector<Bits>{};},[](const auto&,const auto&){});});rejected([&]{store->stage(Bits(8),Bits(64),Bits(64));});++checks;}
 {auto one=new_store(shape,1),two=new_store(shape,2);auto a=one->stage(Bits(8),Bits(64),Bits(64));auto b=two->stage(Bits(8),Bits(64),Bits(64));auto input=a.take_input();(void)input;rejected([&]{a.take_input();});rejected([&]{two->preview(std::move(a),Bits(shape.output_bytes()*8));});one->close();rejected([&]{b.take_input();});++checks;}
 {auto store=new_store(shape,1);auto staged=store->stage(Bits(8),Bits(64),Bits(64));auto input=staged.take_input();(void)input;auto candidate=store->preview(std::move(staged),Bits(shape.output_bytes()*8));auto produced=store->install(std::move(candidate));(void)produced;rejected([&]{store->install(std::move(candidate));});++checks;}
 {auto store=new_store(shape,1);auto staged=store->stage(Bits(8),Bits(64),Bits(64));store.reset();rejected([&]{staged.take_input();});++checks;}
 {auto one=new_store(shape,1),two=new_store(shape,2);std::vector<Request> requests;
  requests.push_back({one.get(),Bits(8),Bits(64),Bits(64,41)});requests.push_back({two.get(),Bits(8),Bits(64),Bits(64,42)});
  auto evaluate=[&](const auto& shapes,std::vector<Bits> inputs){require(shapes.size()==inputs.size());std::vector<Bits> out;for(size_t i=0;i<inputs.size();++i)out.push_back(Bits(shape.output_bytes()*8,1));return out;};
  auto result=signal_mpc::produce_batch_with_checkpoint(std::move(requests),[](const auto&,const auto&){},evaluate,[](const auto&,const auto&){});
  one->response_complete(result[0].ticket);std::vector<Request> next;next.push_back({one.get(),Bits(8),Bits(64),Bits(64,43)});
  auto second=signal_mpc::produce_batch_with_checkpoint(std::move(next),[](const auto&,const auto&){},evaluate,[](const auto&,const auto&){});require(second.size()==1&&second[0].ticket==2);
  two->response_complete(result[1].ticket);one->response_complete(second[0].ticket);++checks;
 }
 {auto store=new_store(shape,1);{auto abandoned=store->stage(Bits(8),Bits(64),Bits(64));}(void)0;rejected([&]{store->response_complete(1);});rejected([&]{store->stage(Bits(8),Bits(64),Bits(64));});++checks;}
 std::filesystem::remove_all(dir);std::cout<<checks<<" staged batch-store checks passed\n";
}
