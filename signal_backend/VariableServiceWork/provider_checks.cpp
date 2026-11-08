#include "PrivateProvider.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <vector>
using Bits=std::vector<unsigned char>;
struct UpgradeProfile{size_t input_bytes()const{return 36;}size_t output_bytes()const{return 17;}};
using Provider=signal_mpc::PrivateProvider<Bits,UpgradeProfile>;
static unsigned rejected_count=0;
template<class F>void rejected(F&& f){try{f();assert(false);}catch(const std::runtime_error&){++rejected_count;}}
int main(int argc,char**argv){assert(argc==2);signal_mpc::VariableShape shape(1,0,false,false);unsigned slot=0,calls=0;
 auto path=[&]{return std::string(argv[1])+"/provider-"+std::to_string(slot++);};
 auto make=[&]{return std::make_unique<Provider>(UpgradeProfile{},Bits(160,7),shape,Bits(8*shape.input_bytes(),3),path());};
 auto upgrade=[&](const auto&,Bits input){assert(input.size()==288);assert(input.front()==7&&input.back()==9);++calls;return Bits(136,11);};
 auto evaluate=[&](const auto&s,Bits input){assert(input.size()==8*s.input_bytes());++calls;return Bits(8*s.output_bytes(),0);};
 auto send=[&](Provider& p){return p.produce(Bits(8,1),Bits(64,2),evaluate);};
 auto activate=[&](Provider&p){auto output=p.upgrade(Bits(128,9),upgrade);assert(output==Bits(136,11));p.upgrade_complete();};
 {auto p=make();activate(*p);auto first=send(*p);assert(first.ticket==1&&first.payload.size()==8*(shape.frame_capacity()+3)&&first.request_id.size()==64);p->response_complete(first.ticket);
  auto second=send(*p);assert(second.ticket==2);p->response_complete(second.ticket);p->close();rejected([&]{send(*p);});}
 {auto p=make();rejected([&]{send(*p);});rejected([&]{p->upgrade(Bits(128,9),upgrade);});}
 {auto p=make();p->upgrade(Bits(128,9),upgrade);rejected([&]{send(*p);});rejected([&]{p->upgrade_complete();});}
 {auto p=make();activate(*p);rejected([&]{p->upgrade(Bits(128,9),upgrade);});rejected([&]{send(*p);});}
 {auto p=make();rejected([&]{p->upgrade_complete();});rejected([&]{p->upgrade(Bits(128,9),upgrade);});}
 {auto p=make();rejected([&]{p->upgrade(Bits(127,9),upgrade);});rejected([&]{p->upgrade(Bits(128,9),upgrade);});}
 {auto p=make();rejected([&]{p->upgrade(Bits(128,9),[](const auto&,Bits){return Bits(1);});});rejected([&]{p->upgrade_complete();});}
 {auto p=make();rejected([&]{p->upgrade(Bits(128,9),[](const auto&,Bits)->Bits{throw std::runtime_error("mock failure");});});rejected([&]{p->upgrade_complete();});}
 {auto p=make();activate(*p);auto first=send(*p);rejected([&]{p->response_complete(first.ticket+1);});rejected([&]{send(*p);});}
 {auto p=make();activate(*p);send(*p);rejected([&]{send(*p);});rejected([&]{p->response_complete(1);});}
 {auto p=make();activate(*p);rejected([&]{p->response_complete(1);});rejected([&]{send(*p);});}
 {auto p=make();activate(*p);rejected([&]{p->produce(Bits(7),Bits(64),evaluate);});rejected([&]{send(*p);});}
 {auto p=make();activate(*p);rejected([&]{p->produce(Bits(8),Bits(64),[](const auto&,Bits){return Bits(1);});});rejected([&]{send(*p);});}
 {auto p=make();activate(*p);rejected([&]{p->produce(Bits(8),Bits(64),[](const auto&,Bits)->Bits{throw std::runtime_error("mock failure");});});rejected([&]{send(*p);});}
 {auto s=path();{Provider p(UpgradeProfile{},Bits(160),shape,Bits(8*shape.input_bytes()),s);p.close();}
  rejected([&]{Provider p(UpgradeProfile{},Bits(160),shape,Bits(8*shape.input_bytes()),s);});}
 {rejected([&]{Provider p(UpgradeProfile{},Bits(159),shape,Bits(8*shape.input_bytes()),path());});}
 {auto p=make();rejected([&]{p->upgrade(Bits(128,9),[&](const auto&,Bits){rejected([&]{p->upgrade_complete();});return Bits(136);});});rejected([&]{p->upgrade_complete();});}
 {auto p=make();rejected([&]{p->upgrade(Bits(128,9),[&](const auto&,Bits){p->close();return Bits(136);});});rejected([&]{p->upgrade_complete();});}
 {auto p=make();activate(*p);rejected([&]{p->produce(Bits(8),Bits(64),[&](const auto&s,Bits){rejected([&]{p->response_complete(1);});return Bits(8*s.output_bytes());});});rejected([&]{send(*p);});}
 {auto p=make();activate(*p);rejected([&]{p->produce(Bits(8),Bits(64),[&](const auto&s,Bits){p->close();return Bits(8*s.output_bytes());});});rejected([&]{send(*p);});}
 {auto p=make();activate(*p);Bits id(64,5);
  auto output=p->produce_with_request_id(Bits(8),Bits(64),id,[&](const auto&s,Bits input){
   const auto offset=8*(s.metadata_offset()+40);
   assert(Bits(input.begin()+offset,input.begin()+offset+64)==id);
   return Bits(8*s.output_bytes(),0);
  });
  assert(output.request_id==id);p->response_complete(output.ticket);
  // Ordinary produce must use the committed selected next ID, not old/override.
  auto next=p->produce(Bits(8),Bits(64),[&](const auto&s,Bits input){
   const auto offset=8*(s.metadata_offset()+40);
   assert(Bits(input.begin()+offset,input.begin()+offset+64)==Bits(64,0));
   return Bits(8*s.output_bytes(),0);
  });assert(next.request_id==Bits(64,0));p->response_complete(next.ticket);
 }
 assert(rejected_count==39&&calls==16);std::cout<<"39 failclosed provider transitions; two-send lifecycle passed\n";
}
