#include "PublicSyntheticProducer.h"
#include <cassert>
#include <iostream>
using Bits=std::vector<bool>;
Bits decode(const std::string& s){Bits b;for(size_t i=0;i<s.size();i+=2){auto c=std::stoul(s.substr(i,2),nullptr,16);for(int j=7;j>=0;--j)b.push_back((c>>j)&1);}return b;}
Bits share(const std::vector<uint8_t>& x){Bits b;for(auto c:x)for(int j=7;j>=0;--j)b.push_back((c>>j)&1);return b;}
int main(){
 signal_mpc::PublicSyntheticProducer<Bits> producer;std::string input,output;size_t count=0;
 while(std::cin>>input>>output){
  auto want=decode(input),answer=decode(output);
  auto framed=producer.produce([&](const signal_mpc::SendShape& shape,Bits actual){assert(shape.input_bytes()==182);assert(actual==want);return answer;},share);
  assert(framed.size()==228*8);
  // Frame tail is exactly the actual shared circuit output wire.
  assert(Bits(framed.end()-72*8,framed.end())==Bits(answer.begin()+73*8,answer.end()));
  producer.transport_complete();++count;
 }
 assert(count==3);
 size_t calls=0;auto failed=[&](const signal_mpc::SendShape&,Bits)->Bits{++calls;throw std::runtime_error("fixture eval failure");};
 auto rejects=[](auto operation){bool bad=false;try{operation();}catch(const std::exception&){bad=true;}assert(bad);};
 rejects([&]{producer.produce(failed,share);});assert(calls==0);
 signal_mpc::PublicSyntheticProducer<Bits> broken;
 rejects([&]{broken.produce(failed,share);});rejects([&]{broken.produce(failed,share);});assert(calls==1);
 std::cout<<"three synthetic producer state/frame transitions passed;228 bytes each\n";
}
