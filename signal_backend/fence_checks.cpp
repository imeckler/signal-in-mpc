#include "PersistentSendFence.h"
#include <cassert>
#include <sys/wait.h>
#include <fstream>
#include <iostream>
using namespace signal_mpc;
template<class F>void rejects(F f){bool bad=false;try{f();}catch(const std::exception&){bad=true;}assert(bad);}
int main(int argc,char** argv){assert(argc==2);std::string dir=argv[1];
 auto path=dir+"/crashed";auto child=fork();assert(child>=0);
 if(child==0){PersistentSendFence fence(path);fence.reserve();_exit(0);}
 int status=0;assert(waitpid(child,&status,0)==child&&WIFEXITED(status)&&WEXITSTATUS(status)==0);
 rejects([&]{PersistentSendFence reused(path);});
 {PersistentSendFence fence(dir+"/normal");fence.reserve();fence.reserve();rejects([&]{PersistentSendFence duplicate(dir+"/normal");});}
 rejects([&]{PersistentSendFence restarted(dir+"/normal");});
 using Bits=std::vector<bool>;FencedSendStore<Bits> store(dir+"/store",Bits(181*8),{});
 size_t calls=0;SendShape shape(0,1,1,1,1,0,false,false);
 rejects([&]{store.produce(shape,Bits(8),[&](const SendShape&,Bits)->Bits{++calls;throw std::runtime_error("injected runtime loss");});});
 rejects([&]{store.produce(shape,Bits(8),[&](const SendShape&,Bits)->Bits{++calls;return {};});});assert(calls==1);
 rejects([&]{PersistentSendFence rollback(dir+"/store");});
 std::ifstream file(path,std::ios::binary);std::string bytes((std::istreambuf_iterator<char>(file)),{});
 assert(bytes.size()==22&&bytes.substr(0,14)=="SIGNAL-BURN-1\n");
 std::cout<<"crash/restart, concurrent slot, normal restart and failed-runtime rollback refused\n";
}
