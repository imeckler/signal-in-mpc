#include "SocketCancellation.h"
#include <unistd.h>
#include <thread>
#include <vector>
#include <array>
#include <condition_variable>
#include <chrono>
#include <cassert>
using namespace tls_caught_failure;
int main(){
 {SocketRegistry registry;int fd[2];assert(socketpair(AF_UNIX,SOCK_STREAM,0,fd)==0);
  {SocketToken token(registry);token.arm(fd[0]);assert(registry.active()==1);
   bool rejected=false;try{SocketToken duplicate(registry);duplicate.arm(fd[0]);}catch(const std::exception&){rejected=true;}assert(rejected);
   SocketToken moved(std::move(token));assert(registry.active()==1);registry.cancel();registry.cancel();char c;assert(read(fd[1],&c,1)==0);
  }assert(registry.active()==0&&registry.cancelled());
  close(fd[0]);close(fd[1]);}
 {SocketRegistry registry;registry.cancel();int fd[2];assert(socketpair(AF_UNIX,SOCK_STREAM,0,fd)==0);
  bool rejected=false;try{SocketToken token(registry);token.arm(fd[0]);}catch(const std::exception&){rejected=true;}assert(rejected&&registry.active()==0);char c;assert(read(fd[1],&c,1)==0);close(fd[0]);close(fd[1]);}
 {SocketRegistry registry;std::array<std::array<int,2>,32> descriptors;std::vector<std::thread> workers;
  std::mutex mutex;std::condition_variable ready;unsigned count=0;
  for(auto& fd:descriptors)assert(socketpair(AF_UNIX,SOCK_STREAM,0,fd.data())==0);
  for(auto& fd:descriptors)workers.emplace_back([&registry,&mutex,&ready,&count,fd]{
    SocketToken token(registry);token.arm(fd[0]);{std::lock_guard lock(mutex);++count;ready.notify_one();}char c;assert(read(fd[0],&c,1)==0);
  });
  {std::unique_lock lock(mutex);assert(ready.wait_for(lock,std::chrono::seconds(2),[&]{return count==32;}));}
  assert(registry.active()==32);registry.cancel();for(auto& worker:workers)worker.join();assert(registry.active()==0);
  for(auto& fd:descriptors){close(fd[0]);close(fd[1]);}
 }
}
