#include <cassert>
#include <thread>
#include <vector>
#include <atomic>
#include <chrono>
#include "Tools/WaitQueue.h"
int main(){
 {WaitQueue<int> q;q.push(42);int n=0;assert(q.pop(n)&&n==42);}
 {WaitQueue<int> q;q.push(42);q.stop();q.push(77);int n=-1;assert(!q.pop(n)&&n==-1);}
 {WaitQueue<int> q;std::atomic<unsigned> ready{0},finished{0};std::vector<std::thread> workers;
  for(unsigned i=0;i<32;++i)workers.emplace_back([&]{++ready;int n=-1;assert(!q.pop(n)&&n==-1);++finished;});
  while(ready!=32)std::this_thread::yield();
  // A signal with no value must not make pop touch an empty deque.
  for(unsigned i=0;i<1000;++i){q.lock();q.signal();q.unlock();}
  q.stop();q.stop();for(auto& w:workers)w.join();assert(finished==32);
 }
 {WaitQueue<int> q;std::thread w([&]{int n;assert(q.pop(n)&&n==19);});
  for(unsigned i=0;i<1000;++i){q.lock();q.signal();q.unlock();}q.push(19);w.join();q.stop();}
}
