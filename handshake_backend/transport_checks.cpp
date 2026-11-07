// Real stream I/O over unnamed local socketpairs. No TCP listener, external
// connection, TLS keys, or MPC party is created by these tests.
#include "TcpRecords.h"
#include <thread>
#include <cassert>
#include <functional>
#include <iostream>
using namespace tls_mpc_worker;
static bool rejected(const std::function<void()>& f){try{f();return false;}catch(const std::runtime_error&){return true;}}
static PublicBytes record(size_t n){PublicBytes b{23,3,3,uint8_t(n>>8),uint8_t(n)};for(size_t i=0;i<n;++i)b.push_back(i%256);return b;}
static void pair(int (&fds)[2]){assert(::socketpair(AF_UNIX,SOCK_STREAM,0,fds)==0);}
static void write_all(int fd,const PublicBytes& bytes,size_t chunk){size_t i=0;while(i<bytes.size()){auto n=::write(fd,bytes.data()+i,std::min(chunk,bytes.size()-i));assert(n>0);i+=n;}}
int main(){
 size_t cases=0;
 for(size_t n:{size_t(0),size_t(1),size_t(16384),size_t(16640)})for(size_t chunk:{size_t(1),size_t(7),size_t(65536)}){
  int fds[2];pair(fds);TcpRecords transport(fds[0]);auto expected=record(n);
  std::thread writer([&]{write_all(fds[1],expected,chunk);auto next=record(3);write_all(fds[1],next,chunk);::close(fds[1]);});
  assert(transport.receive()==expected);assert(transport.receive()==record(3));assert(rejected([&]{transport.receive();}));writer.join();++cases;
 }
 for(auto wire:{PublicBytes{},PublicBytes{23,3},PublicBytes{23,3,3,0,4,1},PublicBytes{23,3,3,65,1}}){
  int fds[2];pair(fds);TcpRecords transport(fds[0]);write_all(fds[1],wire,1);::close(fds[1]);assert(rejected([&]{transport.receive();}));++cases;
 }
 for(size_t n:{size_t(0),size_t(1),size_t(16640)}){
  int fds[2];pair(fds);TcpRecords transport(fds[0]);auto expected=record(n);PublicBytes received(expected.size());
  std::thread reader([&]{size_t i=0;while(i<received.size()){auto count=::read(fds[1],received.data()+i,std::min(size_t(3),received.size()-i));assert(count>0);i+=count;}::close(fds[1]);});
  transport.send(expected);reader.join();assert(received==expected);++cases;
 }
 {int fds[2];pair(fds);TcpRecords transport(fds[0]);assert(rejected([&]{transport.send({23,3,3,0,1});}));::close(fds[1]);++cases;}
 for(size_t n:{size_t(0),size_t(1),size_t(32)}) {
  auto expected=record(n);
  for(size_t cut=0;cut<expected.size();++cut) {
   int fds[2];pair(fds);TcpRecords transport(fds[0]);
   assert(transport.poll_receive().empty());
   write_all(fds[1],PublicBytes(expected.begin(),expected.begin()+cut),3);
   assert(transport.poll_receive().empty());
   // A partial inbound record must not block sending in the other direction.
   auto outgoing=record(2);transport.send(outgoing);PublicBytes got(outgoing.size());
   assert(::read(fds[1],got.data(),got.size())==static_cast<ssize_t>(got.size()));assert(got==outgoing);
   write_all(fds[1],PublicBytes(expected.begin()+cut,expected.end()),3);
   assert(transport.poll_receive()==expected);assert(transport.poll_receive().empty());
   ::close(fds[1]);assert(rejected([&]{transport.poll_receive();}));++cases;
  }
 }
 {int fds[2];pair(fds);TcpRecords transport(fds[0]);auto first=record(3),second=record(4);
  auto both=first;both.insert(both.end(),second.begin(),second.end());write_all(fds[1],both,50);
  assert(transport.poll_receive()==first);assert(transport.poll_receive()==second);::close(fds[1]);++cases;}
 for(auto wire:{PublicBytes{23,3},PublicBytes{23,3,3,0,4,1},PublicBytes{23,3,3,65,1}}) {
  int fds[2];pair(fds);TcpRecords transport(fds[0]);write_all(fds[1],wire,1);::close(fds[1]);
  assert(rejected([&]{transport.poll_receive();}));++cases;
 }
 std::cout<<cases<<" local-stream framing/fragmentation/EOF/send cases passed; no TCP or MPC execution\n";
}
