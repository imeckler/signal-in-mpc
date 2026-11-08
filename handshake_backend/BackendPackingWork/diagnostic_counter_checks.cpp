#include "PublicProtocolMetrics.h"
#include <cassert>
#include <thread>
using namespace tls_public_diagnostics;
int main(){auto before=snapshot();
 {Scope online(Domain::field,Phase::online);sent_bytes(7);
  {Scope prep(Domain::binary,Phase::preprocessing);sent_bytes(11);{Scope nested(Domain::field,Phase::online);sent_bytes(13);}}
  sent_bytes(17);
 }
 try{Scope failure(Domain::binary,Phase::online);sent_bytes(19);throw 1;}catch(int){}
 std::thread child([]{sent_bytes(23);});child.join();
 assert(context.domain==Domain::unattributed&&context.phase==Phase::unattributed);
 auto after=snapshot();assert(after.bytes[4]-before.bytes[4]==24);assert(after.bytes[8]-before.bytes[8]==11);
 assert(after.bytes[5]-before.bytes[5]==13);assert(after.bytes[7]-before.bytes[7]==19);assert(after.bytes[0]-before.bytes[0]==23);
 uint64_t sum=0;for(unsigned i=0;i<9;++i)sum+=after.bytes[i]-before.bytes[i];assert(sum==90);
}
