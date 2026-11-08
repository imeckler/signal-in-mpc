// Compile/link validation only; never starts a runtime or opens data.
#include "NativeWorker.h"
#include "PublicSyntheticProducer.h"
using NativeBits=tls_mpc_worker::Bits;
NativeBits instantiate_fixture(tls_mpc_worker::Worker& worker,
    std::function<NativeBits(const std::vector<uint8_t>&)> constants){
 signal_mpc::PublicSyntheticProducer<NativeBits> producer;
 auto framed=producer.produce([&](const signal_mpc::SendShape& shape,NativeBits bits){
  return worker.signal(shape,std::move(bits));},constants);
 producer.transport_complete();return framed;
}
int main(){return 0;}
