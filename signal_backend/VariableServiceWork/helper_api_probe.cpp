// Compile/link only. main does not execute a runtime or acknowledge responses.
#include "PublicFixtureProducer.h"
void compile_public_fixture_api(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,
 const tls_mpc_worker::PinnedPrograms& pinned,unsigned party,const std::string& slot){
 auto public_bits=[&](const std::vector<unsigned char>& bytes){auto bits=worker.allocate(8*bytes.size());
  for(size_t i=0;i<bits.size();++i){bits[i][0]=tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key());}return bits;};
 signal_mpc::NativeVariableService service(machine,worker,pinned);
 signal_mpc::PublicVariableProducer<tls_mpc_worker::Bits> producer(public_bits,slot);
 auto produced=producer.produce([&](const auto& shape,tls_mpc_worker::Bits in){return service.evaluate(shape,std::move(in));},
  public_bits,public_bits(signal_mpc::PublicVariableFixture::timestamp()));
 (void)produced;
}
int main(){return 0;}
