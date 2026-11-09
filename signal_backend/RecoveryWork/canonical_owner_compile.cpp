// Compile-only candidate API coverage. No runtime admission claim.
#include "NativeCanonicalSendOwner.h"
#include "NativeRecordAdmission.h"
using namespace signal_mpc;
using namespace signal_mpc::recovery;
using Owned=tls_mpc_worker::Bits;
struct Tx {
 void reserve(const std::vector<VariableShape>&,const std::vector<NativeCanonicalSendOwner::Prestate>&){}
 void commit(const std::vector<VariableShape>&,const std::vector<NativeCanonicalSendOwner::Poststate>&){}
};
void exercise(NativeCanonicalSendOwner& owner,std::vector<NativeCanonicalSendOwner::Request> requests,Tx& tx){
 auto batch=NativeCanonicalSendOwner::produce_batch(std::move(requests),[](const std::vector<VariableShape>&,std::vector<Owned>){return std::vector<Owned>{};},tx);
 auto single=owner.produce(Owned{},Owned{},Owned{},tx);
 owner.response_complete(single.ticket);
}
