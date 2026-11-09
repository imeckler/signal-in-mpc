#include "NativeSession.h"
#include "NativeConversation.h"
#include "MuxProviderCoordinator.h"
#include <cassert>
static void instantiate(tls_mpc_worker::Session& session,std::vector<signal_mpc::VariableShape> shapes,std::vector<tls_mpc_worker::Bits> inputs,std::vector<tls_mpc_worker::NativeConversation::BatchRequest> requests){
 auto result=session.evaluate_variable_batch(shapes,std::move(inputs));
 auto produced=tls_mpc_worker::NativeConversation::produce_batch(std::move(requests));
 (void)result;(void)produced;
}
int main(){
 signal_mpc::VariableShape shape(260,80,false,false);
 tls_mpc_worker::VariableBatchShape batch(shape,2);assert(batch.input_bits()==9776&&batch.output_bits()==21968);
 assert(batch.name()=="signal_private_variable_batch_2_signal_private_variable_conversation_260_80_0_0");
 for(size_t n:{0u,5u}){bool caught=false;try{tls_mpc_worker::VariableBatchShape bad(shape,n);}catch(...){caught=true;}assert(caught);}
}
