#include "NativeWorker.h"
#include "Tools/PublicProtocolMetrics.h"
// Public getter must instantiate against the actual patched processor types.
void diagnostic_usage(Machine<tls_mpc_worker::Share>& machine){auto usage=machine.public_function_usage();(void)usage;}
int main(){return 0;}
