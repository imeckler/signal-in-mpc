// Compile/link validation only; no runtime, sockets or secret inputs.
#include "NativeService.h"
#include "NativePayload.h"
#include "NativeUpgrade.h"
auto service_method=&signal_mpc::NativeService::evaluate;
auto payload_method=&signal_mpc::NativePayload::wrap;
auto after_inner_method=&signal_mpc::NativePayload::after_inner;
auto upgrade_method=&signal_mpc::NativeUpgrade::evaluate;
int main(){return 0;}
