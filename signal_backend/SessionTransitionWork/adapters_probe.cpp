// Native compile/link only; candidate is not evaluated, opened or committed.
#include "NativeActiveSpqrReceive.h"
#include "NativeComputedDh.h"
#include "NativePrivateMessageMac.h"
#include "NativeNewDhReceive.h"
auto receive_method=&signal_mpc::NativeActiveSpqrReceive::prepare;
auto dh_method=&signal_mpc::NativeComputedDh::prepare;
auto mac_method=&signal_mpc::NativePrivateMessageMac::verify;
auto new_dh_method=&signal_mpc::NativeNewDhReceive::evaluate;
int main(){return 0;}
