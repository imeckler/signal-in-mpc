// Source feasibility probe only. No parties or preprocessing are executed.
#include "NativeWorker.h"
#include "Protocols/ShuffleSacrifice.hpp"
#include <iostream>
int main(){
    OnlineOptions::singleton.security_parameter=128;
    try{ShuffleSacrifice check(5);(void)check;return 1;}
    catch(const std::runtime_error& error){
        tls_mpc_worker::public_require(std::string(error.what())=="shuffle sacrifice not implemented for more than 40-bit security","unexpected source guard");
        std::cout<<"{\"requested_statistical_security\":128,\"shuffle_sacrifice_supported\":false,\"guard_preserved\":true,\"native_parties\":false}\n";
    }
}
