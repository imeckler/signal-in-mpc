// No network or MPC: exercise descriptor/schedule/bytecode pin validation.
#include "PinnedPrograms.h"
#include <iostream>
int main(int argc,char** argv) {
    if(argc!=3) return 2;
    try {tls_mpc_worker::PinnedPrograms pinned(argv[1]);std::vector<FunctionArgument> args;pinned.verify_function(argv[2],args);std::cout<<"pinned closure accepted\n";return 0;}
    catch(const std::exception& e) {std::cerr<<e.what()<<"\n";return 1;}
}
