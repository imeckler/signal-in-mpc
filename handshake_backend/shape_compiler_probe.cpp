// No MPC/network. Exercise the actual spawn, pin-extension, and ordering path.
#include "ShapeCompiler.h"
#include <iostream>
int main(int argc,char** argv) {
    if(argc!=4)return 2;
    try {
        tls_mpc_worker::PinnedPrograms pinned(argv[1]);
        size_t size=std::stoul(argv[2]),agreements=0;
        auto descriptor=tls_mpc_worker::ShapeCompiler::descriptor(size);
        tls_mpc_worker::ShapeCompiler compiler(pinned,[&](size_t observed,const tls_mpc_worker::PublicBytes& digest){
            if(observed!=size||digest.size()!=32||pinned.contains(descriptor))throw std::runtime_error("extension was registered before agreement");
            ++agreements;
            if(std::string(argv[3])=="reject")throw std::runtime_error("simulated party disagreement");
        });
        try {compiler.prepare(size);compiler.prepare(size);}
        catch(...) {if(pinned.contains(descriptor))throw std::runtime_error("failed agreement registered extension");throw;}
        pinned.verify_descriptor(descriptor);
        std::cout<<agreements<<" agreements\n";return 0;
    } catch(const std::exception& e) {std::cerr<<e.what()<<"\n";return 1;}
}
