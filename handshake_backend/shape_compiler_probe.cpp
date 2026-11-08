// No MPC/network. Exercise the actual spawn, pin-extension, and ordering path.
#include "ShapeCompiler.h"
#include <iostream>
int main(int argc,char** argv) {
    if(argc<4)return 2;
    try {
        tls_mpc_worker::PinnedPrograms pinned(argv[1]);
        using Shape=tls_mpc_worker::KernelShape;
        auto number=[&](int index) {size_t end=0;auto value=std::stoull(argv[index],&end);
            if(end!=std::string(argv[index]).size())throw std::runtime_error("invalid dimension");return value;};
        auto shape=[&]() -> Shape {
            if(argc==4)return Shape::handshake(number(2));
            std::string mode=argv[2];
            if(argc==5) {
                if(mode=="tls-open-record")return Shape::open(number(3));
                if(mode=="tls-route-application")return Shape::route(number(3));
                if(mode=="tls-post-handshake")return Shape::post_handshake(number(3));
            }
            if(argc==7&&mode=="tls-seal-record")return Shape::seal(number(3),number(4),number(5));
            throw std::runtime_error("invalid probe shape");
        }();
        size_t agreements=0;
        auto descriptor=shape.descriptor();
        tls_mpc_worker::ShapeCompiler compiler(pinned,[&](const std::string& observed,const tls_mpc_worker::PublicBytes& digest){
            if(observed!=shape.key()||digest.size()!=32||pinned.contains(descriptor))throw std::runtime_error("extension was registered before agreement");
            ++agreements;
            if(std::string(argv[argc-1])=="reject")throw std::runtime_error("simulated party disagreement");
        });
        try {compiler.prepare(shape);compiler.prepare(shape);}
        catch(...) {if(pinned.contains(descriptor))throw std::runtime_error("failed agreement registered extension");throw;}
        pinned.verify_descriptor(descriptor);
        std::cout<<agreements<<" agreements\n";return 0;
    } catch(const std::exception& e) {std::cerr<<e.what()<<"\n";return 1;}
}
