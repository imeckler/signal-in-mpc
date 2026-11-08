#include "KernelShape.h"
#include <iostream>
#include <limits>
#include <cassert>
using tls_mpc_worker::KernelShape;
int main() {
    size_t valid=0,rejected=0;
    auto inspect=[&](const KernelShape& shape) {
        ++valid;
        for(const auto& argument:shape.arguments())std::cout<<argument<<' ';
        std::cout<<'|'<<shape.key()<<'|'<<shape.descriptor()<<'|'<<shape.output_bytes()<<'\n';
    };
    auto reject=[&](auto operation) {
        try {operation();}catch(const std::runtime_error&) {++rejected;return;}
        throw std::runtime_error("invalid shape accepted");
    };
    for(size_t size:{22,38,1045,1046,16406}) {
        inspect(KernelShape::handshake(size));inspect(KernelShape::open(size));
    }
    for(size_t size:{1,5,1024,1025,16385}) {
        inspect(KernelShape::route(size));inspect(KernelShape::post_handshake(size));
    }
    for(size_t kind:{21,22,23})for(size_t size:{1,1025,16384}) {
        inspect(KernelShape::seal(kind,size,0));inspect(KernelShape::seal(kind,size,16384-size));
    }
    inspect(KernelShape::seal(23,0,0));inspect(KernelShape::seal(23,0,16384));
    for(size_t size:{size_t(0),size_t(21),size_t(16407),std::numeric_limits<size_t>::max()}) {
        reject([&]{KernelShape::handshake(size);});reject([&]{KernelShape::open(size);});
    }
    for(size_t size:{size_t(0),size_t(16386),std::numeric_limits<size_t>::max()}) {
        reject([&]{KernelShape::route(size);});reject([&]{KernelShape::post_handshake(size);});
    }
    for(size_t kind:{0,20,24,255})reject([&]{KernelShape::seal(kind,1,0);});
    for(size_t kind:{21,22})reject([&]{KernelShape::seal(kind,0,0);});
    reject([&]{KernelShape::seal(23,16385,0);});
    reject([&]{KernelShape::seal(23,1,16384);});
    reject([&]{KernelShape::seal(23,std::numeric_limits<size_t>::max(),1);});
    reject([&]{KernelShape::seal(23,1,std::numeric_limits<size_t>::max());});
    assert(valid==40&&rejected==24);
    std::cerr<<valid<<" valid shapes; "<<rejected<<" invalid shapes rejected\n";
}
