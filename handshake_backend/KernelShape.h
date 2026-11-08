#pragma once
#include "PublicProtocol.h"
#include <string>
#include <vector>

namespace tls_mpc_worker {
// Public dimensions only. The constructor is private so every descriptor,
// compiler argument, and agreement identifier comes from a checked shape.
class KernelShape {
    std::string mode_;
    std::vector<size_t> dimensions_;
    size_t input_, output_;
    KernelShape(std::string mode,std::vector<size_t> dimensions,size_t input,size_t output)
        :mode_(std::move(mode)),dimensions_(std::move(dimensions)),input_(input),output_(output){}
    static void wire_size(size_t size) {
        public_require(size>=22&&size<=16406,"invalid AES-GCM record shape");
    }
    static void capacity(size_t size) {
        public_require(size>=1&&size<=16385,"invalid TLS parser capacity");
    }
public:
    static KernelShape handshake(size_t wire) {
        wire_size(wire);return {"tls-open-handshake-record",{wire},36+wire,wire-17};
    }
    static KernelShape open(size_t wire) {
        wire_size(wire);return {"tls-open-record",{wire},36+wire,wire-17};
    }
    static KernelShape route(size_t size) {
        capacity(size);return {"tls-route-application",{size},15+size,15+size};
    }
    static KernelShape post_handshake(size_t size) {
        capacity(size);return {"tls-post-handshake",{size},15+size,15+size};
    }
    static KernelShape seal(size_t kind,size_t size,size_t padding) {
        public_require(kind==21||kind==22||kind==23,"invalid protected content type");
        public_require(size<=16384&&padding<=16384-size,"invalid TLS seal dimensions");
        public_require(kind==23||size>0,"empty TLS control record");
        return {"tls-seal-record",{kind,size,padding},36+size,size+padding+22};
    }
    static KernelShape seal_private(size_t size) {
        public_require(size<=16384,"invalid private TLS capacity");
        return {"tls-seal-private-record",{size},39+size,23+size};
    }
    std::string stem() const {
        auto result=mode_;for(auto dimension:dimensions_)result+="-"+std::to_string(dimension);return result;
    }
    std::string key() const {
        // Keep existing immutable handshake cache names and receipts usable.
        return mode_=="tls-open-handshake-record"?std::to_string(dimensions_[0]):stem();
    }
    std::vector<std::string> arguments() const {
        if(mode_=="tls-open-handshake-record")return {std::to_string(dimensions_[0])};
        std::vector<std::string> result{mode_};
        for(auto dimension:dimensions_)result.push_back(std::to_string(dimension));return result;
    }
    std::string descriptor() const {
        auto name=stem();for(auto& c:name)if(c=='-')c='_';
        return "Programs/Functions/tls_binary_"+name+"-sbv:["+std::to_string(input_*8)+
            "x1]-sbv:["+std::to_string(output_*8)+"x1]";
    }
    size_t output_bytes() const {return output_;}
};
}
