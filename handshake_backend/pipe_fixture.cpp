// PUBLIC FRAMING FIXTURE ONLY. No MPC, secret data or cryptography.
#include "PublicPipe.h"
#include <iostream>
using namespace tls_mpc_worker;
int main(int argc,char** argv) {
    if(argc!=2) return 2;
    std::string mode=argv[1]; RequestSequence sequence;
    if(mode=="duplex") {
        bool sent=false;PublicBytes wire;
        for(unsigned i=0;i<300;++i) {
            auto request=read_request(std::cin);if(!request)return 3;sequence.reserve(request->sequence);
            if(request->operation==Opcode::send) {public_require(!sent,"duplicate duplex send");sent=true;wire=request->payload;write_reply(std::cout,true,{});}
            else {
                public_require(request->operation==Opcode::poll_receive && request->payload.empty(),"unexpected duplex operation");
                write_reply(std::cout,true,sent?wire:PublicBytes{});if(sent)return 0;
            }
        }
        return 4;
    }
    if(mode=="concurrent") {
        for(int i=0;i<32;++i) {auto request=read_request(std::cin);if(!request)return 3;
            sequence.reserve(request->sequence);write_reply(std::cout,true,request->payload);}
        return 0;
    }
    for(int i=0;i<(mode=="valid"?17:1);++i) {
        auto request=read_request(std::cin); if(!request) return 3;
        sequence.reserve(request->sequence);
        if(mode=="oversized") { PublicBytes head{0};put_number(head,max_request_bytes+1,4);std::cout.write(reinterpret_cast<char*>(head.data()),head.size());std::cout.flush();return 0; }
        if(mode=="truncated") { std::cout.put(0);std::cout.flush();return 0; }
        if(mode=="rejected") { write_reply(std::cout,false,{});return 0; }
        if(request->operation==Opcode::authenticate) public_require(authentication_decision(request->payload),"Lean authentication layout mismatch");
        write_reply(std::cout,true,request->payload);
    }
}
