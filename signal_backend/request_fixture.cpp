// Public framing fixture only. Production instantiates with native OwnedBits.
#include "PrivateGrpcRequest.h"
#include <iostream>
#include <iomanip>
#include <cassert>
using Bits=std::vector<uint8_t>;
Bits share(const std::vector<uint8_t>& bytes){Bits bits;for(auto c:bytes)for(int j=7;j>=0;--j)bits.push_back((c>>j)&1);return bits;}
Bits text(const std::string& s){return share(std::vector<uint8_t>(s.begin(),s.end()));}
int main(int argc,char** argv){
 if(argc!=2)return 2;
 auto rejected=[](auto f){bool failed=false;try{f();}catch(const std::exception&){failed=true;}assert(failed);};
 rejected([]{signal_mpc::frame_grpc_request(0,text("a"),text("/"),text("x"),share({1}),share);});
 rejected([]{signal_mpc::frame_grpc_request(2,text("a"),text("/"),text("x"),share({1}),share);});
 rejected([]{signal_mpc::frame_grpc_request(1,text("a"),text("/"),text("x"),Bits{1},share);});
 rejected([]{signal_mpc::frame_grpc_request(1,text("a"),text("/"),text("x"),share(std::vector<uint8_t>(12001)),share);});
 auto request=signal_mpc::frame_grpc_request(1,text("grpc.chat.signal.org"),
    text("/org.signal.chat.messages.Messages/SendMessage"),text("Basic "+std::string(std::stoul(argv[1]),'x')),
    share({10,3,1,2,3}),share);
 for(size_t i=0;i<request.size();i+=8){unsigned c=0;for(size_t j=0;j<8;++j)c=(c<<1)|request[i+j];std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<c;}
 std::cout<<'\n';
}
