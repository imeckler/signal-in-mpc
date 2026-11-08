// Persistent native worker. Public binary RPC only on stdout; all runtime
// diagnostics go to stderr. Five-party execution has not been tested here.
#include "NativeDispatch.h"
#include "PublicPipe.h"
#include "SessionWork/NativeLifecycle.h"
#include <memory>
#include <unistd.h>
#include <cerrno>
#include <charconv>
#include <streambuf>
#include <iostream>

using namespace tls_mpc_worker;
class OutputBuffer : public std::streambuf {
    int fd;
protected:
    std::streamsize xsputn(const char* data,std::streamsize size) override {
        std::streamsize sent=0;
        while(sent<size) { auto n=::write(fd,data+sent,size-sent);if(n<0&&errno==EINTR)continue;if(n<=0)break;sent+=n; }
        return sent;
    }
    int_type overflow(int_type c) override {
        if(traits_type::eq_int_type(c,traits_type::eof()))return traits_type::not_eof(c);
        char byte=traits_type::to_char_type(c);return xsputn(&byte,1)==1?c:traits_type::eof();
    }
public:
    explicit OutputBuffer(int fd):fd(fd){}
    ~OutputBuffer(){::close(fd);}
};
static unsigned number(const std::string& text) {
    unsigned value=0;auto [end,error]=std::from_chars(text.data(),text.data()+text.size(),value);
    public_require(error==std::errc{}&&end==text.data()+text.size(),"invalid worker integer");return value;
}
static PublicBytes hex32(const std::string& text) {
    public_require(text.size()==64,"session ID must contain 32 hex bytes");PublicBytes out;
    auto digit=[](char c)->unsigned {if(c>='0'&&c<='9')return c-'0';if(c>='a'&&c<='f')return c-'a'+10;throw std::runtime_error("noncanonical session ID");};
    for(size_t i=0;i<64;i+=2)out.push_back(16*digit(text[i])+digit(text[i+1]));return out;
}
struct WorkerState {
    std::unique_ptr<Names> names;
    std::unique_ptr<PinnedPrograms> pinned;
    std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;
    std::unique_ptr<Collective> collective;
    std::unique_ptr<ShapeCompiler> shapes;
    std::unique_ptr<NativeLifecycle> lifecycle;
    std::unique_ptr<Session> session;
    std::unique_ptr<Dispatch> dispatcher;
};
int main(int argc,char** argv) {
    SecureGmp::install_before_threads();
    if(argc!=6) {std::cerr<<"usage: tls-worker PARTY HOSTS PORT MANIFEST SESSION_ID_HEX\n";return 2;}
    int rpc_fd=::dup(STDOUT_FILENO);if(rpc_fd<0||::dup2(STDERR_FILENO,STDOUT_FILENO)<0)return 2;
    OutputBuffer buffer(rpc_fd);std::ostream response(&buffer);
    WorkerState* state=new WorkerState;
    auto destroy=[&] {
        if(state) {
            auto previous=state;state=nullptr;
            return ErasedHostCall::run([&] {delete previous;});
        }
        return true;
    };
    try {
        unsigned party=number(argv[1]),port=number(argv[3]);
        public_require(party<5&&port>1024&&port<65530,"invalid worker party/port");
        auto session_id=hex32(argv[5]);
        public_require(ErasedHostCall::run([&] {
            state->pinned=std::make_unique<PinnedPrograms>(argv[4]);
            ShamirOptions::singleton={5,2};
            OnlineOptions options;options.playerno=party;options.live_prep=true;
            options.security_parameter=128;options.lg2=128;options.lgp=255;
            options.prime=1;options.prime<<=255;options.prime-=19;
            state->names=std::make_unique<Names>(party,port,std::string(argv[2]));
            public_require(state->names->num_players()==5,"worker host inventory must have five parties");
            state->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*state->names,true,options);
            state->collective=std::make_unique<Collective>([pointer=state]() -> Player& {return pointer->machine->get_player();},state->pinned->digest(),session_id);
            state->shapes=std::make_unique<ShapeCompiler>(*state->pinned,[pointer=state](const std::string& shape,const PublicBytes& digest){pointer->collective->agree_program(shape,digest);});
            state->lifecycle=std::make_unique<NativeLifecycle>(*state->machine);
            state->session=std::make_unique<Session>(*state->machine,*state->pinned,state->shapes.get(),state->lifecycle.get());
            state->dispatcher=std::make_unique<Dispatch>(*state->session,*state->collective,state->shapes.get());
        }),"native worker bootstrap failed");
        while(auto request=read_request(std::cin)) {
            PublicBytes result;
            public_require(ErasedHostCall::run([&] {result=state->dispatcher->call(*request);}),"native worker operation failed");
            // The return barrier has already joined, destroyed thread-local
            // state and wiped the full host stack before any receipt is sent.
            write_reply(response,true,result);
            if(request->operation==Opcode::abort)break;
        }
        public_require(destroy(),"native worker teardown failed");
        return 0;
    } catch(...) {
        try {destroy();}catch(...){}
        try {write_reply(response,false,{});}catch(...){}
        std::cerr<<"TLS MPC worker aborted\n";return 1;
    }
}
