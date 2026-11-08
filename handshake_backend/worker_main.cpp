// Persistent native worker. Public binary RPC only on stdout; all runtime
// diagnostics go to stderr. Five-party execution has not been tested here.
#include "NativeDispatch.h"
#include "PublicPipe.h"
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
int main(int argc,char** argv) {
    if(argc!=6) {std::cerr<<"usage: tls-worker PARTY HOSTS PORT MANIFEST SESSION_ID_HEX\n";return 2;}
    int rpc_fd=::dup(STDOUT_FILENO);if(rpc_fd<0||::dup2(STDERR_FILENO,STDOUT_FILENO)<0)return 2;
    OutputBuffer buffer(rpc_fd);std::ostream response(&buffer);
    try {
        unsigned party=number(argv[1]),port=number(argv[3]);
        public_require(party<5&&port>1024&&port<65530,"invalid worker party/port");
        auto session_id=hex32(argv[5]);
        PinnedPrograms pinned(argv[4]);
        ShamirOptions::singleton={5,2};
        OnlineOptions options;options.playerno=party;options.live_prep=true;
        options.security_parameter=128;options.lg2=128;options.lgp=255;
        options.prime=1;options.prime<<=255;options.prime-=19;
        // Explicit long-field binary companion. This removes the old CCD40
        // parameter ceiling; native execution and composition audits are still
        // required before an end-to-end statistical-security claim.
        Names names(party,port,std::string(argv[2]));
        public_require(names.num_players()==5,"worker host inventory must have five parties");
        Machine<tls_mpc_worker::Share> machine(names,true,options);
        Collective collective(machine.get_player(),pinned.digest(),session_id);
        ShapeCompiler shapes(pinned,[&](const std::string& shape,const PublicBytes& digest){collective.agree_program(shape,digest);});
        Session session(machine,pinned,&shapes);Dispatch dispatcher(session,collective,&shapes);
        while(auto request=read_request(std::cin)) {
            auto result=dispatcher.call(*request);write_reply(response,true,result);
        }
        session.abort();
        return 0;
    } catch(...) {
        // Library exceptions are not exposed: diagnostics may contain internal
        // values. Report only a public failure status to the controller.
        try {write_reply(response,false,{});}catch(...){}
        std::cerr<<"TLS MPC worker aborted\n";return 1;
    }
}
