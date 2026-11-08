// Persistent native worker. Public binary RPC only on stdout; all runtime
// diagnostics go to stderr. Five-party execution has not been tested here.
#include "NativeDispatch.h"
#include "PublicPipe.h"
#include "SessionWork/NativeLifecycle.h"
#include <memory>
#include "../signal_backend/VariableServiceWork/PublicFixtureProducer.h"
#include <openssl/sha.h>
#include <openssl/evp.h>
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
    std::unique_ptr<signal_mpc::PublicVariableProducer<tls_mpc_worker::Bits>> producer;
    uint64_t ticket=0;size_t produced=0;
    tls_mpc_worker::Bits public_bits(const PublicBytes& input) {
        tls_mpc_worker::Bits result(input.size()*8,std::vector<tls_mpc_worker::Bit>(1));
        for(size_t i=0;i<input.size()*8;++i)result[i][0]=tls_mpc_worker::Bit::constant(
            (input[i/8]>>(7-i%8))&1,names->my_num(),machine->get_bit_mac_key());
        return result;
    }
    void start_websocket(const PublicBytes& nonce) {
        unsigned char key[25]={};EVP_EncodeBlock(key,nonce.data(),16);
        std::string material(reinterpret_cast<char*>(key),24);material+="258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
        unsigned char digest[20],accept[29]={};SHA1(reinterpret_cast<const unsigned char*>(material.data()),material.size(),digest);
        EVP_EncodeBlock(accept,digest,20);
        std::cerr<<"ws fixture stage parser initialization\n";
        session->start_websocket(PublicBytes(accept,accept+28));
        std::cerr<<"ws fixture stage upgrade evaluation\n";
        PublicBytes credentials={0,17,34,51,68,85,102,119,136,153,170,187,204,221,238,255};
        credentials.insert(credentials.end(),22,'x');credentials.insert(credentials.end(),nonce.begin(),nonce.end());
        auto handle=session->retain_fixed_payload(session->evaluate_upgrade(signal_mpc::UpgradeShape(22),public_bits(credentials)));
        public_require(handle==1,"unexpected fixture upgrade handle");std::cerr<<"ws fixture stage upgrade checkpoint\n";session->checkpoint_private_computation();
        std::cerr<<"ws fixture stage upgrade ready\n";
    }
    void produce_fixture(PublicBytes& reply) {
        auto share=[&](const PublicBytes& value){return public_bits(value);};
        auto result=[&] {
            bool readiness_joined=false;
            try {
                if(!producer)producer=std::make_unique<signal_mpc::PublicVariableProducer<tls_mpc_worker::Bits>>(share,
                    "tls-ws-fixture-party-"+std::to_string(names->my_num()));
                return producer->produce([&](const signal_mpc::VariableShape& shape,tls_mpc_worker::Bits input){
                    readiness_joined=true;collective->require_local_success(true);
                    std::cerr<<"ws fixture stage producer evaluation\n";
                    return session->evaluate_variable(shape,std::move(input));},share,public_bits(signal_mpc::PublicVariableFixture::timestamp()));
            } catch(...) {
                if(!readiness_joined){readiness_joined=true;collective->require_local_success(false);}
                throw;
            }
        }();
        ticket=result.ticket;auto handle=session->retain_private_result(std::move(result.payload),1186);
        session->expect_websocket_response(std::move(result.request_id));++produced;
        session->checkpoint_private_computation();put_number(reply,handle,8);put_number(reply,1186,2);
    }

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
            // Candidate measurement policy, not a semantic TLS requirement.
            // Explicit-boundary embeddings retain VM work until their declared
            // checkpoint/KeyUpdate/abort and cannot acknowledge early retirement.
            state->lifecycle=std::make_unique<NativeLifecycle>(*state->machine,ApplicationEpochPolicy::every_record);
            state->session=std::make_unique<Session>(*state->machine,*state->pinned,state->shapes.get(),state->lifecycle.get());
            state->dispatcher=std::make_unique<Dispatch>(*state->session,*state->collective,state->shapes.get());
        }),"native worker bootstrap failed");
        while(auto request=read_request(std::cin)) {
            PublicBytes result;
            const auto old_epochs=state->lifecycle->renewal_count();
            const auto old_time=state->lifecycle->renewal_nanoseconds();
            bool succeeded=ErasedHostCall::run([&] {result=state->dispatcher->call(*request);});
            if(request->operation==Opcode::seal_application)
                std::cerr<<"record epoch policy every-record renewals "<<state->lifecycle->renewal_count()-old_epochs
                    <<" nanoseconds "<<state->lifecycle->renewal_nanoseconds()-old_time<<"\n";
            // This disposable local-service fixture owns no live account state.
            if(request->operation==Opcode::retire)std::cerr<<"ws fixture retire barrier "<<(succeeded?"passed":"failed")<<"\n";
            if(succeeded&&request->operation==Opcode::retire)
                succeeded=ErasedHostCall::run([&]{state->start_websocket(PublicBytes(session_id.begin(),session_id.begin()+16));});
            if(succeeded&&request->operation==Opcode::process_websocket)
                succeeded=ErasedHostCall::run([&]{
                    public_require(result.size()>=3,"invalid WebSocket fixture receipt");
                    if(result[1]){public_require(bool(state->producer),"unsolicited fixture acknowledgement");state->producer->response_complete(state->ticket);}
                    if(result[0]&&((!state->producer)||(result[1]&&state->produced<2)))state->produce_fixture(result);
                    else {put_number(result,0,8);put_number(result,0,2);}
                });
            if(!succeeded||request->operation==Opcode::abort)
                ErasedHostCall::run([&]{if(state->producer)state->producer->close();
                    if(!succeeded)state->dispatcher->fail_from_private_producer();});

            // The return barrier has already joined, destroyed thread-local
            // state and wiped the full host stack before any receipt is sent.
            write_reply(response,succeeded,succeeded?result:PublicBytes{});
            // A failed Dispatch is terminal. Keep only its idempotent abort
            // receipt available; Dispatch rejects every other operation.

        }
        public_require(destroy(),"native worker teardown failed");
        return 0;
    } catch(...) {
        try {destroy();}catch(...){}
        try {write_reply(response,false,{});}catch(...){}
        std::cerr<<"TLS MPC worker aborted\n";return 1;
    }
}
