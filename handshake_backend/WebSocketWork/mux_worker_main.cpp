// Persistent native worker. Public binary RPC only on stdout; all runtime
// diagnostics go to stderr. This explicit profile requires patched lifecycle support.
#include "NativeDispatch.h"
#include "PublicPipe.h"
#include "SessionWork/NativeLifecycle.h"
#include <memory>
#include "MuxProviderCoordinator.h"
#ifdef TLS_ACCOUNT_RESTORE_PROFILE
#include "RestoreAdmissionWork/RecoveryFactory.h"
#endif
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
    std::unique_ptr<PublicMetrics> metrics;
    std::unique_ptr<Collective> collective;
    std::unique_ptr<ShapeCompiler> shapes;
    std::unique_ptr<NativeLifecycle> lifecycle;
    std::unique_ptr<Session> session;
    std::unique_ptr<Dispatch> dispatcher;
    std::unique_ptr<MuxProviderCoordinator> providers;
#ifdef TLS_ACCOUNT_RESTORE_PROFILE
    std::unique_ptr<Worker> import_worker;
    std::unique_ptr<signal_mpc::recovery::AuthorizedRestoredAccount> restored_account;
#endif

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
            state->metrics=std::make_unique<PublicMetrics>(*state->machine,party);
            state->lifecycle=std::make_unique<NativeLifecycle>(*state->machine,ApplicationEpochPolicy::every_record,state->metrics.get());
#ifdef TLS_ACCOUNT_RESTORE_PROFILE
            state->import_worker=std::make_unique<Worker>(*state->machine,*state->pinned);
#else
            state->session=std::make_unique<Session>(*state->machine,*state->pinned,state->shapes.get(),state->lifecycle.get(),state->metrics.get());
            state->dispatcher=std::make_unique<Dispatch>(*state->session,*state->collective,state->shapes.get());
            state->providers=std::make_unique<MuxProviderCoordinator>(*state->session,*state->collective,make_mux_provider_factory(),PublicBytes(session_id.begin(),session_id.begin()+16));
#endif
        }),"native worker bootstrap failed");
#ifdef TLS_ACCOUNT_RESTORE_PROFILE
        auto resolver=make_account_recovery_resolver();
        public_require(ErasedHostCall::run([&]{
            state->collective->agree_provider_availability(bool(resolver));
            if(!resolver)std::cerr<<"TLS account admission rejected category=resolver-absent\n";
            public_require(bool(resolver),"authorized account recovery unavailable");
        }),"authorized account recovery unavailable");
        // The real resolver owns its load/import/helper-erasure/VM-retirement
        // host calls. No Session/TLS state exists until it returns its private,
        // one-shot current-head/full-account capability after both barriers.
        try{state->restored_account=resolver(*state->machine,*state->import_worker,*state->pinned,*state->collective,party);}
        catch(...){state->restored_account.reset();}
        public_require(ErasedHostCall::run([&]{
            resolver={};state->import_worker.reset();
            state->collective->require_local_success(bool(state->restored_account));
            public_require(bool(state->restored_account),"authorized account recovery rejected");
            state->session=std::make_unique<Session>(*state->machine,*state->pinned,state->shapes.get(),state->lifecycle.get(),state->metrics.get());
            state->dispatcher=std::make_unique<Dispatch>(*state->session,*state->collective,state->shapes.get());
            MuxProviderFactory admitted=[pointer=state](Session& session,Collective& collective,unsigned selected_party){
                public_require(bool(pointer->restored_account),"restored account capability consumed");
                auto result=pointer->restored_account->consume(session,collective,selected_party);
                pointer->restored_account.reset();return result;
            };
            state->providers=std::make_unique<MuxProviderCoordinator>(*state->session,*state->collective,std::move(admitted),PublicBytes(session_id.begin(),session_id.begin()+16));
        }),"restored fresh TLS bootstrap failed");
#endif
        auto close_private=[&]{
            state->providers->close();
#ifdef TLS_ACCOUNT_RESTORE_PROFILE
            state->restored_account.reset(); // Failed/aborted handshake cannot retain/reuse admission.
#endif
        };
        while(auto request=read_request(std::cin)) {
            PublicBytes result;
            const auto metric_token=state->metrics->begin();
            const auto old_epochs=state->lifecycle->renewal_count();
            const auto old_time=state->lifecycle->renewal_nanoseconds();
            bool succeeded=ErasedHostCall::run([&] {
                if(request->operation==Opcode::abort)close_private();
                if(static_cast<unsigned>(request->operation)>=19) {
                    result=state->dispatcher->private_extension(*request,[&] {
                        Cursor input{request->payload};
                        if(request->operation==Opcode::mux_catalogue){input.done();return state->providers->catalogue();}
                        if(request->operation==Opcode::mux_process){
                            auto handle=input.number(8);input.done();auto receipt=state->session->process_websocket_mux(handle);
                            PublicBytes out{uint8_t(receipt.upgraded),uint8_t(receipt.completed_slots.size())};
                            out.insert(out.end(),receipt.completed_slots.begin(),receipt.completed_slots.end());out.push_back(receipt.controls.size());
                            for(const auto& control:receipt.controls){out.push_back(control.first);put_number(out,control.second,8);put_number(out,131,2);}return out;
                        }
                        if(request->operation==Opcode::mux_produce_batch){
                            auto count=input.number(1);public_require(count>=1&&count<=4,"invalid mux batch count");
                            std::vector<std::pair<uint64_t,uint64_t>> requests;
                            for(size_t i=0;i<count;++i){auto owner=input.number(8),handle=input.number(8);requests.push_back({owner,handle});}input.done();
                            auto receipts=state->providers->produce_batch(requests);PublicBytes out{1,static_cast<uint8_t>(receipts.size())};
                            for(auto receipt:receipts){put_number(out,receipt.handle,8);put_number(out,receipt.capacity,2);}return out;
                        }
                        ProviderRegistry::Receipt receipt;
                        if(request->operation==Opcode::mux_upgrade){input.done();receipt=state->providers->upgrade();}
                        else if(request->operation==Opcode::mux_produce){auto owner=input.number(8),handle=input.number(8);input.done();receipt=state->providers->produce(owner,handle);}
                        else throw std::runtime_error("unsupported mux operation");
                        PublicBytes out;put_number(out,receipt.handle,8);put_number(out,receipt.capacity,2);return out;
                    });
                }else result=state->dispatcher->call(*request);
            });
            if(request->operation==Opcode::seal_application)
                std::cerr<<"record epoch policy every-record renewals "<<state->lifecycle->renewal_count()-old_epochs
                    <<" nanoseconds "<<state->lifecycle->renewal_nanoseconds()-old_time<<"\n";
            if(succeeded&&request->operation==Opcode::retire)
                succeeded=ErasedHostCall::run([&] {state->providers->initialize(party,[&]{state->dispatcher->fail_from_private_producer();});});
            if(succeeded&&request->operation==Opcode::mux_process)
                succeeded=ErasedHostCall::run([&] {result=state->providers->authenticated_receipt(result);});
            if(!succeeded)ErasedHostCall::run([&] {close_private();state->dispatcher->fail_from_private_producer();});

            // The return barrier has already joined, destroyed thread-local
            // state and wiped the full host stack before any receipt is sent.
            state->metrics->finish(("rpc."+std::to_string(static_cast<unsigned>(request->operation))).c_str(),metric_token,succeeded);
            if(request->operation==Opcode::abort)state->metrics->emit_resources();
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
