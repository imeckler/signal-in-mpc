// Two-party TLS worker on the validated-v3 Boolean engine and the native field
// engine. Speaks the public pipe RPC of TlsMpc/TlsWorkerPipe.lean: each party
// runs its own Lean controller and its own worker; the workers agree on every
// request (operation, sequence, public payload) before acting on it, so a
// controller cannot make the two parties compute on different public inputs.
// Party 0 (ALICE) is the leader and owns the TCP socket to the server; records
// it receives are forwarded to the other party as public data.
//
// Secret state lives in TlsKernels. This file holds no gate logic: it parses
// frames, routes public bytes and calls the Lean-exported kernels.
// Usage: PARTY(0|1) HOSTS(ignored, local) PORT CIRCUIT_CACHE_SCRIPT SESSION_ID_HEX
#include "service_kernels.h"
#include "big_stack.h"
#include <cerrno>
#include <chrono>
#include <iostream>
#include <deque>
#include <netdb.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>
using namespace emp;
using namespace emp_hybrid;
using Bytes=std::vector<uint8_t>;
static bool read_exact(int fd,uint8_t*out,size_t n){while(n){auto r=::read(fd,out,n);if(r<0&&errno==EINTR)continue;if(r<=0)return false;out+=r;n-=size_t(r);}return true;}
static void write_all(int fd,const uint8_t*data,size_t n){while(n){auto r=::write(fd,data,n);if(r<0&&errno==EINTR)continue;if(r<=0)throw std::runtime_error("pipe write");data+=r;n-=size_t(r);}}
static uint64_t big(const uint8_t*p,unsigned n){uint64_t v=0;for(unsigned i=0;i<n;i++)v=v<<8|p[i];return v;}
struct Worker {
    int party;NetIO&io;Challenge&channel;TlsKernels&kernels;std::string session;int server=-1;
    enum class Phase{fresh,begun,derived,finished,retired}phase=Phase::fresh;
    // TEST FIXTURE ONLY (TLS_WORKER_TEST_PRODUCER=bytes in both workers' environment):
    // private payloads neither party knows are produced inside the engines, as
    // handles 1, 2, 5 in the order the Lean application fixture expects.
    ServiceKernels*service=nullptr;bool service_fixture=false;   // TLS_WORKER_SERVICE_FIXTURE=text: admit the public text fixture at retirement
    static Bytes receipt(std::pair<uint64_t,size_t>r){Bytes out;for(int i=7;i>=0;i--)out.push_back(uint8_t(r.first>>(8*i)));out.push_back(uint8_t(r.second>>8));out.push_back(uint8_t(r.second));return out;}
    size_t test_bytes=0;uint64_t produced_handle=0;unsigned produced=0;bool sealed_pending=false;std::deque<uint64_t>awaiting_echo;
    ~Worker(){if(server>=0)::close(server);}
    void need(bool ok,const char*what){if(!ok)throw std::runtime_error(what);}
    // Both workers must have been handed the same request.
    void agree(uint8_t code,uint64_t sequence,const Bytes&payload){
        std::string head="tls-worker-v3:"+session;Bytes frame(head.begin(),head.end());frame.push_back(code);
        for(int i=7;i>=0;i--)frame.push_back(uint8_t(sequence>>(8*i)));
        for(int i=3;i>=0;i--)frame.push_back(uint8_t(uint64_t(payload.size())>>(8*i)));
        frame.insert(frame.end(),payload.begin(),payload.end());
        std::array<uint8_t,32>mine{},peer{};SHA256(frame.data(),frame.size(),mine.data());channel.transfer(mine.data(),peer.data(),32);
        need(mine==peer,"request disagreement");
    }
    // Public ClientHello random: commit, then open, then XOR.
    Bytes joint_random(){
        std::array<uint8_t,32>mine{},peer{},commit{},peer_commit{},check{};{PRG prg;prg.random_data_unaligned(mine.data(),32);}
        SHA256(mine.data(),32,commit.data());channel.transfer(commit.data(),peer_commit.data(),32);channel.transfer(mine.data(),peer.data(),32);
        SHA256(peer.data(),32,check.data());need(check==peer_commit,"random commitment");
        Bytes out(32);for(unsigned i=0;i<32;i++)out[i]=mine[i]^peer[i];return out;
    }
    Bytes call(uint8_t code,uint64_t sequence,const Bytes&p){
        agree(code,sequence,p);
        switch(code){
        case 1:{need(phase==Phase::fresh&&p.empty(),"begin");auto key=kernels.begin();Bytes out(key.begin(),key.end());auto random=joint_random();out.insert(out.end(),random.begin(),random.end());phase=Phase::begun;return out;}
        case 2:{need(phase==Phase::begun&&p.size()==64,"derive");std::array<uint8_t,32>peer{};std::copy_n(p.begin(),32,peer.begin());kernels.derive(peer,Bytes(p.begin()+32,p.end()));phase=Phase::derived;return {};}
        case 3:{need(phase==Phase::derived&&p.size()>=30&&p.size()<=8+16645,"open handshake");return kernels.open_handshake(Bytes(p.begin(),p.begin()+8),Bytes(p.begin()+8,p.end()));}
        case 4:{need(phase==Phase::derived&&!p.empty()&&p.back()==1,"authentication rejected");return {};}   // identical request incl. each party's own decision
        case 5:{need(phase==Phase::derived&&p.size()==68,"verify Finished");return {uint8_t(kernels.verify_finished(Bytes(p.begin(),p.begin()+32),Bytes(p.begin()+32,p.end()))?255:0)};}
        case 6:{need(phase==Phase::derived&&p.size()>=64&&p.size()<=128,"finish");auto wire=kernels.finish(Bytes(p.begin(),p.begin()+32),Bytes(p.begin()+32,p.begin()+64),Bytes(p.begin()+64,p.end()));phase=Phase::finished;return wire;}
        case 7:{
            need(phase==Phase::finished&&p.empty(),"retire");kernels.retire();phase=Phase::retired;
            if(test_bytes){produced_handle=kernels.test_produce(test_bytes);produced=1;}
            if(service_fixture)service->admit_fixture();
            return {};
        }
        // Signal service path (service_kernels.h). Receipts carry a handle and a public capacity.
        case 19:{need(phase==Phase::retired&&service&&p.empty(),"provider catalogue");return service->catalogue();}
        case 20:{
            need(phase==Phase::retired&&service&&p.size()==8&&big(p.data(),8)==1,"provider upgrade");
            auto nonce=joint_random();nonce.resize(16);return receipt(service->upgrade(nonce));
        }
        case 21:{need(phase==Phase::retired&&service&&p.size()==16&&big(p.data(),8)==1,"provider produce");return receipt(service->produce(big(p.data()+8,8)));}
        case 18:{need(phase==Phase::retired&&service&&p.size()==8,"process WebSocket");return service->process(big(p.data(),8));}
        case 12:{
            need(phase==Phase::retired&&p.size()>=30&&p.size()<=8+16406,"open application");
            auto out=kernels.open_application(Bytes(p.begin(),p.begin()+8),Bytes(p.begin()+8,p.end()));
            if(test_bytes&&out[0]==1&&!awaiting_echo.empty()){
                // Fixture diagnostics only: compare an echoed record with the private payload that was sent.
                int same=kernels.test_echo(awaiting_echo.front(),big(out.data()+2,8),5,test_bytes);
                if(same==0)throw std::runtime_error("echo differs from the private payload");
                if(same==1){awaiting_echo.pop_front();std::cerr<<"tls-worker-v3 test echo matches private payload\n";}
            }
            return out;
        }
        case 13:{
            need(phase==Phase::retired&&p.size()==20,"seal application");uint64_t id=big(p.data()+8,8);
            auto wire=kernels.seal_application(Bytes(p.begin(),p.begin()+8),id,big(p.data()+16,2),big(p.data()+18,2));
            if(test_bytes&&id==produced_handle)sealed_pending=true;
            return wire;
        }
        case 14:{
            need(phase==Phase::retired&&p.size()>=11,"seal control");Bytes content(p.begin()+9,p.end());unsigned kind=p[8];
            need((kind==22&&(content==Bytes{24,0,0,1,0}||content==Bytes{24,0,0,1,1}))||(kind==21&&content==Bytes{1,0}),"control content");
            return kernels.seal_control(Bytes(p.begin(),p.begin()+8),kind,content);
        }
        case 15:case 16:{need(phase==Phase::retired&&p.empty(),"rotate");kernels.rotate(code==15);return {};}
        case 17:{
            // Non-blocking: the socket owner reports whether a whole record is available.
            need(server>=0&&p.empty(),"poll");uint8_t size[4]={0,0,0,0};Bytes record;
            if(party==ALICE){
                pollfd watch{server,POLLIN,0};
                if(::poll(&watch,1,0)>0){
                    record.resize(5);need(read_exact(server,record.data(),5),"server closed");size_t n=big(record.data()+3,2);need(n<=16640,"record bound");
                    record.resize(5+n);need(read_exact(server,record.data()+5,n),"server closed");
                }
                for(int i=0;i<4;i++)size[i]=uint8_t(record.size()>>(8*(3-i)));io.send_data(size,4);if(!record.empty())io.send_data(record.data(),record.size());io.flush();
            }else{
                io.recv_data(size,4);size_t n=big(size,4);
                if(n){need(n>=5&&n<=5+16640,"record bound");record.resize(n);io.recv_data(record.data(),n);need(big(record.data()+3,2)+5==n,"record framing");}
            }
            return record;
        }
        case 9:{
            need(server<0&&p.size()>=5,"connect");size_t n=big(p.data(),2);need(p.size()==n+4&&n>0,"connect shape");
            if(party==ALICE){
                std::string host(p.begin()+2,p.begin()+2+n),port=std::to_string(big(p.data()+2+n,2));addrinfo hints{},*list=nullptr;hints.ai_socktype=SOCK_STREAM;
                need(getaddrinfo(host.c_str(),port.c_str(),&hints,&list)==0&&list,"resolve");
                int fd=::socket(list->ai_family,list->ai_socktype,list->ai_protocol);bool ok=fd>=0&&::connect(fd,list->ai_addr,list->ai_addrlen)==0;freeaddrinfo(list);
                if(!ok){if(fd>=0)::close(fd);throw std::runtime_error("connect");}server=fd;
            }else server=0;
            return {};
        }
        case 10:{
            need(server>=0&&p.size()>=5&&p.size()<=5+16640,"send");if(party==ALICE)write_all(server,p.data(),p.size());
            if(sealed_pending){sealed_pending=false;awaiting_echo.push_back(produced_handle);if(produced<3){produced_handle=kernels.test_produce(test_bytes);produced++;}}
            return {};
        }
        case 11:{
            need(server>=0&&p.empty(),"receive");Bytes record(5);uint8_t size[4];
            if(party==ALICE){
                need(read_exact(server,record.data(),5),"server closed");size_t n=big(record.data()+3,2);need(n<=16640,"record bound");
                record.resize(5+n);need(read_exact(server,record.data()+5,n),"server closed");
                for(int i=0;i<4;i++)size[i]=uint8_t(record.size()>>(8*(3-i)));io.send_data(size,4);io.send_data(record.data(),record.size());io.flush();
            }else{
                io.recv_data(size,4);size_t n=big(size,4);need(n>=5&&n<=5+16640,"record bound");record.resize(n);io.recv_data(record.data(),n);
                need(big(record.data()+3,2)+5==n,"record framing");
            }
            return record;
        }
        default:throw std::runtime_error("unsupported operation");
        }
    }
};
static int run(int argc,char**argv){
    if(argc!=6)return 2;
    int rpc=::dup(STDOUT_FILENO);if(rpc<0||::dup2(STDERR_FILENO,STDOUT_FILENO)<0)return 2;
    auto reply=[&](bool ok,const Bytes&payload){Bytes out{uint8_t(ok?0:1)};for(int i=3;i>=0;i--)out.push_back(uint8_t(uint64_t(payload.size())>>(8*i)));out.insert(out.end(),payload.begin(),payload.end());write_all(rpc,out.data(),out.size());};
    try{
        int party=std::stoi(argv[1])+1;unsigned port=std::stoul(argv[3]);std::string session=argv[5];
        if((party!=ALICE&&party!=BOB)||session.size()!=64||session.find_first_not_of("0123456789abcdef")!=std::string::npos)return 2;
        auto started=std::chrono::steady_clock::now();
        NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool threads(4);
        // The split agreement needs about a dozen field products; the ladder thousands.
        const char*route=std::getenv("TLS_WORKER_KEY_AGREEMENT");const bool ladder=route&&std::string(route)=="ladder";
        if(route&&!ladder&&std::string(route)!="split")return 2;
        const char*fixture=std::getenv("TLS_WORKER_SERVICE_FIXTURE");if(fixture&&std::string(fixture)!="text")return 2;
        // Sealed sender needs thousands of field products per send (ladder on a private point).
        DynSession mpc(&io,&threads,party,128);FE field(party-1,port+10,(ladder||fixture)?3000:16);
        Challenge channel{io,party,"tls-worker-v3:session="+session};
        TlsKernels kernels(mpc,field,channel,party,argv[4]);kernels.prepare();
        Worker worker{party,io,channel,kernels,session};
        if(const char*test=std::getenv("TLS_WORKER_TEST_PRODUCER")){worker.test_bytes=std::stoul(test);if(!worker.test_bytes||worker.test_bytes>16384)return 2;std::cerr<<"tls-worker-v3 TEST producer enabled bytes="<<worker.test_bytes<<"\n";}
        // Both workers must be configured alike: the route is part of every agreed request.
        kernels.ladder_agreement=ladder;
        ServiceKernels service(kernels);worker.service=&service;worker.service_fixture=fixture!=nullptr;
        if(fixture)std::cerr<<"tls-worker-v3 TEST service fixture enabled\n";
        worker.session+=kernels.ladder_agreement?":ladder":":split";
        std::cerr<<"tls-worker-v3 security_mode="<<SECURITY_MODE<<" key_agreement="<<(kernels.ladder_agreement?"ladder":"split")<<"\n";
        std::cerr<<"tls-worker-v3 operation 0 ok seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<" and_gates="<<kernels.and_gates()<<" emp_sent_bytes="<<mpc.sent_bytes()<<" field_sent_bytes="<<field.sent_bytes()<<" field_products="<<field.products()<<"\n";
        bool failed=false;uint64_t expected=0;
        for(;;){
            uint8_t head[13];if(!read_exact(STDIN_FILENO,head,13))break;
            uint64_t sequence=big(head+1,8);size_t size=big(head+9,4);if(size>2*1024*1024)throw std::runtime_error("request bound");
            Bytes payload(size);if(size&&!read_exact(STDIN_FILENO,payload.data(),size))break;
            if(head[0]==8){kernels.abort();failed=true;std::cerr<<"tls-worker-v3 operation 8 ok (local abort)\n";reply(true,{});continue;}   // local, idempotent; not an erasure receipt
            if(failed||sequence!=expected++){failed=true;reply(false,{});continue;}
            try{
                auto out=worker.call(head[0],sequence,payload);
                if(!(head[0]==17&&out.empty()))std::cerr<<"tls-worker-v3 operation "<<unsigned(head[0])<<" ok seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<" and_gates="<<kernels.and_gates()<<" emp_sent_bytes="<<mpc.sent_bytes()<<" field_sent_bytes="<<field.sent_bytes()<<" field_products="<<field.products()<<"\n";
                reply(true,out);
            }catch(const std::exception&e){std::cerr<<"tls-worker-v3 operation "<<unsigned(head[0])<<" rejected: "<<e.what()<<"\n";failed=true;kernels.abort();reply(false,{});}
        }
        std::cerr<<"tls-worker-v3 totals and_gates="<<kernels.and_gates()<<" emp_sent_bytes="<<mpc.sent_bytes()<<""<<"\n";
        return 0;
    }catch(const std::exception&e){std::cerr<<"tls-worker-v3 aborted: "<<e.what()<<"\n";try{reply(false,{});}catch(...){}return 1;}
}
int main(int argc,char**argv){
    int code=1;
    try{emp_hybrid::run_with_stack(size_t(1)<<30,[&]{code=run(argc,argv);});}catch(...){return 1;}
    return code;
}
