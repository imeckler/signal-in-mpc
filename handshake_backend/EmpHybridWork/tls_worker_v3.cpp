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
// Usage: PARTY(0|1) HOSTS(ignored; the other worker's address is TLS_WORKER_PEER, peer_link.h) PORT CIRCUIT_CACHE_SCRIPT SESSION_ID_HEX
#include "service_kernels.h"
#include "big_stack.h"
#include "peer_link.h"
#include <cerrno>
#include <csignal>
#include <chrono>
#include <iostream>
#include <deque>
#include <netdb.h>
#include <poll.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>
using namespace emp;
using namespace emp_hybrid;
using Bytes=std::vector<uint8_t>;
static bool read_exact(int fd,uint8_t*out,size_t n){while(n){auto r=::read(fd,out,n);if(r<0&&errno==EINTR)continue;if(r<=0)return false;out+=r;n-=size_t(r);}return true;}
static void write_all(int fd,const uint8_t*data,size_t n){while(n){auto r=::write(fd,data,n);if(r<0&&errno==EINTR)continue;if(r<=0)throw std::runtime_error("pipe write");data+=r;n-=size_t(r);}}
static uint64_t big(const uint8_t*p,unsigned n){uint64_t v=0;for(unsigned i=0;i<n;i++)v=v<<8|p[i];return v;}
// ---- SOCKS5 (RFC 1928) with username/password (RFC 1929), for the leader's connection to the
// server through a local Tor client. The server is named by HOSTNAME (address type 3), so this
// process never resolves it; the proxy's own address must be numeric. Tor puts streams with
// different credentials on different circuits (IsolateSOCKSAuth, on by default), so the
// credentials choose the circuit. Tor is outside the MPC: it only ever sees TLS ciphertext.
struct Socks{std::string host,user,pass;unsigned port=0;};
// Proxy part of a connect request from `at`: host length 2, host, port 2, username length 1,
// username, password length 1, password.
static bool socks_request(const std::vector<uint8_t>&p,size_t at,Socks&out){
    auto take=[&](unsigned width,std::string&s){
        if(at+width>p.size())return false;const size_t n=big(p.data()+at,width);at+=width;
        if(n==0||at+n>p.size())return false;s.assign(p.begin()+at,p.begin()+at+n);at+=n;return true;
    };
    if(!take(2,out.host)||out.host.size()>253||at+2>p.size())return false;
    out.port=unsigned(big(p.data()+at,2));at+=2;
    return take(1,out.user)&&take(1,out.pass)&&at==p.size()&&out.port>0;
}
static int socks_connect(const Socks&via,const std::string&host,unsigned port){
    if(host.empty()||host.size()>255||port==0||port>65535)throw std::runtime_error("proxied endpoint");
    addrinfo hints{},*list=nullptr;hints.ai_socktype=SOCK_STREAM;hints.ai_flags=AI_NUMERICHOST|AI_NUMERICSERV;
    if(getaddrinfo(via.host.c_str(),std::to_string(via.port).c_str(),&hints,&list)!=0||!list)throw std::runtime_error("proxy address (numeric only)");
    int fd=::socket(list->ai_family,list->ai_socktype,list->ai_protocol);bool ok=fd>=0&&::connect(fd,list->ai_addr,list->ai_addrlen)==0;freeaddrinfo(list);
    if(!ok){if(fd>=0)::close(fd);throw std::runtime_error("proxy connect");}
    try{
#ifdef SO_NOSIGPIPE
        {int one=1;::setsockopt(fd,SOL_SOCKET,SO_NOSIGPIPE,&one,sizeof one);}   // a dropped circuit fails the write instead of killing the worker
#endif
        timeval limit{120,0};::setsockopt(fd,SOL_SOCKET,SO_RCVTIMEO,&limit,sizeof limit);   // building a circuit can take a while
        auto put=[&](const std::vector<uint8_t>&b){write_all(fd,b.data(),b.size());};
        auto get=[&](size_t n){std::vector<uint8_t>b(n);if(!read_exact(fd,b.data(),n))throw std::runtime_error("proxy closed");return b;};
        put({5,1,2});   // the only method offered is username/password: the circuit is always chosen by the credentials
        if(get(2)!=std::vector<uint8_t>{5,2})throw std::runtime_error("proxy refused username/password authentication");
        std::vector<uint8_t>auth{1,uint8_t(via.user.size())};auth.insert(auth.end(),via.user.begin(),via.user.end());
        auth.push_back(uint8_t(via.pass.size()));auth.insert(auth.end(),via.pass.begin(),via.pass.end());put(auth);
        if(get(2)!=std::vector<uint8_t>{1,0})throw std::runtime_error("proxy rejected the credentials");
        std::vector<uint8_t>ask{5,1,0,3,uint8_t(host.size())};ask.insert(ask.end(),host.begin(),host.end());ask.push_back(uint8_t(port>>8));ask.push_back(uint8_t(port));put(ask);
        auto head=get(4);
        if(head[0]!=5||head[1]!=0||head[2]!=0)throw std::runtime_error("proxy could not reach the server (SOCKS reply "+std::to_string(head[1])+")");
        const size_t bound=head[3]==1?4:head[3]==4?16:head[3]==3?size_t(get(1)[0]):0;
        if(!bound)throw std::runtime_error("proxy reply address");
        get(bound+2);
        timeval none{0,0};::setsockopt(fd,SOL_SOCKET,SO_RCVTIMEO,&none,sizeof none);
    }catch(...){::close(fd);throw;}
    return fd;
}
struct Worker {
    int party;NetIO&io;Challenge&channel;TlsKernels&kernels;std::string session;int server=-1;
    enum class Phase{fresh,begun,derived,finished,retired}phase=Phase::fresh;
    // TEST FIXTURE ONLY (TLS_WORKER_TEST_PRODUCER=bytes in both workers' environment):
    // private payloads neither party knows are produced inside the engines, as
    // handles 1, 2, 5 in the order the Lean application fixture expects.
    ServiceKernels*service=nullptr;bool service_fixture=false;   // TLS_WORKER_SERVICE_FIXTURE=text: admit the public text fixture at retirement
    static Bytes receipt(std::pair<uint64_t,size_t>r){Bytes out;for(int i=7;i>=0;i--)out.push_back(uint8_t(r.first>>(8*i)));out.push_back(uint8_t(r.second>>8));out.push_back(uint8_t(r.second));return out;}
    size_t test_bytes=0;uint64_t produced_handle=0;unsigned produced=0;bool sealed_pending=false;std::deque<uint64_t>awaiting_echo;
    ~Worker(){if(server>=0)::close(server);drop_connections();}
    void need(bool ok,const char*what){if(!ok)throw std::runtime_error(what);}
    // ---- Connection table (operation 90; one TLS connection per Tor circuit). One connection is
    // active: `server`, `phase`, the TLS secrets in `kernels` and the WebSocket state in `service`
    // are its own. The others are parked here with theirs; the active one's slot holds an empty
    // state. Every operation that touches a connection acts on the active one, so a controller that
    // never selects uses connection 0 exactly as before. Shared by all: the engines, circuits,
    // conversion masks, private buffers, contacts and the account.
    struct Connection{int server=-1;Phase phase=Phase::fresh;TlsKernels::Parked tls;ServiceKernels::Socket socket;};
    std::vector<Connection>parked=std::vector<Connection>(1);size_t active=0;
    int proxied=-1;   // -1 before the first connect; then whether it went through a proxy, the same for every connection
    void exchange(Connection&c){std::swap(server,c.server);std::swap(phase,c.phase);kernels.exchange(c.tls);service->exchange(c.socket);}
    void select(size_t to){
        need(service&&to<64&&to<=parked.size(),"connection index");
        if(to==parked.size())parked.emplace_back();   // a new connection is the next index, fresh
        if(to==active)return;
        exchange(parked[active]);exchange(parked[to]);active=to;
    }
    void drop_connections(){for(auto&c:parked){if(party==ALICE&&c.server>=0)::close(c.server);c=Connection{};}}
    // Leader: one whole record from the server. When the server or the proxy has closed the
    // connection, the other party is told (a size no record has) before this fails, so both
    // workers stop at the same operation instead of one waiting for the other.
    Bytes server_record(){
        Bytes record(5);bool ok=read_exact(server,record.data(),5);const size_t n=ok?big(record.data()+3,2):0;
        if(ok&&n<=16640){record.resize(5+n);ok=read_exact(server,record.data()+5,n);}
        if(!ok||n>16640){uint8_t gone[4]={255,255,255,255};io.send_data(gone,4);io.flush();throw std::runtime_error(ok?"record bound":"server closed");}
        return record;
    }
    // Leader: one whole record, or false when the connection was closed (or what arrived is not
    // a record). Nothing is told to the other party here.
    bool server_record_soft(Bytes&record){
        record.assign(5,0);bool ok=read_exact(server,record.data(),5);const size_t n=ok?big(record.data()+3,2):0;
        if(ok&&n<=16640){record.resize(5+n);ok=read_exact(server,record.data()+5,n);}
        return ok&&n<=16640;
    }
    static ServiceKernels::ContactId contact(const Bytes&p){ServiceKernels::ContactId id{};std::copy_n(p.begin(),16,id.begin());return id;}
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
        ProfileScope scope("operation "+std::to_string(code)+": request agreement and everything not listed separately");
        return dispatch(code,sequence,p);
    }
    Bytes dispatch(uint8_t code,uint64_t sequence,const Bytes&p){
        // Operations 36, 39 and 47 carry this party's PRIVATE bytes after a public prefix; only the
        // prefix and the total size are agreed.
        if(code==36||code==39||code==47||code==53){
            const size_t open=code==36?16:0;need(p.size()>=open,"private request shape");
            Bytes agreed(p.begin(),p.begin()+open);for(int i=3;i>=0;i--)agreed.push_back(uint8_t(uint64_t(p.size())>>(8*i)));
            agree(code,sequence,agreed);
        }else agree(code,sequence,p);
        switch(code){
        // Contact state at rest (service_kernels.h). Ids are u128, big-endian.
        case 36:{need(phase==Phase::retired&&service&&p.size()==48,"contact key");std::array<uint8_t,32>share{};std::copy_n(p.begin()+16,32,share.begin());service->contact_key(contact(p),share);return {};}
        // Reply 255, or 0 when the key check fails: that contact stays unloaded and the session carries on.
        case 37:{need(phase==Phase::retired&&service&&p.size()>40&&p.size()<=40+16384,"contact open");return service->contact_open(contact(p),Bytes(p.begin()+16,p.begin()+24),Bytes(p.begin()+24,p.begin()+40),Bytes(p.begin()+40,p.end()));}
        case 38:{need(phase==Phase::retired&&service&&p.size()==24,"contact seal");return service->contact_seal(contact(p),Bytes(p.begin()+16,p.end()));}
        // Notify path: a send to a contact by id with a public text, then its request frame.
        case 41:{need(phase==Phase::retired&&service&&p.size()>=16+89&&p.size()<=16+330&&((p.size()-26)%80==0||(p.size()-25)%80==0),"contact send");return service->seal_open(contact(p),Bytes(p.begin()+16,p.end()));}
        case 42:{
            need(phase==Phase::retired&&service&&p.size()>28&&p.size()<=28+16384,"contact request");
            std::vector<size_t>offsets;for(int i=0;i<4;i++)offsets.push_back(big(p.data()+16+2*i,2));
            uint64_t id=service->request(contact(p),offsets,Bytes(p.begin()+24,p.begin()+28),Bytes(p.begin()+28,p.end()));
            Bytes out;for(int i=7;i>=0;i--)out.push_back(uint8_t(id>>(8*i)));return out;
        }
        // Local-server testing: admit the account (identity 32, certificate) and a contact's record
        // (id16, record) from an export, and open an unauthenticated chat socket (reply: nonce16, accept28).
        case 46:{need(phase==Phase::retired&&service&&p.size()>32,"account admit");service->admit_account(Bytes(p.begin(),p.begin()+32),Bytes(p.begin()+32,p.end()));return {};}
        case 47:{need(phase==Phase::retired&&service&&!p.empty()&&p.size()<=512,"account credentials");service->account_credentials(p);return {};}
        // A delivered envelope's sealed content: take a range of a record (handle8, offset2, count2), or drop what is held.
        case 48:{need(phase==Phase::retired&&service&&p.size()==12,"envelope take");return service->envelope_take(big(p.data(),8),big(p.data()+8,2),big(p.data()+10,2));}
        case 49:{need(phase==Phase::retired&&service&&p.empty(),"envelope drop");service->envelope_drop();return {};}
        // The account's own record at rest: this party's key share (private), seal (version 8), open (version 8, check 16, ciphertext).
        case 53:{need(phase==Phase::retired&&service&&p.size()==32,"account key");std::array<uint8_t,32>share{};std::copy_n(p.begin(),32,share.begin());service->account_key(share);return {};}
        case 54:{need(phase==Phase::retired&&service&&p.size()==8,"account seal");return service->account_seal(p);}
        case 55:{need(phase==Phase::retired&&service&&p.size()>24&&p.size()<=24+2048,"account open");service->account_open(Bytes(p.begin(),p.begin()+8),Bytes(p.begin()+8,p.begin()+24),Bytes(p.begin()+24,p.end()));return {};}
        // A contact with several devices (service_kernels.h, MULTI_DEVICE.md).
        // 56: contact id 16, payload start 2, UUID slot 2, access-key slot 2, mask 4, the prekey-fetch frame. Reply: handle 8.
        case 56:{
            need(phase==Phase::retired&&service&&p.size()>26&&p.size()<=26+16384,"bundle fetch");
            uint64_t id=service->bundle_fetch(contact(p),big(p.data()+16,2),big(p.data()+18,2),big(p.data()+20,2),Bytes(p.begin()+22,p.begin()+26),Bytes(p.begin()+26,p.end()));
            Bytes out;for(int i=7;i>=0;i--)out.push_back(uint8_t(id>>(8*i)));return out;
        }
        // 57: a range of a record (handle 8, offset 2, count 2) joins the held prekey response body; 58 drops it; 59 opens its punctuation shape.
        case 57:{need(phase==Phase::retired&&service&&p.size()==12,"bundle take");return service->bundle_take(big(p.data(),8),big(p.data()+8,2),big(p.data()+10,2));}
        case 58:{need(phase==Phase::retired&&service&&p.empty(),"bundle drop");service->bundle_drop();return {};}
        case 59:{need(phase==Phase::retired&&service&&p.empty(),"bundle shape");return service->bundle_shape();}
        // 60: contact id 16, request id 8, our registration id 4, device index 1, device count 1, step 1,
        // item offset 4, digit counts 5 (device id, registration id, signed prekey id, one-time prekey id or 0, Kyber prekey id).
        case 60:{
            need(phase==Phase::retired&&service&&p.size()==40,"bundle establish");
            std::array<size_t,6>layout{size_t(big(p.data()+31,4)),p[35],p[36],p[37],p[38],p[39]};
            return service->bundle_establish(contact(p),p[28],p[29],p[30],layout,Bytes(p.begin()+24,p.begin()+28),Bytes(p.begin()+16,p.begin()+24));
        }
        // 61: contact id 16, our address 17 (account id, device id), the built text. Reply: timestamp 8, then per device length 2 and envelope.
        case 61:{need(phase==Phase::retired&&service&&p.size()>=33+89&&p.size()<=33+330&&((p.size()-43)%80==0||(p.size()-42)%80==0),"devices send");return service->seal_devices(contact(p),Bytes(p.begin()+16,p.begin()+33),Bytes(p.begin()+33,p.end()));}
        // 62: contact id 16, payload start 2, UUID slot 2, access-key slot 2, device count 1, per device its id slot 2 and registration-id slot 2, mask 4, frame.
        case 62:{
            need(phase==Phase::retired&&service&&p.size()>23,"devices request");const size_t n=p[22];need(n>=1&&n<=6&&p.size()>27+4*n&&p.size()<=27+4*n+16384,"devices request");
            std::vector<std::pair<size_t,size_t>>slots;for(size_t i=0;i<n;i++)slots.push_back({big(p.data()+23+4*i,2),big(p.data()+25+4*i,2)});
            uint64_t id=service->request_devices(contact(p),big(p.data()+16,2),big(p.data()+18,2),big(p.data()+20,2),slots,Bytes(p.begin()+23+4*n,p.begin()+27+4*n),Bytes(p.begin()+27+4*n,p.end()));
            Bytes out;for(int i=7;i>=0;i--)out.push_back(uint8_t(id>>(8*i)));return out;
        }
        // 63: contact id 16, device count 1, the devices' kinds, version 8, check 16, ciphertext.
        case 63:{
            need(phase==Phase::retired&&service&&p.size()>17,"devices open");const size_t n=p[16];need(n>=1&&n<=6&&p.size()>41+n&&p.size()<=41+n+16384,"devices open");
            return service->contact_open_devices(contact(p),Bytes(p.begin()+17,p.begin()+17+n),Bytes(p.begin()+17+n,p.begin()+25+n),Bytes(p.begin()+25+n,p.begin()+41+n),Bytes(p.begin()+41+n,p.end()));
        }
        // A refresh's new device list is scratch until stored (service_kernels.h, `Establishing`).
        // 64: contact id 16, version 8: the scratch sealed for the database nodes. Reply: check 16, ciphertext.
        // 65: contact id 16: the scratch becomes the contact's state. (58 drops it.)
        case 64:{need(phase==Phase::retired&&service&&p.size()==24,"scratch seal");return service->scratch_seal(contact(p),Bytes(p.begin()+16,p.end()));}
        case 65:{need(phase==Phase::retired&&service&&p.size()==16,"scratch commit");service->scratch_commit(contact(p));return {};}
        // 66: 1 to 64 contact ids (16 each): prepare them for sending, in the same field rounds with
        // TLS_WORKER_HINTED. Reply: one byte per contact (255 prepared, 0 its key is refused, 1 not loaded).
        case 66:{
            need(phase==Phase::retired&&service&&!p.empty()&&p.size()%16==0&&p.size()<=16*64,"contacts prepare");
            std::vector<ServiceKernels::ContactId>ids;for(size_t i=0;i<p.size();i+=16){ServiceKernels::ContactId id{};std::copy_n(p.begin()+i,16,id.begin());ids.push_back(id);}
            return service->prepare_batch(ids);
        }
        case 52:{
            need(phase==Phase::retired&&service&&p.size()==32,"contact assign");ServiceKernels::ContactId to{};std::copy_n(p.begin()+16,16,to.begin());
            return service->contact_assign(contact(p),to);
        }
        // Receive the held envelope as a new contact's first message (service_kernels.h).
        // 50: our identity public key 32, time 8, server key 32, then the two forms of the trusted signer, each with a 2-byte length.
        case 50:{
            need(phase==Phase::retired&&service&&p.size()>=76,"envelope open");const size_t first=big(p.data()+72,2);
            need(p.size()>=76+first,"envelope open");const size_t second=big(p.data()+74+first,2);need(p.size()==76+first+second,"envelope open");
            return service->envelope_open(Bytes(p.begin(),p.begin()+32),Bytes(p.begin()+32,p.begin()+40),Bytes(p.begin()+40,p.begin()+72),
                Bytes(p.begin()+74,p.begin()+74+first),Bytes(p.begin()+76+first,p.end()));
        }
        // 51: new contact id 16, our address 17, signed prekey 32, one-time prekey 32, Kyber secret 32, request id 8.
        case 51:{
            need(phase==Phase::retired&&service&&p.size()==137,"envelope session");std::array<uint8_t,32>signed_key{},one_time{};
            std::copy_n(p.begin()+33,32,signed_key.begin());std::copy_n(p.begin()+65,32,one_time.begin());
            return service->envelope_session(contact(p),Bytes(p.begin()+16,p.begin()+33),signed_key,one_time,Bytes(p.begin()+97,p.begin()+129),Bytes(p.begin()+129,p.end()));
        }
        case 44:{need(phase==Phase::retired&&service&&p.size()>16,"contact admit");service->admit_contact(contact(p),Bytes(p.begin()+16,p.end()));return {};}
        case 45:{need(phase==Phase::retired&&service&&p.empty(),"public upgrade");auto nonce=joint_random();nonce.resize(16);return service->upgrade_public(nonce);}
        case 40:{need(phase==Phase::retired&&service&&p.size()==16,"contact evict");service->contact_evict(contact(p));return {};}
        // Each party sends its private bytes and receives the other's (for values that are safe
        // to reveal, such as parity shares of a consistency check).
        case 39:{need(!p.empty()&&p.size()<=65536,"exchange");Bytes mine=p,peer(p.size());channel.transfer(mine.data(),peer.data(),mine.size());return peer;}
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
        case 18:{need(phase==Phase::retired&&service&&!service->public_receive&&p.size()==8,"process WebSocket");return service->process(big(p.data(),8));}
        // Public-receive profile (PublicServiceController.lean).
        case 29:{need(phase==Phase::retired&&service&&service->public_receive&&p.size()==10,"reveal");return kernels.reveal_byte(big(p.data(),8),big(p.data()+8,2));}
        case 43:{need(phase==Phase::retired&&service&&service->public_receive&&p.size()==12,"reveal range");return kernels.reveal_range(big(p.data(),8),big(p.data()+8,2),big(p.data()+10,2));}
        case 30:{need(phase==Phase::retired&&service&&service->public_receive&&!p.empty(),"public buffer");Bytes out;uint64_t id=kernels.public_buffer(p);for(int i=7;i>=0;i--)out.push_back(uint8_t(id>>(8*i)));return out;}
        case 34:{need(phase==Phase::retired&&service&&p.size()==16&&big(p.data(),8)==1,"seal envelope");return service->seal_open(big(p.data()+8,8));}
        case 35:{
            need(phase==Phase::retired&&service&&p.size()>20&&p.size()<=20+16384,"request frame");
            std::vector<size_t>offsets;for(int i=0;i<4;i++)offsets.push_back(big(p.data()+8+2*i,2));
            uint64_t id=service->request(big(p.data(),8),offsets,Bytes(p.begin()+16,p.begin()+20),Bytes(p.begin()+20,p.end()));
            Bytes out;for(int i=7;i>=0;i--)out.push_back(uint8_t(id>>(8*i)));return out;
        }
        case 33:{need(phase==Phase::retired&&p.empty(),"public random");return joint_random();}   // commit-then-open, 32 public bytes
        case 31:{
            need(phase==Phase::retired&&service&&service->public_receive&&p.size()==16&&big(p.data(),8)==1,"provider produce");
            auto out=receipt(service->produce(big(p.data()+8,8)));out.insert(out.end(),service->last_request_id.begin(),service->last_request_id.end());return out;
        }
        case 32:{
            need(phase==Phase::retired&&service&&p.size()==8&&big(p.data(),8)==1,"provider upgrade");service->public_receive=true;
            auto nonce=joint_random();nonce.resize(16);auto out=receipt(service->upgrade(nonce));out.insert(out.end(),service->accept_bytes.begin(),service->accept_bytes.end());return out;
        }
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
            // A connection that the server or the proxy closed is not the worker's failure: both
            // parties get the one-byte reply {0} (no record is that short), the connection is gone
            // (91 replaces it) and the worker, with every other connection, carries on.
            need(server>=0&&p.empty(),"poll");uint8_t size[4]={0,0,0,0};Bytes record;
            if(party==ALICE){
                pollfd watch{server,POLLIN,0};bool lost=false;
                if(::poll(&watch,1,0)>0)lost=!server_record_soft(record);
                if(lost){uint8_t gone[4]={255,255,255,255};io.send_data(gone,4);io.flush();::close(server);server=-1;return {0};}
                for(int i=0;i<4;i++)size[i]=uint8_t(record.size()>>(8*(3-i)));io.send_data(size,4);if(!record.empty())io.send_data(record.data(),record.size());io.flush();
            }else{
                io.recv_data(size,4);size_t n=big(size,4);
                if(n==0xffffffff){server=-1;return {0};}
                if(n){need(n>=5&&n<=5+16640,"record bound");record.resize(n);io.recv_data(record.data(),n);need(big(record.data()+3,2)+5==n,"record framing");}
            }
            return record;
        }
        // 90: select connection p[0] (the next unused index opens a new, fresh one). Public, agreed.
        case 90:{need(p.size()==1,"use connection");select(p[0]);return {};}
        // 91: the selected connection was reported closed (17). It is replaced by a fresh one: no
        // socket, no TLS and no WebSocket state, to be connected and shaken hands on again (9, 1..7).
        // The other connections, the engines, the contacts and the account are untouched.
        case 91:{need(service&&server<0&&phase==Phase::retired&&p.empty(),"reset connection");Connection fresh;exchange(fresh);return {};}
        case 9:{
            // Host length 2, host, port 2; through a SOCKS5 proxy, followed by the proxy part
            // (socks_request). Both parties agree on all of it, so neither can go direct while the
            // other believes the connection is proxied, or use other credentials (circuit, count).
            need(server<0&&p.size()>=5,"connect");size_t n=big(p.data(),2);need(p.size()>=n+4&&n>0,"connect shape");
            Socks via;const bool proxy=p.size()>n+4;
            need(!proxy||socks_request(p,n+4,via),"proxy shape");
            need(proxied<0||proxied==int(proxy),"every connection of a worker goes the same way");proxied=int(proxy);
            if(party==ALICE&&proxy){server=socks_connect(via,std::string(p.begin()+2,p.begin()+2+n),unsigned(big(p.data()+2+n,2)));return {};}
            if(party==ALICE){
                std::string host(p.begin()+2,p.begin()+2+n),port=std::to_string(big(p.data()+2+n,2));addrinfo hints{},*list=nullptr;hints.ai_socktype=SOCK_STREAM;
                need(getaddrinfo(host.c_str(),port.c_str(),&hints,&list)==0&&list,"resolve");
                int fd=::socket(list->ai_family,list->ai_socktype,list->ai_protocol);bool ok=fd>=0&&::connect(fd,list->ai_addr,list->ai_addrlen)==0;freeaddrinfo(list);
                if(!ok){if(fd>=0)::close(fd);throw std::runtime_error("connect");}server=fd;
            }else server=0;
            return {};
        }
        case 10:{
            // A write to a connection the server or the proxy has closed is dropped: the next poll (17)
            // reports the closure to both parties. (Only the leader could see it here.)
            need(server>=0&&p.size()>=5&&p.size()<=5+16640,"send");if(party==ALICE){try{write_all(server,p.data(),p.size());}catch(const std::runtime_error&){}}
            if(sealed_pending){sealed_pending=false;awaiting_echo.push_back(produced_handle);if(produced<3){produced_handle=kernels.test_produce(test_bytes);produced++;}}
            return {};
        }
        case 11:{
            need(server>=0&&p.empty(),"receive");Bytes record(5);uint8_t size[4];
            if(party==ALICE){
                record=server_record();
                for(int i=0;i<4;i++)size[i]=uint8_t(record.size()>>(8*(3-i)));io.send_data(size,4);io.send_data(record.data(),record.size());io.flush();
            }else{
                io.recv_data(size,4);size_t n=big(size,4);need(n!=0xffffffff,"server closed (reported by the leader)");need(n>=5&&n<=5+16640,"record bound");record.resize(n);io.recv_data(record.data(),n);
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
    ::signal(SIGPIPE,SIG_IGN);   // a write to a closed server connection fails (operation 10 drops it) instead of killing the worker
    auto reply=[&](bool ok,const Bytes&payload){Bytes out{uint8_t(ok?0:1)};for(int i=3;i>=0;i--)out.push_back(uint8_t(uint64_t(payload.size())>>(8*i)));out.insert(out.end(),payload.begin(),payload.end());write_all(rpc,out.data(),out.size());};
    try{
        int party=std::stoi(argv[1])+1;unsigned port=std::stoul(argv[3]);std::string session=argv[5];
        if((party!=ALICE&&party!=BOB)||session.size()!=64||session.find_first_not_of("0123456789abcdef")!=std::string::npos)return 2;
        auto started=std::chrono::steady_clock::now();
        // TEST ONLY (TLS_WORKER_TEST_LINK_SHIFT=N): the connecting party dials PORT+N for every link to
        // the other worker (this channel and its siblings, the field engine and its stock lines), where
        // scripts/delay_relay.cpp listens and forwards to PORT with a fixed delay. The listening party
        // is unchanged. Without the variable nothing changes.
        unsigned link_shift=0;
        if(const char*requested=std::getenv("TLS_WORKER_TEST_LINK_SHIFT")){link_shift=std::stoul(requested);if(link_shift<12||link_shift>1000)return 2;if(party==ALICE)link_shift=0;}
        // The other worker's address (TLS_WORKER_PEER, default 127.0.0.1) and the address this one
        // listens on (TLS_WORKER_LISTEN, default all interfaces): peer_link.h.
        const PeerLink link=PeerLink::from_environment();
        const auto io_owner=link.open(party==ALICE,port+link_shift);NetIO&io=*io_owner;ThreadPool threads(4);
        // The split agreement needs about a dozen field products; the ladder thousands.
        const char*route=std::getenv("TLS_WORKER_KEY_AGREEMENT");const bool ladder=route&&std::string(route)=="ladder";
        if(route&&!ladder&&std::string(route)!="split")return 2;
        const char*fixture=std::getenv("TLS_WORKER_SERVICE_FIXTURE");if(fixture&&std::string(fixture)!="text")return 2;
        // Sealed sender needs thousands of field products per send (ladder on a private point).
        // Field preprocessing batch: large when the Signal service path will run (fixture, or
        // TLS_WORKER_FIELD_BATCH for contacts admitted at run time).
        unsigned batch=(ladder||fixture)?3000:16;
        if(const char*requested=std::getenv("TLS_WORKER_FIELD_BATCH")){batch=std::stoul(requested);if(batch<1||batch>100000)return 2;}
        // AND triples minted ahead of use by background pools of this session (dyn_session.h).
        // TLS_WORKER_TRIPLE_STOCK=FACTORIES[,BATCH[,RESERVE]]; 0 mints inside each circuit run.
        // Both workers must be configured alike: the setting is part of every agreed request.
        unsigned factories=2;size_t stock_batch=size_t(1)<<19,stock_reserve=size_t(1)<<22;
        if(const char*requested=std::getenv("TLS_WORKER_TRIPLE_STOCK")){
            unsigned long long a=2,b=stock_batch,c=stock_reserve;const int n=std::sscanf(requested,"%llu,%llu,%llu",&a,&b,&c);
            if(n<1||a>8||b<1024||b>(1ull<<24)||c>(1ull<<28))return 2;
            factories=unsigned(a);stock_batch=size_t(b);stock_reserve=size_t(c);
        }
        DynSession mpc(&io,&threads,party,128);if(factories)mpc.start_stock(factories,stock_batch,stock_reserve);
        // Field triples generated ahead of use (field_engine.h): TLS_WORKER_FIELD_STOCK=RESERVE[,LINES], 0 for none.
        unsigned field_reserve=8*batch,field_lines=2;
        if(const char*requested=std::getenv("TLS_WORKER_FIELD_STOCK")){
            unsigned long long a=0,b=field_lines;const int n=std::sscanf(requested,"%llu,%llu",&a,&b);
            if(n<1||a>10000000||b<1||b>8)return 2;
            field_reserve=unsigned(a);field_lines=unsigned(b);
        }
        // (With the test shift the field engine's parties connect directly, so that its links pass the relay too.)
        // TLS_WORKER_FIELD_DIRECT=1: the field engine's openings sent by both parties at once (one message
        // delay per multiplication round instead of two; field_engine.h). 0 (default): as before.
        // Both workers must be configured alike: the setting is part of every agreed request.
        bool field_direct=false;
        if(const char*requested=std::getenv("TLS_WORKER_FIELD_DIRECT")){const std::string value(requested);if(value!="0"&&value!="1")return 2;field_direct=value=="1";}
        FE field(party-1,port+10+link_shift,batch,nullptr,field_reserve,field_lines,link.remote()?link.field_peer():std::getenv("TLS_WORKER_TEST_LINK_SHIFT")?"127.0.0.1":nullptr,field_direct);
        Challenge channel{io,party,"tls-worker-v3:session="+session};
        auto&profile=Profile::get();
        profile.gates=[&]{return mpc.and_gates();};profile.products=[&]{return field.products();};
        profile.boolean_bytes=[&]{return uint64_t(mpc.sent_bytes());};profile.field_bytes=[&]{return field.sent_bytes();};
        TlsKernels kernels(mpc,field,channel,party,argv[4]);kernels.prepare();
        Worker worker{party,io,channel,kernels,session};
        if(const char*test=std::getenv("TLS_WORKER_TEST_PRODUCER")){worker.test_bytes=std::stoul(test);if(!worker.test_bytes||worker.test_bytes>16384)return 2;std::cerr<<"tls-worker-v3 TEST producer enabled bytes="<<worker.test_bytes<<"\n";}
        // Both workers must be configured alike: the route is part of every agreed request.
        kernels.ladder_agreement=ladder;
        // Received records. TLS_WORKER_TYPED_OPEN=1 (the default): open the record-type bit first and run
        // the framing scan only on handshake records (TlsMpc/TypedOpenKernels.lean; what the bit reveals
        // and what is proved: NEEDS_REVIEW.md section 2); 0: scan every record.
        // Both workers must be configured alike: the setting is part of every agreed request.
        bool typed_open=true;
        if(const char*requested=std::getenv("TLS_WORKER_TYPED_OPEN")){const std::string value(requested);if(value!="0"&&value!="1")return 2;typed_open=value=="1";}
        kernels.typed_open=typed_open;
        ServiceKernels service(kernels);worker.service=&service;worker.service_fixture=fixture!=nullptr;
        if(fixture)std::cerr<<"tls-worker-v3 TEST service fixture enabled\n";
        // TLS_WORKER_HINTED=1: the constant-depth curve programs (TlsMpc/EdwardsHinted.lean, hinted_points.h)
        // instead of the ladders and chains: a few dozen field rounds where there were thousands. What
        // they open and where they differ on malformed keys: NEEDS_REVIEW.md. 0 (default): as before.
        // Both workers must be configured alike: the setting is part of every agreed request.
        if(const char*requested=std::getenv("TLS_WORKER_HINTED")){const std::string value(requested);if(value!="0"&&value!="1")return 2;service.hinted=value=="1";}
        if(service.hinted)worker.session+=":hinted";
        if(field_direct)worker.session+=":field-direct";
        worker.session+=kernels.ladder_agreement?":ladder":":split";
        worker.session+=kernels.typed_open?":typed-open":":scan-open";
        worker.session+=":stock="+std::to_string(factories)+","+std::to_string(factories?stock_batch:0)+","+std::to_string(factories?stock_reserve:0)
            +":field="+std::to_string(batch)+","+std::to_string(field_reserve)+","+std::to_string(field_lines);
        std::cerr<<"tls-worker-v3 security_mode="<<SECURITY_MODE<<" key_agreement="<<(kernels.ladder_agreement?"ladder":"split")<<"\n";
        std::cerr<<"tls-worker-v3 operation 0 ok seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<" and_gates="<<kernels.and_gates()<<" emp_sent_bytes="<<mpc.sent_bytes()<<" field_sent_bytes="<<field.sent_bytes()<<" field_products="<<field.products()<<"\n";
        bool failed=false;uint64_t expected=0;double busy=0;
        for(;;){
            uint8_t head[13];if(!read_exact(STDIN_FILENO,head,13))break;
            uint64_t sequence=big(head+1,8);size_t size=big(head+9,4);if(size>2*1024*1024)throw std::runtime_error("request bound");
            Bytes payload(size);if(size&&!read_exact(STDIN_FILENO,payload.data(),size))break;
            if(head[0]==8){profile.report(std::cerr,"tls-worker-v3 profile");kernels.abort();worker.drop_connections();failed=true;std::cerr<<"tls-worker-v3 operation 8 ok (local abort)\n";reply(true,{});continue;}   // local, idempotent; not an erasure receipt
            if(failed||sequence!=expected++){failed=true;reply(false,{});continue;}
            try{
                // `busy`: time inside the worker since the last line (this call and any empty polls);
                // the rest of the interval was spent outside it (controller, server, waiting).
                const auto entered=std::chrono::steady_clock::now();
                auto out=worker.call(head[0],sequence,payload);
                busy+=std::chrono::duration<double>(std::chrono::steady_clock::now()-entered).count();
                const double spent=busy;if(!(head[0]==17&&out.empty()))busy=0;
                if(!(head[0]==17&&out.empty()))std::cerr<<"tls-worker-v3 operation "<<unsigned(head[0])<<" ok seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<" and_gates="<<kernels.and_gates()<<" emp_sent_bytes="<<mpc.sent_bytes()<<" field_sent_bytes="<<field.sent_bytes()<<" field_products="<<field.products()<<" busy="<<spent<<"\n";
                reply(true,out);
            }catch(const std::exception&e){std::cerr<<"tls-worker-v3 operation "<<unsigned(head[0])<<" rejected: "<<e.what()<<"\n";failed=true;kernels.abort();worker.drop_connections();reply(false,{});}
        }
        profile.report(std::cerr,"tls-worker-v3 profile");
        std::cerr<<"tls-worker-v3 stock factories="<<factories<<" minted="<<mpc.stock_minted()<<" mint_seconds="<<mpc.stock_seconds()<<"\n";
        std::cerr<<"tls-worker-v3 totals and_gates="<<kernels.and_gates()<<" emp_sent_bytes="<<mpc.sent_bytes()<<""<<"\n";
        return 0;
    }catch(const std::exception&e){std::cerr<<"tls-worker-v3 aborted: "<<e.what()<<"\n";try{reply(false,{});}catch(...){}return 1;}
}
int main(int argc,char**argv){
    int code=1;
    try{emp_hybrid::run_with_stack(size_t(1)<<30,[&]{code=run(argc,argv);});}catch(...){return 1;}
    return code;
}
