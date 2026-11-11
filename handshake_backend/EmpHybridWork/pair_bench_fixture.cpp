// TEST FIXTURE: the per-message work of one worker pair, between two machines, without a
// Signal server, a database or a controller (deployment/vm_pair_test/README.md).
//
// It drives the same layers as the worker and adds no engine code: the Boolean session of
// dyn_session.h (malicious statistical 128, or the semi-honest build) with its AND-triple stock,
// the field engine with its triple stock, the pinned Lean circuits and field programs. Like
// dyn_run_fixture it runs circuits by file and pin; like rounds_fixture it runs the curve programs.
//
// What one iteration is: the per-message field program (the offset agreement's sum,
// edwards_points.h, with the fixture's opening and its comparison against X25519), then every
// circuit of the list once, in order, on private all-zero inputs supplied by party 1, opening the
// first output byte. A circuit's cost does not depend on its input values. What an iteration
// is NOT: the conversion of the agreement into the Boolean engine, the openings and exchanges of
// the real sequence, the controllers, the server. So this is the engines' share of a message.
//
// Before the iterations: one contact's first-send preparation, the way the worker does it by
// default (the offset agreement's `prepare` program and the long-term agreement by the ladder).
//
// Usage: PARTY(1|2) PORT PEER LISTEN CIRCUIT_LIST ITERATIONS
//   PEER    the other party's address (numeric IPv4); party 2 dials it. 127.0.0.1: one machine.
//   LISTEN  the address party 1's Boolean listener binds, or - for all interfaces.
//   CIRCUIT_LIST  first line PAIR_BENCH_CIRCUITS_V1, then rows "SHA256 FILE" (FILE beside the list).
// Ports: PORT (Boolean engine and its siblings) and PORT+10, PORT+11 (field engine).
// Environment, both parties alike: PAIR_BENCH_TRIPLE_STOCK=FACTORIES,BATCH,RESERVE (default
// 2,524288,4194304 as the worker; 0 for none), PAIR_BENCH_FIELD_STOCK=RESERVE,LINES (24000,2;
// 0 for none), PAIR_BENCH_FIELD_BATCH (3000).
// Output: one line per stage and per iteration on stdout, flushed (see `line`).
#include "dyn_session.h"
#include "hinted_points.h"
#include "big_stack.h"
#include "peer_link.h"
#include <sys/resource.h>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <iostream>
using namespace emp;
using namespace emp_hybrid;
using Clock=std::chrono::steady_clock;
static void need(bool ok,const char*what){if(!ok)throw std::runtime_error(what);}
static double since(Clock::time_point t){return std::chrono::duration<double>(Clock::now()-t).count();}
// As rounds_fixture: deterministic test scalars both processes derive alike (public in this fixture).
static Bytes32 test_scalar(const std::string&label,unsigned i){
    Bytes32 out{};std::string s="pair-bench:"+label+":"+std::to_string(i);SHA256(reinterpret_cast<const uint8_t*>(s.data()),s.size(),out.data());
    out[0]&=248;out[31]&=127;out[31]|=64;return out;
}
static uint64_t swap_bit(const Bytes32&scalar,unsigned step,bool top){
    auto bit=[&](unsigned i){return uint64_t((scalar[i/8]>>(i%8))&1);};
    return step==2?bit(3):step==253?(bit(253)^uint64_t(top)):(bit(step+1)^bit(step));
}
// As rounds_fixture and TlsKernels::shared_scalar: ladder swap bits of the XOR of both parties' shares.
static std::vector<H> shared_swaps(FE&f,const WordCircuits&circuits,int party,const Bytes32&share){
    std::vector<uint64_t>local(252);for(unsigned step=2;step<=253;step++)local[step-2]=swap_bit(share,step,party==ALICE);
    auto shares=f.input_coins(local);f.check();
    std::vector<H>all=shares[0];all.insert(all.end(),shares[1].begin(),shares[1].end());
    for(auto&v:f.checked_open(circuits.field_bit_checks(f,all)))for(auto byte:v)need(!byte,"non-bit");
    return circuits.field_bit_xor(f,shares[0],shares[1]);
}
struct Listed {std::string name;std::unique_ptr<LeanCircuit>circuit;};
// Counters of both engines at one moment; `line` prints the difference to an earlier moment.
struct Counters {
    Clock::time_point at;uint64_t ands=0,products=0,boolean_sent=0,field_sent=0;std::array<uint64_t,3>exchanges{};double field_waited=0;
    Counters(DynSession&s,FE&f):at(Clock::now()),ands(s.and_gates()),products(f.products()),boolean_sent(s.sent_bytes()),field_sent(f.sent_bytes()),exchanges(f.exchanges()),field_waited(f.stock_waited()){}
};
static void line(const std::string&head,const Counters&a,const Counters&b){
    std::cout<<head<<" seconds="<<std::chrono::duration<double>(b.at-a.at).count()<<" and_gates="<<b.ands-a.ands<<" field_products="<<b.products-a.products
        <<" field_mul_rounds="<<b.exchanges[0]-a.exchanges[0]<<" field_openings="<<b.exchanges[1]-a.exchanges[1]<<" field_inputs="<<b.exchanges[2]-a.exchanges[2]
        <<" boolean_sent_bytes="<<b.boolean_sent-a.boolean_sent<<" field_sent_bytes="<<b.field_sent-a.field_sent<<" field_stock_waited="<<b.field_waited-a.field_waited<<std::endl;
}
static int run(int argc,char**argv){
    if(argc!=7)return 2;
    const int party=std::stoi(argv[1]);const unsigned port=std::stoul(argv[2]);const std::string listen=argv[4];const size_t iterations=std::stoul(argv[6]);
    if((party!=ALICE&&party!=BOB)||port<1024||port>65000||!iterations||iterations>1000000)return 2;
    const PeerLink link=PeerLink::make(argv[3],listen=="-"?nullptr:listen.c_str());
    unsigned long long factories=2,stock_batch=1ull<<19,stock_reserve=1ull<<22,field_reserve=24000,field_lines=2,field_batch=3000;
    if(const char*s=std::getenv("PAIR_BENCH_TRIPLE_STOCK"))need(std::sscanf(s,"%llu,%llu,%llu",&factories,&stock_batch,&stock_reserve)>=1,"PAIR_BENCH_TRIPLE_STOCK");
    if(const char*s=std::getenv("PAIR_BENCH_FIELD_STOCK"))need(std::sscanf(s,"%llu,%llu",&field_reserve,&field_lines)>=1,"PAIR_BENCH_FIELD_STOCK");
    if(const char*s=std::getenv("PAIR_BENCH_FIELD_BATCH"))field_batch=std::stoull(s);
    need(sodium_init()>=0,"libsodium");
    // Circuits: read, hashed against the list's pins and parsed before any connection.
    auto started=Clock::now();std::vector<Listed>list;
    {
        const std::filesystem::path path(argv[5]);std::ifstream in(path);std::string row;
        need(bool(std::getline(in,row))&&row=="PAIR_BENCH_CIRCUITS_V1","circuit list format");
        while(std::getline(in,row)){
            if(row.empty())continue;
            need(row.size()>66&&row[64]==' ',"circuit list row");
            const std::string sha=row.substr(0,64),name=row.substr(65);
            need(name.find('/')==std::string::npos&&name.find("..")==std::string::npos,"circuit list file name");
            list.push_back({name,std::make_unique<LeanCircuit>((path.parent_path()/name).string(),sha.c_str())});
        }
        need(!list.empty(),"empty circuit list");
    }
    std::cout<<"BENCH start mode="<<SECURITY_MODE<<" party="<<party<<" peer="<<link.peer<<" port="<<port<<" circuits="<<list.size()<<" iterations="<<iterations
        <<" triple_stock="<<factories<<","<<stock_batch<<","<<stock_reserve<<" field_stock="<<field_reserve<<","<<field_lines<<" field_batch="<<field_batch
        <<" load_seconds="<<since(started)<<std::endl;
    started=Clock::now();
    const auto io_owner=link.open(party==ALICE,port);NetIO&io=*io_owner;ThreadPool threads(4);
    DynSession session(&io,&threads,party,128);if(factories)session.start_stock(unsigned(factories),size_t(stock_batch),size_t(stock_reserve));
    FE f(party-1,port+10,unsigned(field_batch),nullptr,unsigned(field_reserve),unsigned(field_lines),link.remote()?link.field_peer():nullptr);
    Challenge channel{io,party,"pair-bench"};
    WordCircuits circuits;X25519Fast curve;OffsetPrograms offsets;
    std::cout<<"BENCH connected seconds="<<since(started)<<std::endl;
    // Our identity key: a scalar neither process knows (XOR of two shares).
    Counters before(session,f);
    Bytes32 share{};{PRG prg;prg.random_data_unaligned(share.data(),32);}
    auto identity=shared_swaps(f,circuits,party,share);
    Counters ready(session,f);line("BENCH identity-scalar",before,ready);
    // One contact's first send: its table (the `prepare` program) and the long-term agreement (ladder).
    const Bytes32 contact=test_scalar("contact",0);Bytes32 contact_u{};need(crypto_scalarmult_base(contact_u.data(),contact.data())==0,"contact key");
    H recipient=f.public_element(contact_u);OffsetAgreement agreement;
    agreement.prepare(offsets,f,channel,party,recipient);
    Counters tabled(session,f);line("BENCH first-send-table",ready,tabled);
    {bool zero=false;curve.evaluate(f,channel,identity,recipient,zero);}
    Counters prepared(session,f);line("BENCH first-send-agreement",tabled,prepared);line("BENCH first-send-total",ready,prepared);
    // Messages.
    const Counters first(session,f);
    for(size_t i=0;i<iterations;i++){
        Counters a(session,f);
        {
            // The per-message field program, checked against X25519 (the fixture's opening).
            const Bytes32 offset=test_scalar("offset",unsigned(i));Bytes32 expected{};
            auto pair=agreement.step(offsets,f,offset);
            need(crypto_scalarmult(expected.data(),contact.data(),pair.first.data())==0,"reference agreement");
            need(f.checked_open({pair.second}).at(0)==expected,"agreement differs from X25519 of the ephemeral key");
        }
        Counters b(session,f);
        for(auto&entry:list){
            Counters c(session,f);
            const std::vector<uint8_t>zeros(entry.circuit->input_bits(),0);
            auto input=session.input_private(ALICE,zeros);
            auto output=session.run(*entry.circuit,input);
            (void)session.open(output.slice(0,std::min<size_t>(8,output.size())));
            if(i==0){Counters d(session,f);line("CIRCUIT "+entry.name,c,d);}
        }
        Counters c(session,f);
        std::cout<<"ITER "<<i<<" field_seconds="<<std::chrono::duration<double>(b.at-a.at).count()<<" boolean_seconds="<<std::chrono::duration<double>(c.at-b.at).count();
        line("",a,c);
    }
    const Counters last(session,f);line("BENCH messages count="+std::to_string(iterations),first,last);
    rusage usage{};getrusage(RUSAGE_SELF,&usage);
#ifdef __APPLE__
    const double peak_gb=double(usage.ru_maxrss)/1073741824.0;   // bytes
#else
    const double peak_gb=double(usage.ru_maxrss)/1048576.0;      // kilobytes
#endif
    std::cout<<"BENCH end peak_rss_gb="<<peak_gb<<" cpu_seconds="<<double(usage.ru_utime.tv_sec+usage.ru_stime.tv_sec)+1e-6*double(usage.ru_utime.tv_usec+usage.ru_stime.tv_usec)
        <<" total_boolean_sent_bytes="<<last.boolean_sent<<" total_field_sent_bytes="<<last.field_sent<<std::endl;
    std::cout<<"pair bench passed"<<std::endl;
    return 0;
}
int main(int argc,char**argv){
    int code=4;
    try{emp_hybrid::run_with_stack(size_t(1)<<30,[&]{try{code=run(argc,argv);}catch(const std::exception&e){std::cerr<<"pair bench failed: "<<e.what()<<"\n";code=4;}});}catch(...){return 4;}
    return code;
}
