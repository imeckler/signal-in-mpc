// TEST FIXTURE: the field engine's curve work alone, two processes, for measuring rounds over a
// link with latency (scripts/delay_relay.cpp) without a server or a Boolean circuit.
// It runs the earlier programs and the constant-depth ones (hinted_points.h) on the same
// inputs, opens both results (fixture only) and requires them equal, and prints for each
// stage: seconds, field products, multiplication rounds, openings, input exchanges.
// Usage: PARTY(1|2) PORT TEST N       TEST: calibrate | prepare | receive | store | load
//   store, load: one contact's table kept between two runs as each party's own shares and MAC
//              shares under a MAC key that persists (a proposal, see SEALED_SENDER_AGREEMENT.md):
//              `load` imports it with no interaction and sends N messages
//   calibrate: N of each kind of exchange, to see what one costs over the link
//   prepare:   N contacts prepared in one batch (and up to 2 the earlier way), then 5 messages each way
//   receive:   the field side of a first message received, N times, both ways
// Environment: TLS_WORKER_TEST_LINK_SHIFT as the worker (the connecting party dials PORT+SHIFT);
// ROUNDS_FIXTURE_STOCK=RESERVE[,LINES] (default 24000,2) and ROUNDS_FIXTURE_BATCH (3000).
#include "hinted_points.h"
#include "big_stack.h"
#include "peer_link.h"
#include <chrono>
#include <fstream>
#include <iostream>
using namespace emp;
using namespace emp_hybrid;
using Clock=std::chrono::steady_clock;
static void need(bool ok,const char*what){if(!ok)throw std::runtime_error(what);}
struct Stage {
    FE&f;Clock::time_point t;uint64_t products=0;std::array<uint64_t,3>ex{};
    explicit Stage(FE&field):f(field){begin();}
    void begin(){t=Clock::now();products=f.products();ex=f.exchanges();}
    void end(const std::string&name,size_t count=1){
        auto now=f.exchanges();
        std::cout<<"RESULT "<<name<<" count="<<count<<" seconds="<<std::chrono::duration<double>(Clock::now()-t).count()<<" products="<<f.products()-products
            <<" mul_rounds="<<now[0]-ex[0]<<" openings="<<now[1]-ex[1]<<" inputs="<<now[2]-ex[2]<<" stock_waited="<<f.stock_waited()<<std::endl;
        begin();
    }
};
// Deterministic test scalars both processes derive alike (they are public in this fixture).
static Bytes32 test_scalar(const std::string&label,unsigned i){
    Bytes32 out{};std::string s="rounds-fixture:"+label+":"+std::to_string(i);SHA256(reinterpret_cast<const uint8_t*>(s.data()),s.size(),out.data());
    out[0]&=248;out[31]&=127;out[31]|=64;return out;
}
static Bytes32 public_u(const Bytes32&scalar){Bytes32 u{};need(crypto_scalarmult_base(u.data(),scalar.data())==0,"base");return u;}
static uint64_t swap_bit(const Bytes32&scalar,unsigned step,bool top){
    auto bit=[&](unsigned i){return uint64_t((scalar[i/8]>>(i%8))&1);};
    return step==2?bit(3):step==253?(bit(253)^uint64_t(top)):(bit(step+1)^bit(step));
}
// As TlsKernels::shared_scalar: ladder swap bits of the XOR of both parties' shares.
static std::vector<H> shared_swaps(FE&f,const WordCircuits&circuits,int party,const Bytes32&share){
    std::vector<uint64_t>local(252);for(unsigned step=2;step<=253;step++)local[step-2]=swap_bit(share,step,party==ALICE);
    auto shares=f.input_coins(local);f.check();
    std::vector<H>all=shares[0];all.insert(all.end(),shares[1].begin(),shares[1].end());
    for(auto&v:f.checked_open(circuits.field_bit_checks(f,all)))for(auto byte:v)need(!byte,"non-bit");
    return circuits.field_bit_xor(f,shares[0],shares[1]);
}
static std::vector<H> public_swaps(FE&f,const Bytes32&scalar){std::vector<H>out;for(unsigned step=2;step<=253;step++)out.push_back(f.constant(swap_bit(scalar,step,true)));return out;}
static int run(int argc,char**argv){
    if(argc!=5)return 2;
    int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);const std::string test=argv[3];const size_t n=std::stoul(argv[4]);
    if((party!=ALICE&&party!=BOB)||!n||n>1000)return 2;
    unsigned shift=0;if(const char*s=std::getenv("TLS_WORKER_TEST_LINK_SHIFT")){shift=std::stoul(s);if(party==ALICE)shift=0;}
    unsigned batch=3000,reserve=24000,lines=2;
    if(const char*s=std::getenv("ROUNDS_FIXTURE_BATCH"))batch=std::stoul(s);
    if(const char*s=std::getenv("ROUNDS_FIXTURE_STOCK")){unsigned long long a=0,b=2;std::sscanf(s,"%llu,%llu",&a,&b);reserve=unsigned(a);lines=unsigned(b);}
    need(sodium_init()>=0,"libsodium");
    // TLS_WORKER_PEER / TLS_WORKER_LISTEN as the worker (peer_link.h): the two processes on two machines.
    const PeerLink link=PeerLink::from_environment();
    const auto io_owner=link.open(party==ALICE,port+shift);NetIO&io=*io_owner;
    // store / load: a MAC key share that outlives the process, and this party's shares of one
    // contact's table, in files of the working directory (fixture only; SEALED_SENDER_AGREEMENT.md,
    // "Keeping the table across sessions", option 1, without the pads and the blob).
    std::array<uint8_t,32>mac{};const std::array<uint8_t,32>*mac_share=nullptr;
    const std::string mac_file="rounds-mac-key-"+std::to_string(party)+".bin",table_file="rounds-table-"+std::to_string(party)+".bin";
    if(test=="store"||test=="load"){
        std::ifstream in(mac_file,std::ios::binary);
        if(!in.read(reinterpret_cast<char*>(mac.data()),32)){
            need(test=="store","no stored MAC key share");randombytes_buf(mac.data(),32);mac[31]&=63;mac[0]|=1;
            std::ofstream(mac_file,std::ios::binary).write(reinterpret_cast<const char*>(mac.data()),32);
        }
        mac_share=&mac;
    }
    FE f(party-1,port+10+shift,batch,mac_share,reserve,lines,link.remote()?link.field_peer():std::getenv("TLS_WORKER_TEST_LINK_SHIFT")?"127.0.0.1":nullptr,std::getenv("ROUNDS_FIXTURE_DIRECT")!=nullptr);
    Challenge channel{io,party,"rounds-fixture"};
    WordCircuits circuits;X25519Fast curve;OffsetPrograms offsets;Hinted hinted;
    Stage stage(f);
    auto opened_equal=[&](H a,H b,const char*what){auto v=f.checked_open({a,b});need(v[0]==v[1],what);};
    if(test=="calibrate"){
        auto masks=FieldProgram::masks(f,4);stage.begin();
        for(size_t i=0;i<n;i++)masks[2]=f.mul({masks[0]},{masks[1]}).at(0);
        stage.end("multiplication rounds of one product",n);
        for(size_t i=0;i<n;i++)f.checked_open({masks[2]});
        stage.end("openings of one value",n);
        for(size_t i=0;i<n;i++){f.input_coins({1});f.check();}
        stage.end("input exchanges of one value (with their check)",n);
        std::vector<H>a(1000,masks[0]),b(1000,masks[1]);
        for(size_t i=0;i<n;i++)f.mul(a,b);
        stage.end("multiplication rounds of 1000 products",n);
        std::array<uint8_t,32>mine{},peer{};
        for(size_t i=0;i<n;i++)channel.transfer(mine.data(),peer.data(),32);
        stage.end("channel transfers",n);
        return 0;
    }
    if(test=="store"){
        // One contact prepared; then each process keeps ITS OWN share of every element and of its MAC.
        OffsetAgreement a;need(hinted.prepare(f,channel,party,{&a},{f.public_element(public_u(test_scalar("contact",0)))}).at(0),"a test contact was refused");
        stage.end("store: prepare one contact");
        std::ofstream out(table_file,std::ios::binary);out.write(reinterpret_cast<const char*>(a.public_key().data()),32);
        for(auto h:a.state()){auto s=f.export_share(h);out.write(reinterpret_cast<const char*>(s.first.data()),32);out.write(reinterpret_cast<const char*>(s.second.data()),32);}
        need(bool(out),"table file");
        stage.end("store: this party's shares and MAC shares written (no exchange)");
        std::cout<<"rounds fixture passed"<<std::endl;
        return 0;
    }
    if(test=="load"){
        // A later process with the same MAC key: the table is imported with no interaction and used.
        // ROUNDS_FIXTURE_TAMPER: party 2 changes one of its value shares; the MAC check must stop the first message.
        std::ifstream in(table_file,std::ios::binary);Bytes32 k0{};need(bool(in.read(reinterpret_cast<char*>(k0.data()),32)),"no stored table");
        const bool tamper=std::getenv("ROUNDS_FIXTURE_TAMPER")!=nullptr;std::vector<H>state;
        for(unsigned i=0;i<2+2*OffsetPrograms::WINDOWS*OffsetPrograms::DIGITS;i++){
            Bytes32 value{},tag{};need(in.read(reinterpret_cast<char*>(value.data()),32)&&in.read(reinterpret_cast<char*>(tag.data()),32),"stored table shape");
            if(tamper&&party==BOB&&i==0)value[0]^=1;
            state.push_back(f.import_share(value,tag));
        }
        OffsetAgreement a;a.install(std::vector<H>(state.begin()+2,state.end()),std::vector<H>(state.begin(),state.begin()+2),k0);
        stage.end("load: the stored table imported (no exchange)");
        const Bytes32 key=test_scalar("contact",0);
        try{
            for(unsigned i=0;i<n;i++){
                Bytes32 expected{};auto pair=hinted.step(a,f,channel,test_scalar("offset",300+i));
                need(crypto_scalarmult(expected.data(),key.data(),pair.first.data())==0,"reference agreement");
                need(f.checked_open({pair.second}).at(0)==expected,"agreement differs from X25519 of the ephemeral key");
            }
        }catch(const std::exception&e){
            if(!tamper)throw;
            std::cout<<"tampered table stopped the first message: "<<e.what()<<"\nrounds fixture passed"<<std::endl;
            std::_Exit(0);   // a failed engine does not shut its background lines down in step with the peer's
        }
        need(!tamper,"a tampered table was not detected");
        stage.end("load: messages on the imported table (with the fixture's opening)",n);
        std::cout<<"rounds fixture passed"<<std::endl;
        return 0;
    }
    // Our identity key: a scalar neither process knows (XOR of two shares), in both forms.
    Bytes32 share{};{PRG prg;prg.random_data_unaligned(share.data(),32);}
    auto identity_swaps=shared_swaps(f,circuits,party,share);auto identity_bits=hinted.shared_bits(f,circuits,share);
    stage.end("setup: identity scalar in both forms");
    if(test=="prepare"){
        std::vector<Bytes32>keys;std::vector<H>recipients;
        for(size_t i=0;i<n;i++){keys.push_back(test_scalar("contact",unsigned(i)));recipients.push_back(f.public_element(public_u(keys.back())));}
        // The earlier way, one contact at a time (at most two: it is about 1,800 round trips each).
        const size_t old=std::min<size_t>(n,2);std::vector<OffsetAgreement>before(old);
        if(!std::getenv("ROUNDS_FIXTURE_SKIP_OLD")){
            for(size_t i=0;i<old;i++)before[i].prepare(offsets,f,channel,party,recipients[i]);
            stage.end("prepare, earlier program, one at a time",old);
            for(size_t i=0;i<old;i++){bool zero=false;curve.evaluate(f,channel,identity_swaps,recipients[i],zero);}
            stage.end("long-term agreement, ladder, one at a time",old);
        }
        std::vector<OffsetAgreement>after(n);std::vector<OffsetAgreement*>list;for(auto&a:after)list.push_back(&a);
        auto ok=hinted.prepare(f,channel,party,list,recipients);
        for(auto flag:ok)need(flag,"a test contact was refused");
        stage.end("prepare, hinted program, one batch",n);
        std::vector<std::pair<const std::vector<H>*,std::vector<H>>>jobs;for(auto&a:after)jobs.push_back({&identity_bits,a.powers()});
        std::vector<bool>zero;auto statics=hinted.agree_affine(f,channel,jobs,zero);
        stage.end("long-term agreements from the tables, one batch",n);
        if(!std::getenv("ROUNDS_FIXTURE_SKIP_OLD")){
            bool none=false;opened_equal(statics[0],curve.evaluate(f,channel,identity_swaps,recipients[0],none),"long-term agreement differs from the ladder");
        }
        // An invalid key (a twist point) in a batch with a valid one: refused alone.
        {
            Bytes32 twist{};twist[0]=2;   // u = 2 is not on the curve
            std::vector<OffsetAgreement>pair(2);auto flags=hinted.prepare(f,channel,party,{&pair[0],&pair[1]},{f.public_element(twist),recipients[0]});
            need(!flags[0]&&flags[1]&&!pair[0].prepared()&&pair[1].prepared(),"invalid key in a batch");
        }
        stage.begin();
        // Messages: the offset must be the same in both processes (public); the agreement must be
        // X25519(contact's private key, ephemeral public key).
        auto message=[&](OffsetAgreement&a,const Bytes32&key,unsigned index,bool fast){
            Bytes32 offset=test_scalar("offset",index),expected{};
            auto pair=fast?hinted.step(a,f,channel,offset):a.step(offsets,f,offset);
            need(crypto_scalarmult(expected.data(),key.data(),pair.first.data())==0,"reference agreement");
            auto got=f.checked_open({pair.second}).at(0);need(got==expected,"agreement differs from X25519 of the ephemeral key");
        };
        if(!std::getenv("ROUNDS_FIXTURE_SKIP_OLD")){
            for(unsigned i=0;i<5;i++)message(before[0],keys[0],i,false);
            stage.end("message, earlier sum (with the fixture's opening)",5);
        }
        for(unsigned i=0;i<5;i++)message(after[i%n],keys[i%n],100+i,true);
        stage.end("message, fast sum (with the fixture's opening)",5);
        for(unsigned i=0;i<5;i++)message(after[i%n],keys[i%n],200+i,false);   // the earlier sum on a hinted table
        stage.end("message, earlier sum on a hinted table",5);
        std::cout<<"rounds fixture passed"<<std::endl;
        return 0;
    }
    if(test!="receive")return 2;
    for(size_t round=0;round<n;round++){
        // The points of a first message: the envelope's ephemeral key, the sender's identity key,
        // its base key and its ratchet key; and our signed and one-time prekeys (public scalars).
        auto point=[&](const char*label){return f.public_element(public_u(test_scalar(label,unsigned(round))));};
        H ephemeral=point("ephemeral"),sender=point("sender"),base=point("base"),ratchet=point("ratchet");
        Bytes32 signed_key=test_scalar("signed",0),one_time=test_scalar("one-time",0),server_scalar=test_scalar("server",0),seed=test_scalar("seed",unsigned(round));
        Bytes32 mine{};if(party==ALICE)mine=seed;
        auto ratchet_swaps=shared_swaps(f,circuits,party,mine);auto ratchet_bits=hinted.shared_bits(f,circuits,mine);
        // A signature's inputs: flip, h, s as field bits (public test values).
        std::vector<H>flip_h_s;{Bytes32 a=test_scalar("h",unsigned(round)),b=test_scalar("s",unsigned(round));
            flip_h_s.push_back(f.constant(a[0]&1));for(unsigned i=0;i<256;i++)flip_h_s.push_back(f.constant((a[i/8]>>(i%8))&1));for(unsigned i=0;i<253;i++)flip_h_s.push_back(f.constant((b[i/8]>>(i%8))&1));}
        FieldProgram recover{std::string(EMP_WORD_CIRCUIT_DIR)+"/xeddsa-recover.flat",XEDDSA_RECOVER_SHA},check{std::string(EMP_WORD_CIRCUIT_DIR)+"/xeddsa-check.flat",XEDDSA_CHECK_SHA},
            torsion{std::string(EMP_WORD_CIRCUIT_DIR)+"/receive-torsion.flat",RECEIVE_TORSION_SHA};
        auto ours=public_swaps(f,signed_key),once=public_swaps(f,one_time);
        std::vector<H>before;std::array<Bytes32,2>server_point{};std::vector<H>old_signature;
        stage.begin();
        if(!std::getenv("ROUNDS_FIXTURE_SKIP_OLD")){
            bool zero=false;
            auto server=f.checked_open(recover.evaluate_all(f,{{f.public_element(public_u(server_scalar))}}).at(0));server_point={server[1],server[2]};
            stage.end("earlier: server key lift (once per process)");
            before.push_back(curve.evaluate(f,channel,identity_swaps,ephemeral,zero));
            before.push_back(curve.evaluate(f,channel,identity_swaps,sender,zero));
            std::vector<H>challenge{f.public_element(server[1]),f.public_element(server[2])};challenge.insert(challenge.end(),flip_h_s.begin(),flip_h_s.end());
            old_signature=check.evaluate_all(f,{challenge}).at(0);
            stage.end("earlier: unseal agreements and certificate signature (envelope_open)");
            auto lifted=recover.evaluate_all(f,{{base}}).at(0);auto order=torsion.evaluate_all(f,{{lifted.at(1),lifted.at(2)}}).at(0);
            std::vector<std::pair<const std::vector<H>*,H>>jobs{{&ours,sender},{&identity_swaps,base},{&ours,base},{&ours,ratchet},{&ratchet_swaps,ratchet},{&ratchet_swaps,f.constant(9)},{&once,base}};
            std::vector<bool>zeros;auto agreed=curve.evaluate_many(f,channel,jobs,zeros);before.insert(before.end(),agreed.begin(),agreed.end());
            for(auto&v:f.checked_open({lifted.at(0),order.at(0),order.at(1)}))(void)v;
            stage.end("earlier: base key lift, torsion, seven agreements (envelope_session)");
        }
        std::vector<H>after;std::vector<bool>zeros;
        auto bits_ours=hinted.public_bits(f,signed_key),bits_once=hinted.public_bits(f,one_time);
        stage.begin();
        auto first=hinted.lift(f,{ephemeral});auto first_table=hinted.tables(f,party,{&first[0]});
        after.push_back(hinted.agree(f,channel,{{&identity_bits,&first_table[0],first[0].valid}},zeros).at(0));
        auto second=hinted.lift(f,{sender});auto sender_table=hinted.tables(f,party,{&second[0]});
        after.push_back(hinted.agree(f,channel,{{&identity_bits,&sender_table[0],second[0].valid}},zeros).at(0));
        std::vector<std::array<H,2>>new_signature;
        if(!old_signature.empty()){
            auto key=hinted.public_table(f,hinted.local.encode(server_point[0],server_point[1]));
            new_signature=hinted.signatures(f,{{&key,&flip_h_s}});
        }
        stage.end("hinted: unseal agreements and certificate signature (envelope_open)");
        auto third=hinted.lift(f,{base,ratchet});auto free=hinted.torsion(f,party,third[0]);auto more=hinted.tables(f,party,{&third[0],&third[1]});
        H one=f.constant(1);
        auto agreed=hinted.agree(f,channel,{{&bits_ours,&sender_table[0],second[0].valid},{&identity_bits,&more[0],third[0].valid},{&bits_ours,&more[0],third[0].valid},
            {&bits_ours,&more[1],third[1].valid},{&ratchet_bits,&more[1],third[1].valid},{&ratchet_bits,&hinted.base_table(f),one},{&bits_once,&more[0],third[0].valid}},zeros);
        after.insert(after.end(),agreed.begin(),agreed.end());
        stage.end("hinted: base key lift, torsion, seven agreements (envelope_session)");
        // Fixture only: open and compare.
        {auto v=f.checked_open({free[0],free[1],third[0].valid,third[1].valid});Bytes32 unit{};unit[0]=1;Bytes32 none{};need(v[0]==none&&v[1]==none&&v[2]==unit&&v[3]==unit,"hinted torsion or validity");}
        if(!before.empty()){
            need(before.size()==after.size(),"agreement count");
            for(size_t i=0;i<before.size();i++)opened_equal(before[i],after[i],"a hinted agreement differs from the ladder");
            opened_equal(old_signature[0],new_signature[0][0],"signature point x");opened_equal(old_signature[1],new_signature[0][1],"signature point y");
        }
        stage.begin();
    }
    std::cout<<"rounds fixture passed"<<std::endl;
    return 0;
}
int main(int argc,char**argv){
    int code=4;
    try{emp_hybrid::run_with_stack(size_t(1)<<30,[&]{try{code=run(argc,argv);}catch(const std::exception&e){std::cerr<<"rounds fixture failed: "<<e.what()<<"\n";code=4;}});}catch(...){return 4;}
    return code;
}
