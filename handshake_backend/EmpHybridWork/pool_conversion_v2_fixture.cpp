#include "dabit_generator.h"
#include "modp_program.h"
#include "pad_program.h"
#include <iostream>
#include <optional>
using namespace emp;
using namespace emp_hybrid;
int main(int argc,char**argv){
    if(argc!=5)return 2;
    const char*stage="setup";
    try{
        int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        std::string expectedhex=argv[3];if(expectedhex.size()!=64)throw std::runtime_error("fixture expected width");std::array<uint8_t,32>expected{};
        for(unsigned i=0;i<32;i++)expected[i]=std::stoul(expectedhex.substr(i*2,2),nullptr,16);
        struct FinalCounters {~FinalCounters(){std::cout<<"EMP_EXACT_SOCKET_BYTES sent="<<NetIO::benchmark_sent.load()<<" received="<<NetIO::benchmark_received.load()<<"\n";}} counters;
        NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool pool(4);AG2PCSession session(&io,&pool,party,40);
        FE field(party-1,port+10);std::string closure=argv[4];if(closure.size()!=64||closure.find_first_not_of("0123456789abcdef")!=std::string::npos)throw std::runtime_error("program closure identity");Challenge challenge{io,party,"pool-conversion:LE255:epoch0:program-closure="+closure};
        stage="generation";auto generation=DaBitGeneratorV1::generate<256>(session,field,challenge,party);
        stage="pool-reserve";auto binding=generation.pool.binding();EngineOwners owners{&session,&field};
        if(party==BOB&&std::getenv("EMP_TEST_WRONG_POOL_SESSION"))binding.nonce[0]^=1;
        if(party==BOB&&std::getenv("EMP_TEST_WRONG_POOL_OWNER"))owners.boolean=nullptr;
        std::optional<CheckedMaskPool::Lease> lease;std::vector<uint8_t>frame;
        uint8_t ready=1,peer_ready=1;
        try{lease.emplace(generation.pool.reserve(binding,owners,0,Direction::FieldToBoolean,255));frame=lease->frame();}catch(...){ready=0;}
        // A caught local guard failure must reach the peer BEFORE either side
        // unwinds native protocol owners or waits for the next EMP message.
        challenge.transfer(&ready,&peer_ready,1);
        if(!ready||!peer_ready){generation.pool.poison();throw std::runtime_error("collective reserve rejection");}
        auto peer=frame;
        if(party==BOB&&std::getenv("EMP_TEST_WRONG_POOL_FRAME"))frame[8]^=1;
        challenge.transfer(frame.data(),peer.data(),frame.size());if(frame!=peer){generation.pool.poison();throw std::runtime_error("pool peer frame");}
        stage="pool-consume";std::vector<MaskPair>consumed;ready=peer_ready=1;
        try{consumed=lease->consume(binding,owners,0,Direction::FieldToBoolean);
            if(std::getenv("EMP_TEST_REUSE_POOL_LEASE"))lease->consume(binding,owners,0,Direction::FieldToBoolean);
        }catch(...){ready=0;}
        challenge.transfer(&ready,&peer_ready,1);
        if(!ready||!peer_ready){generation.pool.poison();throw std::runtime_error("collective consume rejection");}
        std::array<uint32_t,255>mask_ids{};std::vector<H>fm;
        for(unsigned i=0;i<255;i++){mask_ids[i]=consumed[i].wire;fm.push_back(consumed[i].field);}
        auto mask=V<255>::from_wires(session.ctx(),mask_ids.data());session.checkpoint(mask,generation.held);
        // Consume255 checked pairs. Range must settle BEFORE native masked open.
        stage="mask-range";std::cerr<<"fixture stage=mask-range\n";auto range=emp_hybrid::pad_program(emp_hybrid::range_program(),1024);
        if(range.dummy_inputs!=2048||range.dummy_outputs!=1024)throw std::runtime_error("range padding profile");
        auto da=session.input<V<1024>>(ALICE,fresh<1024>()),db=session.input<V<1024>>(BOB,fresh<1024>());
        auto rangeout=session.run_artifact<V<1025>>(range.program,mask,da,db);session.checkpoint(mask,rangeout,generation.held);
        auto accepted=select<1025,1>(session,rangeout,{0});auto valid=session.reveal(accepted,PUBLIC,mask,generation.held);if(!valid||!(*valid)[0])throw std::runtime_error("mask out of range; batch burned");
        stage="field-operation";auto rfield=field.constant(0);for(int i=254;i>=0;i--)rfield=field.add(field.add(rfield,rfield),fm[i]);
        auto in=field.input_coins({party==ALICE?123u:321u});auto x=field.add(in[0][0],in[1][0]);for(unsigned i=0;i<8;i++)x=field.mul({x},{x})[0];
        auto public_c=field.checked_open({field.sub(x,rfield)}).at(0);
        std::array<uint8_t,32> peer_c{};challenge.transfer(public_c.data(),peer_c.data(),32);if(public_c!=peer_c)throw std::runtime_error("public mask frame mismatch");
        stage="canonical-conversion";std::cerr<<"fixture stage=canonical-conversion\n";auto arithmetic=emp_hybrid::pad_program(emp_hybrid::modp_program(public_c),1024);
        auto ma=session.input<V<1024>>(ALICE,fresh<1024>()),mb=session.input<V<1024>>(BOB,fresh<1024>());
        auto modular=session.run_artifact<V<1279>>(arithmetic.program,mask,ma,mb);session.checkpoint(modular,generation.held);
        std::vector<unsigned>original(255);std::iota(original.begin(),original.end(),0);auto value=select<1279,255>(session,modular,original);session.checkpoint(value,generation.held);
        // Independent fixture expectation is public; comparison remains inside
        // EMP. Neither unmasked native x nor recovered Boolean x opens.
        stage="equality";std::cerr<<"fixture stage=equality\n";circuit::BooleanProgram eq;eq.num_inputs=255;eq.num_wires=255;std::vector<unsigned>leaves;
        for(unsigned i=0;i<255;i++){unsigned wire=i;if(!((expected[i/8]>>(i%8))&1)){wire=eq.num_wires++;eq.gates.push_back({i,0,wire,circuit::Op::Not});}leaves.push_back(wire);}
        while(leaves.size()>1){std::vector<unsigned>next;for(size_t i=0;i<leaves.size();i+=2){if(i+1==leaves.size())next.push_back(leaves[i]);else{unsigned wire=eq.num_wires++;eq.gates.push_back({leaves[i],leaves[i+1],wire,circuit::Op::And});next.push_back(wire);}}leaves=next;}
        eq.outputs=leaves;auto padded=emp_hybrid::pad_program(eq,1024);if(padded.dummy_outputs!=1024)throw std::runtime_error("equality padding profile");
        auto ea=session.input<V<1024>>(ALICE,fresh<1024>()),eb=session.input<V<1024>>(BOB,fresh<1024>());
        auto all=session.run_artifact<V<1025>>(padded.program,value,ea,eb);session.checkpoint(all,generation.held);auto equality=select<1025,1>(session,all,{0});auto result=session.reveal(equality,PUBLIC,generation.held);
        if(!result||!(*result)[0])throw std::runtime_error("field conversion mismatch");
        std::cout<<"field conversion fixture passed pairs_consumed=255 private_result_equality=1\n";
    }catch(...){std::cerr<<"field conversion fixture rejected category=protocol-or-consistency stage="<<stage<<"\n";return 4;}
}
