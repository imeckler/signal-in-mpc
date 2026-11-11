// Generic runner on the runtime-sized layer: one binary for every pinned Lean
// circuit profile. Every input bit is XOR-shared between the two parties, all
// outputs stay private, and one bit is opened: whether the output equals a
// public expectation. Share-combining XOR and the comparison are Lean circuits.
#include "dyn_session.h"
#include "word_circuit_pins.h"
#include <chrono>
#include <fstream>
#include <iostream>
#ifndef EMP_WORD_CIRCUIT_DIR
#error "EMP_WORD_CIRCUIT_DIR must name the directory of pinned Lean circuit exports"
#endif
using namespace emp;
using namespace emp_hybrid;
using Clock=std::chrono::steady_clock;
static double elapsed(Clock::time_point start){return std::chrono::duration<double>(Clock::now()-start).count();}
static std::vector<uint8_t> read_bits(const char*path,size_t expected){
    std::ifstream in(path,std::ios::binary);std::vector<uint8_t>out;char x;
    while(in.get(x)){if(x<0||x>1)throw std::runtime_error("bit file encoding");out.push_back(uint8_t(x));}
    if(out.size()!=expected)throw std::runtime_error("bit file length");return out;
}
int main(int argc,char**argv){
    // party, port, circuit path, circuit sha256, own input share, public expected
    // output, equality circuit path, its sha256, metrics.
    if(argc!=10)return 2;const char*stage="public-load";
    try{
        int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        auto start=Clock::now(),t=start;
        LeanCircuit circuit(argv[3],argv[4]),equal(argv[7],argv[8]),xor_bit(std::string(EMP_WORD_CIRCUIT_DIR)+"/xor-bit.flat",WORD_XOR_BIT_SHA);
        const size_t in_bits=circuit.input_bits(),out_bits=circuit.output_bits();
        if(equal.input_bits()!=2*out_bits||equal.output_bits()!=1)throw std::runtime_error("circuit shape");
        auto mine=read_bits(argv[5],in_bits);auto expected=read_bits(argv[6],out_bits);
        double load=elapsed(t),setup=0,run_time=0;uint64_t ands=0;
        {
            NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool threads(4);t=Clock::now();
            {
                DynSession session(&io,&threads,party,128);
                // EMP_TEST_TRIPLE_STOCK=FACTORIES,BATCH,RESERVE (both parties alike): AND triples
                // minted ahead of use by background pools, as the worker runs (dyn_session.h).
                if(const char*stock=std::getenv("EMP_TEST_TRIPLE_STOCK")){
                    unsigned long long factories=0,batch=0,reserve=0;
                    if(std::sscanf(stock,"%llu,%llu,%llu",&factories,&batch,&reserve)!=3)throw std::runtime_error("triple stock setting");
                    session.start_stock(unsigned(factories),size_t(batch),size_t(reserve));
                }
                setup=elapsed(t);
                stage="inputs";auto shares=session.input_both(mine);
                auto input=session.run(xor_bit.parallel(in_bits),DynSession::interleave(shares.first,shares.second));
                stage="circuit";t=Clock::now();auto output=session.run(circuit,input);run_time=elapsed(t);
                stage="equality";auto reference=session.public_bits(expected);
                auto same=session.open(session.run(equal,DynSession::concat({&output,&reference})));
                if(same.size()!=1||!same[0])throw std::runtime_error("output mismatch");
                ands=session.and_gates();
                std::cout<<"dyn run fixture passed private_output_bits="<<out_bits<<" opened_bits=1\n";
            }
        }
        std::ofstream report(argv[9]);report<<"{\"load_seconds\":"<<load<<",\"setup_seconds\":"<<setup<<",\"circuit_seconds\":"<<run_time<<",\"wall_seconds\":"<<elapsed(start)<<",\"boolean_and_gates\":"<<ands<<",\"emp_sent_bytes\":"<<NetIO::benchmark_sent.load()<<",\"emp_received_bytes\":"<<NetIO::benchmark_received.load()<<"}\n";
    }catch(...){std::cerr<<"dyn run rejected category=protocol-or-validity stage="<<stage<<"\n";return 4;}
    return 0;
}
