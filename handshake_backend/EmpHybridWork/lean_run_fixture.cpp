// Generic runner: execute one pinned Lean circuit on the validated Boolean
// engine with every input XOR-shared between the two parties, keep every
// output private, and open a single bit saying whether the output equals a
// public expectation. All gates come from Lean exports: the circuit itself, the
// share-combining XOR and the comparison. This file only supplies inputs and
// hands wires over in order. Widths are fixed at build time
// (EMP_RUN_INPUT_BITS, EMP_RUN_OUTPUT_BITS). Statistical-128 profile.
#include "word_mask.h"
#include "big_stack.h"
#include <chrono>
#include <fstream>
#include <iostream>
#if !defined(EMP_RUN_INPUT_BITS) || !defined(EMP_RUN_OUTPUT_BITS)
#error "EMP_RUN_INPUT_BITS and EMP_RUN_OUTPUT_BITS are required"
#endif
using namespace emp;
using namespace emp_hybrid;
using Clock=std::chrono::steady_clock;
constexpr unsigned IN=EMP_RUN_INPUT_BITS,OUT=EMP_RUN_OUTPUT_BITS;
static double elapsed(Clock::time_point start){return std::chrono::duration<double>(Clock::now()-start).count();}
template<size_t N>static std::unique_ptr<std::array<bool,N>> read_bits(const char*path){
    auto out=std::make_unique<std::array<bool,N>>();std::ifstream in(path,std::ios::binary);for(auto &b:*out){char x;if(!in.get(x)||x<0||x>1)throw std::runtime_error("bit file encoding");b=x;}char extra;if(in.get(extra))throw std::runtime_error("bit file length");return out;
}
static int run(int argc,char**argv){
    // party, port, circuit path, circuit sha256, own input share (IN bits),
    // public expected output (OUT bits), equality circuit path, its sha256, metrics.
    if(argc!=10)return 2;const char*stage="public-load";
    try{
        int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        auto start=Clock::now(),t=start;
        LeanCircuit circuit(argv[3],argv[4]),equal(argv[7],argv[8]);LeanCircuit xor_bit(std::string(EMP_WORD_CIRCUIT_DIR)+"/xor-bit.flat",WORD_XOR_BIT_SHA);
        if(circuit.input_bits()!=IN||circuit.output_bits()!=OUT||equal.input_bits()!=2*OUT||equal.output_bits()!=1)throw std::runtime_error("circuit shape");
        auto mine=read_bits<IN>(argv[5]);auto expected=read_bits<OUT>(argv[6]);
        double load=elapsed(t),setup=0,input_time=0,run_time=0;uint64_t ands=0;
        {
            NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool threads(4);t=Clock::now();
            {
                AG2PCSession session(&io,&threads,party,128);setup=elapsed(t);
                stage="inputs";t=Clock::now();
                auto a=session.input<V<IN>>(ALICE,*mine),b=session.input<V<IN>>(BOB,*mine);session.checkpoint(a,b);
                auto pair=std::make_unique<std::array<uint32_t,2*IN>>();
                {auto x=std::make_unique<std::array<uint32_t,IN>>(),y=std::make_unique<std::array<uint32_t,IN>>();a.pack_wires(x->data());b.pack_wires(y->data());for(unsigned i=0;i<IN;i++){(*pair)[2*i]=(*x)[i];(*pair)[2*i+1]=(*y)[i];}}
                auto input=session.run_artifact<V<IN>>(xor_bit.parallel(IN),V<2*IN>::from_wires(session.ctx(),pair->data()));session.checkpoint(input);input_time=elapsed(t);
                stage="circuit";t=Clock::now();
                auto output=session.run_artifact<V<OUT>>(circuit.parallel(1),input);session.checkpoint(output);run_time=elapsed(t);
                stage="equality";
                auto reference=session.input<V<OUT>>(PUBLIC,*expected);session.checkpoint(output,reference);
                auto both=std::make_unique<std::array<uint32_t,2*OUT>>();output.pack_wires(both->data());reference.pack_wires(both->data()+OUT);
                auto same=session.run_artifact<V<1>>(equal.parallel(1),V<2*OUT>::from_wires(session.ctx(),both->data()));
                auto clear=session.reveal(same,PUBLIC,output);
                if(!clear||!(*clear)[0])throw std::runtime_error("output mismatch");
                ands=session.num_and();
                std::cout<<"lean run fixture passed private_output_bits="<<OUT<<" opened_bits=1\n";
            }
        }
        std::ofstream report(argv[9]);report<<"{\"load_seconds\":"<<load<<",\"setup_seconds\":"<<setup<<",\"input_seconds\":"<<input_time<<",\"circuit_seconds\":"<<run_time<<",\"wall_seconds\":"<<elapsed(start)<<",\"boolean_and_gates\":"<<ands<<",\"emp_sent_bytes\":"<<NetIO::benchmark_sent.load()<<",\"emp_received_bytes\":"<<NetIO::benchmark_received.load()<<"}\n";
    }catch(...){std::cerr<<"lean run rejected category=protocol-or-validity stage="<<stage<<"\n";return 4;}
    return 0;
}
int main(int argc,char**argv){
    int code=4;
    try{emp_hybrid::run_with_stack(size_t(1)<<30,[&]{code=run(argc,argv);});}catch(...){std::cerr<<"lean run rejected category=runtime stage=stack\n";return 4;}
    return code;
}
