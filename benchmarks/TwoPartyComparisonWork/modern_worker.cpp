// Unaudited current EMP candidate. Imports exported gates; no Signal rewrite.
#include <emp-ag2pc/emp-ag2pc.h>
#include <chrono>
#include <fstream>
#include <memory>
#include <stdexcept>
#include <sys/resource.h>
using namespace emp;
using Clock=std::chrono::steady_clock;
static double seconds(Clock::time_point t){return std::chrono::duration<double>(Clock::now()-t).count();}
struct Times{double setup=0,input=0,run=0,reveal=0,close=0;uint64_t ands=0;};

static circuit::BooleanProgram load(const char*path,uint32_t&n1,uint32_t&n2,uint32_t&m){
    std::ifstream f(path);uint32_t gates,wires;
    if(!(f>>gates>>wires>>n1>>n2>>m)||gates>12000000||wires!=n1+n2+gates)throw std::runtime_error("graph dimensions");
    circuit::BooleanProgram p;p.num_inputs=n1+n2;p.num_wires=wires;p.gates.reserve(gates);
    uint64_t ands=0;
    for(uint32_t i=0;i<gates;i++){
        uint32_t arity,outputs,a,b=0,out;std::string op;
        if(!(f>>arity>>outputs>>a)||outputs!=1)throw std::runtime_error("gate row");
        if(arity==2){if(!(f>>b>>out>>op))throw std::runtime_error("binary row");}
        else if(arity==1){if(!(f>>out>>op))throw std::runtime_error("unary row");}
        else throw std::runtime_error("arity");
        circuit::Op kind;
        if(op=="AND"&&arity==2){kind=circuit::Op::And;ands++;}
        else if(op=="XOR"&&arity==2)kind=circuit::Op::Xor;
        else if(op=="INV"&&arity==1)kind=circuit::Op::Not;
        else throw std::runtime_error("operation");
        if(out!=p.num_inputs+i||a>=out||(arity==2&&b>=out))throw std::runtime_error("gate ordering");
        p.gates.push_back({a,b,out,kind});
    }
    std::string extra;if(f>>extra)throw std::runtime_error("trailing gate data");
    for(uint32_t i=wires-m;i<wires;i++)p.outputs.push_back(i);
    // Do not rely on current source's1024-floor sizing for smaller real chunks.
    if(ands>0&&ands<1024)throw std::runtime_error("unsupported tiny chunk parameters");
    return p;
}

template<int A,int B,int O> Times evaluate(const circuit::BooleanProgram&p,int party,int port,const char*input,const char*output){
    using Ctx=AG2PCSession::ctx_t;
    using Bob=BitVec_T<Ctx,A>;using Alice=BitVec_T<Ctx,B>;using Out=BitVec_T<Ctx,O>;
    typename Bob::clear_t bob{};typename Alice::clear_t alice{};
    std::ifstream f(input,std::ios::binary);
    const int size=party==BOB?A:B;
    for(int i=0;i<size;i++){char bit;if(!f.get(bit)||bit<0||bit>1)throw std::runtime_error("input shape");if(party==BOB)bob[i]=bit;else alice[i]=bit;}
    char extra;if(f.get(extra))throw std::runtime_error("trailing input");
    Times t;auto close_start=Clock::now();
    {
        auto io=std::make_unique<NetIO>(party==ALICE?nullptr:"127.0.0.1",port,true);
        ThreadPool pool(4);
        auto start=Clock::now();
        {
            AG2PCSession session(io.get(),&pool,party,40);t.setup=seconds(start);
            start=Clock::now();
            auto left=session.input<Bob>(BOB,bob);
            auto right=session.input<Alice>(ALICE,alice);t.input=seconds(start);
            if(party==BOB&&std::getenv("EMP_MODERN_TEST_CORRUPT_DELTA"))session.protocol().Delta=session.protocol().Delta^makeBlock(0,4);
            start=Clock::now();
            auto result=session.run_artifact<Out>(p,left,right);
            session.checkpoint(result);t.run=seconds(start);
            start=Clock::now();auto clear=session.reveal(result,BOB);t.reveal=seconds(start);
            if(party==BOB){
                if(!clear)throw std::runtime_error("missing private result");
                std::ofstream out(output,std::ios::binary);for(bool bit:*clear)out.put(bit?1:0);
            }else if(clear)throw std::runtime_error("nonrecipient received result");
            t.ands=session.num_and();close_start=Clock::now();
        }
    }
    t.close=seconds(close_start);return t;
}

int main(int argc,char**argv){
    if(argc!=7)return 2;
    try{
        const int party=std::stoi(argv[1]),port=std::stoi(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        auto total=Clock::now(),start=total;uint32_t a,b,o;
        auto program=load(argv[3],a,b,o);double load_seconds=seconds(start);Times t;
        if(a==384&&b==512&&o==128)t=evaluate<384,512,128>(program,party,port,argv[4],argv[5]);
        else if(a==768&&b==1024&&o==256)t=evaluate<768,1024,256>(program,party,port,argv[4],argv[5]);
        else if(a==1464&&b==1464&&o==1)t=evaluate<1464,1464,1>(program,party,port,argv[4],argv[5]);
        else throw std::runtime_error("unpinned profile");
        rusage usage{};getrusage(RUSAGE_SELF,&usage);auto tv=[](timeval x){return x.tv_sec+x.tv_usec/1e6;};
        std::ofstream report(argv[6]);
        report<<"{\"party\":"<<party<<",\"unaudited_rewrite\":true,\"ssp\":40,\"load_seconds\":"<<load_seconds
              <<",\"setup_seconds\":"<<t.setup<<",\"input_seconds\":"<<t.input<<",\"run_seconds\":"<<t.run
              <<",\"reveal_seconds\":"<<t.reveal<<",\"close_seconds\":"<<t.close<<",\"wall_seconds\":"<<seconds(total)
              <<",\"cpu_seconds\":"<<tv(usage.ru_utime)+tv(usage.ru_stime)<<",\"peak_rss_bytes\":"<<usage.ru_maxrss
              <<",\"and_gates\":"<<t.ands<<",\"sent_bytes\":"<<NetIO::benchmark_sent.load()
              <<",\"received_bytes\":"<<NetIO::benchmark_received.load()<<"}\n";
        return 0;
    }catch(...){std::cerr<<"benchmark rejected category=adapter-exception\n";return 4;}
}
