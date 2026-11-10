// Public-known fixture only: two imported AES calls, private authenticated state.
// No reconstructed logical AES key, first ciphertext, or carried value at host.
#include <emp-ag2pc/emp-ag2pc.h>
#include <chrono>
#include <fstream>
#include <memory>
#include <stdexcept>
#include <sys/resource.h>
using namespace emp;
using Clock=std::chrono::steady_clock;
static double sec(Clock::time_point t){return std::chrono::duration<double>(Clock::now()-t).count();}

static circuit::BooleanProgram load(const char*path){
    std::ifstream f(path);uint32_t ng,nw,a,b,o;
    if(!(f>>ng>>nw>>a>>b>>o)||a!=384||b!=512||o!=128||nw!=a+b+ng||ng>100000)throw std::runtime_error("fixture graph dimensions");
    circuit::BooleanProgram p;p.num_inputs=a+b;p.num_wires=nw;uint64_t ands=0;
    for(uint32_t i=0;i<ng;i++){
        uint32_t n,m,x,y=0,z;std::string op;
        if(!(f>>n>>m>>x)||m!=1)throw std::runtime_error("gate row");
        if(n==2){if(!(f>>y>>z>>op))throw std::runtime_error("binary row");}
        else if(n==1){if(!(f>>z>>op))throw std::runtime_error("unary row");}
        else throw std::runtime_error("arity");
        circuit::Op kind;
        if(op=="AND"&&n==2){kind=circuit::Op::And;ands++;}
        else if(op=="XOR"&&n==2)kind=circuit::Op::Xor;
        else if(op=="INV"&&n==1)kind=circuit::Op::Not;
        else throw std::runtime_error("op");
        if(z!=p.num_inputs+i||x>=z||(n==2&&y>=z))throw std::runtime_error("gate ordering");
        p.gates.push_back({x,y,z,kind});
    }
    std::string extra;if(f>>extra)throw std::runtime_error("trailing graph data");
    if(ands!=8832)throw std::runtime_error("unpinned fixture nonlinear profile");
    for(uint32_t i=nw-o;i<nw;i++)p.outputs.push_back(i);
    return p;
}
template<size_t N>static std::array<bool,N> read(const char*path){
    std::array<bool,N> out{};std::ifstream f(path,std::ios::binary);
    for(size_t i=0;i<N;i++){char b;if(!f.get(b)||b<0||b>1)throw std::runtime_error("input bits");out[i]=b;}
    char extra;if(f.get(extra))throw std::runtime_error("extra input");return out;
}
int main(int argc,char**argv){
    // party port circuit own-input fresh-Alice-pad output metrics
    if(argc!=8)return 2;
    try{
        int party=std::stoi(argv[1]),port=std::stoi(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        auto total=Clock::now(),t=total;auto program=load(argv[3]);double load_sec=sec(t);
        using Ctx=AG2PCSession::ctx_t;using A=BitVec_T<Ctx,512>;using B=BitVec_T<Ctx,384>;using O=BitVec_T<Ctx,128>;
        A::clear_t av{};B::clear_t bv{};O::clear_t pad{};
        if(party==ALICE){av=read<512>(argv[4]);pad=read<128>(argv[5]);}else bv=read<384>(argv[4]);
        double setup=0,inputs=0,first=0,second=0,close=0;uint64_t first_sent=0,first_recv=0,second_sent=0,second_recv=0,ands=0;
        {
            auto io=std::make_unique<NetIO>(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool pool(4);
            t=Clock::now();
            {
                AG2PCSession session(io.get(),&pool,party,40);setup=sec(t);t=Clock::now();
                auto bob=session.input<B>(BOB,bv);auto alice=session.input<A>(ALICE,av);auto fresh=session.input<O>(ALICE,pad);inputs=sec(t);
                auto sent=[&]{return io->send_counter+session.protocol().sib->send_counter;};
                auto received=[&]{return io->recv_counter+session.protocol().sib->recv_counter;};
                auto s=sent(),r=received();t=Clock::now();
                auto carried=session.run_artifact<O>(program,bob,alice);
                session.checkpoint(carried,bob,alice,fresh);
                first=sec(t);first_sent=sent()-s;first_recv=received()-r;
                // Reassemble only wire IDs. The first AES output is still padded
                // and authenticated. XOR with Alice's old pad occurs INSIDE the
                // second imported graph, never at a host.
                std::array<uint32_t,384> bw{},next_b{};std::array<uint32_t,512> aw{},next_a{};
                std::array<uint32_t,128> cw{},pw{};
                bob.pack_wires(bw.data());alice.pack_wires(aw.data());carried.pack_wires(cw.data());fresh.pack_wires(pw.data());
                for(size_t i=0;i<256;i++){next_b[i]=bw[i];next_a[i]=aw[i];}
                for(size_t i=0;i<128;i++){next_b[256+i]=cw[i];next_a[256+i]=aw[384+i];next_a[384+i]=pw[i];}
                auto b2=B::from_wires(session.ctx(),next_b.data());auto a2=A::from_wires(session.ctx(),next_a.data());
                session.checkpoint(b2,a2);
                if(party==BOB&&std::getenv("EMP_TEST_CORRUPT_RETAINED_DELTA"))session.protocol().Delta=session.protocol().Delta^makeBlock(0,4);
                s=sent();r=received();t=Clock::now();
                auto result=session.run_artifact<O>(program,b2,a2);session.checkpoint(result);
                second=sec(t);second_sent=sent()-s;second_recv=received()-r;
                auto clear=session.reveal(result,BOB);
                if(party==BOB){if(!clear)throw std::runtime_error("missing result");std::ofstream out(argv[6],std::ios::binary);for(bool bit:*clear)out.put(bit?1:0);}
                else if(clear)throw std::runtime_error("wrong recipient");
                ands=session.num_and();if(ands!=17664)throw std::runtime_error("replay work mismatch");t=Clock::now();
            }
            close=sec(t);
        }
        rusage u{};getrusage(RUSAGE_SELF,&u);auto tv=[](timeval x){return x.tv_sec+x.tv_usec/1e6;};
        std::ofstream out(argv[7]);out<<"{\"party\":"<<party<<",\"load_seconds\":"<<load_sec<<",\"setup_seconds\":"<<setup
            <<",\"input_seconds\":"<<inputs<<",\"first_seconds\":"<<first<<",\"second_seconds\":"<<second<<",\"close_seconds\":"<<close
            <<",\"first_sent_bytes\":"<<first_sent<<",\"first_received_bytes\":"<<first_recv<<",\"second_sent_bytes\":"<<second_sent
            <<",\"second_received_bytes\":"<<second_recv<<",\"and_gates\":"<<ands<<",\"sent_bytes\":"<<NetIO::benchmark_sent.load()
            <<",\"received_bytes\":"<<NetIO::benchmark_received.load()<<",\"wall_seconds\":"<<sec(total)<<",\"cpu_seconds\":"<<tv(u.ru_utime)+tv(u.ru_stime)
            <<",\"peak_rss_bytes\":"<<u.ru_maxrss<<"}\n";return 0;
    }catch(...){std::cerr<<"fixture rejected category=adapter-exception\n";return 4;}
}
