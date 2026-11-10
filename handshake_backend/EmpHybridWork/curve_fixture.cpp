#include "checked_converter.h"
#include "curve_program.h"
#include <chrono>
#include <fstream>
#include <iostream>
using namespace emp;
using namespace emp_hybrid;
using Clock=std::chrono::steady_clock;
static double elapsed(Clock::time_point start){return std::chrono::duration<double>(Clock::now()-start).count();}
static V<512>::clear_t read_share(const char*path){
    V<512>::clear_t out{};std::ifstream in(path,std::ios::binary);for(auto &b:out){char x;if(!in.get(x)||x<0||x>1)throw std::runtime_error("fixture share encoding");b=x;}char extra;if(in.get(extra))throw std::runtime_error("fixture share length");return out;
}
int main(int argc,char**argv){
    // party,port,own XOR share,public fixture expectation,pinned flat DAG,
    // public full closure identity,metrics output.
    if(argc!=8)return 2;const char*stage="public-load";
    try{
        int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        auto start=Clock::now(),t=start;CurveProgram curve(argv[5]);auto mine=read_share(argv[3]);
        std::string hex=argv[4],closure=argv[6];if(hex.size()!=64||closure.size()!=64||closure.find_first_not_of("0123456789abcdef")!=std::string::npos)throw std::runtime_error("fixture public profile");
        std::array<uint8_t,32>expected{};for(unsigned i=0;i<32;i++)expected[i]=std::stoul(hex.substr(i*2,2),nullptr,16);double load=elapsed(t),setup=0,generation_time=0,tofield=0,curve_time=0,tobool=0;uint64_t ands=0;
        {
            NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool threads(4);t=Clock::now();
            {
                AG2PCSession session(&io,&threads,party,40);FE field(party-1,port+10);setup=elapsed(t);
                Challenge challenge{io,party,"curve:LE32-MSB:epoch0:program-closure="+closure};
                stage="checked-pairs";t=Clock::now();auto generated=DaBitGeneratorV1::generate<1024>(session,field,challenge,party);generation_time=elapsed(t);
                CheckedConverter<1024>converter(session,field,challenge,generated);
                auto a=session.input<V<512>>(ALICE,mine),b=session.input<V<512>>(BOB,mine);std::vector<std::pair<unsigned,unsigned>>pairs;
                for(unsigned i=0;i<512;i++)pairs.emplace_back(i,512+i);
                auto application=session.run_artifact<V<512>>(xor_program(1024,pairs),a,b);session.checkpoint(application,generated.held);
                std::vector<unsigned>numeric_indices;for(unsigned i=0;i<256;i++)numeric_indices.push_back(8*(i/8)+7-i%8);
                // RFC7748 coordinate high bit is ignored INSIDE MPC.
                for(unsigned i=0;i<255;i++)numeric_indices.push_back(256+8*(i/8)+7-i%8);
                auto numeric=select<512,511>(session,application,numeric_indices);
                stage="boolean-to-field";t=Clock::now();auto native=converter.boolean_to_field(numeric,application);tofield=elapsed(t);
                std::array<H,257>input{};for(unsigned i=0;i<256;i++)input[i]=native[i];
                auto point=field.constant(0);for(int i=254;i>=0;i--)point=field.add(field.add(point,point),native[256+i]);input[256]=point;
                stage="native-x25519";t=Clock::now();auto dh=curve.evaluate(field,input);curve_time=elapsed(t);
                stage="field-to-boolean";t=Clock::now();auto value=converter.field_to_bytes(dh,application);tobool=elapsed(t);
                // Output is equality+nonzero ONLY. Actual canonical DH bytes
                // remain authenticated/private for a later Signal/TLS caller.
                circuit::BooleanProgram eq;eq.num_inputs=256;eq.num_wires=256;std::vector<unsigned>same,zero;
                auto gate=[&](circuit::Op op,unsigned a,unsigned b=0){unsigned out=eq.num_wires++;eq.gates.push_back({a,b,out,op});return out;};
                for(unsigned i=0;i<256;i++){auto neg=gate(circuit::Op::Not,i);zero.push_back(neg);same.push_back(((expected[i/8]>>(7-i%8))&1)?i:neg);}
                auto reduce=[&](std::vector<unsigned>v){while(v.size()>1){std::vector<unsigned>next;for(size_t i=0;i<v.size();i+=2)next.push_back(i+1<v.size()?gate(circuit::Op::And,v[i],v[i+1]):v[i]);v=std::move(next);}return v.at(0);};
                auto equal=reduce(same),nonzero=gate(circuit::Op::Not,reduce(zero));eq.outputs={equal,nonzero};auto checked=pad_program(eq,1024);
                auto da=session.input<V<1024>>(ALICE,fresh<1024>()),db=session.input<V<1024>>(BOB,fresh<1024>());
                auto all=session.run_artifact<V<1026>>(checked.program,value,da,db);session.checkpoint(all,generated.held,application);
                auto status=select<1026,2>(session,all,{0,1});auto clear=session.reveal(status,PUBLIC,generated.held,application);
                if(!clear)throw std::runtime_error("missing status");stage="curve-nonzero";if(!(*clear)[1])throw std::runtime_error("low-order rejection");stage="curve-equality";if(!(*clear)[0])throw std::runtime_error("fixture mismatch");
                ands=session.num_and();if(ands<3072)throw std::runtime_error("missing checked padding");
                std::cout<<"hybrid curve fixture passed canonical_private_bytes=32 consumed_pairs=766\n";
            }
        }
        std::ofstream report(argv[7]);report<<"{\"load_seconds\":"<<load<<",\"setup_seconds\":"<<setup<<",\"pair_generation_seconds\":"<<generation_time<<",\"boolean_to_field_seconds\":"<<tofield<<",\"native_curve_seconds\":"<<curve_time<<",\"field_to_boolean_seconds\":"<<tobool<<",\"wall_seconds\":"<<elapsed(start)<<",\"boolean_and_gates\":"<<ands<<",\"emp_sent_bytes\":"<<NetIO::benchmark_sent.load()<<",\"emp_received_bytes\":"<<NetIO::benchmark_received.load()<<"}\n";
    }catch(...){std::cerr<<"hybrid curve rejected category=protocol-or-validity stage="<<stage<<"\n";return 4;}
}
