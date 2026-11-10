// Native X25519 with (a) the scalar's ladder swap bits held as field-bit shares,
// (b) full-width masks for the coordinate in and the result out, and the leaner
// Lean ladder (TlsMpc.X25519Fast) with a masked inversion. Every Boolean gate and
// field product comes from a pinned Lean export; same public status openings as
// curve_fixture.cpp. Candidate for review; statistical-128 profile only.
#include "x25519_fast.h"
#include "big_stack.h"
// Build-time profile: mask batch size, and whether the scalar arrives as field
// bits (default; lever 3a) or as Boolean bits converted through single-bit
// pairs (lever 3c; for scalars that only exist inside the Boolean engine).
#ifndef EMP_WORD_BATCH
#define EMP_WORD_BATCH 16
#endif
#ifndef EMP_SCALAR_BOOLEAN
#define EMP_SCALAR_BOOLEAN 0
#endif
#include <chrono>
#include <fstream>
#include <iostream>
using namespace emp;
using namespace emp_hybrid;
using Clock=std::chrono::steady_clock;
static double elapsed(Clock::time_point start){return std::chrono::duration<double>(Clock::now()-start).count();}
static std::array<bool,512> read_share(const char*path){
    std::array<bool,512> out{};std::ifstream in(path,std::ios::binary);for(auto &b:out){char x;if(!in.get(x)||x<0||x>1)throw std::runtime_error("fixture share encoding");b=x;}char extra;if(in.get(extra))throw std::runtime_error("fixture share length");return out;
}
static int run(int argc,char**argv){
    // party,port,own XOR share,public fixture expectation,pinned flat DAG,
    // public full closure identity,metrics output.
    // argv[5] (the older flat program path) is accepted for interface
    // compatibility and unused: the ladder is the pinned Lean export.
    if(argc!=8)return 2;const char*stage="public-load";constexpr unsigned NB=EMP_SCALAR_BOOLEAN?1:0;
    try{
        int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        auto start=Clock::now(),t=start;WordCircuits circuits;X25519Fast curve;auto mine=read_share(argv[3]);
        std::string hex=argv[4],closure=argv[6];if(hex.size()!=64||closure.size()!=64||closure.find_first_not_of("0123456789abcdef")!=std::string::npos)throw std::runtime_error("fixture public profile");
        std::array<uint8_t,32>expected{};for(unsigned i=0;i<32;i++)expected[i]=std::stoul(hex.substr(i*2,2),nullptr,16);double load=elapsed(t),setup=0,generation_time=0,scalar_time=0,tofield=0,curve_time=0,tobool=0;uint64_t ands=0;
        {
            NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool threads(4);t=Clock::now();
            {
                AG2PCSession session(&io,&threads,party,128);FE field(party-1,port+10);setup=elapsed(t);
                Challenge challenge{io,party,"curve-v2:LE32-MSB:epoch0:program-closure="+closure};
                stage="word-masks";t=Clock::now();auto batch=WordMaskGeneratorV1::generate<EMP_WORD_BATCH>(session,field,challenge,party,circuits,NB);generation_time=elapsed(t);
                WordConverter<EMP_WORD_BATCH>converter(session,field,challenge,batch,circuits);
#if EMP_SCALAR_BOOLEAN
                // (c) Scalar exists only as Boolean XOR shares: derive the 252
                // ladder swap bits with the Lean swap-bit circuit (no AND gates),
                // then convert each through one verified single-bit pair.
                stage="scalar-boolean-bits";t=Clock::now();
                std::array<bool,256>scalar_share{};for(unsigned i=0;i<256;i++)scalar_share[i]=mine[i];
                auto sa=session.input<V<256>>(ALICE,scalar_share),sb=session.input<V<256>>(BOB,scalar_share);
                auto scalar_bits=circuits.xor_values(session,sa,sb);session.checkpoint(scalar_bits,batch.held);
                std::vector<unsigned>scalar_numeric;for(unsigned i=0;i<256;i++)scalar_numeric.push_back(8*(i/8)+7-i%8);
                auto swap_wires=session.run_artifact<V<252>>(curve.swap_bits.parallel(1),select<256,256>(session,scalar_bits,scalar_numeric));
                session.checkpoint(swap_wires,scalar_bits,batch.held);
                auto scalar=converter.bits_to_field(swap_wires,scalar_bits);scalar_time=elapsed(t);
#else
                // (a) Scalar: each party inputs its XOR share of every ladder swap
                // bit straight into the field. A swap bit is an XOR of adjacent
                // scalar bits, so a party derives its share of it locally from its
                // own scalar share (TlsMpc.X25519SwapBits.swapBit_shares); ALICE
                // alone complements step 253. Bitness of every contribution is
                // checked by opening b*(b-1); then one field XOR per bit.
                stage="scalar-field-bits";t=Clock::now();
                auto k=[&](unsigned i){return uint64_t(mine[8*(i/8)+7-i%8]);};
                std::vector<uint64_t>local(252);
                for(unsigned step=2;step<=253;step++)local[step-2]=step==2?k(3):step==253?(k(253)^uint64_t(party==ALICE)):(k(step+1)^k(step));
                if(party==BOB&&std::getenv("EMP_TEST_SCALAR_NONBIT"))local[5]=2;
                auto shares=field.input_coins(local);field.check();
                {
                    // Lean field programs: b*(b-1) per contribution, then a+b-2ab per bit.
                    std::vector<H>all=shares[0];all.insert(all.end(),shares[1].begin(),shares[1].end());
                    for(auto&v:field.checked_open(circuits.field_bit_checks(field,all)))for(auto byte:v)if(byte)throw std::runtime_error("non-bit scalar contribution");
                }
                auto scalar=circuits.field_bit_xor(field,shares[0],shares[1]);scalar_time=elapsed(t);
#endif
                // Coordinate: Boolean XOR shares, then ONE masked opening into the field.
                std::array<bool,256>point_share{};for(unsigned i=0;i<256;i++)point_share[i]=mine[256+i];
                auto a=session.input<V<256>>(ALICE,point_share),b=session.input<V<256>>(BOB,point_share);
                auto application=circuits.xor_values(session,a,b);session.checkpoint(application,batch.held);
                // RFC7748 coordinate high bit is ignored INSIDE MPC.
                std::vector<unsigned>numeric_indices;for(unsigned i=0;i<255;i++)numeric_indices.push_back(8*(i/8)+7-i%8);
                auto numeric=select<256,255>(session,application,numeric_indices);
                stage="boolean-to-field";t=Clock::now();auto point=converter.boolean_to_field(numeric,application);tofield=elapsed(t);
                bool zero_result=false;
                stage="native-x25519";t=Clock::now();auto dh=curve.evaluate(field,challenge,scalar,point,zero_result);curve_time=elapsed(t);
                stage="field-to-boolean";t=Clock::now();auto value=converter.field_to_boolean(dh,application);tobool=elapsed(t);
                // Output is equality+nonzero ONLY. The canonical DH bits stay
                // authenticated/private for a later Signal/TLS caller.
                // The comparison circuit is the Lean-exported status circuit.
                if(expected[31]&128)throw std::runtime_error("fixture expectation range");
                auto status=converter.status(value,expected,application);auto clear=session.reveal(status,PUBLIC,batch.held,value);
                if(!clear)throw std::runtime_error("missing status");stage="curve-nonzero";if(!(*clear)[1])throw std::runtime_error("low-order rejection");stage="curve-equality";if(!(*clear)[0])throw std::runtime_error("fixture mismatch");
                ands=session.num_and();
                std::cout<<"hybrid curve v2 fixture passed private_result_bits=255 word_masks_generated="<<batch.masks.size()<<" word_masks_consumed="<<converter.consumed()<<" bit_pairs_consumed="<<converter.bits_consumed()<<"\n";
            }
        }
        std::ofstream report(argv[7]);report<<"{\"load_seconds\":"<<load<<",\"setup_seconds\":"<<setup<<",\"mask_generation_seconds\":"<<generation_time<<",\"scalar_seconds\":"<<scalar_time<<",\"boolean_to_field_seconds\":"<<tofield<<",\"native_curve_seconds\":"<<curve_time<<",\"field_to_boolean_seconds\":"<<tobool<<",\"wall_seconds\":"<<elapsed(start)<<",\"boolean_and_gates\":"<<ands<<",\"emp_sent_bytes\":"<<NetIO::benchmark_sent.load()<<",\"emp_received_bytes\":"<<NetIO::benchmark_received.load()<<"}\n";
    }catch(...){std::cerr<<"hybrid curve v2 rejected category=protocol-or-validity stage="<<stage<<"\n";return 4;}
    return 0;
}
int main(int argc,char**argv){
    // Large mask batches keep wire-id arrays inline in typed values.
    int code=4;
    try{emp_hybrid::run_with_stack(size_t(1)<<30,[&]{code=run(argc,argv);});}catch(...){std::cerr<<"hybrid curve v2 rejected category=runtime stage=stack\n";return 4;}
    return code;
}
