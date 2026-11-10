// Private X25519 feeding the TLS 1.3 handshake key schedule without opening
// the shared secret (REMAINING_WORK.md section 4 step 6).
//
// Scalar and peer coordinate are XOR-shared. The DH result returns from the
// field as 255 private Boolean bits and is wired directly into the Lean
// handshake-secrets circuit together with a public transcript hash. The four
// derived secrets stay private; the fixture opens only (1) whether the DH
// result is nonzero, as TLS requires, and (2) one bit saying the derived
// secrets equal the value an independent implementation computed.
// Every circuit is a pinned Lean export. Statistical-128 profile only.
#include "x25519_fast.h"
#include "kdf_circuit_pins.h"
#include "big_stack.h"
#include <chrono>
#include <fstream>
#include <iostream>
// Build-time mode. TLS (default): handshake secrets from the DH result and a
// public transcript hash; the nonzero bit is opened as TLS requires. Signal
// (EMP_KDF_SIGNAL=1): RootKey::create_chain from an XOR-shared root key and
// the DH result; the all-zero case is handled inside the circuit (old root
// kept, status byte private), so nothing but the fixture's equality bit opens.
#ifndef EMP_KDF_SIGNAL
#define EMP_KDF_SIGNAL 0
#endif
using namespace emp;
using namespace emp_hybrid;
using Clock=std::chrono::steady_clock;
#if EMP_KDF_SIGNAL
constexpr unsigned SHARE_BITS=768,OUT_BYTES=69;
#else
constexpr unsigned SHARE_BITS=512,OUT_BYTES=128;
#endif
static double elapsed(Clock::time_point start){return std::chrono::duration<double>(Clock::now()-start).count();}
static std::array<bool,SHARE_BITS> read_share(const char*path){
    std::array<bool,SHARE_BITS> out{};std::ifstream in(path,std::ios::binary);for(auto &b:out){char x;if(!in.get(x)||x<0||x>1)throw std::runtime_error("fixture share encoding");b=x;}char extra;if(in.get(extra))throw std::runtime_error("fixture share length");return out;
}
template<size_t N>static std::array<bool,8*N> hex_bits(const std::string&hex){
    if(hex.size()!=2*N||hex.find_first_not_of("0123456789abcdef")!=std::string::npos)throw std::runtime_error("fixture hex");
    std::array<bool,8*N>out{};for(size_t i=0;i<N;i++){unsigned byte=std::stoul(hex.substr(2*i,2),nullptr,16);for(unsigned b=0;b<8;b++)out[8*i+b]=(byte>>b)&1;}return out;
}
static int run(int argc,char**argv){
    // party, port, own XOR share (scalar||coordinate), expected secrets (128
    // bytes hex), public transcript hash (32 bytes hex), closure id, metrics.
    if(argc!=8)return 2;const char*stage="public-load";
    try{
        int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        auto start=Clock::now(),t=start;WordCircuits circuits;X25519Fast curve;
#if EMP_KDF_SIGNAL
        LeanCircuit kdf(std::string(EMP_WORD_CIRCUIT_DIR)+"/signal-dh-ratchet.flat",SIGNAL_DH_RATCHET_SHA),equal(std::string(EMP_WORD_CIRCUIT_DIR)+"/equal-552.flat",EQUAL_552_SHA);
#else
        LeanCircuit kdf(std::string(EMP_WORD_CIRCUIT_DIR)+"/tls-handshake-secrets.flat",TLS_HANDSHAKE_SECRETS_SHA),equal(std::string(EMP_WORD_CIRCUIT_DIR)+"/equal-1024.flat",EQUAL_1024_SHA);
#endif
        if(kdf.input_bits()!=511||kdf.output_bits()!=8*OUT_BYTES||equal.input_bits()!=16*OUT_BYTES||equal.output_bits()!=1)throw std::runtime_error("kdf circuit shape");
        auto mine=read_share(argv[3]);auto expected=hex_bits<OUT_BYTES>(argv[4]);std::string closure=argv[6];
#if !EMP_KDF_SIGNAL
        auto transcript=hex_bits<32>(argv[5]);
#endif
        if(closure.size()!=64||closure.find_first_not_of("0123456789abcdef")!=std::string::npos)throw std::runtime_error("fixture public profile");
        double load=elapsed(t),setup=0,generation_time=0,curve_time=0,kdf_time=0;uint64_t ands=0;
        {
            NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool threads(4);t=Clock::now();
            {
                AG2PCSession session(&io,&threads,party,128);FE field(party-1,port+10);setup=elapsed(t);
                Challenge challenge{io,party,"curve-kdf:LE32-MSB:epoch0:program-closure="+closure};
                stage="word-masks";t=Clock::now();auto batch=WordMaskGeneratorV1::generate<16>(session,field,challenge,party,circuits,0);generation_time=elapsed(t);
                WordConverter<16>converter(session,field,challenge,batch,circuits);
                stage="scalar-field-bits";t=Clock::now();
                auto k=[&](unsigned i){return uint64_t(mine[8*(i/8)+7-i%8]);};
                std::vector<uint64_t>local(252);
                for(unsigned step=2;step<=253;step++)local[step-2]=step==2?k(3):step==253?(k(253)^uint64_t(party==ALICE)):(k(step+1)^k(step));
                auto shares=field.input_coins(local);field.check();
                {
                    std::vector<H>all=shares[0];all.insert(all.end(),shares[1].begin(),shares[1].end());
                    for(auto&v:field.checked_open(circuits.field_bit_checks(field,all)))for(auto byte:v)if(byte)throw std::runtime_error("non-bit scalar contribution");
                }
                auto scalar=circuits.field_bit_xor(field,shares[0],shares[1]);
                std::array<bool,256>point_share{};for(unsigned i=0;i<256;i++)point_share[i]=mine[256+i];
                auto a=session.input<V<256>>(ALICE,point_share),b=session.input<V<256>>(BOB,point_share);
                auto application=circuits.xor_values(session,a,b);session.checkpoint(application,batch.held);
                std::vector<unsigned>numeric_indices;for(unsigned i=0;i<255;i++)numeric_indices.push_back(8*(i/8)+7-i%8);
                auto point=converter.boolean_to_field(select<256,255>(session,application,numeric_indices),application);
                bool zero_result=false;
                stage="native-x25519";auto dh=curve.evaluate(field,challenge,scalar,point,zero_result);
                auto value=converter.field_to_boolean(dh);curve_time=elapsed(t);
                constexpr unsigned OUT=8*OUT_BYTES;
#if EMP_KDF_SIGNAL
                // Root key: XOR-shared private state, never opened.
                std::array<bool,256>root_share{};for(unsigned i=0;i<256;i++)root_share[i]=mine[512+i];
                auto ra=session.input<V<256>>(ALICE,root_share),rb=session.input<V<256>>(BOB,root_share);
                auto other=circuits.xor_values(session,ra,rb);
#else
                // TLS must reject an all-zero shared secret: open only the nonzero bit.
                stage="curve-nonzero";
                {
                    auto status=converter.status(value,std::array<uint8_t,32>{},batch.held);session.checkpoint(status,value,batch.held);
                    auto nonzero=session.reveal(select<2,1>(session,status,{1}),PUBLIC,value,batch.held);
                    if(!nonzero||!(*nonzero)[0])throw std::runtime_error("all-zero shared secret");
                }
                auto other=session.input<V<256>>(PUBLIC,transcript);
#endif
                // Key derivation on the private DH word. The Lean circuit
                // (TlsMpc/HybridKdf.lean) takes the 255-bit word exactly as the
                // conversion produced it, then the other 32 bytes; the split into
                // little-endian bytes happens inside the circuit.
                stage="key-schedule";t=Clock::now();
                session.checkpoint(value,other,batch.held);
                auto input_ids=std::make_unique<std::array<uint32_t,511>>();
                value.pack_wires(input_ids->data());other.pack_wires(input_ids->data()+255);
                auto secrets=session.run_artifact<V<OUT>>(kdf.parallel(1),V<511>::from_wires(session.ctx(),input_ids->data()));
                session.checkpoint(secrets,batch.held);kdf_time=elapsed(t);
                // Fixture check only: one equality bit against the independent value.
                stage="secrets-equality";
                auto reference=session.input<V<OUT>>(PUBLIC,expected);session.checkpoint(secrets,reference,batch.held);
                auto pair_ids=std::make_unique<std::array<uint32_t,2*OUT>>();secrets.pack_wires(pair_ids->data());reference.pack_wires(pair_ids->data()+OUT);
                auto same=session.run_artifact<V<1>>(equal.parallel(1),V<2*OUT>::from_wires(session.ctx(),pair_ids->data()));
                auto clear=session.reveal(same,PUBLIC,secrets,batch.held);
                if(!clear||!(*clear)[0])throw std::runtime_error("derived secrets mismatch");
                ands=session.num_and();
                std::cout<<"curve kdf fixture passed private_secret_bytes="<<OUT_BYTES<<" dh_opened=0 word_masks_consumed="<<converter.consumed()<<"\n";
            }
        }
        std::ofstream report(argv[7]);report<<"{\"load_seconds\":"<<load<<",\"setup_seconds\":"<<setup<<",\"mask_generation_seconds\":"<<generation_time<<",\"scalar_and_curve_seconds\":"<<curve_time<<",\"key_schedule_seconds\":"<<kdf_time<<",\"wall_seconds\":"<<elapsed(start)<<",\"boolean_and_gates\":"<<ands<<",\"emp_sent_bytes\":"<<NetIO::benchmark_sent.load()<<",\"emp_received_bytes\":"<<NetIO::benchmark_received.load()<<"}\n";
    }catch(...){std::cerr<<"curve kdf rejected category=protocol-or-validity stage="<<stage<<"\n";return 4;}
    return 0;
}
int main(int argc,char**argv){
    int code=4;
    try{emp_hybrid::run_with_stack(size_t(1)<<30,[&]{code=run(argc,argv);});}catch(...){std::cerr<<"curve kdf rejected category=runtime stage=stack\n";return 4;}
    return code;
}
