// Native field/configuration tests only. No peers, sockets or MPC execution.
#include "NativeWorker.h"
#include <type_traits>
#include <cassert>
#include <iostream>
using S=tls_mpc_worker::Share;
static_assert(std::is_same_v<S::bit_type,GC::MaliciousCcdSecret<gf2n_long>>);
static_assert(std::is_same_v<S::BasicProtocol,Beaver<S>>);
static_assert(std::is_same_v<S::MAC_Check,MaliciousShamirMC<S>>);
static_assert(S::malicious);
int main(){
    ShamirOptions::singleton={5,2};
    bigint p=1;p<<=255;p-=19;tls_mpc_worker::Field::init_field(p);
    Machine<S>::init_binary_domains(128,128);
    assert(gf2n_long::length()==128);
    assert(S::bit_type::part_type::open_type::length()==128);
    assert(tls_mpc_worker::Field::pr()==p);
    gf2n_long zero(0),one(1);
    assert(!::Bit(zero).get());assert(::Bit(one).get());
    size_t rejected=0;
    for(int i=1;i<128;++i){
        gf2n_long value=one<<i;
        try{::Bit bad(value);(void)bad;}catch(const std::runtime_error&){++rejected;}
        assert(value*value.invert()==one);
    }
    assert(rejected==127);
    // Verify malicious Shamir's evaluation field has five distinct points.
    for(int i=1;i<=5;++i)for(int j=1;j<=5;++j)if(i!=j)
        assert(!(gf2n_long(i)+gf2n_long(j)).is_zero());
    // BITCOMS/BITDECS/XORS operate on local native shares. Test non-bit local
    // field values too: a share of a secret bit is generally NOT itself 0/1.
    // No reconstruction, peers, multiplication protocol, or plaintext key.
    size_t lanes_checked=0;
    using B=S::bit_type;
    for(int width=1;width<=64;++width) {
        StackedVector<B> registers(4*width);
        ArgVector left,right,output;
        for(int i=0;i<width;++i) {
            gf2n_long x=gf2n_long(i+1)+(one<<(64+i%64));
            gf2n_long y=gf2n_long(width-i)+(one<<(32+i%32));
            registers[i]=B(typename B::part_type(x));
            registers[width+i]=B(typename B::part_type(y));
            left.push_back(width-1-i);right.push_back(width+i);output.push_back(2*width+i);
        }
        B packed_left,packed_right,result;
        packed_left.bitcom(registers,left);packed_right.bitcom(registers,right);
        result.xor_(width,packed_left,packed_right);
        result.bitdec(registers,output);
        for(int i=0;i<width;++i) {
            assert(registers[output[i]].get_regs().size()==1);
            gf2n_long expected=registers[left[i]].get_reg(0)+registers[right[i]].get_reg(0);
            assert(registers[output[i]].get_reg(0)==expected);
            ++lanes_checked;
        }
    }
    // Public evidence for a remaining erasure boundary: this pinned AES-CTR
    // PRNG retains its original seed after use. Later possession of that seed
    // reproduces earlier output. Overwriting key containers cannot prevent it.
    PRNG history,replay;std::array<unsigned char,SEED_SIZE> seed;
    for(size_t i=0;i<seed.size();++i)seed[i]=i+1;
    history.SetSeed(seed.data());
    std::array<unsigned char,1024> previous,reproduced,discard;
    history.get_octets(previous.data(),previous.size());
    for(int i=0;i<4;++i)history.get_octets(discard.data(),discard.size());
    replay.SetSeed(history.get_seed());
    replay.get_octets(reproduced.data(),reproduced.size());assert(previous==reproduced);
    assert(lanes_checked==2080);
    // Actual CCD share storage, including packed widths1..64, is overwritten
    // without changing its shape or the independently copied buffer.
    size_t wiped=0;
    for(int width=1;width<=64;++width) {
        B packed;packed.resize_regs(width);
        for(int i=0;i<width;++i)packed.get_reg(i)=typename B::part_type(one<<(i%128));
        tls_mpc_worker::Bits owned(2,std::vector<B>{packed});
        auto copied=owned;owned.wipe();
        for(size_t row=0;row<owned.size();++row)for(int bit=0;bit<width;++bit) {
            assert(owned[row][0].get_reg(bit)==zero);
            assert(copied[row][0].get_reg(bit)==packed.get_reg(bit));++wiped;
        }
    }
    std::cout<<"Fp25519 / five-party t2 / CCD GF(2^128) types initialized; 127 non-bit openings rejected; no MPC execution\n";
    std::cout<<"2080 native local-share lane packing/XOR/unpacking checks passed (widths1..64)\n";
    std::cout<<wiped<<" native field-slot overwrites checked; NOT full VM erasure\n";
    std::cout<<"1024 earlier PRNG bytes reproduced from retained seed after 4096 further bytes; public fixture only\n";
}
