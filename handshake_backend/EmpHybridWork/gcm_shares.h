#pragma once
// AES-GCM tags from XOR shares of the GHASH key powers.
// Design: GHASH_SHARES.md. Security statements: TlsMpc/GhashShares.lean.
//
// For one traffic key (one direction, until the next KeyUpdate) each party
// holds one XOR share of H, H^2, ..., H^n. The engines produce the shares
// (kernels gcm-key-share and gcm-multiply, opened to one party only); even
// powers come from squaring one's own share locally. For a record whose
// ciphertext is public, each party evaluates its half of the tag polynomial
// here, in the clear, on its own shares and the public blocks, and supplies it
// as a private input to gcm-tag (seal) or gcm-check (open).
//
// What this file computes is local arithmetic on a party's own shares and on
// public data; it is outside the Lean kernel theorems. A wrong half can only
// make a tag wrong (see GhashShares.accept_unique_pad / seal_deviation).
#include "kernel.h"
#include <array>
namespace emp_hybrid {
using Block=std::array<uint8_t,16>;
// GF(2^128) multiplication in the GCM bit order (NIST SP 800-38D, algorithm 1).
inline Block gf_multiply(const Block&x,Block v){
    Block z{};
    for(unsigned i=0;i<128;i++){
        if((x[i/8]>>(7-i%8))&1)for(unsigned j=0;j<16;j++)z[j]^=v[j];
        const bool low=v[15]&1;
        for(int j=15;j>0;j--)v[j]=uint8_t((v[j]>>1)|((v[j-1]&1)<<7));
        v[0]>>=1;if(low)v[0]^=0xe1;
    }
    return z;
}
class GcmShares {
    std::vector<Block>power;   // power[i-1]: this party's share of H^i
    static std::vector<uint8_t> bits(const Block&b){return byte_bits(std::vector<uint8_t>(b.begin(),b.end()));}
    static Block random(){Block b{};emp::PRG prg;prg.random_data_unaligned(b.data(),16);return b;}
    // The garbling party keeps a fresh mask as its share; the masked value is opened to the other party.
    Block reshare(DynSession&s,const Kernel&kernel,Binding bound,int party){
        Block mask=party==emp::ALICE?random():Block{};auto wires=s.input_private(emp::ALICE,bits(mask));bound.push_back({"mask",&wires});
        auto seen=kernel.open_to(s,kernel.run(s,bound),"masked",emp::BOB);
        if(party==emp::ALICE)return mask;
        if(seen.size()!=16)throw std::runtime_error("key share width");
        Block share{};std::copy(seen.begin(),seen.end(),share.begin());return share;
    }
public:
    void clear(){for(auto&b:power)b.fill(0);power.clear();}
    // Shares of H^1..H^count under the traffic key held in `traffic`.
    void ensure(DynSession&s,KernelCache&cache,int party,const Wires&traffic,size_t count){
        if(power.empty()&&count)power.push_back(reshare(s,cache.get("gcm-key-share"),{{"traffic",&traffic}},party));
        while(power.size()<count){
            const size_t next=power.size()+1;
            if(next%2==0){power.push_back(gf_multiply(power[next/2-1],power[next/2-1]));continue;}   // squaring is additive
            const Block none{};
            auto left_a=s.input_private(emp::ALICE,bits(party==emp::ALICE?power[next-2]:none)),left_b=s.input_private(emp::BOB,bits(party==emp::BOB?power[next-2]:none));
            auto right_a=s.input_private(emp::ALICE,bits(party==emp::ALICE?power[0]:none)),right_b=s.input_private(emp::BOB,bits(party==emp::BOB?power[0]:none));
            power.push_back(reshare(s,cache.get("gcm-multiply"),{{"leftA",&left_a},{"leftB",&left_b},{"rightA",&right_a},{"rightB",&right_b}},party));
        }
    }
    // Number of GHASH blocks of a record with this additional data and ciphertext.
    static size_t blocks(size_t aad,size_t ciphertext){return (aad+15)/16+(ciphertext+15)/16+1;}
    // This party's half of the tag polynomial over the public blocks.
    Block half(const std::vector<uint8_t>&aad,const std::vector<uint8_t>&ciphertext)const{
        std::vector<uint8_t>data(aad);data.resize(16*((aad.size()+15)/16),0);
        data.insert(data.end(),ciphertext.begin(),ciphertext.end());data.resize(data.size()+(16-ciphertext.size()%16)%16,0);
        for(uint64_t length:{uint64_t(8*aad.size()),uint64_t(8*ciphertext.size())})for(int i=7;i>=0;i--)data.push_back(uint8_t(length>>(8*i)));
        const size_t count=data.size()/16;if(count>power.size())throw std::runtime_error("key power shares");
        Block total{};
        for(size_t i=0;i<count;i++){
            Block block{};std::copy_n(data.begin()+16*i,16,block.begin());
            auto term=gf_multiply(block,power[count-i-1]);for(unsigned j=0;j<16;j++)total[j]^=term[j];
        }
        return total;
    }
    // Both parties' halves as private inputs, in the order (garbling party's, evaluating party's).
    std::pair<Wires,Wires> supply(DynSession&s,int party,const std::vector<uint8_t>&aad,const std::vector<uint8_t>&ciphertext)const{
        const Block mine=half(aad,ciphertext),none{};
        auto a=s.input_private(emp::ALICE,bits(party==emp::ALICE?mine:none));auto b=s.input_private(emp::BOB,bits(party==emp::BOB?mine:none));
        return {std::move(a),std::move(b)};
    }
};
}
