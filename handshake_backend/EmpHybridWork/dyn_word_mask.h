#pragma once
// Full-width conversion masks on the runtime-sized layer. Same construction and
// the same Lean circuits as word_mask.h (see that file and
// CONVERSION_COST_LEVERS.md); only the wire handling differs. No gate logic.
#include "dyn_session.h"
#include "word_mask.h"
namespace emp_hybrid {
struct DynMask {Wires bits;H field;bool used=false;};
// One uniform bit nobody knows, as a private Boolean wire and as a field share of the same bit.
struct DynBitPair {Wires bit;H field;};
inline unsigned word_bucket_for(unsigned n){
    if(n==16)return 22;if(n==64)return 17;if(n==256)return 14;if(n==1024)return 12;throw std::invalid_argument("mask batch size");
}
inline std::array<uint8_t,32> bits_to_bytes(const std::vector<uint8_t>&bits,size_t at){
    std::array<uint8_t,32>out{};for(unsigned i=0;i<255;i++)if(bits.at(at+i))out[i/8]|=uint8_t(1u<<(i%8));return out;
}
#ifdef EMP_HYBRID_SEMI_HONEST
// Semi-honest mode: parties follow the protocol, so a mask is r = rA + rB with
// each party supplying its own canonical r to both engines. No cut, no buckets.
inline std::vector<DynMask> generate_masks(DynSession&s,FE&field,Challenge&,int party,const WordCircuits&circuits,unsigned N,unsigned bit_blocks=0,std::vector<DynBitPair>*pairs=nullptr){
    ProfileScope scope("conversion masks: generate");
    if(s.party()!=party||field.party_id()!=unsigned(party-1))throw std::runtime_error("engine party mapping");
    if(bit_blocks){
        // Bit pairs: each party supplies its own random bits to both engines; the pair is their XOR.
        if(!pairs||bit_blocks>N)throw std::runtime_error("bit block count");
        const size_t n=size_t(bit_blocks)*255;std::vector<uint8_t>bits(n);std::vector<uint64_t>coins(n);
        {emp::PRG prg;prg.random_data_unaligned(bits.data(),int(n));for(size_t i=0;i<n;i++){bits[i]&=1;coins[i]=bits[i];}}
        auto wires=s.input_both(bits);auto shares=field.input_coins(coins);field.check();
        auto joined=s.run(circuits.xor_bit.parallel(uint32_t(n)),DynSession::interleave(wires.first,wires.second));
        auto combined=circuits.field_bit_xor(field,shares[0],shares[1]);
        for(size_t i=0;i<n;i++)pairs->push_back({joined.slice(i,i+1),combined[i]});
    }
    const unsigned W=255;std::vector<uint8_t>mine(size_t(N)*W);std::vector<std::array<uint8_t,32>>local(N);
    {emp::PRG prg;for(unsigned j=0;j<N;j++){std::array<uint8_t,32>c{};do{prg.random_data_unaligned(c.data(),32);c[31]&=127;}while(!canonical(c));local[j]=c;for(unsigned i=0;i<W;i++)mine[size_t(j)*W+i]=(c[i/8]>>(i%8))&1;}}
    auto shares=s.input_both(mine);auto native=field.input_elements(local);
    std::vector<DynMask>masks;
    for(unsigned j=0;j<N;j++){
        auto a=shares.first.slice(size_t(j)*W,size_t(j+1)*W),b=shares.second.slice(size_t(j)*W,size_t(j+1)*W);
        auto sum=s.run(circuits.finalize_mask,DynSession::concat({&a,&b}));
        masks.push_back({sum.slice(0,255),field.add(native[0][j],native[1][j])});
    }
    return masks;
}
#else
// The first `bit_blocks` kept references become 255 single-bit pairs each (appended to `pairs`),
// by the construction of word_mask.h (lever 3c); the rest become full-width masks.
inline std::vector<DynMask> generate_masks(DynSession&s,FE&field,Challenge&challenge,int party,const WordCircuits&circuits,unsigned N,unsigned bit_blocks=0,std::vector<DynBitPair>*pairs=nullptr){
    ProfileScope scope("conversion masks: generate");
    if(s.party()!=party||field.party_id()!=unsigned(party-1))throw std::runtime_error("engine party mapping");
    if(bit_blocks>N||(bit_blocks&&!pairs))throw std::runtime_error("bit block count");
    const unsigned B=word_bucket_for(N),K=B*N,M=2*K,W=255;
    challenge.domain="WORDMASK-dyn-v1:p25519:n"+std::to_string(N)+":bits"+std::to_string(bit_blocks)+":B"+std::to_string(B)+":C2:S128:local-AB:"+challenge.domain;
    // 1. Candidates fixed in both engines before any challenge.
    std::vector<uint8_t>mine(size_t(M)*W);std::vector<std::array<uint8_t,32>>local(M);
    {emp::PRG prg;for(unsigned j=0;j<M;j++){std::array<uint8_t,32>c{};do{prg.random_data_unaligned(c.data(),32);c[31]&=127;}while(!canonical(c));local[j]=c;for(unsigned i=0;i<W;i++)mine[size_t(j)*W+i]=(c[i/8]>>(i%8))&1;}}
    auto shares=s.input_both(mine);Wires all=DynSession::concat({&shares.first,&shares.second});
    auto native=field.input_elements(local);field.check();
    auto index=[&](unsigned owner,unsigned cand,unsigned bit){return size_t(owner)*M*W+size_t(cand)*W+bit;};
    // 2. Cut.
    auto permutation=challenge.permutation(M);std::vector<unsigned>cut(permutation.begin(),permutation.begin()+K),remain(permutation.begin()+K,permutation.end());
    {
        std::vector<size_t>ids;std::vector<H>fcut;
        for(unsigned owner=0;owner<2;owner++)for(auto j:cut){for(unsigned i=0;i<W;i++)ids.push_back(index(owner,j,i));fcut.push_back(native[owner][j]);}
        auto opened=field.checked_open(fcut);auto bits=s.open(DynSession::pick(all,ids));
        for(unsigned q=0;q<2*K;q++){auto v=bits_to_bytes(bits,size_t(q)*W);if(!canonical(v)||v!=opened[q])throw std::runtime_error("cross-domain candidate mismatch");}
    }
    // 3. Buckets.
    auto buckets=challenge.permutation(K);
    auto candidate=[&](unsigned bucket,unsigned k){return remain[buckets[B*bucket+k]];};
    {
        const unsigned D=2*N*(B-1);std::vector<size_t>ids;std::vector<H>sums;ids.reserve(size_t(D)*2*W);
        for(unsigned owner=0;owner<2;owner++)for(unsigned j=0;j<N;j++)for(unsigned k=1;k<B;k++){
            for(unsigned i=0;i<W;i++)ids.push_back(index(owner,candidate(j,0),i));
            for(unsigned i=0;i<W;i++)ids.push_back(index(owner,candidate(j,k),i));
            sums.push_back(field.add(native[owner][candidate(j,0)],native[owner][candidate(j,k)]));
        }
        auto out=s.run(circuits.modadd.parallel(D),DynSession::pick(all,ids));
        auto opened=field.checked_open(sums);auto bits=s.open(out);
        for(unsigned z=0;z<D;z++)if(bits_to_bytes(bits,size_t(z)*W)!=opened[z])throw std::runtime_error("cross-domain bucket mismatch");
    }
    // 4. Kept references: (rA+rB) mod p and a canonical flag per mask.
    std::vector<size_t>ids;for(unsigned j=0;j<N;j++){for(unsigned i=0;i<W;i++)ids.push_back(index(0,candidate(j,0),i));for(unsigned i=0;i<W;i++)ids.push_back(index(1,candidate(j,0),i));}
    // mask: (rA+rB) mod p, flag = both canonical; bits: rA xor rB, flag = both canonical and both >= 32.
    Wires final_wires;{
        auto chosen=DynSession::pick(all,ids);const size_t split=size_t(bit_blocks)*2*W;
        if(!bit_blocks)final_wires=s.run(circuits.finalize_mask.parallel(N),chosen);
        else{
            auto head=s.run(circuits.finalize_bits.parallel(bit_blocks),chosen.slice(0,split));
            if(bit_blocks<N){auto tail=s.run(circuits.finalize_mask.parallel(N-bit_blocks),chosen.slice(split,size_t(N)*2*W));final_wires=DynSession::concat({&head,&tail});}
            else final_wires=head;
        }
    }
    std::vector<size_t>flags;for(unsigned j=0;j<N;j++)flags.push_back(size_t(j)*256+255);
    for(auto bit:s.open(DynSession::pick(final_wires,flags)))if(!bit)throw std::runtime_error("kept reference out of range");
    field.check();
    std::vector<DynMask>masks;
    for(unsigned j=bit_blocks;j<N;j++)masks.push_back({final_wires.slice(size_t(j)*256,size_t(j)*256+255),field.add(native[0][candidate(j,0)],native[1][candidate(j,0)])});
    if(bit_blocks){
        // Each party inputs the 255 bits of its own kept reference as field elements. Checked:
        // every input is a bit, and the bits recompose to the already-verified reference. With
        // the reference canonical and >= 32, that forces each field bit to equal the Boolean
        // bit. Then one field XOR per bit. All three steps are Lean field programs.
        std::vector<uint64_t>bits(size_t(bit_blocks)*W);
        for(unsigned j=0;j<bit_blocks;j++)for(unsigned i=0;i<W;i++)bits[size_t(j)*W+i]=(local[candidate(j,0)][i/8]>>(i%8))&1;
        auto shares=field.input_coins(bits);field.check();
        std::vector<H>all_bits;std::vector<std::vector<H>>blocks;
        for(unsigned owner=0;owner<2;owner++){
            for(auto h:shares[owner])all_bits.push_back(h);
            for(unsigned j=0;j<bit_blocks;j++){
                std::vector<H>instance(shares[owner].begin()+size_t(j)*W,shares[owner].begin()+size_t(j+1)*W);instance.push_back(native[owner][candidate(j,0)]);blocks.push_back(instance);
            }
        }
        auto zero=circuits.recompose.evaluate(field,blocks);
        for(auto h:circuits.field_bit_checks(field,all_bits))zero.push_back(h);
        for(auto&v:field.checked_open(zero))for(auto byte:v)if(byte)throw std::runtime_error("bit block inconsistent with verified reference");
        auto combined=circuits.field_bit_xor(field,shares[0],shares[1]);field.check();
        for(unsigned j=0;j<bit_blocks;j++)for(unsigned i=0;i<W;i++)pairs->push_back({final_wires.slice(size_t(j)*256+i,size_t(j)*256+i+1),combined[size_t(j)*W+i]});
    }
    return masks;
}
#endif
// One field share -> 255 private Boolean bits (numeric order), consuming one mask.
inline Wires field_to_word(DynSession&s,FE&f,Challenge&channel,const WordCircuits&circuits,DynMask&mask,H value){
    ProfileScope scope("conversion: field value to boolean word");
    if(mask.used)throw std::runtime_error("word mask reuse");mask.used=true;
    auto c=f.checked_open({f.sub(value,mask.field)}).at(0);if(!canonical(c))throw std::runtime_error("noncanonical public field mask");
    std::array<uint8_t,32>peer{};channel.transfer(c.data(),peer.data(),32);if(c!=peer)throw std::runtime_error("public masked value disagreement");
    std::vector<uint8_t>bits(255);for(unsigned i=0;i<255;i++)bits[i]=(c[i/8]>>(i%8))&1;
    auto constant=s.public_bits(bits);
    return s.run(circuits.modadd,DynSession::concat({&mask.bits,&constant}));   // (r+c) mod p
}
}
