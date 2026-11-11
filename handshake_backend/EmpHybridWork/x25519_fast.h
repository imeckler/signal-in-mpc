#pragma once
// X25519 on field shares using the Lean program TlsMpc.X25519Fast (projective
// output) followed by a masked inversion. The arithmetic is two Lean field
// programs; this file only samples the mask, opens one value and divides by it.
//
// Masked inversion: with r = rA + rB uniform and unknown to either party, open
// z*r (MAC-checked). If z != 0 the opened value is uniform and reveals nothing;
// x/z = (x*r)/(z*r). If it opens to zero then z = 0 (or r = 0, probability
// 2^-255): the RFC result is zero, which callers reject publicly anyway, so the
// only thing revealed is the all-zero outcome.
#include "word_mask.h"
namespace emp_hybrid {
struct X25519Fast {
    FieldProgram ladder{std::string(EMP_WORD_CIRCUIT_DIR)+"/x25519-fast.flat",X25519_FAST_SHA};
    FieldProgram mask_pair{std::string(EMP_WORD_CIRCUIT_DIR)+"/field-mask-pair.flat",FIELD_MASK_PAIR_SHA};
    LeanCircuit swap_bits{std::string(EMP_WORD_CIRCUIT_DIR)+"/swap-bits.flat",SWAP_BITS_SHA};
    X25519Fast(){
        if(ladder.input_count()!=257||ladder.output_count()!=2||mask_pair.input_count()!=3||mask_pair.output_count()!=2||swap_bits.input_bits()!=256||swap_bits.output_bits()!=252)throw std::runtime_error("x25519 program shape");
    }
    // swaps[k] is the swap bit of ladder step k+2 (252 field-bit shares).
    H evaluate(FE&f,Challenge&channel,const std::vector<H>&swaps,H point,bool&zero_result)const{
        if(swaps.size()!=252)throw std::runtime_error("swap bit count");
        std::vector<H>input(257,f.constant(0));for(unsigned k=0;k<252;k++)input[k+2]=swaps[k];input[256]=point;
        auto xz=ladder.evaluate_all(f,{input}).at(0);
        return quotient(f,channel,xz[0],xz[1],zero_result);
    }
    // Several independent agreements together: the same programs on several instances, so the
    // ladders share their rounds (about 255 rounds in all instead of 255 each) and the masked
    // inversions share one. Each instance has its own mask; `zero[i]` as in `evaluate`.
    std::vector<H> evaluate_many(FE&f,Challenge&channel,const std::vector<std::pair<const std::vector<H>*,H>>&jobs,std::vector<bool>&zero)const{
        const size_t n=jobs.size();zero.assign(n,false);if(!n)return {};
        std::vector<std::vector<H>>inputs;
        for(auto&job:jobs){
            if(job.first->size()!=252)throw std::runtime_error("swap bit count");
            std::vector<H>input(257,f.constant(0));for(unsigned k=0;k<252;k++)input[k+2]=(*job.first)[k];input[256]=job.second;inputs.push_back(std::move(input));
        }
        auto xz=ladder.evaluate_all(f,inputs);
        std::vector<std::array<uint8_t,32>>mine(n);
        {PRG prg;for(auto&m:mine)do{prg.random_data_unaligned(m.data(),32);m[31]&=127;}while(!canonical(m));}
        auto contributions=f.input_elements(mine);f.check();
        std::vector<std::vector<H>>pairs;for(size_t i=0;i<n;i++)pairs.push_back({xz[i][0],xz[i][1],f.add(contributions[0][i],contributions[1][i])});
        auto masked=mask_pair.evaluate_all(f,pairs);
        std::vector<H>denominators;for(auto&m:masked)denominators.push_back(m[1]);
        auto opened=f.checked_open(denominators);
        std::vector<uint8_t>flat(32*n),peer(32*n);for(size_t i=0;i<n;i++)std::copy(opened[i].begin(),opened[i].end(),flat.begin()+32*i);
        channel.transfer(flat.data(),peer.data(),flat.size());if(flat!=peer)throw std::runtime_error("masked denominator disagreement");
        std::vector<H>out;
        for(size_t i=0;i<n;i++){
            bool none=true;for(auto byte:opened[i])if(byte)none=false;
            zero[i]=none;out.push_back(none?f.constant(0):f.divide_public(masked[i][0],opened[i]));
        }
        return out;
    }
    // x/z by masked inversion (see the note at the top of this file).
    H quotient(FE&f,Challenge&channel,H x,H z,bool&zero_result)const{
        std::array<H,2>xz{x,z};
        std::array<uint8_t,32>mine{};{PRG prg;do{prg.random_data_unaligned(mine.data(),32);mine[31]&=127;}while(!canonical(mine));}
        auto contributions=f.input_elements({mine});f.check();
        auto mask=f.add(contributions[0][0],contributions[1][0]);
        auto masked=mask_pair.evaluate_all(f,{{xz[0],xz[1],mask}}).at(0);
        auto opened=f.checked_open({masked[1]}).at(0);std::array<uint8_t,32>peer{};channel.transfer(opened.data(),peer.data(),32);
        if(opened!=peer)throw std::runtime_error("masked denominator disagreement");
        zero_result=true;for(auto byte:opened)if(byte)zero_result=false;
        return zero_result?f.constant(0):f.divide_public(masked[0],opened);
    }
};
}
