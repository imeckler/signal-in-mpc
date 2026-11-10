#pragma once
#include <emp-ag2pc/emp-ag2pc.h>
#include <openssl/sha.h>
#include "mask_pool.h"
#include <algorithm>
#include <array>
#include <numeric>
#include <stdexcept>
namespace emp_hybrid {
using namespace emp;
using FE=emp_hybrid::FieldEngine;
using H=FE::Handle;
using C=AG2PCSession::ctx_t;
template<size_t N>using V=BitVec_T<C,N>;
struct Challenge {
    NetIO&io;int party;uint64_t phase=0;std::array<uint8_t,32> joint_session{};std::string domain;
    Challenge(NetIO&i,int p,std::string d):io(i),party(p),domain(std::move(d)){}
    void transfer(const uint8_t*send,uint8_t*receive,size_t n){
        if(party==ALICE){io.send_data(send,n);io.flush();io.recv_data(receive,n);}
        else{io.recv_data(receive,n);io.send_data(send,n);io.flush();}
    }
    std::vector<unsigned> permutation(unsigned n){
        // Both domain-bound commitments precede either opening. Context is an
        // explicit LOCAL fixture identity; remote deployment identity is open.
        std::array<uint8_t,64> local{},other{};PRG prg;prg.random_data_unaligned(local.data(),32);
        
        std::array<uint8_t,32> domain_hash{};SHA256(reinterpret_cast<const uint8_t*>(domain.data()),domain.size(),domain_hash.data());std::copy_n(domain_hash.begin(),24,local.begin()+32);
        for(unsigned i=0;i<8;i++)local[56+i]=uint8_t(phase>>(8*i));
        std::array<uint8_t,32> commit{},peer{},check{};SHA256(local.data(),local.size(),commit.data());
        transfer(commit.data(),peer.data(),32);transfer(local.data(),other.data(),64);
        SHA256(other.data(),other.size(),check.data());
        if(peer!=check||!std::equal(local.begin()+32,local.end(),other.begin()+32))throw std::runtime_error("challenge frame");
        std::array<uint8_t,72> seed{};
        auto &a=party==ALICE?local:other;auto &b=party==ALICE?other:local;
        std::copy_n(a.begin(),32,seed.begin());std::copy_n(b.begin(),32,seed.begin()+32);
        if(phase==0)SHA256(seed.data(),64,joint_session.data());
        uint64_t counter=0;std::array<uint8_t,32> block{};size_t pos=32;
        auto word=[&](){if(pos==32){for(unsigned i=0;i<8;i++)seed[64+i]=uint8_t(counter>>(8*i));counter++;SHA256(seed.data(),seed.size(),block.data());pos=0;}uint32_t x=0;for(unsigned i=0;i<4;i++)x|=uint32_t(block[pos++])<<(8*i);return x;};
        std::vector<unsigned> out(n);std::iota(out.begin(),out.end(),0);
        for(unsigned i=n;i>1;i--){uint64_t limit=(uint64_t(1)<<32)/i*i;uint32_t x;do{x=word();}while(x>=limit);std::swap(out[i-1],out[x%i]);}
        phase++;return out;
    }
};
template<size_t N,size_t M>V<M> select(AG2PCSession&s,const V<N>&source,const std::vector<unsigned>&indices){
    if(indices.size()!=M)throw std::runtime_error("selection size");std::array<uint32_t,N>old{};std::array<uint32_t,M>ids{};source.pack_wires(old.data());
    for(size_t i=0;i<M;i++){if(indices[i]>=N)throw std::runtime_error("selection range");ids[i]=old[indices[i]];}return V<M>::from_wires(s.ctx(),ids.data());
}
static circuit::BooleanProgram xor_program(unsigned inputs,const std::vector<std::pair<unsigned,unsigned>>&pairs){
    circuit::BooleanProgram p;p.num_inputs=inputs;p.num_wires=inputs;
    for(auto [a,b]:pairs){unsigned o=p.num_wires++;p.gates.push_back({a,b,o,circuit::Op::Xor});p.outputs.push_back(o);}return p;
}
static std::vector<H> field_xor(FE&f,const std::vector<H>&a,const std::vector<H>&b){
    auto product=f.mul(a,b);std::vector<H>out;for(size_t i=0;i<a.size();i++)out.push_back(f.sub(f.add(a[i],b[i]),f.add(product[i],product[i])));return out;
}
template<size_t N>static void compare(const std::vector<std::array<uint8_t,32>>&native,const std::array<bool,N>&binary){
    if(native.size()!=N)throw std::runtime_error("comparison shape");
    for(size_t i=0;i<N;i++){for(size_t j=1;j<32;j++)if(native[i][j])throw std::runtime_error("nonbit native coin");if(native[i][0]>1||bool(native[i][0])!=binary[i])throw std::runtime_error("cross-domain coin mismatch");}
}
template<size_t N>typename V<N>::clear_t fresh(){typename V<N>::clear_t out{};std::array<uint8_t,N>bytes{};PRG prg;prg.random_data_unaligned(bytes.data(),bytes.size());for(size_t i=0;i<N;i++)out[i]=bytes[i]&1;return out;}
template<unsigned Ell>struct Generation {CheckedMaskPool pool;V<Ell> held;};
class DaBitGeneratorV1 {
public:
    // Only these exact public profiles are admitted by this implementation.
    // Parameter receipts must cover each before native use; no user sizing.
    template<unsigned Ell>static Generation<Ell> generate(AG2PCSession&session,FE&field,Challenge&challenge,int party){
        static_assert(Ell==256||Ell==512||Ell==1024);
        if(session.protocol().party!=party||field.party_id()!=unsigned(party-1))throw std::runtime_error("engine party mapping");
        constexpr unsigned B=5,K=B*Ell,M=2*K,D=K-Ell;
        if(challenge.phase!=0)throw std::runtime_error("generator challenge reuse");
        challenge.domain="RW2019-v1:p25519:ell"+std::to_string(Ell)+":B5:C2:S40:local-AB:"+challenge.domain;
        auto mine=fresh<M>();std::vector<uint64_t>local;for(auto b:mine)local.push_back(b);
        if(party==BOB&&std::getenv("EMP_TEST_BAD_NATIVE_COINS"))std::fill(local.begin(),local.end(),2);
        auto a=session.input<V<M>>(ALICE,mine),b=session.input<V<M>>(BOB,mine);session.checkpoint(a,b);
        auto native=field.input_coins(local);field.check();
        auto permutation=challenge.permutation(M);std::vector<unsigned>cut(permutation.begin(),permutation.begin()+K),remain(permutation.begin()+K,permutation.end());
        auto acut=select<M,K>(session,a,cut),bcut=select<M,K>(session,b,cut);std::vector<H>fcut;
        for(auto i:cut)fcut.push_back(native[0][i]);for(auto i:cut)fcut.push_back(native[1][i]);
        auto opened=field.checked_open(fcut);auto ao=session.reveal(acut,PUBLIC,a,b,bcut),bo=session.reveal(bcut,PUBLIC,a,b);if(!ao||!bo)throw std::runtime_error("cut open");
        std::array<bool,M>cutbits{};std::copy(ao->begin(),ao->end(),cutbits.begin());std::copy(bo->begin(),bo->end(),cutbits.begin()+K);compare(opened,cutbits);
        std::vector<std::pair<unsigned,unsigned>>pairs;std::vector<H>fa,fb;
        for(auto i:remain){pairs.emplace_back(i,M+i);fa.push_back(native[0][i]);fb.push_back(native[1][i]);}
        auto combined=session.run_artifact<V<K>>(xor_program(2*M,pairs),a,b);session.checkpoint(combined);
        auto fc=field_xor(field,fa,fb);field.check();
        auto buckets=challenge.permutation(K);pairs.clear();fa.clear();fb.clear();std::vector<unsigned>kept;
        for(unsigned j=0;j<Ell;j++){unsigned ref=buckets[B*j];kept.push_back(ref);for(unsigned k=1;k<B;k++){unsigned i=buckets[B*j+k];pairs.emplace_back(i,ref);fa.push_back(fc[i]);fb.push_back(fc[ref]);}}
        auto differences=session.run_artifact<V<D>>(xor_program(K,pairs),combined);session.checkpoint(combined,differences);
        auto fd=field_xor(field,fa,fb);opened=field.checked_open(fd);auto diffs=session.reveal(differences,PUBLIC,combined);if(!diffs)throw std::runtime_error("bucket open");compare(opened,*diffs);
        auto held=select<K,Ell>(session,combined,kept);session.checkpoint(held);std::array<uint32_t,Ell>ids{};held.pack_wires(ids.data());
        std::vector<MaskPair>verified;for(unsigned i=0;i<Ell;i++)verified.push_back({ids[i],fc[kept[i]]});
        SessionBinding binding;binding.nonce=challenge.joint_session;SHA256(reinterpret_cast<const uint8_t*>(challenge.domain.data()),challenge.domain.size(),binding.configuration.data());
        // Sole constructor call; actual checks above settle before capability.
        return {CheckedMaskPool(binding,{&session,&field},std::move(verified)),held};
    }
};
} // namespace emp_hybrid
