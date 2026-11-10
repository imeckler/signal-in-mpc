// Candidate RW2019/207 coin checking, ell16/B8/C2. No production API.
#include <emp-ag2pc/emp-ag2pc.h>
#include <openssl/sha.h>
#include "field_engine.h"
#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <stdexcept>
using namespace emp;
using FE=emp_hybrid::FieldEngine;
using H=FE::Handle;
using C=AG2PCSession::ctx_t;
template<size_t N>using V=BitVec_T<C,N>;
struct Challenge {
    NetIO&io;int party;uint64_t phase=0;
    void transfer(const uint8_t*send,uint8_t*receive,size_t n){
        if(party==ALICE){io.send_data(send,n);io.flush();io.recv_data(receive,n);}
        else{io.recv_data(receive,n);io.send_data(send,n);io.flush();}
    }
    std::vector<unsigned> permutation(unsigned n){
        // Both domain-bound commitments precede either opening. Context is an
        // explicit LOCAL fixture identity; remote deployment identity is open.
        std::array<uint8_t,64> local{},other{};PRG prg;prg.random_data(local.data(),32);
        const std::string domain="EMP-native-RW-v1:p25519:ell16:B8:C2:local-A-B";
        std::copy(domain.begin(),domain.begin()+std::min(size_t(24),domain.size()),local.begin()+32);
        for(unsigned i=0;i<8;i++)local[56+i]=uint8_t(phase>>(8*i));
        std::array<uint8_t,32> commit{},peer{},check{};SHA256(local.data(),local.size(),commit.data());
        transfer(commit.data(),peer.data(),32);transfer(local.data(),other.data(),64);
        SHA256(other.data(),other.size(),check.data());
        if(peer!=check||!std::equal(local.begin()+32,local.end(),other.begin()+32))throw std::runtime_error("challenge frame");
        std::array<uint8_t,72> seed{};
        auto &a=party==ALICE?local:other;auto &b=party==ALICE?other:local;
        std::copy_n(a.begin(),32,seed.begin());std::copy_n(b.begin(),32,seed.begin()+32);
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
int main(int argc,char**argv){
    if(argc!=3)return 2;
    try{
        int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        struct FinalCounters {~FinalCounters(){std::cout<<"EMP_EXACT_SOCKET_BYTES sent="<<NetIO::benchmark_sent.load()<<" received="<<NetIO::benchmark_received.load()<<"\n";}} counters;
        NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool pool(4);AG2PCSession session(&io,&pool,party,40);
        FE field(party-1,port+10);Challenge challenge{io,party};
        V<256>::clear_t mine{};std::array<uint8_t,256>random{};PRG prg;prg.random_data(random.data(),random.size());std::vector<uint64_t>local;
        for(size_t i=0;i<256;i++){mine[i]=random[i]&1;local.push_back(mine[i]);}
        if(party==BOB&&std::getenv("EMP_TEST_BAD_NATIVE_COINS"))std::fill(local.begin(),local.end(),2);
        auto a=session.input<V<256>>(ALICE,mine),b=session.input<V<256>>(BOB,mine);session.checkpoint(a,b);
        auto native=field.input_coins(local);field.check();
        auto permutation=challenge.permutation(256);std::vector<unsigned>cut(permutation.begin(),permutation.begin()+128),remain(permutation.begin()+128,permutation.end());
        auto acut=select<256,128>(session,a,cut),bcut=select<256,128>(session,b,cut);
        std::vector<H> fcut;for(auto i:cut)fcut.push_back(native[0][i]);for(auto i:cut)fcut.push_back(native[1][i]);
        auto opened=field.checked_open(fcut);
        auto ao=session.reveal(acut,PUBLIC,a,b,bcut);auto bo=session.reveal(bcut,PUBLIC,a,b);if(!ao||!bo)throw std::runtime_error("cut open");
        std::array<bool,256>cutbits{};std::copy(ao->begin(),ao->end(),cutbits.begin());std::copy(bo->begin(),bo->end(),cutbits.begin()+128);compare(opened,cutbits);
        std::vector<std::pair<unsigned,unsigned>>pairs;std::vector<H>fa,fb;
        for(auto i:remain){pairs.emplace_back(i,256+i);fa.push_back(native[0][i]);fb.push_back(native[1][i]);}
        auto combined=session.run_artifact<V<128>>(xor_program(512,pairs),a,b);session.checkpoint(combined);
        auto fc=field_xor(field,fa,fb);field.check();
        auto buckets=challenge.permutation(128);pairs.clear();fa.clear();fb.clear();std::vector<unsigned>kept;
        for(unsigned j=0;j<16;j++){unsigned ref=buckets[8*j];kept.push_back(ref);for(unsigned k=1;k<8;k++){unsigned i=buckets[8*j+k];pairs.emplace_back(i,ref);fa.push_back(fc[i]);fb.push_back(fc[ref]);}}
        auto differences=session.run_artifact<V<112>>(xor_program(128,pairs),combined);session.checkpoint(combined,differences);
        auto fd=field_xor(field,fa,fb);opened=field.checked_open(fd);
        auto diffs=session.reveal(differences,PUBLIC,combined);if(!diffs)throw std::runtime_error("bucket open");compare(opened,*diffs);
        // Only here may the candidate pairs enter the usable set.
        auto mask=select<128,16>(session,combined,kept);session.checkpoint(mask);std::vector<H>fm;for(auto i:kept)fm.push_back(fc[i]);
        // Consume all16 verified pairs once for E-bit→native-field conversion.
        V<16>::clear_t input{};for(unsigned i=0;i<16;i++)input[i]=i%3==0;
        auto x=session.input<V<16>>(ALICE,input);auto masked=session.run_artifact<V<16>>(xor_program(32,{{0,16},{1,17},{2,18},{3,19},{4,20},{5,21},{6,22},{7,23},{8,24},{9,25},{10,26},{11,27},{12,28},{13,29},{14,30},{15,31}}),x,mask);
        auto d=session.reveal(masked,PUBLIC);if(!d)throw std::runtime_error("masked conversion open");
        auto one=field.constant(1);std::vector<H>equal;
        for(unsigned i=0;i<16;i++){auto result=(*d)[i]?field.sub(one,fm[i]):fm[i];equal.push_back(field.sub(result,field.constant(i%3==0)));}
        opened=field.checked_open(equal);for(auto &value:opened)for(auto byte:value)if(byte)throw std::runtime_error("conversion equality");
        std::cout<<"bridge fixture passed verified_pairs=16 consumed=16 equality_only=16\n";
    }catch(...){std::cerr<<"bridge fixture rejected category=protocol-or-consistency\n";return 4;}
}
