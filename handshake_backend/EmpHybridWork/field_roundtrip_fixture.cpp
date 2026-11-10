// Candidate RW2019/207 coin checking, ell256/B5/C2. No production API.
#include <emp-ag2pc/emp-ag2pc.h>
#include <openssl/sha.h>
#include "field_engine.h"
#include "modp_program.h"
#include "pad_program.h"
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
        std::array<uint8_t,64> local{},other{};PRG prg;prg.random_data_unaligned(local.data(),32);
        const std::string domain="EMP-native-RW-v1:p25519:ell256:B5:C2:local-A-B";
        std::array<uint8_t,32> domain_hash{};SHA256(reinterpret_cast<const uint8_t*>(domain.data()),domain.size(),domain_hash.data());std::copy_n(domain_hash.begin(),24,local.begin()+32);
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
template<size_t N>typename V<N>::clear_t fresh(){typename V<N>::clear_t out{};std::array<uint8_t,N>bytes{};PRG prg;prg.random_data_unaligned(bytes.data(),bytes.size());for(size_t i=0;i<N;i++)out[i]=bytes[i]&1;return out;}
int main(int argc,char**argv){
    if(argc!=4)return 2;
    const char*stage="setup";
    try{
        int party=std::stoi(argv[1]);unsigned port=std::stoul(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
        std::string expectedhex=argv[3];if(expectedhex.size()!=64)throw std::runtime_error("fixture expected width");std::array<uint8_t,32>expected{};
        for(unsigned i=0;i<32;i++)expected[i]=std::stoul(expectedhex.substr(i*2,2),nullptr,16);
        struct FinalCounters {~FinalCounters(){std::cout<<"EMP_EXACT_SOCKET_BYTES sent="<<NetIO::benchmark_sent.load()<<" received="<<NetIO::benchmark_received.load()<<"\n";}} counters;
        NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool pool(4);AG2PCSession session(&io,&pool,party,40);
        FE field(party-1,port+10);Challenge challenge{io,party};
        stage="inputs";auto mine=fresh<2560>();std::vector<uint64_t>local;for(auto b:mine)local.push_back(b);
        if(party==BOB&&std::getenv("EMP_TEST_BAD_NATIVE_COINS"))std::fill(local.begin(),local.end(),2);
        auto a=session.input<V<2560>>(ALICE,mine),b=session.input<V<2560>>(BOB,mine);session.checkpoint(a,b);
        auto native=field.input_coins(local);field.check();
        auto permutation=challenge.permutation(2560);std::vector<unsigned>cut(permutation.begin(),permutation.begin()+1280),remain(permutation.begin()+1280,permutation.end());
        auto acut=select<2560,1280>(session,a,cut),bcut=select<2560,1280>(session,b,cut);
        std::vector<H> fcut;for(auto i:cut)fcut.push_back(native[0][i]);for(auto i:cut)fcut.push_back(native[1][i]);
        stage="cut-native-open";auto opened=field.checked_open(fcut);stage="cut-emp-open";auto ao=session.reveal(acut,PUBLIC,a,b,bcut);auto bo=session.reveal(bcut,PUBLIC,a,b);if(!ao||!bo)throw std::runtime_error("cut open");
        std::array<bool,2560>cutbits{};std::copy(ao->begin(),ao->end(),cutbits.begin());std::copy(bo->begin(),bo->end(),cutbits.begin()+1280);stage="cut-consistency";compare(opened,cutbits);stage="combine";
        std::vector<std::pair<unsigned,unsigned>>pairs;std::vector<H>fa,fb;
        for(auto i:remain){pairs.emplace_back(i,2560+i);fa.push_back(native[0][i]);fb.push_back(native[1][i]);}
        auto combined=session.run_artifact<V<1280>>(xor_program(5120,pairs),a,b);session.checkpoint(combined);
        auto fc=field_xor(field,fa,fb);field.check();
        auto buckets=challenge.permutation(1280);pairs.clear();fa.clear();fb.clear();std::vector<unsigned>kept;
        for(unsigned j=0;j<256;j++){unsigned ref=buckets[5*j];kept.push_back(ref);for(unsigned k=1;k<5;k++){unsigned i=buckets[5*j+k];pairs.emplace_back(i,ref);fa.push_back(fc[i]);fb.push_back(fc[ref]);}}
        auto differences=session.run_artifact<V<1024>>(xor_program(1280,pairs),combined);session.checkpoint(combined,differences);
        stage="bucket";auto fd=field_xor(field,fa,fb);opened=field.checked_open(fd);auto diffs=session.reveal(differences,PUBLIC,combined);if(!diffs)throw std::runtime_error("bucket open");compare(opened,*diffs);
        kept.resize(255);auto mask=select<1280,255>(session,combined,kept);session.checkpoint(mask);std::vector<H>fm;for(auto i:kept)fm.push_back(fc[i]);
        // Consume255 checked pairs. Range must settle BEFORE native masked open.
        stage="mask-range";std::cerr<<"fixture stage=mask-range\n";auto range=emp_hybrid::pad_program(emp_hybrid::range_program(),1024);
        if(range.dummy_inputs!=2048||range.dummy_outputs!=1024)throw std::runtime_error("range padding profile");
        auto da=session.input<V<1024>>(ALICE,fresh<1024>()),db=session.input<V<1024>>(BOB,fresh<1024>());
        auto rangeout=session.run_artifact<V<1025>>(range.program,mask,da,db);session.checkpoint(mask,rangeout);
        auto accepted=select<1025,1>(session,rangeout,{0});auto valid=session.reveal(accepted,PUBLIC,mask);if(!valid||!(*valid)[0])throw std::runtime_error("mask out of range; batch burned");
        stage="field-operation";auto rfield=field.constant(0);for(int i=254;i>=0;i--)rfield=field.add(field.add(rfield,rfield),fm[i]);
        auto in=field.input_coins({party==ALICE?123u:321u});auto x=field.add(in[0][0],in[1][0]);for(unsigned i=0;i<8;i++)x=field.mul({x},{x})[0];
        auto public_c=field.checked_open({field.sub(x,rfield)}).at(0);
        std::array<uint8_t,32> peer_c{};challenge.transfer(public_c.data(),peer_c.data(),32);if(public_c!=peer_c)throw std::runtime_error("public mask frame mismatch");
        stage="canonical-conversion";std::cerr<<"fixture stage=canonical-conversion\n";auto arithmetic=emp_hybrid::pad_program(emp_hybrid::modp_program(public_c),1024);
        auto ma=session.input<V<1024>>(ALICE,fresh<1024>()),mb=session.input<V<1024>>(BOB,fresh<1024>());
        auto modular=session.run_artifact<V<1279>>(arithmetic.program,mask,ma,mb);session.checkpoint(modular);
        std::vector<unsigned>original(255);std::iota(original.begin(),original.end(),0);auto value=select<1279,255>(session,modular,original);session.checkpoint(value);
        // Independent fixture expectation is public; comparison remains inside
        // EMP. Neither unmasked native x nor recovered Boolean x opens.
        stage="equality";std::cerr<<"fixture stage=equality\n";circuit::BooleanProgram eq;eq.num_inputs=255;eq.num_wires=255;std::vector<unsigned>leaves;
        for(unsigned i=0;i<255;i++){unsigned wire=i;if(!((expected[i/8]>>(i%8))&1)){wire=eq.num_wires++;eq.gates.push_back({i,0,wire,circuit::Op::Not});}leaves.push_back(wire);}
        while(leaves.size()>1){std::vector<unsigned>next;for(size_t i=0;i<leaves.size();i+=2){if(i+1==leaves.size())next.push_back(leaves[i]);else{unsigned wire=eq.num_wires++;eq.gates.push_back({leaves[i],leaves[i+1],wire,circuit::Op::And});next.push_back(wire);}}leaves=next;}
        eq.outputs=leaves;auto padded=emp_hybrid::pad_program(eq,1024);if(padded.dummy_outputs!=1024)throw std::runtime_error("equality padding profile");
        auto ea=session.input<V<1024>>(ALICE,fresh<1024>()),eb=session.input<V<1024>>(BOB,fresh<1024>());
        auto all=session.run_artifact<V<1025>>(padded.program,value,ea,eb);session.checkpoint(all);auto equality=select<1025,1>(session,all,{0});auto result=session.reveal(equality,PUBLIC);
        if(!result||!(*result)[0])throw std::runtime_error("field conversion mismatch");
        std::cout<<"field conversion fixture passed pairs_consumed=255 private_result_equality=1\n";
    }catch(...){std::cerr<<"field conversion fixture rejected category=protocol-or-consistency stage="<<stage<<"\n";return 4;}
}
