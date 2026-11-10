#pragma once
#include "dabit_generator.h"
#include "modp_program.h"
#include "pad_program.h"
#include <optional>
namespace emp_hybrid {
// One serialized converter over the SAME two engine owners as the generator.
// It exposes no unmasked opening and burns a frame before using any mask.
template<unsigned Ell>class CheckedConverter {
    AG2PCSession&s;FE&f;Challenge&channel;Generation<Ell>&generation;uint64_t operation=0;
    std::vector<MaskPair> take(Direction direction,size_t count){
        EngineOwners owners{&s,&f};auto binding=generation.pool.binding();
        std::optional<CheckedMaskPool::Lease>lease;std::vector<uint8_t>frame;uint8_t ready=1,peer_ready=1;
        try{lease.emplace(generation.pool.reserve(binding,owners,operation,direction,count));frame=lease->frame();}catch(...){ready=0;}
        channel.transfer(&ready,&peer_ready,1);
        if(!ready||!peer_ready){generation.pool.poison();throw std::runtime_error("converter collective reserve");}
        auto peer=frame;channel.transfer(frame.data(),peer.data(),frame.size());
        if(frame!=peer){generation.pool.poison();throw std::runtime_error("converter peer frame");}
        std::vector<MaskPair>pairs;ready=peer_ready=1;
        try{pairs=lease->consume(binding,owners,operation,direction);}catch(...){ready=0;}
        channel.transfer(&ready,&peer_ready,1);
        if(!ready||!peer_ready){generation.pool.poison();throw std::runtime_error("converter collective consume");}
        operation++;return pairs;
    }
public:
    CheckedConverter(AG2PCSession&session,FE&field,Challenge&challenge,Generation<Ell>&g):s(session),f(field),channel(challenge),generation(g){}
    template<emp::WireValue Bits,class...Keep>std::vector<H> boolean_to_field(const Bits&bits,const Keep&...keep){
        static_assert(std::same_as<typename Bits::context_type,C>);constexpr unsigned N=Bits::width();
        auto pairs=take(Direction::BooleanToField,N);std::array<uint32_t,N>ids{};for(size_t i=0;i<N;i++)ids[i]=pairs[i].wire;
        auto mask=V<N>::from_wires(s.ctx(),ids.data());std::vector<std::pair<unsigned,unsigned>>edges;for(unsigned i=0;i<N;i++)edges.emplace_back(i,N+i);
        auto masked=s.template run_artifact<V<N>>(xor_program(2*N,edges),bits,mask);
        auto d=s.reveal(masked,PUBLIC,generation.held,bits,keep...);if(!d){generation.pool.poison();throw std::runtime_error("missing Boolean mask");}
        auto one=f.constant(1);std::vector<H>out;for(size_t i=0;i<N;i++)out.push_back((*d)[i]?f.sub(one,pairs[i].field):pairs[i].field);
        return out;
    }
    template<class...Keep>V<255> field_to_boolean(H value,const Keep&...keep){
        auto pairs=take(Direction::FieldToBoolean,255);std::array<uint32_t,255>ids{};for(unsigned i=0;i<255;i++)ids[i]=pairs[i].wire;
        auto mask=V<255>::from_wires(s.ctx(),ids.data());s.checkpoint(mask,generation.held,keep...);
        auto range=pad_program(range_program(),1024);auto da=s.input<V<1024>>(ALICE,fresh<1024>()),db=s.input<V<1024>>(BOB,fresh<1024>());
        auto all=s.template run_artifact<V<1025>>(range.program,mask,da,db);s.checkpoint(mask,all,generation.held,keep...);
        auto accepted=select<1025,1>(s,all,{0});auto valid=s.reveal(accepted,PUBLIC,mask,generation.held,keep...);
        if(!valid||!(*valid)[0]){generation.pool.poison();throw std::runtime_error("noncanonical private mask; burned");}
        auto r=f.constant(0);for(int i=254;i>=0;i--)r=f.add(f.add(r,r),pairs[i].field);
        auto c=f.checked_open({f.sub(value,r)}).at(0);std::array<uint8_t,32>peer{};channel.transfer(c.data(),peer.data(),32);
        if(c!=peer){generation.pool.poison();throw std::runtime_error("public field mask disagreement");}
        auto p=pad_program(modp_program(c),1024);auto ma=s.input<V<1024>>(ALICE,fresh<1024>()),mb=s.input<V<1024>>(BOB,fresh<1024>());
        auto modular=s.template run_artifact<V<1279>>(p.program,mask,ma,mb);s.checkpoint(modular,generation.held,keep...);
        std::vector<unsigned>indices(255);std::iota(indices.begin(),indices.end(),0);auto out=select<1279,255>(s,modular,indices);s.checkpoint(out,generation.held,keep...);return out;
    }
    // Exact existing application encoding:32 little-endian bytes; within each
    // byte wires run MSB-first. Numeric bit255 is the public canonical zero.
    template<class...Keep>V<256> field_to_bytes(H value,const Keep&...keep){
        auto numeric=field_to_boolean(value,keep...);auto zero=s.input<V<1>>(PUBLIC,{false});
        s.checkpoint(numeric,zero,generation.held,keep...);
        std::array<uint32_t,255>n{};std::array<uint32_t,1>z{};std::array<uint32_t,256>wire{};numeric.pack_wires(n.data());zero.pack_wires(z.data());
        for(unsigned i=0;i<256;i++){unsigned bit=8*(i/8)+7-i%8;wire[i]=bit==255?z[0]:n[bit];}
        auto out=V<256>::from_wires(s.ctx(),wire.data());s.checkpoint(out,generation.held,keep...);return out;
    }
};
}
