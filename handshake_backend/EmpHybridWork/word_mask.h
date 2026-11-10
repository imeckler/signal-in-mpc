#pragma once
// Full-width conversion masks: a uniform r in F_p held as ONE native field share
// and as 255 authenticated Boolean bits. Candidate construction for review
// (CONVERSION_COST_LEVERS.md, lever 3b/3c). All nonlinear checking is Boolean; the
// field side uses only inputs, additions, MAC-checked openings and, for bit
// blocks, one bitness product and one XOR product per bit.
//
// Every Boolean gate here comes from a circuit defined and proved in Lean
// (TlsMpc/WordMask.lean), exported and pinned by lower_word_circuits.py. This
// file only routes wires, draws coins and compares openings.
//
// Bit order is NUMERIC: bit i of a word is 2^i.
#include "dabit_generator.h"
#include "lean_circuit.h"
#include "field_program.h"
#include "word_circuit_pins.h"
#ifndef EMP_WORD_CIRCUIT_DIR
#error "EMP_WORD_CIRCUIT_DIR must name the directory of pinned Lean circuit exports"
#endif
namespace emp_hybrid {
struct WordCircuits {
    LeanCircuit modadd{std::string(EMP_WORD_CIRCUIT_DIR)+"/modadd.flat",WORD_MODADD_SHA};
    LeanCircuit finalize_mask{std::string(EMP_WORD_CIRCUIT_DIR)+"/finalize-mask.flat",WORD_FINALIZE_MASK_SHA};
    LeanCircuit finalize_bits{std::string(EMP_WORD_CIRCUIT_DIR)+"/finalize-bits.flat",WORD_FINALIZE_BITS_SHA};
    LeanCircuit into_field{std::string(EMP_WORD_CIRCUIT_DIR)+"/into-field.flat",WORD_INTO_FIELD_SHA};
    LeanCircuit status{std::string(EMP_WORD_CIRCUIT_DIR)+"/status.flat",WORD_STATUS_SHA};
    LeanCircuit xor_bit{std::string(EMP_WORD_CIRCUIT_DIR)+"/xor-bit.flat",WORD_XOR_BIT_SHA};
    // Field-side programs (TlsMpc/FieldBits.lean).
    FieldProgram bit_check{std::string(EMP_WORD_CIRCUIT_DIR)+"/field-bit-check.flat",FIELD_BIT_CHECK_SHA};
    FieldProgram bit_xor{std::string(EMP_WORD_CIRCUIT_DIR)+"/field-bit-xor.flat",FIELD_BIT_XOR_SHA};
    FieldProgram recompose{std::string(EMP_WORD_CIRCUIT_DIR)+"/field-recompose.flat",FIELD_RECOMPOSE_SHA};
    WordCircuits(){
        if(modadd.input_bits()!=510||modadd.output_bits()!=255||finalize_mask.output_bits()!=256||finalize_bits.output_bits()!=256||into_field.output_bits()!=255||status.output_bits()!=2||xor_bit.input_bits()!=2||xor_bit.output_bits()!=1
            ||bit_check.input_count()!=1||bit_xor.input_count()!=2||recompose.input_count()!=256)throw std::runtime_error("lean circuit shape");
    }
    // Field XOR of two vectors of bit shares, one Lean program instance per bit.
    std::vector<H> field_bit_xor(FE&f,const std::vector<H>&a,const std::vector<H>&b)const{
        if(a.size()!=b.size())throw std::runtime_error("bit xor shape");
        std::vector<std::vector<H>>instances;for(size_t i=0;i<a.size();i++)instances.push_back({a[i],b[i]});return bit_xor.evaluate(f,instances);
    }
    // Bitness check values b*(b-1), one per share; all must open to zero.
    std::vector<H> field_bit_checks(FE&f,const std::vector<H>&bits)const{
        std::vector<std::vector<H>>instances;for(auto h:bits)instances.push_back({h});return bit_check.evaluate(f,instances);
    }
    // Boolean XOR of two n-bit values through n copies of the Lean XOR circuit.
    template<class A,class B>auto xor_values(AG2PCSession&s,const A&first,const B&second)const{
        constexpr unsigned n=A::width();static_assert(unsigned(B::width())==n);
        std::array<uint32_t,n>x{},y{};first.pack_wires(x.data());second.pack_wires(y.data());
        auto ids=std::make_unique<std::array<uint32_t,2*n>>();for(unsigned i=0;i<n;i++){(*ids)[2*i]=x[i];(*ids)[2*i+1]=y[i];}
        return s.template run_artifact<V<n>>(xor_bit.parallel(n),V<2*n>::from_wires(s.ctx(),ids->data()));
    }
};
struct WordMask {std::array<uint32_t,255> wires;H field;bool used=false;};
inline std::array<uint8_t,32> bits_to_bytes(const bool*bits){std::array<uint8_t,32>out{};for(unsigned i=0;i<255;i++)if(bits[i])out[i/8]|=uint8_t(1u<<(i%8));return out;}
inline bool canonical(const std::array<uint8_t,32>&c){
    static const std::array<uint8_t,32> prime=[](){std::array<uint8_t,32>p{};p.fill(255);p[0]=237;p[31]=127;return p;}();
    for(int i=31;i>=0;i--)if(c[i]!=prime[i])return c[i]<prime[i];return false;
}
// Bucket sizes: parameters.choose(N,128) for the cut/bucket counting bound.
template<unsigned N>constexpr unsigned word_bucket(){return N==16?22:N==64?17:N==256?14:12;}
template<unsigned N>struct WordMaskBatch {
    std::vector<WordMask> masks;      // full-width masks (N minus the bit blocks)
    std::vector<MaskPair> bit_pairs;  // single-bit pairs, 255 per bit block
    size_t bit_cursor=0;
    V<N*255> held;   // keeps the Boolean wires alive across checkpoints
};
class WordMaskGeneratorV1 {
public:
    // N kept references per party. The first `bit_blocks` are turned into 255
    // single-bit pairs each (lever 3c); the rest become full-width masks.
    template<unsigned N>static WordMaskBatch<N> generate(AG2PCSession&session,FE&field,Challenge&challenge,int party,const WordCircuits&circuits,unsigned bit_blocks=0){
        static_assert(N==16||N==64||N==256||N==1024);
#if EMP_HYBRID_STATISTICAL!=128
#error "word masks are defined for the statistical-128 profile only"
#endif
        if(bit_blocks>N)throw std::runtime_error("bit block count");
        if(session.protocol().party!=party||field.party_id()!=unsigned(party-1))throw std::runtime_error("engine party mapping");
        constexpr unsigned B=word_bucket<N>(),K=B*N,M=2*K,W=255;
        if(challenge.phase!=0)throw std::runtime_error("generator challenge reuse");
        challenge.domain="WORDMASK-v2:p25519:n"+std::to_string(N)+":bits"+std::to_string(bit_blocks)+":B"+std::to_string(B)+":C2:S128:local-AB:"+challenge.domain;
        // 1. Each party fixes M uniform candidates in BOTH engines before any challenge.
        auto mine=std::make_unique<typename V<M*W>::clear_t>();std::vector<std::array<uint8_t,32>>local(M);
        {PRG prg;for(unsigned j=0;j<M;j++){std::array<uint8_t,32>c{};do{prg.random_data_unaligned(c.data(),32);c[31]&=127;}while(!canonical(c));local[j]=c;for(unsigned i=0;i<W;i++)(*mine)[j*W+i]=(c[i/8]>>(i%8))&1;}}
        if(party==BOB&&std::getenv("EMP_TEST_WORD_INCONSISTENT"))for(unsigned j=0;j<M;j++)(*mine)[j*W]=!(*mine)[j*W];
        if(party==BOB&&std::getenv("EMP_TEST_WORD_ONE_BAD"))(*mine)[0]=!(*mine)[0];
        auto a=session.input<V<M*W>>(ALICE,*mine),b=session.input<V<M*W>>(BOB,*mine);session.checkpoint(a,b);
        auto native=field.input_elements(local);field.check();
        auto ida=std::make_unique<std::array<uint32_t,M*W>>(),idb=std::make_unique<std::array<uint32_t,M*W>>();
        a.pack_wires(ida->data());b.pack_wires(idb->data());
        auto wire=[&](unsigned owner,unsigned cand,unsigned bit){return (owner?*idb:*ida)[cand*W+bit];};
        // 2. Cut: open half of the candidates in both engines and compare.
        auto permutation=challenge.permutation(M);std::vector<unsigned>cut(permutation.begin(),permutation.begin()+K),remain(permutation.begin()+K,permutation.end());
        {
            auto ids=std::make_unique<std::array<uint32_t,2*K*W>>();std::vector<H>fcut;
            for(unsigned q=0;q<K;q++)for(unsigned i=0;i<W;i++){(*ids)[q*W+i]=wire(0,cut[q],i);(*ids)[(K+q)*W+i]=wire(1,cut[q],i);}
            for(auto j:cut)fcut.push_back(native[0][j]);for(auto j:cut)fcut.push_back(native[1][j]);
            auto opened=field.checked_open(fcut);auto bits=session.reveal(V<2*K*W>::from_wires(session.ctx(),ids->data()),PUBLIC,a,b);
            if(!bits)throw std::runtime_error("cut open");
            for(unsigned q=0;q<2*K;q++){auto v=bits_to_bytes(bits->data()+q*W);if(!canonical(v)||v!=opened[q])throw std::runtime_error("cross-domain candidate mismatch");}
        }
        // 3. Buckets: reference + (B-1) one-use partners per party. Open ref+s in
        // both engines; the Boolean side is D copies of the Lean modadd circuit.
        auto buckets=challenge.permutation(K);
        auto candidate=[&](unsigned bucket,unsigned k){return remain[buckets[B*bucket+k]];};
        {
            constexpr unsigned D=2*N*(B-1);auto ids=std::make_unique<std::array<uint32_t,D*2*W>>();std::vector<H>sums;unsigned q=0;
            for(unsigned owner=0;owner<2;owner++)for(unsigned j=0;j<N;j++)for(unsigned k=1;k<B;k++,q++){
                for(unsigned i=0;i<W;i++){(*ids)[q*2*W+i]=wire(owner,candidate(j,0),i);(*ids)[q*2*W+W+i]=wire(owner,candidate(j,k),i);}
                sums.push_back(field.add(native[owner][candidate(j,0)],native[owner][candidate(j,k)]));
            }
            auto out=session.run_artifact<V<D*W>>(circuits.modadd.parallel(D),V<D*2*W>::from_wires(session.ctx(),ids->data()));session.checkpoint(a,b,out);
            auto opened=field.checked_open(sums);auto bits=session.reveal(out,PUBLIC,a,b);if(!bits)throw std::runtime_error("bucket open");
            for(unsigned z=0;z<D;z++)if(bits_to_bytes(bits->data()+z*W)!=opened[z])throw std::runtime_error("cross-domain bucket mismatch");
        }
        // 4. Kept references, as N copies of a Lean finalize circuit on (rA,rB):
        //   mask: (rA+rB) mod p, flag = both canonical;
        //   bits: rA xor rB,     flag = both canonical and both >= 32.
        constexpr unsigned X=256;auto pair_ids=std::make_unique<std::array<uint32_t,N*2*W>>();
        for(unsigned j=0;j<N;j++)for(unsigned i=0;i<W;i++){(*pair_ids)[j*2*W+i]=wire(0,candidate(j,0),i);(*pair_ids)[j*2*W+W+i]=wire(1,candidate(j,0),i);}
        // One program: bit-block copies first, then mask copies.
        emp::circuit::BooleanProgram final_program;
        {
            auto bits=circuits.finalize_bits.parallel(bit_blocks),masks=circuits.finalize_mask.parallel(N-bit_blocks);
            final_program.num_inputs=N*2*W;final_program.num_wires=final_program.num_inputs;
            auto place=[&](const emp::circuit::BooleanProgram&part,uint32_t input_offset){
                const uint32_t base=final_program.num_wires;auto map=[&](uint32_t w){return w<part.num_inputs?input_offset+w:base+(w-part.num_inputs);};
                for(auto&g:part.gates)final_program.gates.push_back({map(g.in0),g.op==emp::circuit::Op::Not?0u:map(g.in1),final_program.num_wires++,g.op});
                for(auto w:part.outputs)final_program.outputs.push_back(map(w));
            };
            place(bits,0);place(masks,bit_blocks*2*W);
        }
        auto all=session.run_artifact<V<N*X>>(final_program,V<N*2*W>::from_wires(session.ctx(),pair_ids->data()));session.checkpoint(all);
        auto ids=std::make_unique<std::array<uint32_t,N*X>>();all.pack_wires(ids->data());
        auto kept=std::make_unique<std::array<uint32_t,N*W>>();std::array<uint32_t,N>flags{};
        for(unsigned j=0;j<N;j++){for(unsigned i=0;i<W;i++)(*kept)[j*W+i]=(*ids)[j*X+i];flags[j]=(*ids)[j*X+W];}
        auto held=V<N*W>::from_wires(session.ctx(),kept->data());
        auto valid=session.reveal(V<N>::from_wires(session.ctx(),flags.data()),PUBLIC,held);
        if(!valid)throw std::runtime_error("missing reference flags");
        for(auto bit:*valid)if(!bit)throw std::runtime_error("kept reference out of range");
        session.checkpoint(held);field.check();
        WordMaskBatch<N> batch{{},{},0,held};
        for(unsigned j=bit_blocks;j<N;j++){WordMask m;for(unsigned i=0;i<W;i++)m.wires[i]=(*kept)[j*W+i];m.field=field.add(native[0][candidate(j,0)],native[1][candidate(j,0)]);batch.masks.push_back(m);}
        if(bit_blocks){
            // 5. Bit blocks: each party inputs the 255 bits of its own kept
            // reference as field elements. Checked: every input is a bit, and the
            // bits recompose to the already-verified reference. With the
            // reference canonical and >= 32, that forces each field bit to equal
            // the corresponding Boolean bit. Then one field XOR per bit.
            std::vector<uint64_t>bits(bit_blocks*W);
            for(unsigned j=0;j<bit_blocks;j++)for(unsigned i=0;i<W;i++)bits[j*W+i]=(local[candidate(j,0)][i/8]>>(i%8))&1;
            if(party==BOB&&std::getenv("EMP_TEST_BITBLOCK_WRONG"))bits[0]^=1;
            if(party==BOB&&std::getenv("EMP_TEST_BITBLOCK_NONBIT"))for(unsigned i=0;i+1<W;i++)if(bits[i]==0&&bits[i+1]==1){bits[i]=2;bits[i+1]=0;break;}
            auto shares=field.input_coins(bits);field.check();
            // All three steps are Lean field programs (TlsMpc/FieldBits.lean).
            std::vector<H>all_bits;std::vector<std::vector<H>>blocks;
            for(unsigned owner=0;owner<2;owner++){
                for(auto h:shares[owner])all_bits.push_back(h);
                for(unsigned j=0;j<bit_blocks;j++){
                    std::vector<H>instance(shares[owner].begin()+j*W,shares[owner].begin()+(j+1)*W);instance.push_back(native[owner][candidate(j,0)]);blocks.push_back(instance);
                }
            }
            auto zero=circuits.recompose.evaluate(field,blocks);
            for(auto h:circuits.field_bit_checks(field,all_bits))zero.push_back(h);
            for(auto&v:field.checked_open(zero))for(auto byte:v)if(byte)throw std::runtime_error("bit block inconsistent with verified reference");
            auto combined=circuits.field_bit_xor(field,shares[0],shares[1]);field.check();
            for(unsigned q=0;q<bit_blocks*W;q++)batch.bit_pairs.push_back({(*kept)[q],combined[q]});
        }
        return batch;
    }
};
// One-use conversions over a verified batch. Each mask is consumed exactly once.
template<unsigned N>class WordConverter {
    AG2PCSession&s;FE&f;Challenge&channel;WordMaskBatch<N>&batch;const WordCircuits&circuits;unsigned cursor=0;
    WordMask&take(){if(cursor>=batch.masks.size()||batch.masks[cursor].used)throw std::runtime_error("word mask exhausted");auto&m=batch.masks[cursor++];m.used=true;return m;}
    void agree(const std::array<uint8_t,32>&c){std::array<uint8_t,32>peer{};channel.transfer(c.data(),peer.data(),32);if(c!=peer)throw std::runtime_error("public masked value disagreement");}
    template<class A,class B>V<510> pair(const A&first,const B&second){
        std::array<uint32_t,510>ids{};first.pack_wires(ids.data());second.pack_wires(ids.data()+255);return V<510>::from_wires(s.ctx(),ids.data());
    }
public:
    WordConverter(AG2PCSession&session,FE&field,Challenge&challenge,WordMaskBatch<N>&b,const WordCircuits&c):s(session),f(field),channel(challenge),batch(b),circuits(c){}
    unsigned consumed()const{return cursor;}
    size_t bits_consumed()const{return batch.bit_cursor;}
    // n private Boolean bits -> n field shares holding the same bits, each
    // through one single-bit pair: open bit xor rho, then select rho or 1-rho.
    template<emp::WireValue Bits,class...Keep>std::vector<H> bits_to_field(const Bits&bits,const Keep&...keep){
        static_assert(std::same_as<typename Bits::context_type,C>);constexpr unsigned n=Bits::width();
        if(n>batch.bit_pairs.size()-batch.bit_cursor)throw std::runtime_error("bit pairs exhausted");
        std::array<uint32_t,n>ids{};std::vector<H>rho;
        for(unsigned i=0;i<n;i++){auto&p=batch.bit_pairs[batch.bit_cursor++];ids[i]=p.wire;rho.push_back(p.field);}
        auto mask=V<n>::from_wires(s.ctx(),ids.data());
        auto masked=circuits.xor_values(s,bits,mask);
        auto d=s.reveal(masked,PUBLIC,batch.held,bits,keep...);if(!d)throw std::runtime_error("missing masked bits");
        auto one=f.constant(1);std::vector<H>out;for(unsigned i=0;i<n;i++)out.push_back((*d)[i]?f.sub(one,rho[i]):rho[i]);
        return out;
    }
    // 255 private numeric bits (any value < 2^255, reduced mod p as RFC 7748 does) -> one field share.
    template<class...Keep>H boolean_to_field(const V<255>&value,const Keep&...keep){
        auto&m=take();auto mask=V<255>::from_wires(s.ctx(),m.wires.data());
        auto masked=s.template run_artifact<V<255>>(circuits.into_field.parallel(1),pair(value,mask));   // ((u mod p)+r) mod p
        auto t=s.reveal(masked,PUBLIC,batch.held,value,keep...);if(!t)throw std::runtime_error("missing masked word");
        auto c=bits_to_bytes(t->data());if(!canonical(c))throw std::runtime_error("noncanonical masked word");agree(c);
        return f.sub(f.public_element(c),m.field);
    }
    // One field share -> 255 private numeric bits of its canonical representative.
    template<class...Keep>V<255> field_to_boolean(H value,const Keep&...keep){
        auto&m=take();auto mask=V<255>::from_wires(s.ctx(),m.wires.data());
        auto c=f.checked_open({f.sub(value,m.field)}).at(0);if(!canonical(c))throw std::runtime_error("noncanonical public field mask");agree(c);
        typename V<255>::clear_t bits{};for(unsigned i=0;i<255;i++)bits[i]=(c[i/8]>>(i%8))&1;
        auto constant=s.template input<V<255>>(PUBLIC,bits);
        auto out=s.template run_artifact<V<255>>(circuits.modadd.parallel(1),pair(mask,constant));s.checkpoint(out,batch.held,keep...);return out;   // (r+c) mod p
    }
    // [equal to the public expectation, nonzero] for a private 255-bit value.
    template<class...Keep>V<2> status(const V<255>&value,const std::array<uint8_t,32>&expected,const Keep&...keep){
        if(!canonical(expected))throw std::runtime_error("expectation range");
        typename V<255>::clear_t bits{};for(unsigned i=0;i<255;i++)bits[i]=(expected[i/8]>>(i%8))&1;
        auto constant=s.template input<V<255>>(PUBLIC,bits);
        return s.template run_artifact<V<2>>(circuits.status.parallel(1),pair(value,constant));
    }
};
}
