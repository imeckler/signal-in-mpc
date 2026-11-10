#pragma once
// Runtime side of the offset sealed-sender agreement.
// Design: SEALED_SENDER_AGREEMENT.md (variant C). What it computes:
// TlsMpc/OffsetAgreement.lean. All arithmetic on private values is in two Lean
// field programs (TlsMpc/EdwardsAffine.lean: `prepare`, `offsetSum`); this file
// only supplies their inputs, opens the values they say must be zero, and does
// the public-point arithmetic (libsodium) and the commit-then-open exchange.
#include "x25519_fast.h"
#include <sodium.h>
namespace emp_hybrid {
struct OffsetPrograms {
    static constexpr unsigned WINDOWS=64,DIGITS=8,BITS=252,CHECKS=1+2*BITS;
    FieldProgram prepare{std::string(EMP_WORD_CIRCUIT_DIR)+"/edwards-prepare.flat",EDWARDS_PREPARE_SHA};
    FieldProgram sum{std::string(EMP_WORD_CIRCUIT_DIR)+"/edwards-offset-sum.flat",EDWARDS_OFFSET_SUM_SHA};
    OffsetPrograms(){
        if(prepare.input_count()!=2+2*BITS||prepare.output_count()!=CHECKS+2+2*WINDOWS*DIGITS||sum.input_count()!=2+3*WINDOWS||sum.output_count()!=1)throw std::runtime_error("offset agreement program shape");
    }
};
class OffsetAgreement {
    using P=OffsetPrograms;
    std::vector<H>table;   // entry 8*w + (j-1) = (j·16^w)·R for j = 1..8, as x then y
    std::vector<H>initial;std::array<uint8_t,32>initial_public{};bool ready=false;
    static void need(bool ok,const char*what){if(!ok)throw std::runtime_error(what);}
public:
    bool prepared()const{return ready;}
    // Once per conversation: each party's private scalar bits go into the `prepare` program
    // with the private recipient key; it returns the table, the shared point k0·R for
    // k0 = kA + kB, and the values that must be zero. The public point K0 = kA·B + kB·B is
    // exchanged commit-then-open so neither half depends on the other.
    void prepare(const OffsetPrograms&programs,FE&f,Challenge&channel,int party,H recipient_u){
        need(!ready&&sodium_init()>=0,"offset agreement state");
        std::array<uint8_t,32>scalar{};{emp::PRG prg;prg.random_data_unaligned(scalar.data(),32);scalar[31]&=15;}
        std::vector<uint64_t>local(P::BITS);for(unsigned i=0;i<P::BITS;i++)local[i]=(scalar[i/8]>>(i%8))&1;
        auto bits=f.input_coins(local);f.check();
        std::vector<H>inputs{recipient_u,FieldProgram::masks(f,1).at(0)};
        inputs.insert(inputs.end(),bits[0].begin(),bits[0].end());inputs.insert(inputs.end(),bits[1].begin(),bits[1].end());
        auto out=programs.prepare.evaluate_all(f,{inputs}).at(0);
        for(auto&v:f.checked_open(std::vector<H>(out.begin(),out.begin()+P::CHECKS)))for(auto byte:v)if(byte)throw std::runtime_error("offset agreement: invalid recipient key or scalar contribution");
        initial.assign(out.begin()+P::CHECKS,out.begin()+P::CHECKS+2);table.assign(out.begin()+P::CHECKS+2,out.end());
        std::array<uint8_t,32>mine{},nonce{},peer{},peer_nonce{},commit{},peer_commit{},check{};
        need(crypto_scalarmult_ed25519_base_noclamp(mine.data(),scalar.data())==0,"initial key share");sodium_memzero(scalar.data(),32);
        {emp::PRG prg;prg.random_data_unaligned(nonce.data(),32);}
        auto bind=[](int who,const std::array<uint8_t,32>&n,const std::array<uint8_t,32>&point,std::array<uint8_t,32>&out){
            std::array<uint8_t,83>frame{};const char tag[]="offset-agreement-K";std::copy_n(tag,18,frame.begin());frame[18]=uint8_t(who);std::copy_n(n.begin(),32,frame.begin()+19);std::copy_n(point.begin(),32,frame.begin()+51);
            SHA256(frame.data(),frame.size(),out.data());
        };
        bind(party,nonce,mine,commit);
        channel.transfer(commit.data(),peer_commit.data(),32);channel.transfer(nonce.data(),peer_nonce.data(),32);channel.transfer(mine.data(),peer.data(),32);
        bind(party==emp::ALICE?emp::BOB:emp::ALICE,peer_nonce,peer,check);
        need(check==peer_commit&&crypto_core_ed25519_is_valid_point(peer.data())==1,"initial key share commitment");
        const auto&a=party==emp::ALICE?mine:peer;const auto&b=party==emp::ALICE?peer:mine;
        need(crypto_core_ed25519_add(initial_public.data(),a.data(),b.data())==0&&crypto_core_ed25519_is_valid_point(initial_public.data())==1,"initial public key");
        ready=true;
    }
    // Per message, for a public offset (below 2^252) both parties agreed on: the ephemeral
    // public key u(K0 + offset·B), in the clear, and the shared agreement u(k0·R + offset·R)
    // from the `offsetSum` program on the table entries the offset's digits name.
    std::pair<std::array<uint8_t,32>,H> step(const OffsetPrograms&programs,FE&f,std::array<uint8_t,32>offset){
        need(ready,"offset agreement not prepared");offset[31]&=15;
        std::array<uint8_t,32>shift{},key{},u{};
        need(crypto_scalarmult_ed25519_base_noclamp(shift.data(),offset.data())==0&&crypto_core_ed25519_add(key.data(),initial_public.data(),shift.data())==0
            &&crypto_core_ed25519_is_valid_point(key.data())==1&&crypto_sign_ed25519_pk_to_curve25519(u.data(),key.data())==0,"ephemeral public key");
        // The public offset in signed base-16 digits -8..8; the program applies each sign.
        std::array<uint8_t,32>minus_one{};minus_one.fill(0xff);minus_one[0]=0xec;minus_one[31]=0x7f;
        std::vector<H>inputs=initial;int carry=0;
        for(unsigned w=0;w<P::WINDOWS;w++){
            int digit=int((offset[w/2]>>(4*(w%2)))&15)+carry;carry=digit>8;digit-=16*carry;
            const unsigned at=2*(P::DIGITS*w+unsigned(digit<0?-digit:digit)-1);
            if(digit){inputs.push_back(table.at(at));inputs.push_back(table.at(at+1));inputs.push_back(digit>0?f.constant(1):f.public_element(minus_one));}
            else{inputs.push_back(f.constant(0));inputs.push_back(f.constant(1));inputs.push_back(f.constant(1));}   // the neutral element
        }
        need(!carry,"offset recoding");
        return {u,programs.sum.evaluate_all(f,{inputs}).at(0).at(0)};
    }
};
}
