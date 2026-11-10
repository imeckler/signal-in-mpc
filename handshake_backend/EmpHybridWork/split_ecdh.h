#pragma once
// X25519 key agreement with an additively shared scalar and a PUBLIC peer point.
//
// The ephemeral scalar is k = kA + kB, each summand a multiple of 8 known to
// one party only. Because the base point and the server's key share are both
// public, each party does its own scalar multiplication locally and in the
// clear on its own summand:
//
//   key generation:  P_A = kA·B, P_B = kB·B are exchanged (commit, then open, so
//                    neither share can depend on the other); the client's key
//                    share is u(P_A + P_B), computed in the clear.
//   agreement:       T_A = kA·S, T_B = kB·S stay private. Their coordinates are
//                    private inputs to the field engine, which checks each lies
//                    on the curve and computes u(T_A + T_B) with three products
//                    and one masked inversion (TlsMpc/EdwardsShare.lean).
//
// Compared with the shared-scalar Montgomery ladder (x25519_fast.h, about 2,800
// field products per agreement plus bit conversion of the scalar) this is about
// 11 products. It applies only when the peer point is public, which is the TLS
// case; Signal's DH ratchet on private points keeps the ladder.
//
// Rejected publicly before any private work: a peer share that is off the
// curve (a twist point), non-canonical after reduction, of small order or
// outside the prime-order subgroup. RFC 7748 would compute on such inputs; an
// honest TLS server never sends them, and rejecting them removes the all-zero
// and small-subgroup cases.
//
// What a deviating party can do: publish a share P_A that does not match the
// summand it uses later, or input a curve point other than kA·S. Either makes
// the two sides of the handshake derive different secrets, so the server's
// flight fails to authenticate and the session aborts; the deviating party
// learns nothing because the other summand's multiple of S never leaves the
// engines. Local arithmetic uses libsodium and OpenSSL bignums on public
// values and on the party's own summand only.
//
// Assumptions not mechanised in Lean: the Edwards addition law and its
// completeness on this curve, and the birational map to the Montgomery form.
// The exported programs are checked against an independent ladder
// (lower_word_circuits.py), and a wrong result cannot complete a handshake.
#include "x25519_fast.h"
#include <openssl/bn.h>
#include <sodium.h>
namespace emp_hybrid {
using Bytes32=std::array<uint8_t,32>;
// Arithmetic on public values and on one party's own secret summand.
class LocalCurve {
    BN_CTX*ctx=BN_CTX_new();BIGNUM*p=BN_new(),*d=BN_new();
    struct Number {BIGNUM*v=BN_new();~Number(){BN_clear_free(v);}Number()=default;Number(const Number&)=delete;};
    static void need(bool ok){if(!ok)throw std::runtime_error("local curve arithmetic");}
    void load(Number&n,const Bytes32&bytes)const{need(BN_lebin2bn(bytes.data(),32,n.v)&&BN_cmp(n.v,p)<0);}
    Bytes32 store(const Number&n)const{Bytes32 out{};need(BN_bn2lebinpad(n.v,out.data(),32)==32);return out;}
public:
    LocalCurve(){
        need(ctx&&p&&d&&sodium_init()>=0&&BN_one(p)&&BN_lshift(p,p,255)&&BN_sub_word(p,19));
        Number a,b;need(BN_set_word(a.v,121665)&&BN_set_word(b.v,121666)&&BN_mod_inverse(b.v,b.v,p,ctx)&&BN_mod_mul(d,a.v,b.v,p,ctx)&&BN_sub(d,p,d));   // d = -121665/121666
    }
    ~LocalCurve(){BN_free(d);BN_free(p);BN_CTX_free(ctx);}
    LocalCurve(const LocalCurve&)=delete;
    // Canonical Montgomery u -> compressed Edwards point with even x: y = (u-1)/(u+1).
    Bytes32 lift(const Bytes32&u)const{
        Number x,top,bottom;load(x,u);
        need(BN_copy(top.v,x.v)&&BN_copy(bottom.v,x.v)&&BN_mod_sub(top.v,top.v,BN_value_one(),p,ctx)&&BN_mod_add(bottom.v,bottom.v,BN_value_one(),p,ctx));
        if(BN_is_zero(bottom.v))throw std::runtime_error("peer key share rejected");
        need(BN_mod_inverse(bottom.v,bottom.v,p,ctx)&&BN_mod_mul(top.v,top.v,bottom.v,p,ctx));return store(top);
    }
    // Compressed Edwards point -> canonical affine (x, y).
    std::pair<Bytes32,Bytes32> coordinates(Bytes32 point)const{
        const bool odd=point[31]>>7;point[31]&=127;Number y,yy,top,bottom,x;load(y,point);
        need(BN_mod_sqr(yy.v,y.v,p,ctx)&&BN_mod_sub(top.v,yy.v,BN_value_one(),p,ctx)&&BN_mod_mul(bottom.v,d,yy.v,p,ctx)&&BN_mod_add(bottom.v,bottom.v,BN_value_one(),p,ctx)
            &&BN_mod_inverse(bottom.v,bottom.v,p,ctx)&&BN_mod_mul(top.v,top.v,bottom.v,p,ctx)&&BN_mod_sqrt(x.v,top.v,p,ctx));
        if(bool(BN_is_odd(x.v))!=odd)need(BN_sub(x.v,p,x.v));
        return {store(x),store(y)};
    }
};
struct SplitEcdh {
    FieldProgram on_curve{std::string(EMP_WORD_CIRCUIT_DIR)+"/edwards-on-curve.flat",EDWARDS_ON_CURVE_SHA};
    FieldProgram add_u{std::string(EMP_WORD_CIRCUIT_DIR)+"/edwards-add-u.flat",EDWARDS_ADD_U_SHA};
    LocalCurve curve;Bytes32 scalar{};bool ready=false;
    SplitEcdh(){if(on_curve.input_count()!=2||add_u.input_count()!=4||add_u.output_count()!=2)throw std::runtime_error("edwards program shape");}
    ~SplitEcdh(){sodium_memzero(scalar.data(),32);}
    // Returns the client's public key share u(P_A + P_B).
    Bytes32 begin(Challenge&channel,int party){
        {emp::PRG prg;do{prg.random_data_unaligned(scalar.data(),32);scalar[0]&=248;scalar[31]&=31;}while(sodium_is_zero(scalar.data(),32));}
        Bytes32 mine{},nonce{},peer{},peer_nonce{},commit{},peer_commit{},check{};
        if(crypto_scalarmult_ed25519_base_noclamp(mine.data(),scalar.data())!=0)throw std::runtime_error("key share");
        {emp::PRG prg;prg.random_data_unaligned(nonce.data(),32);}
        auto bind=[](int who,const Bytes32&n,const Bytes32&point,Bytes32&out){
            std::array<uint8_t,81>frame{};const char tag[]="split-ecdh-share";std::copy_n(tag,16,frame.begin());frame[16]=uint8_t(who);std::copy_n(n.begin(),32,frame.begin()+17);std::copy_n(point.begin(),32,frame.begin()+49);
            SHA256(frame.data(),frame.size(),out.data());
        };
        bind(party,nonce,mine,commit);
        channel.transfer(commit.data(),peer_commit.data(),32);channel.transfer(nonce.data(),peer_nonce.data(),32);channel.transfer(mine.data(),peer.data(),32);
        bind(party==emp::ALICE?emp::BOB:emp::ALICE,peer_nonce,peer,check);
        if(check!=peer_commit||crypto_core_ed25519_is_valid_point(peer.data())!=1)throw std::runtime_error("peer key share commitment");
        const Bytes32&a=party==emp::ALICE?mine:peer;const Bytes32&b=party==emp::ALICE?peer:mine;Bytes32 sum{},u{};
        if(crypto_core_ed25519_add(sum.data(),a.data(),b.data())!=0||crypto_core_ed25519_is_valid_point(sum.data())!=1||crypto_sign_ed25519_pk_to_curve25519(u.data(),sum.data())!=0)throw std::runtime_error("joint key share");
        ready=true;return u;
    }
    // The shared secret u((kA+kB)·S) as a private field element. `peer_u` is canonical.
    H agree(FE&f,Challenge&channel,const X25519Fast&inverter,const Bytes32&peer_u,bool&zero){
        if(!ready)throw std::runtime_error("agreement state");
        auto point=curve.lift(peer_u);
        if(crypto_core_ed25519_is_valid_point(point.data())!=1)throw std::runtime_error("peer key share rejected");
        Bytes32 multiple{};
        if(crypto_scalarmult_ed25519_noclamp(multiple.data(),scalar.data(),point.data())!=0)throw std::runtime_error("local agreement");
        sodium_memzero(scalar.data(),32);ready=false;
        auto xy=curve.coordinates(multiple);sodium_memzero(multiple.data(),32);
        auto in=f.input_elements({xy.first,xy.second});f.check();
        sodium_memzero(xy.first.data(),32);sodium_memzero(xy.second.data(),32);
        for(auto&v:f.checked_open(on_curve.evaluate(f,{{in[0][0],in[0][1]},{in[1][0],in[1][1]}})))for(auto byte:v)if(byte)throw std::runtime_error("agreement share is not a curve point");
        auto xz=add_u.evaluate_all(f,{{in[0][0],in[0][1],in[1][0],in[1][1]}}).at(0);
        return inverter.quotient(f,channel,xz[0],xz[1],zero);
    }
};
}
