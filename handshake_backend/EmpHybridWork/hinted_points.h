#pragma once
// Runtime side of TlsMpc/EdwardsHinted.lean: the constant-depth curve programs (design and
// what is proved: that file's header; what is opened: NEEDS_REVIEW.md, "Constant-depth curve
// programs"). All arithmetic on private values is in the Lean field programs. This file
//   - supplies their inputs: uniform masks, each party's private random bits and mask points,
//     and each party's HINTS (multiples of points it knows, computed locally with libsodium);
//   - opens exactly what the programs mark: check values that must be zero, the masked value
//     `w` of a lift, the masked point `Z` of a lift, masked denominators;
//   - converts PUBLIC or LOCAL values between libsodium's point encoding and the affine
//     coordinates the programs take, and takes the public square root of an opened `w`.
// A hint is never trusted: the programs check every hinted multiple against the one before it
// (EdwardsHinted.entries_sound), and a failed check is a failed opening (the session stops).
#include "edwards_points.h"
#include <openssl/bn.h>
namespace emp_hybrid {
using Bytes32=std::array<uint8_t,32>;
// ---- Public and local values only.
class LocalField {
    BN_CTX*ctx=BN_CTX_new();BIGNUM*p=BN_new(),*d=BN_new(),*c=nullptr,*half=BN_new();
    static void need(bool ok){if(!ok)throw std::runtime_error("local field arithmetic");}
    BIGNUM*load(const Bytes32&v)const{BIGNUM*n=BN_lebin2bn(v.data(),32,nullptr);need(n&&BN_cmp(n,p)<0);return n;}
    Bytes32 store(const BIGNUM*n)const{Bytes32 out{};need(BN_bn2lebinpad(n,out.data(),32)==32);return out;}
public:
    LocalField(){
        need(ctx&&p&&d&&half&&BN_set_bit(p,255)&&BN_sub_word(p,19));
        BIGNUM*t=BN_new();need(t&&BN_set_word(t,121666)&&BN_mod_inverse(t,t,p,ctx)&&BN_mul_word(t,121665)&&BN_mod(t,t,p,ctx)&&BN_sub(d,p,t));   // d = -121665/121666
        need(BN_set_word(half,2)&&BN_mod_inverse(half,half,p,ctx));
        // EdwardsHinted.sqrtMinusA2: a square root of -486664.
        need(BN_dec2bn(&c,"6853475219497561581579357271197624642482790079785650197046958215289687604742")&&BN_mod_sqr(t,c,p,ctx)&&BN_add_word(t,486664)&&BN_cmp(t,p)==0);
        BN_free(t);
    }
    ~LocalField(){BN_free(p);BN_free(d);BN_free(c);BN_free(half);BN_CTX_free(ctx);}
    LocalField(const LocalField&)=delete;LocalField&operator=(const LocalField&)=delete;
    // Affine coordinates (x, y) of a point in libsodium's encoding (y, and the parity of x in the top bit).
    std::array<Bytes32,2> affine(const Bytes32&encoded)const{
        Bytes32 yb=encoded;const bool odd=yb[31]>>7;yb[31]&=127;
        BIGNUM*y=load(yb),*yy=BN_new(),*n=BN_new(),*m=BN_new(),*x=BN_new();need(yy&&n&&m&&x);
        need(BN_mod_sqr(yy,y,p,ctx)&&BN_copy(n,yy)&&BN_sub_word(n,1)&&BN_nnmod(n,n,p,ctx)&&BN_mod_mul(m,d,yy,p,ctx)&&BN_add_word(m,1)&&BN_nnmod(m,m,p,ctx)
            &&BN_mod_inverse(m,m,p,ctx)&&BN_mod_mul(n,n,m,p,ctx));
        if(BN_is_zero(n))BN_zero(x);else need(BN_mod_sqrt(x,n,p,ctx)!=nullptr);
        need(BN_mod_sqr(m,x,p,ctx)&&BN_cmp(m,n)==0);   // a point of the curve
        if(bool(BN_is_odd(x))!=odd)need(!BN_is_zero(x)&&BN_sub(x,p,x));
        std::array<Bytes32,2>out{store(x),store(y)};BN_free(y);BN_free(yy);BN_free(n);BN_free(m);BN_free(x);return out;
    }
    Bytes32 encode(const Bytes32&x,const Bytes32&y)const{need(canonical(x)&&canonical(y));Bytes32 out=y;out[31]|=uint8_t((x[0]&1)<<7);return out;}
    // x·y, for the fourth coordinate of a PUBLIC point.
    Bytes32 product(const Bytes32&a,const Bytes32&b)const{
        BIGNUM*x=load(a),*y=load(b);need(BN_mod_mul(x,x,y,p,ctx));auto out=store(x);BN_free(x);BN_free(y);return out;
    }
    // For an opened nonzero w (EdwardsHinted.liftOpen): whether it is a square (`sel`), and
    // sqrt(-486664)/s for s a root of w (when it is) or of w/2 (when it is not).
    std::pair<bool,Bytes32> root(const Bytes32&opened)const{
        BIGNUM*w=load(opened),*s=BN_new();need(s&&!BN_is_zero(w));
        const int symbol=BN_kronecker(w,p,ctx);need(symbol==1||symbol==-1);
        if(symbol==-1)need(BN_mod_mul(w,w,half,p,ctx));
        need(BN_mod_sqrt(s,w,p,ctx)!=nullptr&&BN_mod_inverse(s,s,p,ctx)&&BN_mod_mul(s,s,c,p,ctx));
        auto out=store(s);BN_free(w);BN_free(s);return {symbol==1,out};
    }
    Bytes32 number(const char*decimal)const{BIGNUM*n=nullptr;need(BN_dec2bn(&n,decimal));auto out=store(n);BN_free(n);return out;}
};
// Local group operations on encoded points (libsodium). Unlike its scalar multiplication,
// these accept every point of the curve, which a masked point need not be in the prime-order subgroup.
struct Ed {
    static void need(bool ok){if(!ok)throw std::runtime_error("local point arithmetic");}
    static Bytes32 add(const Bytes32&a,const Bytes32&b){Bytes32 r{};need(crypto_core_ed25519_add(r.data(),a.data(),b.data())==0);return r;}
    static Bytes32 sub(const Bytes32&a,const Bytes32&b){Bytes32 r{};need(crypto_core_ed25519_sub(r.data(),a.data(),b.data())==0);return r;}
    static Bytes32 times16(Bytes32 a){for(int i=0;i<4;i++)a=add(a,a);return a;}
    static Bytes32 neutral(){Bytes32 r{};r[0]=1;return r;}
    // k·a for a public scalar (little-endian), by doubling and adding.
    static Bytes32 times(const Bytes32&k,const Bytes32&a){
        Bytes32 r=neutral();
        for(int i=255;i>=0;i--){r=add(r,r);if((k[i/8]>>(i%8))&1)r=add(r,a);}
        return r;
    }
    // A point of order 8.
    static Bytes32 torsion(){
        static const char*hex="c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a";Bytes32 t{};
        for(unsigned i=0;i<32;i++)t[i]=uint8_t(std::stoul(std::string(hex+2*i,2),nullptr,16));
        auto four=add(add(t,t),add(t,t));need(four!=neutral()&&add(four,four)==neutral());return t;
    }
    // Uniform over the whole group of the curve (prime-order part and the 8 torsion points).
    static Bytes32 random(){
        need(sodium_init()>=0);Bytes32 r{};crypto_core_ed25519_random(r.data());
        static const Bytes32 t=torsion();
        for(uint32_t i=randombytes_uniform(8);i;i--)r=add(r,t);
        return r;
    }
};
struct HintedPrograms {
    static std::string at(const char*name){return std::string(EMP_WORD_CIRCUIT_DIR)+"/"+name+".flat";}
    FieldProgram lift_open{at("lift-open"),LIFT_OPEN_SHA},lift_point{at("lift-point"),LIFT_POINT_SHA};
    FieldProgram prepare{at("edwards-prepare-hinted"),EDWARDS_PREPARE_HINTED_SHA},offset_sum{at("edwards-offset-sum-fast"),EDWARDS_OFFSET_SUM_FAST_SHA};
    FieldProgram bit_table{at("edwards-bit-table"),EDWARDS_BIT_TABLE_SHA},bit_sum{at("edwards-bit-sum"),EDWARDS_BIT_SUM_SHA};
    FieldProgram signature_sum{at("edwards-signature-sum"),EDWARDS_SIGNATURE_SUM_SHA},torsion{at("edwards-torsion-hinted"),EDWARDS_TORSION_HINTED_SHA};
    FieldProgram mask_pair{at("field-mask-pair"),FIELD_MASK_PAIR_SHA},affine_bit_sum{at("edwards-affine-bit-sum"),EDWARDS_AFFINE_BIT_SUM_SHA};
    HintedPrograms(){
        if(affine_bit_sum.input_count()!=757||affine_bit_sum.output_count()!=2)throw std::runtime_error("hinted program shape");
        auto shape=[](const FieldProgram&p,unsigned in,unsigned out){if(p.input_count()!=in||p.output_count()!=out)throw std::runtime_error("hinted program shape");};
        shape(lift_open,8,6);shape(lift_point,9,5);shape(prepare,884,630+2+1024);shape(offset_sum,194,2);shape(bit_table,380,126+1024);
        shape(bit_sum,1261,2);shape(signature_sum,2546,2);shape(torsion,7,2);shape(mask_pair,3,2);
    }
};
// A lifted point: private validity and coordinates, the opened masked point Z = P + M_A + M_B,
// and this party's own mask point. `zero`: the Montgomery coordinate was 0 (opened; see NEEDS_REVIEW.md).
struct Lifted {H valid,x,y;Bytes32 z{},mask{};bool zero=false;};
using ExtTable=std::vector<H>;   // 256 points 2^i·P, four coordinates each
class Hinted {
    static void need(bool ok,const char*what){if(!ok)throw std::runtime_error(what);}
    static bool is_zero(const Bytes32&v){for(auto b:v)if(b)return false;return true;}
    ExtTable base;   // 2^i·B for the public base point, as public elements (per engine)
public:
    static constexpr unsigned WINDOWS=64,LINKS=2*(WINDOWS-1),BITS=251;
    HintedPrograms programs;LocalField local;
    // Montgomery coordinates -> points (EdwardsHinted.liftOpen, liftPoint), all in the same rounds.
    // Opened: per point two bit checks and two curve checks (zero), then w (uniform, or zero for u = 0), then Z (uniform).
    std::vector<Lifted> lift(FE&f,const std::vector<H>&us){
        const size_t n=us.size();std::vector<Lifted>out(n);if(!n)return out;
        need(sodium_init()>=0,"libsodium");
        auto r=FieldProgram::masks(f,n);std::vector<uint64_t>coin(n);std::vector<Bytes32>mine;
        for(size_t i=0;i<n;i++){coin[i]=randombytes_uniform(2);out[i].mask=Ed::random();auto xy=local.affine(out[i].mask);mine.push_back(xy[0]);mine.push_back(xy[1]);}
        auto bits=f.input_coins(coin);auto points=f.input_elements(mine);f.check();
        std::vector<std::vector<H>>first;
        for(size_t i=0;i<n;i++)first.push_back({us[i],r[i],bits[0][i],bits[1][i],points[0][2*i],points[0][2*i+1],points[1][2*i],points[1][2*i+1]});
        auto opened=programs.lift_open.evaluate_all(f,first);
        std::vector<H>checks,ws;for(auto&o:opened){checks.insert(checks.end(),o.begin()+1,o.begin()+5);ws.push_back(o[0]);}
        for(auto&v:f.checked_open(checks))need(is_zero(v),"hinted lift: a mask contribution is not a bit or not a curve point");
        auto w=f.checked_open(ws);
        std::vector<std::vector<H>>second;
        for(size_t i=0;i<n;i++){
            H cs=f.constant(0),sel=f.constant(0),b=f.constant(0);out[i].zero=is_zero(w[i]);
            if(!out[i].zero){auto root=local.root(w[i]);cs=f.public_element(root.second);sel=f.constant(root.first?1:0);b=opened[i][5];}
            second.push_back({cs,sel,us[i],r[i],b,points[0][2*i],points[0][2*i+1],points[1][2*i],points[1][2*i+1]});
        }
        auto lifted=programs.lift_point.evaluate_all(f,second);
        std::vector<H>zs;for(auto&o:lifted){zs.push_back(o[3]);zs.push_back(o[4]);}
        auto z=f.checked_open(zs);
        for(size_t i=0;i<n;i++){
            out[i].valid=lifted[i][0];out[i].x=lifted[i][1];out[i].y=lifted[i][2];out[i].z=local.encode(z[2*i],z[2*i+1]);
            Ed::add(out[i].z,out[i].z);   // a point of the curve
        }
        return out;
    }
    // Each party's hints for the 63 window bases of each point: A enters 16^w·(Z - M_A), B enters 16^w·M_B.
    // Returns per point the 252 inputs in program order (A's x, y, then B's x, y, per window).
    std::vector<std::vector<H>> hints(FE&f,int party,const std::vector<const Lifted*>&points){
        std::vector<Bytes32>mine;
        for(auto p:points){
            Bytes32 at=party==emp::ALICE?Ed::sub(p->z,p->mask):p->mask;
            for(unsigned w=1;w<WINDOWS;w++){at=Ed::times16(at);auto xy=local.affine(at);mine.push_back(xy[0]);mine.push_back(xy[1]);}
        }
        auto entered=f.input_elements(mine);f.check();
        std::vector<std::vector<H>>out;const size_t each=2*(WINDOWS-1);
        for(size_t i=0;i<points.size();i++){
            std::vector<H>row;
            for(size_t w=0;w+1<WINDOWS;w++)for(unsigned owner=0;owner<2;owner++){row.push_back(entered[owner][each*i+2*w]);row.push_back(entered[owner][each*i+2*w+1]);}
            out.push_back(std::move(row));
        }
        return out;
    }
    // x/z for each pair by masked inversion, as X25519Fast::evaluate_many: a zero denominator opens as zero
    // (`zero[i]`, result 0); every other opening is uniform.
    std::vector<H> quotients(FE&f,Challenge&channel,const std::vector<std::array<H,2>>&pairs,std::vector<bool>&zero){
        const size_t n=pairs.size();zero.assign(n,false);if(!n)return {};
        auto mask=FieldProgram::masks(f,n);std::vector<std::vector<H>>in;
        for(size_t i=0;i<n;i++)in.push_back({pairs[i][0],pairs[i][1],mask[i]});
        auto masked=programs.mask_pair.evaluate_all(f,in);
        std::vector<H>denominators;for(auto&m:masked)denominators.push_back(m[1]);
        auto opened=f.checked_open(denominators);
        std::vector<uint8_t>flat(32*n),peer(32*n);for(size_t i=0;i<n;i++)std::copy(opened[i].begin(),opened[i].end(),flat.begin()+32*i);
        channel.transfer(flat.data(),peer.data(),flat.size());need(flat==peer,"masked denominator disagreement");
        std::vector<H>out;
        for(size_t i=0;i<n;i++){zero[i]=is_zero(opened[i]);out.push_back(zero[i]?f.constant(0):f.divide_public(masked[i][0],opened[i]));}
        return out;
    }
    // ---- The offset agreement's per-contact preparation (EdwardsHinted.prepareHinted) for several
    // contacts in the same rounds. `ok[i]` false: that contact's key is not a point of the curve
    // (what EdwardsAffine.prepare's curve check opened); its agreement stays unprepared.
    // Any other failed check is a party's deviation and throws.
    std::vector<bool> prepare(FE&f,Challenge&channel,int party,const std::vector<OffsetAgreement*>&agreements,const std::vector<H>&recipients){
        using P=OffsetPrograms;const size_t n=agreements.size();need(n==recipients.size(),"prepare batch shape");
        std::vector<bool>ok(n,false);if(!n)return ok;
        for(auto a:agreements)need(a&&!a->prepared(),"offset agreement state");
        auto lifted=lift(f,recipients);
        // Validity is opened, as before: an invalid key is that contact's failure.
        std::vector<H>valid;for(auto&l:lifted)valid.push_back(l.valid);
        auto flags=f.checked_open(valid);std::vector<size_t>live;std::vector<const Lifted*>points;
        Bytes32 one{};one[0]=1;
        for(size_t i=0;i<n;i++){need(flags[i]==one||is_zero(flags[i]),"lift validity");if(flags[i]==one&&!lifted[i].zero){live.push_back(i);points.push_back(&lifted[i]);}}
        const size_t m=live.size();if(!m)return ok;
        auto hinted=hints(f,party,points);auto masks=FieldProgram::masks(f,LINKS*m);
        std::vector<std::array<uint8_t,32>>scalars(m);std::vector<uint64_t>local_bits;
        for(auto&scalar:scalars){emp::PRG prg;prg.random_data_unaligned(scalar.data(),32);scalar[31]&=15;for(unsigned i=0;i<P::BITS;i++)local_bits.push_back((scalar[i/8]>>(i%8))&1);}
        auto bits=f.input_coins(local_bits);f.check();
        std::vector<std::vector<H>>in;
        for(size_t j=0;j<m;j++){
            std::vector<H>row{lifted[live[j]].x,lifted[live[j]].y};row.insert(row.end(),hinted[j].begin(),hinted[j].end());
            row.insert(row.end(),masks.begin()+LINKS*j,masks.begin()+LINKS*(j+1));
            for(unsigned owner=0;owner<2;owner++)row.insert(row.end(),bits[owner].begin()+P::BITS*j,bits[owner].begin()+P::BITS*(j+1));
            in.push_back(std::move(row));
        }
        auto out=programs.prepare.evaluate_all(f,in);
        const size_t checks=2*P::BITS+LINKS;std::vector<H>zero;for(auto&o:out)zero.insert(zero.end(),o.begin(),o.begin()+checks);
        for(auto&v:f.checked_open(zero))need(is_zero(v),"offset agreement: a scalar contribution is not a bit or a hint is wrong");
        // K0 = kA·B + kB·B per contact, the halves exchanged commit-then-open (as OffsetAgreement::prepare), one exchange for the batch.
        std::vector<uint8_t>mine(32*m),nonce(32*m),commit(32*m),peer(32*m),peer_nonce(32*m),peer_commit(32*m);
        auto bind=[](int who,const uint8_t*n,const uint8_t*point,uint8_t*out){
            std::array<uint8_t,83>frame{};const char tag[]="offset-agreement-K";std::copy_n(tag,18,frame.begin());frame[18]=uint8_t(who);std::copy_n(n,32,frame.begin()+19);std::copy_n(point,32,frame.begin()+51);
            SHA256(frame.data(),frame.size(),out);
        };
        {emp::PRG prg;prg.random_data_unaligned(nonce.data(),int(nonce.size()));}
        for(size_t j=0;j<m;j++){
            need(crypto_scalarmult_ed25519_base_noclamp(mine.data()+32*j,scalars[j].data())==0,"initial key share");sodium_memzero(scalars[j].data(),32);
            bind(party,nonce.data()+32*j,mine.data()+32*j,commit.data()+32*j);
        }
        channel.transfer(commit.data(),peer_commit.data(),commit.size());channel.transfer(nonce.data(),peer_nonce.data(),nonce.size());channel.transfer(mine.data(),peer.data(),mine.size());
        for(size_t j=0;j<m;j++){
            std::array<uint8_t,32>check{},key{};bind(party==emp::ALICE?emp::BOB:emp::ALICE,peer_nonce.data()+32*j,peer.data()+32*j,check.data());
            need(std::equal(check.begin(),check.end(),peer_commit.begin()+32*j)&&crypto_core_ed25519_is_valid_point(peer.data()+32*j)==1,"initial key share commitment");
            const uint8_t*a=(party==emp::ALICE?mine.data():peer.data())+32*j,*b=(party==emp::ALICE?peer.data():mine.data())+32*j;
            need(crypto_core_ed25519_add(key.data(),a,b)==0&&crypto_core_ed25519_is_valid_point(key.data())==1,"initial public key");
            auto&o=out[j];
            agreements[live[j]]->install(std::vector<H>(o.begin()+checks+2,o.end()),std::vector<H>(o.begin()+checks,o.begin()+checks+2),key);
            ok[live[j]]=true;
        }
        return ok;
    }
    // Per message (EdwardsHinted.offsetSumFast): as OffsetAgreement::step, in 2·7 levels and one opening.
    std::pair<std::array<uint8_t,32>,H> step(OffsetAgreement&agreement,FE&f,Challenge&channel,std::array<uint8_t,32>offset){
        std::array<uint8_t,32>u{};auto inputs=agreement.step_inputs(f,offset,u);
        auto out=programs.offset_sum.evaluate_all(f,{inputs}).at(0);
        std::vector<bool>zero;auto agreed=quotients(f,channel,{{out[0],out[1]}},zero);
        need(!zero[0],"offset agreement: neutral sum");
        return {u,agreed[0]};
    }
    // ---- Bit tables: all 2^i·P for lifted points (EdwardsHinted.bitTable), in the same rounds.
    // Opened: the masked links (zero).
    std::vector<ExtTable> tables(FE&f,int party,const std::vector<const Lifted*>&points){
        const size_t n=points.size();std::vector<ExtTable>out;if(!n)return out;
        auto hinted=hints(f,party,points);auto masks=FieldProgram::masks(f,LINKS*n);
        std::vector<std::vector<H>>in;
        for(size_t i=0;i<n;i++){
            std::vector<H>row{points[i]->x,points[i]->y};row.insert(row.end(),hinted[i].begin(),hinted[i].end());
            row.insert(row.end(),masks.begin()+LINKS*i,masks.begin()+LINKS*(i+1));in.push_back(std::move(row));
        }
        auto made=programs.bit_table.evaluate_all(f,in);
        std::vector<H>zero;for(auto&o:made)zero.insert(zero.end(),o.begin(),o.begin()+LINKS);
        for(auto&v:f.checked_open(zero))need(is_zero(v),"bit table: a hint is wrong");
        for(auto&o:made)out.emplace_back(o.begin()+LINKS,o.end());
        return out;
    }
    // The same table for a PUBLIC point, computed locally and entered as public elements.
    ExtTable public_table(FE&f,Bytes32 point){
        ExtTable out;H one=f.constant(1);
        for(unsigned i=0;i<4*WINDOWS;i++){
            auto xy=local.affine(point);
            out.push_back(f.public_element(xy[0]));out.push_back(f.public_element(xy[1]));out.push_back(one);out.push_back(f.public_element(local.product(xy[0],xy[1])));
            point=Ed::add(point,point);
        }
        return out;
    }
    const ExtTable&base_table(FE&f){
        if(base.empty()){Bytes32 b{};b.fill(0x66);b[0]=0x58;base=public_table(f,b);}   // the base point: y = 4/5, x even
        return base;
    }
    // ---- X25519 from bit tables (EdwardsHinted.bitSum). `bits`: scalar bits 3..253 as field bits.
    // `table` null: the point's coordinate was 0 and the result is 0 (RFC 7748), as `zero` reports.
    struct Job {const std::vector<H>*bits;const ExtTable*table;H valid;};
    std::vector<H> agree(FE&f,Challenge&channel,const std::vector<Job>&jobs,std::vector<bool>&zero){
        const size_t n=jobs.size();zero.assign(n,false);std::vector<H>out(n);
        std::vector<size_t>live;for(size_t i=0;i<n;i++){if(jobs[i].table)live.push_back(i);else{zero[i]=true;out[i]=f.constant(0);}}
        if(live.empty())return out;
        auto rho=FieldProgram::masks(f,live.size());std::vector<std::vector<H>>in;
        for(size_t j=0;j<live.size();j++){
            auto&job=jobs[live[j]];need(job.bits->size()==BITS&&job.table->size()==16*WINDOWS,"agreement job shape");
            std::vector<H>row{job.valid,rho[j]};row.insert(row.end(),job.table->begin()+4*3,job.table->begin()+4*255);
            row.insert(row.end(),job.bits->begin(),job.bits->end());in.push_back(std::move(row));
        }
        auto sums=programs.bit_sum.evaluate_all(f,in);
        std::vector<std::array<H,2>>pairs;for(auto&s:sums)pairs.push_back({s[0],s[1]});
        std::vector<bool>none;auto u=quotients(f,channel,pairs,none);
        for(size_t j=0;j<live.size();j++){out[live[j]]=u[j];zero[live[j]]=none[j];}
        return out;
    }
    // The same from affine points 2^i·P, i = 3..254 (OffsetAgreement::powers: a prepared contact's
    // table already holds them), for points known to be valid (EdwardsHinted.affineBitSum).
    std::vector<H> agree_affine(FE&f,Challenge&channel,const std::vector<std::pair<const std::vector<H>*,std::vector<H>>>&jobs,std::vector<bool>&zero){
        const size_t n=jobs.size();zero.assign(n,false);if(!n)return {};
        auto rho=FieldProgram::masks(f,n);std::vector<std::vector<H>>in;H one=f.constant(1);
        for(size_t j=0;j<n;j++){
            need(jobs[j].first->size()==BITS&&jobs[j].second.size()==2*(BITS+1),"agreement job shape");
            std::vector<H>row{one,rho[j]};row.insert(row.end(),jobs[j].second.begin(),jobs[j].second.end());
            row.insert(row.end(),jobs[j].first->begin(),jobs[j].first->end());in.push_back(std::move(row));
        }
        auto sums=programs.affine_bit_sum.evaluate_all(f,in);
        std::vector<std::array<H,2>>pairs;for(auto&s:sums)pairs.push_back({s[0],s[1]});
        return quotients(f,channel,pairs,zero);
    }
    // ---- XEdDSA verification points [s]B - [h]A (EdwardsHinted.signatureSum), several in the same rounds.
    // `flip_h_s`: flip, the 256 bits of h, the 253 bits of s (as XEdDsaField.signedRun takes them).
    struct Signature {const ExtTable*key;const std::vector<H>*flip_h_s;};
    std::vector<std::array<H,2>> signatures(FE&f,const std::vector<Signature>&jobs){
        auto&b=base_table(f);std::vector<std::vector<H>>in;
        for(auto&job:jobs){
            need(job.key->size()==16*WINDOWS&&job.flip_h_s->size()==1+256+253,"signature job shape");
            std::vector<H>row{job.flip_h_s->at(0)};row.insert(row.end(),job.key->begin(),job.key->end());
            row.insert(row.end(),job.flip_h_s->begin()+1,job.flip_h_s->begin()+257);
            row.insert(row.end(),b.begin(),b.begin()+4*253);row.insert(row.end(),job.flip_h_s->begin()+257,job.flip_h_s->end());
            in.push_back(std::move(row));
        }
        std::vector<std::array<H,2>>out;for(auto&r:programs.signature_sum.evaluate_all(f,in))out.push_back({r[0],r[1]});
        return out;
    }
    // ---- Torsion check of a lifted point (EdwardsHinted.torsionHinted): two private values that are
    // zero exactly when the point is in the prime-order subgroup. Nothing is opened.
    std::array<H,2> torsion(FE&f,int party,const Lifted&point){
        // 1/8 modulo the group order.
        static const Bytes32 eighth=local.number("2713877091499598330239944961141122840321418634767465352250731601857045344121");
        auto xy=local.affine(Ed::times(eighth,party==emp::ALICE?Ed::sub(point.z,point.mask):point.mask));
        auto entered=f.input_elements({xy[0],xy[1]});f.check();
        auto out=programs.torsion.evaluate_all(f,{{point.x,point.y,entered[0][0],entered[0][1],entered[1][0],entered[1][1],FieldProgram::masks(f,1).at(0)}}).at(0);
        return {out[0],out[1]};
    }
    // ---- Scalars as field bits 3..253 (bit 254 is set and bits 0..2 are clear by clamping).
    // The XOR of both parties' `share` arguments; every contribution is checked to be a bit.
    std::vector<H> shared_bits(FE&f,const WordCircuits&circuits,const std::array<uint8_t,32>&share){
        std::vector<uint64_t>local_bits(BITS);for(unsigned i=0;i<BITS;i++)local_bits[i]=(share[(i+3)/8]>>((i+3)%8))&1;
        auto shares=f.input_coins(local_bits);f.check();
        std::vector<H>all=shares[0];all.insert(all.end(),shares[1].begin(),shares[1].end());
        for(auto&v:f.checked_open(circuits.field_bit_checks(f,all)))need(is_zero(v),"non-bit scalar contribution");
        return circuits.field_bit_xor(f,shares[0],shares[1]);
    }
    // A scalar BOTH parties know, as constants.
    std::vector<H> public_bits(FE&f,const std::array<uint8_t,32>&scalar){
        std::vector<H>out;for(unsigned i=0;i<BITS;i++)out.push_back(f.constant((scalar[(i+3)/8]>>((i+3)%8))&1));return out;
    }
};
}
