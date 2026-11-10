// TEST FIXTURE: the field engine started with a supplied MAC key share, and
// stored values imported as authenticated shares (the format the share
// database will deliver: additive shares of x and of key·x modulo 2^255-19).
//
// Both processes derive the same test dealing from a fixed public seed and
// each uses only its own half. Checks: an imported value opens to itself; a
// product of imported values opens correctly; an exported share re-imports;
// and (argument "tamper", malicious build) a party that shifts its value share
// makes the opening fail its MAC check.
// Usage: PARTY(0|1) PORT [tamper]
#include "field_engine.h"
#include <openssl/bn.h>
#include <openssl/sha.h>
#include <iostream>
#include <stdexcept>
#include <string>
using namespace emp_hybrid;
using Bytes32=std::array<uint8_t,32>;
struct Field {
    BN_CTX*ctx=BN_CTX_new();BIGNUM*p=BN_new();
    Field(){BN_one(p);BN_lshift(p,p,255);BN_sub_word(p,19);}
    ~Field(){BN_free(p);BN_CTX_free(ctx);}
    BIGNUM*derive(const std::string&label)const{
        uint8_t digest[64];SHA512(reinterpret_cast<const uint8_t*>(label.data()),label.size(),digest);
        BIGNUM*x=BN_bin2bn(digest,64,nullptr);BN_mod(x,x,p,ctx);return x;
    }
    Bytes32 bytes(const BIGNUM*x)const{Bytes32 out{};if(BN_bn2lebinpad(x,out.data(),32)!=32)throw std::runtime_error("field encoding");return out;}
};
int main(int argc,char**argv){
    try{
        if(argc<3)return 2;
        const unsigned party=std::stoul(argv[1]),port=std::stoul(argv[2]);const bool tamper=argc>3&&std::string(argv[3])=="tamper";
        if(party>1)return 2;
        Field f;
        // Dealing: key = kA + kB; for each value x: x = xA + xB and key·x = mA + mB.
        BIGNUM*key_share[2]={f.derive("fixture key share 0"),f.derive("fixture key share 1")};
        BIGNUM*key=BN_new();BN_mod_add(key,key_share[0],key_share[1],f.p,f.ctx);
        BIGNUM*value[2],*value_share[2][2],*mac_share[2][2];
        for(int i=0;i<2;i++){
            value[i]=f.derive("fixture value "+std::to_string(i));
            value_share[i][0]=f.derive("fixture value share "+std::to_string(i));value_share[i][1]=BN_new();BN_mod_sub(value_share[i][1],value[i],value_share[i][0],f.p,f.ctx);
            BIGNUM*mac=BN_new();BN_mod_mul(mac,key,value[i],f.p,f.ctx);
            mac_share[i][0]=f.derive("fixture mac share "+std::to_string(i));mac_share[i][1]=BN_new();BN_mod_sub(mac_share[i][1],mac,mac_share[i][0],f.p,f.ctx);
        }
        BIGNUM*product=BN_new();BN_mod_mul(product,value[0],value[1],f.p,f.ctx);
        bool with_key=true;
#ifdef EMP_HYBRID_SEMI_HONEST
        with_key=false;
#endif
        const Bytes32 my_key=f.bytes(key_share[party]);
        FieldEngine engine(party,port,16,with_key?&my_key:nullptr);
        Bytes32 first=f.bytes(value_share[0][party]);
        if(tamper&&party==1)first[0]^=1;   // shift this party's share of the first value
        auto a=engine.import_share(first,f.bytes(mac_share[0][party]));
        auto b=engine.import_share(f.bytes(value_share[1][party]),f.bytes(mac_share[1][party]));
        auto c=engine.mul({a},{b}).at(0);
        // Export and re-import the product: the stored form round-trips.
        auto stored=engine.export_share(c);auto again=engine.import_share(stored.first,stored.second);
        bool rejected=false;std::vector<Bytes32>opened;
        try{opened=engine.checked_open({a,b,c,again});}catch(const std::exception&e){rejected=true;std::cout<<"FIELD_IMPORT rejected: "<<e.what()<<"\n";}
        bool expect_reject=tamper&&with_key;
        bool ok;
        if(expect_reject)ok=rejected;
        else if(tamper)ok=!rejected;   // semi-honest: no MACs, a shifted share is not detected
        else ok=!rejected&&opened.at(0)==f.bytes(value[0])&&opened.at(1)==f.bytes(value[1])&&opened.at(2)==f.bytes(product)&&opened.at(3)==f.bytes(product);
        std::cout<<"FIELD_IMPORT party="<<party<<" tamper="<<tamper<<" with_key="<<with_key<<" rejected="<<rejected<<" ok="<<ok<<"\n";
        return ok?0:1;
    }catch(const std::exception&e){std::cerr<<"field import fixture: "<<e.what()<<"\n";return 1;}
}
