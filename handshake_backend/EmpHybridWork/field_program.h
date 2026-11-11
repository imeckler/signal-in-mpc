#pragma once
// Loader and batched evaluator for field programs exported from Lean
// (FieldDag flat format). The file is read once, hash-checked against its pin
// and parsed from the same bytes. Evaluation runs any number of independent
// instances together so their multiplications share rounds. A product with a
// public constant operand is linear and uses no triple.
#include "field_engine.h"
#include "profile.h"
#include <openssl/bn.h>
#include <openssl/rand.h>
#include <openssl/sha.h>
#include <array>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
namespace emp_hybrid {
class FieldProgram {
    struct Node {char op;unsigned a=0,b=0,depth=0;uint64_t constant=0;std::array<uint8_t,32>wide{};};
    std::vector<Node>nodes;std::vector<std::vector<unsigned>>linear,multiplications,divisions;unsigned inputs=0,division_count=0;std::vector<unsigned>outputs;
    std::string label;   // for the profile only
public:
    // Uniform shared field elements nobody knows: the sum of both parties' private inputs.
    static std::vector<FieldEngine::Handle> masks(FieldEngine&f,size_t count){
        std::vector<FieldEngine::Handle>out;if(!count)return out;
        std::vector<std::array<uint8_t,32>>mine(count);
        for(auto&m:mine)for(;;){
            if(RAND_bytes(m.data(),32)!=1)throw std::runtime_error("field mask randomness");
            m[31]&=127;bool top=m[31]==127&&m[0]>=0xed;for(unsigned i=1;i<31&&top;i++)top=m[i]==0xff;
            if(!top)break;   // below 2^255-19
        }
        auto shares=f.input_elements(mine);f.check();
        for(size_t i=0;i<count;i++)out.push_back(f.add(shares[0][i],shares[1][i]));return out;
    }
    FieldProgram(const std::string&path,const char*expected_sha){
        label=path.substr(path.find_last_of('/')+1);label=label.substr(0,label.find('.'));
        std::ifstream file(path,std::ios::binary);std::string bytes(4000001,'\0');file.read(bytes.data(),bytes.size());auto size=file.gcount();
        if(size<=0||size>4000000)throw std::runtime_error("field program size");bytes.resize(size);
        std::array<uint8_t,32>digest{};SHA256(reinterpret_cast<const uint8_t*>(bytes.data()),bytes.size(),digest.data());
        const char*hex="0123456789abcdef";std::string encoded;for(auto b:digest){encoded+=hex[b>>4];encoded+=hex[b&15];}
        if(encoded!=expected_sha)throw std::runtime_error("field program identity");
        // V1: header's third number is the single output node. V2: it is the
        // output count and a final "O ..." row lists the output nodes.
        std::istringstream in(bytes);std::string magic,prime;unsigned count,third;
        if(!(in>>magic>>inputs>>count>>third>>prime)||(magic!="EMP_HYBRID_FIELD_DAG_V1"&&magic!="EMP_HYBRID_FIELD_DAG_V2")||!inputs||!count||prime!="57896044618658097711785492504343953926634992332820282019728792003956564819949")throw std::runtime_error("field program profile");
        const bool multi=magic=="EMP_HYBRID_FIELD_DAG_V2";
        if(!multi){if(third>=count)throw std::runtime_error("field program output");outputs={third};}
        nodes.reserve(count);unsigned maximum=0;
        for(unsigned i=0;i<count;i++){
            Node n;if(!(in>>n.op))throw std::runtime_error("field program row");
            if(n.op=='C'){
                // Machine-word constants scale linearly; wider ones become public elements ('P').
                std::string digits;if(!(in>>digits)||digits.empty()||digits.size()>77||digits.find_first_not_of("0123456789")!=std::string::npos)throw std::runtime_error("field constant");
                if(digits.size()<=18)n.constant=std::stoull(digits);
                else{
                    BIGNUM*value=nullptr,*p=BN_new();bool ok=p&&BN_dec2bn(&value,digits.c_str())&&BN_dec2bn(&p,prime.c_str())&&BN_cmp(value,p)<0&&BN_bn2lebinpad(value,n.wide.data(),32)==32;
                    BN_free(value);BN_free(p);if(!ok)throw std::runtime_error("field constant");n.op='P';
                }
            }
            else if(n.op=='I'){if(!(in>>n.a)||n.a>=inputs)throw std::runtime_error("field input");}
            else if(n.op=='D'){
                // a / b by masked inversion: one round of two products, then an opening.
                if(!(in>>n.a>>n.b)||n.a>=i||n.b>=i)throw std::runtime_error("field dependency");
                n.depth=std::max(nodes[n.a].depth,nodes[n.b].depth)+1;division_count++;
            }
            else if(n.op=='A'||n.op=='S'||n.op=='M'){
                if(!(in>>n.a>>n.b)||n.a>=i||n.b>=i)throw std::runtime_error("field dependency");
                bool secret=n.op=='M'&&nodes[n.a].op!='C'&&nodes[n.b].op!='C';
                n.depth=std::max(nodes[n.a].depth,nodes[n.b].depth)+secret;
                if(n.op=='M'&&!secret)n.op=nodes[n.a].op=='C'?'L':'R';   // scale by the left / right constant
            }else throw std::runtime_error("field opcode");
            maximum=std::max(maximum,n.depth);nodes.push_back(n);
        }
        if(multi){
            std::string tag;if(!(in>>tag)||tag!="O"||!third)throw std::runtime_error("field program outputs");
            for(unsigned i=0;i<third;i++){unsigned w;if(!(in>>w)||w>=count)throw std::runtime_error("field program output");outputs.push_back(w);}
        }
        std::string trailing;if(in>>trailing)throw std::runtime_error("field program trailing data");
        linear.resize(maximum+1);multiplications.resize(maximum+1);divisions.resize(maximum+1);
        for(unsigned i=0;i<nodes.size();i++)(nodes[i].op=='M'?multiplications:nodes[i].op=='D'?divisions:linear)[nodes[i].depth].push_back(i);
    }
    unsigned input_count()const{return inputs;}
    unsigned output_count()const{return outputs.size();}
    // The same program on PUBLIC inputs, evaluated in the clear: no engine and no rounds. For
    // values both parties know (canonical, little-endian). A division by zero throws.
    std::vector<std::array<uint8_t,32>> evaluate_clear(const std::vector<std::array<uint8_t,32>>&values)const{
        if(values.size()!=inputs)throw std::runtime_error("field program arity");
        BN_CTX*ctx=BN_CTX_new();BIGNUM*p=BN_new();std::vector<BIGNUM*>v(nodes.size(),nullptr);bool ok=ctx&&p&&BN_set_bit(p,255)&&BN_sub_word(p,19);
        for(unsigned i=0;ok&&i<nodes.size();i++){
            const auto&n=nodes[i];v[i]=BN_new();ok=v[i]!=nullptr;if(!ok)break;
            if(n.op=='C')ok=BN_set_word(v[i],n.constant);
            else if(n.op=='P')ok=BN_lebin2bn(n.wide.data(),32,v[i])!=nullptr;
            else if(n.op=='I')ok=BN_lebin2bn(values[n.a].data(),32,v[i])!=nullptr&&BN_cmp(v[i],p)<0;
            else if(n.op=='A')ok=BN_mod_add(v[i],v[n.a],v[n.b],p,ctx);
            else if(n.op=='S')ok=BN_mod_sub(v[i],v[n.a],v[n.b],p,ctx);
            else if(n.op=='D')ok=!BN_is_zero(v[n.b])&&BN_mod_inverse(v[i],v[n.b],p,ctx)&&BN_mod_mul(v[i],v[i],v[n.a],p,ctx);
            else ok=BN_mod_mul(v[i],v[n.a],v[n.b],p,ctx);   // 'M', and 'L'/'R' (a product with a constant)
        }
        std::vector<std::array<uint8_t,32>>out;
        for(auto o:outputs){std::array<uint8_t,32>bytes{};ok=ok&&BN_bn2lebinpad(v[o],bytes.data(),32)==32;out.push_back(bytes);}
        for(auto x:v)BN_free(x);BN_free(p);BN_CTX_free(ctx);
        if(!ok)throw std::runtime_error("field program clear evaluation");
        return out;
    }
    // Single-output programs: one handle per instance.
    std::vector<FieldEngine::Handle> evaluate(FieldEngine&f,const std::vector<std::vector<FieldEngine::Handle>>&instances)const{
        if(outputs.size()!=1)throw std::runtime_error("field program is multi-output");
        std::vector<FieldEngine::Handle>out;for(auto&v:evaluate_all(f,instances))out.push_back(v[0]);return out;
    }
    // All outputs per instance; instance k reads instances[k][0..inputs).
    std::vector<std::vector<FieldEngine::Handle>> evaluate_all(FieldEngine&f,const std::vector<std::vector<FieldEngine::Handle>>&instances)const{
        using H=FieldEngine::Handle;
        ProfileScope scope("field program (local work): "+label);
        for(auto&v:instances)if(v.size()!=inputs)throw std::runtime_error("field program arity");
        std::vector<std::vector<H>>values(instances.size(),std::vector<H>(nodes.size()));
        auto mask=masks(f,size_t(division_count)*instances.size());size_t next_mask=0;
        for(unsigned level=0;level<linear.size();level++){
            if(level){
                std::vector<H>a,b;
                for(size_t k=0;k<instances.size();k++)for(auto id:multiplications[level]){a.push_back(values[k][nodes[id].a]);b.push_back(values[k][nodes[id].b]);}
                // Division a/b: with a uniform shared mask r, open b·r and return (a·r)/(b·r).
                // The opening is uniform for nonzero b; a zero denominator aborts.
                for(size_t k=0;k<instances.size();k++)for(auto id:divisions[level]){H r=mask.at(next_mask++);a.push_back(values[k][nodes[id].a]);b.push_back(r);a.push_back(values[k][nodes[id].b]);b.push_back(r);}
                if(!a.empty()){
                    // A multiplication round. The engine makes triples in batches when it runs out,
                    // inside this call: a round that sent far more than its openings made a batch.
                    // With a triple stock (field_engine.h) a round only waits when the stock is behind.
                    Profile::get().enter();const uint64_t before=f.sent_bytes();const double waited=f.stock_waited();
                    auto out=f.mul(a,b);
                    Profile::get().credit("field triples: waiting for stock: "+label,f.stock_waited()-waited);
                    Profile::get().leave(!f.stocked()&&f.sent_bytes()-before>4096+512*a.size()?"field triples: generation (with the round that needed them): "+label:"field multiplication rounds (triples in stock): "+label);
                    size_t q=0;for(size_t k=0;k<instances.size();k++)for(auto id:multiplications[level])values[k][id]=out[q++];
                    std::vector<H>denominators;for(size_t j=q+1;j<out.size();j+=2)denominators.push_back(out[j]);
                    if(!denominators.empty()){
                        auto opened=f.checked_open(denominators);size_t j=0;
                        for(size_t k=0;k<instances.size();k++)for(auto id:divisions[level]){
                            bool zero=true;for(auto byte:opened[j])if(byte)zero=false;
                            if(zero)throw std::runtime_error("field program division by zero");
                            values[k][id]=f.divide_public(out[q+2*j],opened[j]);j++;
                        }
                    }
                }
            }
            for(size_t k=0;k<instances.size();k++)for(auto id:linear[level]){const auto&n=nodes[id];auto&v=values[k];
                if(n.op=='C')v[id]=f.constant(n.constant);else if(n.op=='P')v[id]=f.public_element(n.wide);else if(n.op=='I')v[id]=instances[k][n.a];
                else if(n.op=='A')v[id]=f.add(v[n.a],v[n.b]);else if(n.op=='S')v[id]=f.sub(v[n.a],v[n.b]);
                else if(n.op=='L')v[id]=f.scale(v[n.b],nodes[n.a].constant);else v[id]=f.scale(v[n.a],nodes[n.b].constant);
            }
        }
        std::vector<std::vector<H>>out;for(auto&v:values){std::vector<H>row;for(auto o:outputs)row.push_back(v[o]);out.push_back(row);}return out;
    }
};
}
