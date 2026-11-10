#pragma once
// Loader and batched evaluator for field programs exported from Lean
// (FieldDag flat format). The file is read once, hash-checked against its pin
// and parsed from the same bytes. Evaluation runs any number of independent
// instances together so their multiplications share rounds. A product with a
// public constant operand is linear and uses no triple.
#include "field_engine.h"
#include <openssl/sha.h>
#include <array>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
namespace emp_hybrid {
class FieldProgram {
    struct Node {char op;unsigned a=0,b=0,depth=0;uint64_t constant=0;};
    std::vector<Node>nodes;std::vector<std::vector<unsigned>>linear,multiplications;unsigned inputs=0;std::vector<unsigned>outputs;
public:
    FieldProgram(const std::string&path,const char*expected_sha){
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
            if(n.op=='C'){if(!(in>>n.constant))throw std::runtime_error("field constant");}
            else if(n.op=='I'){if(!(in>>n.a)||n.a>=inputs)throw std::runtime_error("field input");}
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
        linear.resize(maximum+1);multiplications.resize(maximum+1);
        for(unsigned i=0;i<nodes.size();i++)(nodes[i].op=='M'?multiplications:linear)[nodes[i].depth].push_back(i);
    }
    unsigned input_count()const{return inputs;}
    unsigned output_count()const{return outputs.size();}
    // Single-output programs: one handle per instance.
    std::vector<FieldEngine::Handle> evaluate(FieldEngine&f,const std::vector<std::vector<FieldEngine::Handle>>&instances)const{
        if(outputs.size()!=1)throw std::runtime_error("field program is multi-output");
        std::vector<FieldEngine::Handle>out;for(auto&v:evaluate_all(f,instances))out.push_back(v[0]);return out;
    }
    // All outputs per instance; instance k reads instances[k][0..inputs).
    std::vector<std::vector<FieldEngine::Handle>> evaluate_all(FieldEngine&f,const std::vector<std::vector<FieldEngine::Handle>>&instances)const{
        using H=FieldEngine::Handle;
        for(auto&v:instances)if(v.size()!=inputs)throw std::runtime_error("field program arity");
        std::vector<std::vector<H>>values(instances.size(),std::vector<H>(nodes.size()));
        for(unsigned level=0;level<linear.size();level++){
            if(level){
                std::vector<H>a,b;
                for(size_t k=0;k<instances.size();k++)for(auto id:multiplications[level]){a.push_back(values[k][nodes[id].a]);b.push_back(values[k][nodes[id].b]);}
                if(!a.empty()){auto out=f.mul(a,b);size_t q=0;for(size_t k=0;k<instances.size();k++)for(auto id:multiplications[level])values[k][id]=out[q++];}
            }
            for(size_t k=0;k<instances.size();k++)for(auto id:linear[level]){const auto&n=nodes[id];auto&v=values[k];
                if(n.op=='C')v[id]=f.constant(n.constant);else if(n.op=='I')v[id]=instances[k][n.a];
                else if(n.op=='A')v[id]=f.add(v[n.a],v[n.b]);else if(n.op=='S')v[id]=f.sub(v[n.a],v[n.b]);
                else if(n.op=='L')v[id]=f.scale(v[n.b],nodes[n.a].constant);else v[id]=f.scale(v[n.a],nodes[n.b].constant);
            }
        }
        std::vector<std::vector<H>>out;for(auto&v:values){std::vector<H>row;for(auto o:outputs)row.push_back(v[o]);out.push_back(row);}return out;
    }
};
}
