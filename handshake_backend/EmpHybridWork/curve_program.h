#pragma once
#include "field_engine.h"
#include "field_curve_pin.h"
#include <openssl/sha.h>
#include <array>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
namespace emp_hybrid {
class CurveProgram {
    struct Node {char op;unsigned a=0,b=0,depth=0;uint64_t constant=0;};
    std::vector<Node>nodes;
    std::vector<std::vector<unsigned>>linear,multiplications;
public:
    explicit CurveProgram(const char*path){
        // Read ONCE into bounded public storage, verify the exact authorized
        // bytes, then interpret that same snapshot. Filename is not identity.
        std::ifstream file(path,std::ios::binary);std::string bytes(300001,'\0');file.read(bytes.data(),bytes.size());auto size=file.gcount();
        if(size<=0||size>300000)throw std::runtime_error("field program size");bytes.resize(size);
        std::array<uint8_t,32>digest{};SHA256(reinterpret_cast<const uint8_t*>(bytes.data()),bytes.size(),digest.data());
        const char*hex="0123456789abcdef";std::string encoded;for(auto b:digest){encoded+=hex[b>>4];encoded+=hex[b&15];}
        if(encoded!=FIELD_FLAT_SHA)throw std::runtime_error("field program identity");
        std::istringstream in(bytes);std::string magic,prime;unsigned inputs,count,output;
        if(!(in>>magic>>inputs>>count>>output>>prime)||magic!="EMP_HYBRID_FIELD_DAG_V1"||inputs!=257||count!=9437||output!=9436||prime!="57896044618658097711785492504343953926634992332820282019728792003956564819949")throw std::runtime_error("field program profile");
        nodes.reserve(count);unsigned maximum=0,muls=0;
        for(unsigned i=0;i<count;i++){
            Node n;if(!(in>>n.op))throw std::runtime_error("field program row");
            if(n.op=='C'){if(!(in>>n.constant)||(n.constant!=0&&n.constant!=1&&n.constant!=2&&n.constant!=121665))throw std::runtime_error("field constant");}
            else if(n.op=='I'){if(!(in>>n.a)||n.a>=257)throw std::runtime_error("field input");}
            else if(n.op=='A'||n.op=='S'||n.op=='M'){
                if(!(in>>n.a>>n.b)||n.a>=i||n.b>=i)throw std::runtime_error("field dependency");
                n.depth=std::max(nodes[n.a].depth,nodes[n.b].depth)+(n.op=='M');muls+=n.op=='M';
            }else throw std::runtime_error("field opcode");
            maximum=std::max(maximum,n.depth);nodes.push_back(n);
        }
        std::string trailing;if(in>>trailing||maximum!=1531||muls!=4589)throw std::runtime_error("field program closure");
        linear.resize(maximum+1);multiplications.resize(maximum+1);
        for(unsigned i=0;i<nodes.size();i++)(nodes[i].op=='M'?multiplications:linear)[nodes[i].depth].push_back(i);
    }
    FieldEngine::Handle evaluate(FieldEngine&f,const std::array<FieldEngine::Handle,257>&input)const{
        std::vector<FieldEngine::Handle>values(nodes.size());
        for(unsigned level=0;level<linear.size();level++){
            for(auto id:linear[level]){auto n=nodes[id];
                if(n.op=='C')values[id]=f.constant(n.constant);else if(n.op=='I')values[id]=input[n.a];else if(n.op=='A')values[id]=f.add(values[n.a],values[n.b]);else values[id]=f.sub(values[n.a],values[n.b]);
            }
            if(level+1<multiplications.size()){
                const auto&ids=multiplications[level+1];std::vector<FieldEngine::Handle>a,b;
                // A product with a PUBLIC constant operand is linear: same value,
                // no triple. The pinned program and its node count are unchanged.
                std::vector<unsigned>secret;
                for(auto id:ids){const auto&n=nodes[id];
                    if(nodes[n.a].op=='C')values[id]=f.scale(values[n.b],nodes[n.a].constant);
                    else if(nodes[n.b].op=='C')values[id]=f.scale(values[n.a],nodes[n.b].constant);
                    else{secret.push_back(id);a.push_back(values[n.a]);b.push_back(values[n.b]);}
                }
                if(!secret.empty()){auto out=f.mul(a,b);for(size_t i=0;i<secret.size();i++)values[secret[i]]=out[i];}
            }
        }
        f.check();return values.at(9436);
    }
};
}
