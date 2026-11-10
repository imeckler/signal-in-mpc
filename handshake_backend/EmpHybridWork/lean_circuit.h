#pragma once
// Loader for Boolean circuits exported from Lean (TlsMpc/WordMask.lean via
// lower_word_circuits.py). The file is read once, its SHA-256 is compared with
// the pin generated alongside it, and the same bytes are parsed. No gate logic
// is written here; `parallel` only places k disjoint copies side by side.
#include <emp-tool/ir/program.h>
#include <openssl/sha.h>
#include <array>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
namespace emp_hybrid {
class LeanCircuit {
    struct Gate {char op;uint32_t a,b;};
    uint32_t inputs=0;std::vector<Gate>gates;std::vector<uint32_t>outputs;
public:
    LeanCircuit(const std::string&path,const char*expected_sha){
        // Read once into memory (bounded), then hash and parse those same bytes.
        constexpr std::streamoff limit=std::streamoff(1)<<31;
        std::ifstream file(path,std::ios::binary|std::ios::ate);if(!file)throw std::runtime_error("lean circuit file");
        const std::streamoff length=file.tellg();if(length<=0||length>limit)throw std::runtime_error("lean circuit size");
        std::string bytes(size_t(length),'\0');file.seekg(0);file.read(bytes.data(),length);
        if(file.gcount()!=length||file.peek()!=std::char_traits<char>::eof())throw std::runtime_error("lean circuit read");
        std::array<uint8_t,32>digest{};SHA256(reinterpret_cast<const uint8_t*>(bytes.data()),bytes.size(),digest.data());
        const char*hex="0123456789abcdef";std::string encoded;for(auto b:digest){encoded+=hex[b>>4];encoded+=hex[b&15];}
        if(encoded!=expected_sha)throw std::runtime_error("lean circuit identity");
        std::istringstream in(bytes);std::string magic;uint32_t count,width;
        if(!(in>>magic>>inputs>>count>>width)||magic!="EMP_HYBRID_BOOL_V1"||!inputs||!width)throw std::runtime_error("lean circuit profile");
        gates.reserve(count);
        for(uint32_t i=0;i<count;i++){
            Gate g{};if(!(in>>g.op))throw std::runtime_error("lean circuit row");
            if(g.op=='N'){if(!(in>>g.a))throw std::runtime_error("lean circuit operand");g.b=0;}
            else if(g.op=='A'||g.op=='X'){if(!(in>>g.a>>g.b))throw std::runtime_error("lean circuit operand");}
            else throw std::runtime_error("lean circuit opcode");
            if(g.a>=inputs+i||g.b>=inputs+i)throw std::runtime_error("lean circuit dependency");
            gates.push_back(g);
        }
        std::string tag;if(!(in>>tag)||tag!="O")throw std::runtime_error("lean circuit outputs");
        for(uint32_t i=0;i<width;i++){uint32_t w;if(!(in>>w)||w>=inputs+count)throw std::runtime_error("lean circuit output");outputs.push_back(w);}
        std::string trailing;if(in>>trailing)throw std::runtime_error("lean circuit trailing data");
    }
    uint32_t input_bits()const{return inputs;}
    uint32_t output_bits()const{return outputs.size();}
    // k independent copies: copy j reads inputs [j*inputs,(j+1)*inputs) and
    // writes outputs [j*width,(j+1)*width).
    emp::circuit::BooleanProgram parallel(uint32_t k)const{
        emp::circuit::BooleanProgram p;p.num_inputs=k*inputs;p.num_wires=p.num_inputs;
        for(uint32_t j=0;j<k;j++){
            const uint32_t base=p.num_wires;
            auto map=[&](uint32_t w){return w<inputs?j*inputs+w:base+(w-inputs);};
            for(auto&g:gates){
                auto op=g.op=='A'?emp::circuit::Op::And:g.op=='X'?emp::circuit::Op::Xor:emp::circuit::Op::Not;
                p.gates.push_back({map(g.a),g.op=='N'?0u:map(g.b),p.num_wires++,op});
            }
            for(auto w:outputs)p.outputs.push_back(map(w));
        }
        return p;
    }
};
}
