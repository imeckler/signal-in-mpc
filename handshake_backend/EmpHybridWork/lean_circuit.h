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
        // Whitespace-separated tokens, read directly from the hashed bytes (the stream
        // extractors took most of a worker's start-up time on the 100 MB circuits). Stricter
        // than the extractors: a number is decimal digits only and must fit 32 bits.
        const char*at=bytes.data(),*const end=at+bytes.size();
        auto skip=[&]{while(at<end&&(*at==' '||*at=='\n'||*at=='\r'||*at=='\t'))at++;};
        auto number=[&](uint32_t&out){
            skip();if(at>=end||*at<'0'||*at>'9')return false;
            uint64_t v=0;while(at<end&&*at>='0'&&*at<='9'){v=v*10+uint64_t(*at-'0');if(v>0xffffffffull)return false;at++;}
            out=uint32_t(v);return true;
        };
        auto word=[&]{skip();const char*start=at;while(at<end&&!(*at==' '||*at=='\n'||*at=='\r'||*at=='\t'))at++;return std::string(start,at);};
        uint32_t count=0,width=0;
        if(word()!="EMP_HYBRID_BOOL_V1"||!number(inputs)||!number(count)||!number(width)||!inputs||!width)throw std::runtime_error("lean circuit profile");
        if(uint64_t(inputs)+count>0xffffffffull)throw std::runtime_error("lean circuit profile");
        gates.reserve(count);
        for(uint32_t i=0;i<count;i++){
            Gate g{};skip();if(at>=end)throw std::runtime_error("lean circuit row");g.op=*at++;
            if(g.op=='N'){if(!number(g.a))throw std::runtime_error("lean circuit operand");g.b=0;}
            else if(g.op=='A'||g.op=='X'){if(!number(g.a)||!number(g.b))throw std::runtime_error("lean circuit operand");}
            else throw std::runtime_error("lean circuit opcode");
            if(g.a>=inputs+i||g.b>=inputs+i)throw std::runtime_error("lean circuit dependency");
            gates.push_back(g);
        }
        if(word()!="O")throw std::runtime_error("lean circuit outputs");
        outputs.reserve(width);
        for(uint32_t i=0;i<width;i++){uint32_t w;if(!number(w)||w>=inputs+count)throw std::runtime_error("lean circuit output");outputs.push_back(w);}
        skip();if(at!=end)throw std::runtime_error("lean circuit trailing data");
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
