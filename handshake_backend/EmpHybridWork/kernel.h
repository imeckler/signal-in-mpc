#pragma once
// Worker kernels: Lean circuits with a named field layout (TlsMpc/HybridKernels.lean).
//
// The runtime's whole interface to a circuit is: bind a wire bundle to each
// named input, receive a wire bundle per named output, and open an output only
// if Lean marked it as one that may be opened. Field order, offsets, widths and
// the open/private marking all come from the layout Lean emitted; both parties
// compare the circuit pin and the layout pin before first use. Nothing in this
// file or its callers knows where a field sits inside a circuit.
#include "dyn_session.h"
#include "dabit_generator.h"
#include "profile.h"
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <map>
#include <memory>
#include <sstream>
namespace emp_hybrid {
using Values=std::map<std::string,Wires>;
using Binding=std::vector<std::pair<std::string,const Wires*>>;
inline std::vector<uint8_t> byte_bits(const std::vector<uint8_t>&bytes){std::vector<uint8_t>out;out.reserve(8*bytes.size());for(auto b:bytes)for(unsigned i=0;i<8;i++)out.push_back((b>>i)&1);return out;}
inline std::vector<uint8_t> bits_bytes(const std::vector<uint8_t>&bits){if(bits.size()%8)throw std::runtime_error("whole bytes expected");std::vector<uint8_t>out(bits.size()/8);for(size_t i=0;i<bits.size();i++)if(bits[i])out[i/8]|=uint8_t(1u<<(i%8));return out;}
class Kernel {
    // opened: 0 private, 1 public, 2 garbling party only, 3 evaluating party only (as marked in Lean).
    struct Field {std::string name;size_t bits;int opened;};
    LeanCircuit circuit;std::vector<Field>inputs,outputs;
public:
    std::string label;   // for the profile only
    Kernel(const std::string&path,const std::string&sha,const std::string&layout_path,const std::string&layout_sha):circuit(path,sha.c_str()){
        std::ifstream in(layout_path,std::ios::binary);std::string text((std::istreambuf_iterator<char>(in)),{});
        std::array<uint8_t,32>digest{};SHA256(reinterpret_cast<const uint8_t*>(text.data()),text.size(),digest.data());
        std::string hex;const char*digits="0123456789abcdef";for(auto b:digest){hex+=digits[b>>4];hex+=digits[b&15];}
        if(hex!=layout_sha)throw std::runtime_error("kernel layout pin");
        std::istringstream rows(text);std::string line;if(!std::getline(rows,line)||line!="EMP_HYBRID_KERNEL_LAYOUT_V1")throw std::runtime_error("kernel layout format");
        size_t in_bits=0,out_bits=0;
        while(std::getline(rows,line)){
            std::istringstream row(line);std::string kind,name;size_t bits=0;int opened=0;
            if(!(row>>kind>>name>>bits))throw std::runtime_error("kernel layout row");   // an input may be empty (e.g. no client certificate)
            if(kind=="I"){inputs.push_back({name,bits,0});in_bits+=bits;}
            else if(kind=="O"&&(row>>opened)&&opened>=0&&opened<=3){outputs.push_back({name,bits,opened});out_bits+=bits;}
            else throw std::runtime_error("kernel layout row");
        }
        if(in_bits!=circuit.input_bits()||out_bits!=circuit.output_bits())throw std::runtime_error("kernel layout shape");
    }
    // The width Lean declared for an input.
    size_t input_bits(const std::string&name)const{for(auto&field:inputs)if(field.name==name)return field.bits;throw std::runtime_error("kernel input "+name);}
    // Every input field exactly once, by name, with the width Lean declared.
    Values run(DynSession&s,const Binding&bound)const{
        ProfileScope scope("boolean circuit: "+label);
        if(bound.size()!=inputs.size())throw std::runtime_error("kernel binding count");
        std::vector<const Wires*>ordered;
        for(auto&field:inputs){
            const Wires*found=nullptr;
            for(auto&b:bound)if(b.first==field.name){if(found)throw std::runtime_error("kernel field bound twice");found=b.second;}
            if(!found||found->size()!=field.bits)throw std::runtime_error("kernel input "+field.name);
            ordered.push_back(found);
        }
        auto all=s.run(circuit,DynSession::concat(ordered));Values out;size_t at=0;
        for(auto&field:outputs){out[field.name]=all.slice(at,at+field.bits);at+=field.bits;}
        return out;
    }
    // Opens an output only if Lean marked it as one that may be opened.
    std::vector<uint8_t> open(DynSession&s,const Values&out,const std::string&name)const{
        ProfileScope scope("open boolean outputs");
        for(auto&field:outputs)if(field.name==name){
            if(field.opened!=1)throw std::runtime_error("kernel output "+name+" is not public");
            return bits_bytes(s.open(out.at(name)));
        }
        throw std::runtime_error("kernel output "+name);
    }
    // Opens an output to one party only, and only if Lean marked it for that party.
    // The other party's return value carries no information.
    std::vector<uint8_t> open_to(DynSession&s,const Values&out,const std::string&name,int party)const{
        for(auto&field:outputs)if(field.name==name){
            if(field.opened!=(party==emp::ALICE?2:3))throw std::runtime_error("kernel output "+name+" is not for that party");
            return bits_bytes(s.open_to(out.at(name),party));
        }
        throw std::runtime_error("kernel output "+name);
    }
};
// Kernels are produced on demand by the Lean emitter through the cache script;
// both parties compare circuit and layout pins before a kernel is used.
class KernelCache {
    std::string script;Challenge&channel;std::map<std::string,std::unique_ptr<Kernel>>loaded;
public:
    KernelCache(std::string s,Challenge&c):script(std::move(s)),channel(c){}
    // A kernel that is already in the cache, found the way circuit_cache.py finds it (the
    // directory named by the emitter binary's hash, the files named by the arguments, the
    // pins from the record written with them) without starting an interpreter, which cost
    // about 90 ms per kernel. Anything missing or unexpected returns false and the script is
    // asked instead. Nothing is trusted here: Kernel checks both files against the pins, and
    // the parties compare the pins, exactly as for the script's reply.
    bool cached(const std::string&arguments,std::string&path,std::string&sha,std::string&layout,std::string&layout_sha)const{
        namespace fs=std::filesystem;
        try{
            const fs::path root=fs::path(script).parent_path().parent_path().parent_path();
            std::ifstream binary(root/".lake/build/bin/flat_kernel_emitter",std::ios::binary);if(!binary)return false;
            const std::string bytes((std::istreambuf_iterator<char>(binary)),{});if(bytes.empty())return false;
            std::array<uint8_t,32>digest{};SHA256(reinterpret_cast<const uint8_t*>(bytes.data()),bytes.size(),digest.data());
            std::string hex;const char*digits="0123456789abcdef";for(unsigned i=0;i<8;i++){hex+=digits[digest[i]>>4];hex+=digits[digest[i]&15];}
            std::string name="kernel-"+arguments;for(auto&ch:name)if(ch==' ')ch='-';
            const fs::path directory=root/".deps/emp-hybrid-word-v1/cache"/("lean-"+hex);
            std::ifstream record(directory/(name+".json"),std::ios::binary);if(!record)return false;
            const std::string text((std::istreambuf_iterator<char>(record)),{});
            auto field=[&](const std::string&key,std::string&out){
                const std::string start="\""+key+"\": \"";const auto at=text.find(start);if(at==std::string::npos||text.size()<at+start.size()+65)return false;
                out=text.substr(at+start.size(),64);
                return text[at+start.size()+64]=='"'&&out.find_first_not_of("0123456789abcdef")==std::string::npos&&text.find(start,at+1)==std::string::npos;
            };
            if(!field("sha256",sha)||!field("layout_sha256",layout_sha))return false;
            const fs::path flat=directory/(name+".flat"),fields=directory/(name+".layout");
            if(!fs::is_regular_file(flat)||!fs::is_regular_file(fields))return false;
            path=flat.string();layout=fields.string();
            // The record of what was asked for, as the script keeps it (a harness produces these ahead of the next run).
            if(const char*log=std::getenv("CIRCUIT_CACHE_LOG")){std::ofstream out(log,std::ios::app);out<<"kernel "<<arguments<<"\n";}
            return true;
        }catch(...){return false;}
    }
    const Kernel&get(const std::string&arguments){
        auto it=loaded.find(arguments);if(it!=loaded.end())return *it->second;
        ProfileScope scope("circuit load (cache lookup, read, pin comparison)");
        for(char ch:arguments)if(!(std::isalnum(static_cast<unsigned char>(ch))||ch=='-'||ch==' '))throw std::runtime_error("kernel arguments");
        std::string path,sha,layout,layout_sha;
        if(!cached(arguments,path,sha,layout,layout_sha)){
            std::string command="python3 '"+script+"' kernel "+arguments;FILE*pipe=popen(command.c_str(),"r");if(!pipe)throw std::runtime_error("kernel cache launch");
            char buffer[4096];std::string line;while(fgets(buffer,sizeof buffer,pipe))line+=buffer;if(pclose(pipe)!=0)throw std::runtime_error("kernel cache failed");
            std::istringstream in(line);size_t inputs,outputs;
            if(!(in>>path>>sha>>inputs>>outputs>>layout>>layout_sha))throw std::runtime_error("kernel cache reply");
        }
        if(sha.size()!=64||layout_sha.size()!=64)throw std::runtime_error("kernel cache reply");
        std::array<uint8_t,128>mine{},peer{};std::copy(sha.begin(),sha.end(),mine.begin());std::copy(layout_sha.begin(),layout_sha.end(),mine.begin()+64);
        channel.transfer(mine.data(),peer.data(),128);if(mine!=peer)throw std::runtime_error("kernel pin disagreement");
        auto&kernel=*(loaded[arguments]=std::make_unique<Kernel>(path,sha,layout,layout_sha));
        kernel.label=arguments.substr(0,arguments.find(' '));return kernel;
    }
};
}
