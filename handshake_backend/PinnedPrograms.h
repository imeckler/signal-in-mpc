#pragma once
#include "PublicProtocol.h"
#include "Processor/FunctionArgument.h"
#include <sodium.h>
#include <fstream>
#include <sstream>
#include <map>
#include <set>
#include <array>
#include <algorithm>
namespace tls_mpc_worker {
class PinnedPrograms {
    std::map<std::string, std::string> files;
    PublicBytes manifest_digest;
    static std::string hex(const PublicBytes& bytes) {
        const char* digits="0123456789abcdef";std::string out;
        for(auto b:bytes) {out+=digits[b>>4];out+=digits[b&15];}return out;
    }
    static bool safe_name(const std::string& name) {
        return !name.empty() && name.size()<=512 && name.find("..") == std::string::npos &&
            std::all_of(name.begin(),name.end(),[](unsigned char c){return std::isalnum(c)||c=='_'||c=='-'||c=='.';});
    }
    static bool safe_path(const std::string& path) {
        if(path.size()>2048 || path.find("..")!=std::string::npos || path.find('\\')!=std::string::npos) return false;
        for(auto prefix:{"Programs/Functions/","Programs/Schedules/","Programs/Bytecode/","Worker-Public/"}) {
            std::string p=prefix;
            if(path.rfind(p,0)==0) {
                auto tail=path.substr(p.size());return !tail.empty() && tail.find('/')==std::string::npos &&
                    std::all_of(tail.begin(),tail.end(),[](unsigned char c){return std::isalnum(c)||std::string("_-.:[]").find(c)!=std::string::npos;});
            }
        }return false;
    }
    static PublicBytes hash_file(const std::string& path) {
        std::ifstream input(path,std::ios::binary);public_require(bool(input),"pinned file unavailable");
        crypto_hash_sha256_state state;crypto_hash_sha256_init(&state);
        std::array<char,65536> buffer;size_t total=0;
        while(input) {input.read(buffer.data(),buffer.size());auto n=input.gcount();total+=n;
            public_require(total<=size_t(1024)*1024*1024,"pinned file too large");
            crypto_hash_sha256_update(&state,reinterpret_cast<const unsigned char*>(buffer.data()),n);}
        public_require(input.eof(),"pinned file read failed");PublicBytes out(32);crypto_hash_sha256_final(&state,out.data());return out;
    }
    void verify_file(const std::string& path) const {
        public_require(safe_path(path),"unsafe pinned path");auto found=files.find(path);
        public_require(found!=files.end(),"required file absent from pinned manifest");
        public_require(hex(hash_file(path))==found->second,"pinned file digest mismatch");
    }
public:
    explicit PinnedPrograms(const std::string& manifest) {
        public_require(sodium_init()>=0,"hash initialization failed");
        std::ifstream input(manifest,std::ios::binary);public_require(bool(input),"manifest unavailable");
        std::string text; std::array<char,4096> buffer;
        while(input) {input.read(buffer.data(),buffer.size());text.append(buffer.data(),input.gcount());public_require(text.size()<=4*1024*1024,"manifest too large");}
        public_require(input.eof(),"manifest read failed");
        manifest_digest.resize(32);crypto_hash_sha256(manifest_digest.data(),reinterpret_cast<const unsigned char*>(text.data()),text.size());
        std::istringstream lines(text);std::string line;
        public_require(bool(std::getline(lines,line))&&line=="tls-mpc-pinned-files-v1","unsupported manifest");
        while(std::getline(lines,line)) {
            public_require(line.size()>65&&line[64]==' ',"malformed manifest line");
            auto digest=line.substr(0,64), path=line.substr(65);
            public_require(std::all_of(digest.begin(),digest.end(),[](char c){return (c>='0'&&c<='9')||(c>='a'&&c<='f');})&&safe_path(path),"invalid manifest entry");
            public_require(files.emplace(path,digest).second,"duplicate manifest file");
            public_require(files.size()<=4096,"too many manifest entries");
        }
        public_require(!files.empty(),"empty manifest");
        for(const auto& [path,_]:files) verify_file(path);
    }
    const PublicBytes& digest() const {return manifest_digest;}
    bool contains(const std::string& path) const {return files.count(path)!=0;}
    void verify_public(const std::string& path) const {
        public_require(path.rfind("Worker-Public/",0)==0,"not a pinned public tool/config");
        verify_file(path);
    }
    // Append only AFTER the caller collectively agrees this extension's hash.
    // The boot digest stays fixed; each extension is separately context-bound.
    void append(const PinnedPrograms& extension) {
        for(const auto& [path,hash]:extension.files) {
            auto old=files.find(path);
            public_require(old==files.end()||old->second==hash,"pinned extension replaces an existing file");
            extension.verify_file(path);
        }
        files.insert(extension.files.begin(),extension.files.end());
    }
    std::set<std::string> verify_descriptor(const std::string& path) const {
        public_require(path.rfind("Programs/Functions/",0)==0,"invalid function descriptor path");
        verify_file(path);
        std::set<std::string> closure{path};
        std::ifstream function(path);std::string program;function>>program;
        public_require(safe_name(program),"unsafe function program name");
        auto schedule="Programs/Schedules/"+program+".sch";verify_file(schedule);closure.insert(schedule);
        std::ifstream input(schedule);size_t threads=0,tapes=0;input>>threads>>tapes;
        public_require(bool(input)&&threads>0&&threads<=64&&tapes>0&&tapes<=4096,"invalid pinned schedule dimensions");
        std::set<std::string> seen;
        for(size_t i=0;i<tapes;++i) {
            std::string token;input>>token;auto colon=token.find(':');
            public_require(bool(input)&&colon!=std::string::npos,"invalid pinned tape entry");
            auto tape=token.substr(0,colon);public_require(safe_name(tape)&&seen.insert(tape).second,"invalid tape name");
            auto file="Programs/Bytecode/"+tape+".bc";verify_file(file);closure.insert(file);
        }
        return closure;
    }
    void verify_exact_closure(const std::string& descriptor) const {
        auto closure=verify_descriptor(descriptor);
        public_require(closure.size()==files.size(),"unrelated file in program extension");
    }
    void verify_function(const std::string& name,std::vector<FunctionArgument>& arguments) const {
        public_require(safe_name(name),"unsafe exported function name");
        auto path="Programs/Functions/"+name;
        for(auto& arg:arguments) path+="-"+arg.get_type_string();
        verify_descriptor(path);
    }
};
}
