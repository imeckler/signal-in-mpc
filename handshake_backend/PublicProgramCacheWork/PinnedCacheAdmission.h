#pragma once
#include "../PinnedPrograms.h"
#include "PinnedPublicCode.h"
namespace tls_mpc_worker {
// Candidate embedding adapter. The canonical PinnedPrograms still validates
// the exact descriptor/closure; this adds no untyped RPC or default provider.
class PinnedCacheAdmission {
 PinnedPrograms pinned;std::map<std::string,std::string> files;
public:
 explicit PinnedCacheAdmission(const std::string&manifest):pinned(manifest){
  std::ifstream input(manifest);std::string line;std::getline(input,line);
  while(std::getline(input,line))files.emplace(line.substr(65),line.substr(0,64));
 }
 const PinnedPrograms& programs()const{return pinned;}
 template<class Machine>void run(Machine&machine,const std::string&name,FunctionArgument&result,std::vector<FunctionArgument>&args)const{
  std::string descriptor="Programs/Functions/"+name;
  for(auto&arg:args)descriptor+="-"+arg.get_type_string();
  auto closure=pinned.verify_descriptor(descriptor);
  std::map<std::string,std::string> admitted;
  for(const auto&path:closure)admitted.emplace(path,files.at(path));
  std::string identity=name+"\n";
  for(auto&arg:args)identity+=arg.get_type_string()+"\n";
  for(const auto&entry:admitted)identity+=entry.second+" "+entry.first+"\n";
  machine.run_function_pinned(name,result,args,tls_public_code::sha256(identity),admitted);
 }
};
}
