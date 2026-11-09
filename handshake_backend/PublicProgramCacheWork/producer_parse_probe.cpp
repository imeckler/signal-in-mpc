// Public-only actual producer parser/cache resource probe: no parties, VM
// execution, inputs, preprocessing, keys, network or private state.
#include "Processor/Program.h"
#include "Processor/BaseMachine.h"
#include "Processor/Instruction.hpp"
#include "Math/gf2n.h"
#include "Tools/PublicCodeCache.h"
#include "Tools/PinnedPublicCode.h"
#include <sys/resource.h>
#include <time.h>
#include <iostream>
#include <iomanip>
struct Image {std::vector<Program> programs;size_t bytes=0;std::string identity;};
static double clock_raw(){timespec value;clock_gettime(CLOCK_MONOTONIC_RAW,&value);return value.tv_sec+value.tv_nsec/1e9;}
static std::string metadata(const Program&p){std::ostringstream out;out<<p.get_hash()<<":"<<p.size()<<":"<<p.writes_persistence<<":"<<p.usage_unknown();for(int type=0;type<MAX_REG_TYPE;++type)out<<":"<<p.num_reg(RegType(type))<<":"<<p.direct_mem(RegType(type));auto usage=p.get_offline_data_used();for(auto&values:usage.files)for(auto value:values)out<<":"<<value;return tls_public_code::sha256(out.str());}
int main(int argc,char**argv){
 if(argc!=5)return 2;if(sodium_init()<0)return 2;BaseMachine dummy;gf2n::init_field(128);
 std::map<std::string,std::string> pins{{argv[1],argv[2]},{argv[3],argv[4]}};
 tls_public_code::Cache<Image> cache(size_t(1024)*1024*1024,16);size_t parses=0;
 auto load=[&](const std::string&path){auto start=clock_raw();tls_public_code::read(path,pins);auto key=pins.at(path)+":public-parse-n5-current-runtime";auto image=cache.take(key);bool hit=bool(image);
  if(!image){image=std::make_unique<Image>();image->programs.emplace_back(5);image->programs.back().parse_pinned(path,pins);image->identity=metadata(image->programs.back());image->bytes=image->programs.back().public_storage_bytes();++parses;}
  auto seconds=clock_raw()-start;auto identity=image->identity;auto bytes=image->bytes;auto instructions=image->programs.back().size();
  cache.put(key,std::move(image),bytes);
  std::cout<<"PARSE_METRIC {\"hit\":"<<(hit?"true":"false")<<",\"seconds\":"<<std::setprecision(12)<<seconds<<",\"accounted_bytes\":"<<bytes<<",\"instructions\":"<<instructions<<",\"parse_count\":"<<parses<<"}\n"<<std::flush;
  return identity;
 };
 auto first=load(argv[1]);load(argv[3]);auto repeated=load(argv[1]);if(first!=repeated||parses!=2||cache.hits!=1)return 1;
 rusage usage;getrusage(RUSAGE_SELF,&usage);
 std::cout<<"PARSE_RESULT {\"passed\":true,\"retained_accounted_bytes\":"<<cache.retained_bytes()<<",\"maxrss_bytes\":"<<usage.ru_maxrss<<",\"private_execution\":false}\n";
}
