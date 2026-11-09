// Public-only actual observed closure working-set stress. Not an execution
// trace, MPC test, network benchmark or application-throughput measurement.
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
struct Closure {bool producer;std::string key,descriptor,schedule;std::vector<std::string> tapes;std::map<std::string,std::string> pins;};
struct Image {std::vector<Program> programs;size_t bytes=sizeof(Image);std::string identity;};
static double clock_raw(){timespec t;clock_gettime(CLOCK_MONOTONIC_RAW,&t);return t.tv_sec+t.tv_nsec/1e9;}
int main(int argc,char**argv){
 if(argc!=2)return 2;if(sodium_init()<0)return 2;BaseMachine dummy;gf2n::init_field(128);
 std::ifstream trace(argv[1]);size_t count;trace>>count;if(!trace||count>256||count<2)return 2;std::vector<Closure> closures;size_t producer=0;
 for(size_t i=0;i<count;++i){Closure c;size_t tapes;trace>>c.producer>>c.key>>c.descriptor>>c.schedule>>tapes;if(!trace||tapes>4096)return 2;std::string digest;trace>>digest;c.pins[c.descriptor]=digest;trace>>digest;c.pins[c.schedule]=digest;for(size_t j=0;j<tapes;++j){std::string path;trace>>digest>>path;c.pins[path]=digest;c.tapes.push_back(path);}if(c.producer)producer=i;closures.push_back(std::move(c));}
 if(!trace||!closures[producer].producer)return 2;
 tls_public_code::ReservedCache<Image> cache(size_t(2048)*1024*1024,size_t(256)*1024*1024,16);size_t parses=0,producer_parses=0;
 auto load=[&](size_t index){auto&c=closures.at(index);auto start=clock_raw();for(const auto&pin:c.pins)tls_public_code::read(pin.first,c.pins);auto image=cache.take(c.key);bool hit=bool(image);
  if(!image){image=std::make_unique<Image>();for(const auto&path:c.tapes){image->programs.emplace_back(5);auto&p=image->programs.back();p.parse_pinned(path,c.pins);image->bytes+=p.public_storage_bytes();image->identity+=p.get_hash();}++parses;if(c.producer)++producer_parses;}
  auto identity=tls_public_code::sha256(image->identity);auto bytes=image->bytes;
  cache.put(c.key,std::move(image),bytes,c.producer);
  std::cout<<"SET_METRIC {\"index\":"<<index<<",\"producer\":"<<(c.producer?"true":"false")<<",\"hit\":"<<(hit?"true":"false")<<",\"seconds\":"<<std::setprecision(12)<<clock_raw()-start<<",\"accounted_bytes\":"<<bytes<<",\"retained_bytes\":"<<cache.retained_bytes()<<",\"parse_count\":"<<parses<<"}\n"<<std::flush;
  return identity;
 };
 auto original=load(producer);for(size_t i=0;i<count;++i)if(i!=producer)load(i);auto repeated=load(producer);
 if(producer_parses!=1||original!=repeated)return 1;
 rusage usage;getrusage(RUSAGE_SELF,&usage);
 std::cout<<"SET_RESULT {\"passed\":true,\"producer_parse_count\":"<<producer_parses<<",\"closure_count\":"<<count<<",\"cache_hits\":"<<cache.hits<<",\"evictions\":"<<cache.evictions<<",\"retained_accounted_bytes\":"<<cache.retained_bytes()<<",\"maxrss_bytes\":"<<usage.ru_maxrss<<",\"private_execution\":false}\n";
}
