// Optional synthetic benchmark ONLY: three parties/one corruption/statistical40.
// Not a production profile and not a128-bit security claim.
#include "GC/ShareParty.h"
#include "GC/ShareParty.hpp"
#include "GC/ShareSecret.hpp"
#include "GC/MaliciousRepSecret.h"
#include "GC/RepPrep.h"
#include "GC/Machine.hpp"
#include "GC/Processor.hpp"
#include "GC/Program.hpp"
#include "GC/Thread.hpp"
#include "GC/ThreadMaster.hpp"
#include "GC/RepPrep.hpp"
#include "Processor/Instruction.hpp"
#include "Protocols/MaliciousRepMC.hpp"
#include "Protocols/MAC_Check_Base.hpp"
#include "Protocols/Beaver.hpp"
#include "../BackendPackingWork/emit_backend_totals.h"
int main(int argc,const char**argv){
 unsigned count=0;
 for(int i=1;i<argc;++i){std::string token(argv[i]);
  if(token=="-S"){if(++count!=1||i+1>=argc||std::string(argv[++i])!="40")throw std::runtime_error("benchmark requires explicit statistical40");}
  else if(token.rfind("-S",0)==0||token.rfind("--security",0)==0)throw std::runtime_error("unsupported security spelling");
 }
 if(count!=1)throw std::runtime_error("benchmark requires explicit statistical40");
 GC::simple_binary_main<GC::MaliciousRepSecret>(argc,argv);
 emit_backend_totals("rep3-stat40-benchmark-only");
}
