#include "BootstrapOrder.h"
#include <iostream>
using namespace signal_mpc::recovery;
int main(){unsigned checks=0;
 for(unsigned fail=0;fail<=4;++fail){BootstrapOrder order;std::vector<unsigned> trace;bool returned=false;
  auto load=[&](){trace.push_back(1);require(fail!=1,"load reject");return QuarantinedEvaluations(SecretBytes(16));};
  auto ready=[&](bool local){trace.push_back(2);require(local==(fail!=1),"wrong readiness");return fail!=2&&local;};
  auto import=[&](QuarantinedEvaluations q){trace.push_back(3);require(q.bit_count()==1,"bad quarantine");require(fail!=3,"import reject");return SecretBytes(1);};
  auto retire=[&](){trace.push_back(4);require(fail!=4,"barrier reject");};
  try{auto result=order.resolve(load,ready,import,retire);returned=result.size()==1;}catch(const std::runtime_error&){}
  require(returned==(fail==0)&&order.complete()==returned,"bootstrap fail-open");++checks;
  std::vector<unsigned> expected=fail==1||fail==2?std::vector<unsigned>{1,2}:fail==3?std::vector<unsigned>{1,2,3}:std::vector<unsigned>{1,2,3,4};
  require(trace==expected,"bootstrap stage order");++checks;
  bool retry=false;try{auto result=order.resolve(load,ready,import,retire);retry=true;}catch(const std::runtime_error&){}require(!retry,"bootstrap retry reused attempt");++checks;
 }
 std::cout<<checks<<" bootstrap order checks passed\n";
}
