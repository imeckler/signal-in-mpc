#pragma once
#include "PinnedCacheAdmission.h"
#include "../BatchThroughputWork/NativeBatchService.h"
namespace tls_mpc_worker {
// Isolated candidate adapter: same pinned mixed-field+Boolean entry and exact
// shape checks as NativeBatchService, through the validated public-code cache.
class CachedBatchService {
 Machine<Share>& machine;Worker& allocation;const PinnedCacheAdmission& admission;
public:
 CachedBatchService(Machine<Share>&m,Worker&w,const PinnedCacheAdmission&p):machine(m),allocation(w),admission(p){}
 std::vector<Bits> evaluate(const std::vector<signal_mpc::VariableShape>&shapes,std::vector<Bits>inputs){
  if(shapes.empty()||shapes.size()!=inputs.size())throw std::runtime_error("invalid cached conversation batch dimensions");
  VariableBatchShape shape(shapes.front(),shapes.size());
  auto joined=allocation.allocate(0);
  for(size_t i=0;i<inputs.size();++i){
   if(shapes[i].descriptor()!=shape.single().descriptor()||inputs[i].size()!=shape.single().input_bytes()*8)throw std::runtime_error("cached conversation shape mismatch");
   joined.insert(joined.end(),inputs[i].begin(),inputs[i].end());inputs[i].clear();
  }
  auto output=allocation.allocate(shape.output_bits());std::vector<FunctionArgument>args={{1,joined.function_argument()},{1,output.function_argument()}};FunctionArgument ignored;
  admission.run(machine,shape.name(),ignored,args);
  std::vector<Bits> result;result.reserve(shape.count());auto width=shape.single().output_bytes()*8;
  for(size_t i=0;i<shape.count();++i)result.emplace_back(output.begin()+i*width,output.begin()+(i+1)*width);
  return result; // Caller still commits ALL selected states before release.
 }
};
}
