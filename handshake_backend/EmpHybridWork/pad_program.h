#pragma once
#include <emp-tool/ir/program.h>
#include <algorithm>
#include <cstdint>
#include <limits>
#include <stdexcept>

namespace emp_hybrid {
// Public code only. Caller supplies two NEW independent secret bits per dummy
// AND. Keep appended outputs live through run_program's authentication checks;
// afterwards retain exactly original_outputs and discard the dummy tail.
struct PaddedProgram {
    emp::circuit::BooleanProgram program;
    uint32_t original_inputs, original_outputs, dummy_inputs, dummy_outputs;
};
inline PaddedProgram pad_program(const emp::circuit::BooleanProgram& source,uint32_t fixed_dummy=0) {
    using namespace emp::circuit;
    if(source.num_wires!=source.num_inputs+source.gates.size())throw std::invalid_argument("dense SSA required");
    uint32_t real=0;
    for(size_t i=0;i<source.gates.size();i++) {
        const auto&g=source.gates[i];
        if(g.out!=source.num_inputs+i)throw std::invalid_argument("gate ordering");
        bool unary=g.op==Op::Not, constant=g.op==Op::Const0||g.op==Op::Const1;
        if(!constant&&(g.in0>=g.out||(!unary&&g.in1>=g.out)))throw std::invalid_argument("gate dependency");
        if(g.op==Op::And)real++;
        else if(g.op!=Op::Xor&&!unary&&!constant)throw std::invalid_argument("unknown gate");
    }
    for(auto w:source.outputs)if(w>=source.num_wires)throw std::invalid_argument("output range");
    if(fixed_dummy>1024)throw std::invalid_argument("dummy budget");
    uint32_t d=std::max(real&&real<1024?1024-real:0,fixed_dummy);
    if(source.num_wires>std::numeric_limits<uint32_t>::max()-3*d)throw std::overflow_error("padded wire count");
    PaddedProgram result{source,source.num_inputs,uint32_t(source.outputs.size()),2*d,d};
    if(!d)return result;
    auto &p=result.program;
    auto remap=[&](uint32_t w){return w<source.num_inputs?w:w+2*d;};
    p.num_inputs+=2*d;p.num_wires+=3*d;
    for(auto &g:p.gates){
        if(g.op!=Op::Const0&&g.op!=Op::Const1){g.in0=remap(g.in0);if(g.op!=Op::Not)g.in1=remap(g.in1);}
        g.out+=2*d;
    }
    for(auto&w:p.outputs)w=remap(w);
    for(uint32_t i=0;i<d;i++) {
        uint32_t out=source.num_wires+2*d+i;
        p.gates.push_back({source.num_inputs+i,source.num_inputs+d+i,out,Op::And});
        p.outputs.push_back(out);
    }
    return result;
}
} // namespace emp_hybrid
