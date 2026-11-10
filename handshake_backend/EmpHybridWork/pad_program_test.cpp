#include "pad_program.h"
#include <cassert>
#include <iostream>
#include <random>
using namespace emp::circuit;
static std::vector<bool> eval(const BooleanProgram&p,const std::vector<bool>&input){
    assert(input.size()==p.num_inputs);std::vector<bool>w=input;w.resize(p.num_wires);
    for(auto g:p.gates)switch(g.op){
        case Op::And:w[g.out]=w[g.in0]&w[g.in1];break;
        case Op::Xor:w[g.out]=w[g.in0]^w[g.in1];break;
        case Op::Not:w[g.out]=!w[g.in0];break;
        case Op::Const0:w[g.out]=false;break;
        case Op::Const1:w[g.out]=true;break;
    }
    std::vector<bool>out;for(auto i:p.outputs)out.push_back(w[i]);return out;
}
int main(){
    std::mt19937 gen(991);unsigned checks=0;
    for(unsigned n:{0,1,2,15,1023,1024,1025}) for(unsigned fixed:{0,1024}) {
        BooleanProgram p;p.num_inputs=4;p.num_wires=4;
        auto gate=[&](Op op,unsigned a,unsigned b=0){auto out=p.num_wires++;p.gates.push_back({a,b,out,op});return out;};
        auto z=gate(Op::Const0,0),one=gate(Op::Const1,0);
        auto w=gate(Op::Xor,0,1);
        for(unsigned i=0;i<n;i++)w=gate(Op::And,w,2+i%2);
        auto v=gate(Op::Not,w);p.outputs={w,v,0,z,one,w};
        auto padded=emp_hybrid::pad_program(p,fixed);
        assert(padded.dummy_outputs==std::max(n&&n<1024?1024-n:0,fixed));
        unsigned ands=0;for(auto g:padded.program.gates)ands+=g.op==Op::And;
        assert(ands==n+padded.dummy_outputs);
        for(unsigned input=0;input<16;input++)for(unsigned trial=0;trial<4;trial++){
            std::vector<bool>in;for(unsigned i=0;i<4;i++)in.push_back((input>>i)&1);
            auto expected=eval(p,in);
            for(unsigned i=0;i<padded.dummy_inputs;i++)in.push_back(gen()&1);
            auto actual=eval(padded.program,in);
            assert(std::equal(expected.begin(),expected.end(),actual.begin()));
            for(unsigned i=0;i<padded.dummy_outputs;i++)assert(actual[expected.size()+i]==(in[4+i]&in[4+padded.dummy_outputs+i]));
            checks++;
        }
    }
    BooleanProgram bad;bad.num_inputs=1;bad.num_wires=2;bad.gates.push_back({2,0,1,Op::And});
    bool rejected=false;try{emp_hybrid::pad_program(bad);}catch(const std::invalid_argument&){rejected=true;}assert(rejected);
    std::cout<<"{\"passed\":true,\"equivalence_cases\":"<<checks<<",\"malformed_rejected\":true}\n";
}
