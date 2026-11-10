#include "modp_program.h"
#include <boost/multiprecision/cpp_int.hpp>
#include <iostream>
#include <vector>
using boost::multiprecision::cpp_int;
static std::vector<bool> eval(const emp::circuit::BooleanProgram&p,cpp_int input){
    std::vector<bool>w(p.num_wires);for(unsigned i=0;i<255;i++)w[i]=bool((input>>i)&1);
    using emp::circuit::Op;
    for(auto g:p.gates)switch(g.op){case Op::And:w[g.out]=w[g.in0]&w[g.in1];break;case Op::Xor:w[g.out]=w[g.in0]^w[g.in1];break;case Op::Not:w[g.out]=!w[g.in0];break;case Op::Const0:w[g.out]=false;break;case Op::Const1:w[g.out]=true;break;}
    std::vector<bool>out;for(auto id:p.outputs)out.push_back(w[id]);return out;
}
int main(){
    auto range=emp_hybrid::range_program();std::string rhex,chex;
    while(std::cin>>rhex>>chex){cpp_int r("0x"+rhex),c("0x"+chex);std::array<uint8_t,32>bytes{};for(unsigned i=0;i<32;i++)bytes[i]=uint8_t((c>>(8*i))&255);
        auto p=emp_hybrid::modp_program(bytes);auto result=eval(p,r);cpp_int value=0;for(unsigned i=0;i<255;i++)if(result[i])value|=cpp_int(1)<<i;
        std::cout<<eval(range,r)[0]<<" "<<std::hex<<value<<"\n";
    }
    std::array<uint8_t,32>invalid{};invalid.fill(255);bool rejected=false;try{emp_hybrid::modp_program(invalid);}catch(const std::invalid_argument&){rejected=true;}if(!rejected)return 1;
}
