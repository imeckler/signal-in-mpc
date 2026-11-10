#pragma once
#include <emp-tool/ir/program.h>
#include <array>
#include <cstdint>
#include <stdexcept>
namespace emp_hybrid {
// Domain bit i is numeric2^i (NOT byte/MSB-first application wire order).
// Public c is authenticated canonical32LE; private r has255 numeric bits.
struct ModpBuilder {
    emp::circuit::BooleanProgram p;
    uint32_t zero,one;
    ModpBuilder(){p.num_inputs=255;p.num_wires=255;zero=gate(emp::circuit::Op::Xor,0,0);one=gate(emp::circuit::Op::Not,zero);}
    uint32_t gate(emp::circuit::Op op,uint32_t a=0,uint32_t b=0){auto out=p.num_wires++;p.gates.push_back({a,b,out,op});return out;}
    uint32_t x(uint32_t a,uint32_t b){if(a==b)return zero;if(a==zero)return b;if(b==zero)return a;if(a==one)return n(b);if(b==one)return n(a);return gate(emp::circuit::Op::Xor,a,b);}
    uint32_t a(uint32_t x,uint32_t y){if(x==zero||y==zero)return zero;if(x==one)return y;if(y==one||x==y)return x;return gate(emp::circuit::Op::And,x,y);}
    uint32_t n(uint32_t x){if(x==zero)return one;if(x==one)return zero;return gate(emp::circuit::Op::Not,x);}
    std::array<uint32_t,256> add(const std::array<uint32_t,256>&x,const std::array<uint32_t,256>&y,uint32_t carry,uint32_t&last){
        std::array<uint32_t,256>out{};
        for(unsigned i=0;i<256;i++){auto t=this->x(x[i],y[i]);out[i]=this->x(t,carry);carry=this->x(a(x[i],y[i]),a(t,carry));}
        last=carry;return out;
    }
    std::array<uint32_t,256> negative_p(){
        // Two's complement -p mod2^256 =2^255+19.
        std::array<uint32_t,256>v{};for(unsigned i=0;i<256;i++)v[i]=(i==255||i==4||i==1||i==0)?one:zero;return v;
    }
    std::array<uint32_t,256> mask(){std::array<uint32_t,256>v{};for(unsigned i=0;i<255;i++)v[i]=i;v[255]=zero;return v;}
};
inline emp::circuit::BooleanProgram range_program(){
    ModpBuilder b;uint32_t no_borrow;b.add(b.mask(),b.negative_p(),b.zero,no_borrow);
    b.p.outputs={b.n(no_borrow)};return b.p; //1 iff0<=r<p.
}
inline emp::circuit::BooleanProgram modp_program(const std::array<uint8_t,32>&c){
    // Canonical c<p is PUBLIC and must be rejected before circuit execution.
    constexpr std::array<uint8_t,32> prime=[](){std::array<uint8_t,32>p{};p.fill(255);p[0]=237;p[31]=127;return p;}();
    bool less=false;for(int i=31;i>=0;i--)if(c[i]!=prime[i]){less=c[i]<prime[i];break;}
    if(!less)throw std::invalid_argument("noncanonical public field mask");
    ModpBuilder b;std::array<uint32_t,256>pub{};for(unsigned i=0;i<256;i++)pub[i]=((c[i/8]>>(i%8))&1)?b.one:b.zero;
    uint32_t carry;auto sum=b.add(b.mask(),pub,b.zero,carry);
    uint32_t no_borrow;auto reduced=b.add(sum,b.negative_p(),b.zero,no_borrow);
    for(unsigned i=0;i<255;i++)b.p.outputs.push_back(b.x(sum[i],b.a(no_borrow,b.x(sum[i],reduced[i]))));
    return b.p;
}
}
