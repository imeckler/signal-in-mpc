// Real pinned StackedVector and CCD field objects, public local test values.
#include "NativeWorker.h"
#include <iostream>
using namespace tls_mpc_worker;
int main() {
    Machine<tls_mpc_worker::Share>::init_binary_domains(128,128);
    size_t slots=0;
    for(size_t width=1;width<=64;++width) {
        tls_mpc_worker::Bit bit;bit.resize_regs(width);
        for(size_t i=0;i<width;++i)
            bit.get_reg(i)=tls_mpc_worker::Bit::part_type(gf2n_long(1)<<(i+32));
        StackedVector<tls_mpc_worker::Bit> values(2,bit);
        values.push_stack();values.resize(3);
        for(auto& x:values)x=bit;
        values.push_stack();values.resize(4);
        for(auto& x:values)x=bit;
        // Hide live constructed objects through shrink and stack pops.
        values.resize(1);
        values.pop_stack({},SBIT);values.pop_stack({},SBIT);
        public_require(values.size()==2,"stack view changed unexpectedly");
        size_t visited=0;
        values.visit_full_storage([&](tls_mpc_worker::Bit& x) {
            public_require(x.get_regs().size()==width,"lost hidden register shape");
            wipe_bit_storage(x);++visited;slots+=width;
        });
        public_require(visited==9 && values.size()==2,"hidden backing objects missed");
        values.visit_full_storage([&](const tls_mpc_worker::Bit& x) {
            for(const auto& field:x.get_regs())
                public_require(field.is_zero(),"backing field not wiped");
        });
        // Full visitation must preserve stack/view state for subsequent use.
        values.push_stack();values.resize(7);
        public_require(values.size()==7,"cannot reuse cleaned stack");
        for(const auto& x:values)for(const auto& field:x.get_regs())
            public_require(field.is_zero(),"hidden field resurrected");
        values.pop_stack({},SBIT);
        for(const auto& field:bit.get_regs())
            public_require(!field.is_zero(),"independent input was wiped");
    }
    std::cout<<"stacked storage passed: 64 packed widths; "<<slots
             <<" fields; hidden nested frames, shrink, pop, reuse; no MPC execution\n";
}
