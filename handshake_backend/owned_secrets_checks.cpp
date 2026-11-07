// Instrumented storage only; verifies zeroing BEFORE object destruction,
// including copies, replacement and exceptions. No real secrets or MPC.
#include "OwnedSecrets.h"
#include <cassert>
#include <cstdint>
#include <iostream>
static size_t destroyed=0,dirty=0;
static int assignment_budget=-1;
struct Field {
    uint64_t value=0;
    bool tracked=false;
    static constexpr size_t N_BYTES=sizeof(value);
    const void* get_ptr() const {return &value;}
};
struct Part:Field {
    using open_type=Field;
    Part& operator=(const Part& source) {
        value=source.value;tracked=true;
        if(assignment_budget==0)throw std::runtime_error("injected field assignment failure");
        if(assignment_budget>0)--assignment_budget;
        return *this;
    }
    ~Part(){if(tracked){++destroyed;if(value)++dirty;}}
};
struct Bit {
    using part_type=Part;
    std::vector<Part> registers;
    auto& get_regs(){return registers;}
    const auto& get_regs() const{return registers;}
};
using Owned=tls_mpc_worker::OwnedBits<Bit>;
int main() {
    std::vector<Bit> row(1);row[0].registers.resize(3);
    for(auto& part:row[0].registers)part.value=0x123456789abcdefULL;
    {
        Owned a(4,row),b(a);
        a.wipe();for(auto& r:a)for(auto& p:r[0].registers)assert(p.value==0);
        assert(b[0][0].registers[0].value==row[0].registers[0].value);
        b.resize(1);assert(dirty==0);b=b;assert(b[0][0].registers[0].value!=0);
        b=a;assert(dirty==0);
        Owned c(3,row);b=std::move(c);assert(dirty==0);b.clear();assert(dirty==0);
        Owned d(a.begin(),a.end());d.insert(d.end(),a.begin(),a.end());
        assert(d.size()==8);
    }
    assert(dirty==0);
    for(int fail=0;fail<12;++fail) {
        assignment_budget=fail;
        bool rejected=false;
        try{Owned doomed(4,row);}catch(const std::runtime_error&){rejected=true;}
        assert(rejected && dirty==0);
    }
    assignment_budget=-1;
    Owned source(4,row);
    for(int fail=0;fail<12;++fail) {
        assignment_budget=fail;bool rejected=false;
        try{Owned doomed;doomed.insert(doomed.end(),source.begin(),source.end());}
        catch(const std::runtime_error&){rejected=true;}
        assert(rejected && dirty==0);
    }
    assignment_budget=-1;source.clear();assert(dirty==0 && destroyed>100);
    assert(row[0].registers[0].value!=0); // The source was never consumed.
    std::cout<<destroyed<<" instrumented share destructions observed zero; 24 injected failure paths passed\n";
}
