#pragma once
#include <array>
#include <cstdint>
#include <memory>
#include <vector>
namespace emp_hybrid {
// Native authenticated values never leave Impl. Owner serialized, no VM sharing.
class FieldEngine {
    struct Impl;std::unique_ptr<Impl> impl;
public:
    class Handle {
        uint64_t owner=0,index=0;
        Handle(uint64_t o,uint64_t i):owner(o),index(i){}
        friend class FieldEngine;
    public:
        Handle()=default;
    };
    FieldEngine(unsigned party,unsigned port);
    ~FieldEngine();
    FieldEngine(const FieldEngine&)=delete;FieldEngine&operator=(const FieldEngine&)=delete;
    // Both contributions are fixed by one native input exchange. Local uint64
    // is for bounded preprocessing coins/fixture data, not imported shares.
    std::array<std::vector<Handle>,2> input_coins(const std::vector<uint64_t>&local);
    std::vector<Handle> mul(const std::vector<Handle>&a,const std::vector<Handle>&b);
    Handle add(Handle a,Handle b);
    Handle sub(Handle a,Handle b);
    Handle constant(uint64_t value);
    // Restricted bridge use: sacrificed coins/uniform masks only. This API is
    // internal candidate, not a generic host/RPC secret opening capability.
    std::vector<std::array<uint8_t,32>> checked_open(const std::vector<Handle>&a);
    void check();
};
}
