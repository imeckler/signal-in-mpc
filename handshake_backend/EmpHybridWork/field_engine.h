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
    // `batch`: preprocessing batch size (triples produced per refill). A caller
    // that needs only a handful of products should ask for a small batch.
    // `mac_key_share` (malicious build only): this party's additive share of the MAC key,
    // as delivered by the share database, instead of a freshly sampled one. Stored values
    // authenticated under that key can then be imported and exported as shares.
    FieldEngine(unsigned party,unsigned port,unsigned batch=10000,const std::array<uint8_t,32>*mac_key_share=nullptr);
    ~FieldEngine();
    // This party's share of a stored value and of its MAC (value times the MAC key), both
    // canonical. Nothing is checked here: a wrong share or MAC makes any later opening that
    // depends on it fail its MAC check. The semi-honest build ignores the MAC share.
    Handle import_share(const std::array<uint8_t,32>&value_share,const std::array<uint8_t,32>&mac_share);
    // The reverse, for storing a value: (value share, MAC share).
    std::pair<std::array<uint8_t,32>,std::array<uint8_t,32>> export_share(Handle a);
    FieldEngine(const FieldEngine&)=delete;FieldEngine&operator=(const FieldEngine&)=delete;
    // Both contributions are fixed by one native input exchange. Local uint64
    // is for bounded preprocessing coins/fixture data, not imported shares.
    std::array<std::vector<Handle>,2> input_coins(const std::vector<uint64_t>&local);
    std::vector<Handle> mul(const std::vector<Handle>&a,const std::vector<Handle>&b);
    Handle add(Handle a,Handle b);
    Handle sub(Handle a,Handle b);
    Handle constant(uint64_t value);
    // Multiplication by a PUBLIC constant is linear: no triple, no interaction.
    Handle scale(Handle a,uint64_t constant);
    // Public canonical field element (32 little-endian bytes, value < p).
    Handle public_element(const std::array<uint8_t,32>&canonical);
    // a / c for a PUBLIC nonzero canonical c (already opened and MAC-checked
    // by the caller). Linear: no triple, no interaction.
    Handle divide_public(Handle a,const std::array<uint8_t,32>&c);
    // Private full-width inputs: each party contributes local.size() canonical
    // field elements in one native input exchange (candidate masks only).
    std::array<std::vector<Handle>,2> input_elements(const std::vector<std::array<uint8_t,32>>&local);
    // Restricted bridge use: sacrificed coins/uniform masks only. This API is
    // internal candidate, not a generic host/RPC secret opening capability.
    std::vector<std::array<uint8_t,32>> checked_open(const std::vector<Handle>&a);
    void check();
    unsigned party_id()const;
    // Public cost counters: bytes this party has sent, products completed.
    uint64_t sent_bytes()const;
    uint64_t products()const;
};
}
