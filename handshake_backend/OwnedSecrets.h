#pragma once
#include <sodium.h>
#include <vector>
#include <utility>
#include <stdexcept>

namespace tls_mpc_worker {
// sbv:[...x1] owns one field cell per logical bit. The upstream constant
// default is a64-cell packed word; never narrow/truncate that after creation.
template<class Bit,class Mac> Bit single_cell_constant(unsigned value,int party,const Mac& mac){
    if(value>1)throw std::runtime_error("non-bit public constant");
    return Bit::constant(value,party,mac,1);
}

// Only the currently owned native share storage is covered. This does NOT
// erase VM copies, allocator history inside MP-SPDZ, registers, preprocessing,
// PRNG state, swap/core dumps, or copies made by callers outside this owner.
// Never use this component alone as an operational retirement receipt.
template<class Bit> void wipe_bit_storage(Bit& bit) noexcept {
    using Field=typename Bit::part_type::open_type;
    for(auto& part:bit.get_regs()) {
        auto& field=static_cast<Field&>(part);
        // The field object is mutable; this pinned field's accessor exposes
        // its fixed-width value storage through a const-qualified pointer.
        sodium_memzero(const_cast<void*>(field.get_ptr()),Field::N_BYTES);
    }
}

// Same vector layout expected by FunctionArgument, with explicit destruction
// and replacement cleanup. Allocations moved by vector growth keep ownership;
// copied buffers each have their own cleanup. Public inheritance is only for
// the pinned FunctionArgument API; callers must not delete through Base* or
// mutate via a Base&. The current worker uses only the methods below/append.
template<class Bit> class OwnedBits : public std::vector<std::vector<Bit>> {
    using Base=std::vector<std::vector<Bit>>;
    static void wipe_row(std::vector<Bit>& row) noexcept {
        for(auto& bit:row)wipe_bit_storage(bit);
    }
    void append_copy(const std::vector<Bit>& source) {
        // Publish empty destinations into this owner before any allocating
        // deep copy. If allocation fails, all completed copies remain owned.
        Base::emplace_back();auto& destination=Base::back();
        destination.resize(source.size());
        for(size_t i=0;i<source.size();++i) {
            auto& dst=destination[i].get_regs();const auto& src=source[i].get_regs();
            dst.resize(src.size());
            for(size_t j=0;j<src.size();++j)dst[j]=src[j];
        }
    }
public:
    OwnedBits()=default;
    OwnedBits(size_t count,const std::vector<Bit>& row) {
        try {Base::reserve(count);for(size_t i=0;i<count;++i)append_copy(row);}
        catch(...){wipe();throw;}
    }
    template<class Iterator> OwnedBits(Iterator first,Iterator last) {
        try {for(;first!=last;++first)append_copy(*first);}
        catch(...){wipe();throw;}
    }
    OwnedBits(const OwnedBits& other):OwnedBits(other.begin(),other.end()) {}
    OwnedBits(OwnedBits&& other) noexcept:Base(std::move(other)) {}
    OwnedBits& operator=(const OwnedBits& other) {
        if(this!=&other){OwnedBits replacement(other);Base::swap(replacement);}return *this;
    }
    OwnedBits& operator=(OwnedBits&& other) noexcept {
        if(this!=&other){wipe();Base::operator=(std::move(other));}return *this;
    }
    ~OwnedBits(){wipe();}
    void wipe() noexcept {for(auto& row:*this)wipe_row(row);}
    void clear() noexcept {wipe();Base::clear();}
    void resize(size_t count) {
        for(size_t i=count;i<this->size();++i)wipe_row((*this)[i]);
        Base::resize(count);
    }
    template<class Iterator> typename Base::iterator insert(typename Base::const_iterator where,Iterator first,Iterator last) {
        if(where!=this->end())throw std::runtime_error("OwnedBits supports append only");
        size_t offset=this->size();
        for(;first!=last;++first)append_copy(*first);
        return this->begin()+offset;
    }
    // Explicit API adaptation; the callee overwrites existing output shares.
    Base& function_argument() {return *this;}
};
}
