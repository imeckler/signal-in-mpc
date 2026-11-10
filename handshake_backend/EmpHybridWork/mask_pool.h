#pragma once
#include "field_engine.h"
#include <array>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <vector>
namespace emp_hybrid {
class DaBitGeneratorV1;
struct SessionBinding {
    std::array<uint8_t,32> nonce{},configuration{};
    uint64_t epoch=0;
    bool operator==(const SessionBinding&)const=default;
};
struct EngineOwners {const void* boolean;const FieldEngine* field;bool operator==(const EngineOwners&)const=default;};
enum class Direction:uint8_t {BooleanToField=1,FieldToBoolean=2};
struct MaskPair {uint32_t wire;FieldEngine::Handle field;};
// Allocation/consumption guard only. Actual constructor is reachable only from
// the concrete generator after its native+EMP consistency/authentication checks.
// It is not a security proof and does not erase the engines' secret storage.
class CheckedMaskPool {
    struct State {bool active=true;SessionBinding binding;EngineOwners owners;uint64_t next_operation=0;};
    std::shared_ptr<State> state;
    std::vector<MaskPair> pairs;
    size_t cursor=0;
    CheckedMaskPool(SessionBinding binding,EngineOwners owners,std::vector<MaskPair> values):state(std::make_shared<State>()),pairs(std::move(values)){state->binding=binding;state->owners=owners;}
    friend class DaBitGeneratorV1;
    [[noreturn]] void fail(){poison();throw std::runtime_error("mask pool binding/range/replay");}
public:
    class Lease {
        std::weak_ptr<State> state;SessionBinding binding;EngineOwners owners;uint64_t operation,begin;Direction direction;
        std::vector<MaskPair> pairs;bool consumed=false;
        friend class CheckedMaskPool;
        Lease(std::shared_ptr<State>s,uint64_t op,uint64_t first,Direction d,std::vector<MaskPair>v):state(s),binding(s->binding),owners(s->owners),operation(op),begin(first),direction(d),pairs(std::move(v)){}
        [[noreturn]] void fail(){if(auto s=state.lock())s->active=false;pairs.clear();throw std::runtime_error("mask lease binding/replay");}
    public:
        Lease(const Lease&)=delete;Lease&operator=(const Lease&)=delete;
        Lease(Lease&&other)noexcept:state(std::move(other.state)),binding(other.binding),owners(other.owners),operation(other.operation),begin(other.begin),direction(other.direction),pairs(std::move(other.pairs)),consumed(other.consumed){other.consumed=true;}
        Lease&operator=(Lease&&)=delete;
        // Canonical public frame: fixed version, full session/config, epoch,
        // operation, burned range and direction. Peers must compare it BEFORE
        // either engine opens any masked value for this lease.
        std::vector<uint8_t> frame()const {
            std::vector<uint8_t>v={'E','M','P','F','P','D','V',1};v.insert(v.end(),binding.nonce.begin(),binding.nonce.end());v.insert(v.end(),binding.configuration.begin(),binding.configuration.end());
            auto be=[&](uint64_t x){for(int i=7;i>=0;i--)v.push_back(uint8_t(x>>(8*i)));};
            be(binding.epoch);be(operation);be(begin);be(pairs.size());v.push_back(uint8_t(direction));return v;
        }
        std::vector<MaskPair> consume(const SessionBinding&b,EngineOwners actual,uint64_t op,Direction d){
            auto s=state.lock();if(!s||!s->active||consumed||actual!=owners||s->owners!=owners||b!=binding||s->binding!=binding||op!=operation||d!=direction)fail();
            consumed=true;return std::move(pairs);
        }
    };
    CheckedMaskPool(const CheckedMaskPool&)=delete;CheckedMaskPool&operator=(const CheckedMaskPool&)=delete;
    CheckedMaskPool(CheckedMaskPool&&)=default;CheckedMaskPool&operator=(CheckedMaskPool&&)=delete;
    ~CheckedMaskPool(){poison();}
    const SessionBinding&binding()const{if(!state||!state->active)throw std::runtime_error("mask pool closed");return state->binding;}
    void poison(){if(state)state->active=false;pairs.clear();}
    Lease reserve(const SessionBinding&b,EngineOwners actual,uint64_t operation,Direction d,size_t count){
        if(!state||!state->active||actual!=state->owners||b!=state->binding||operation!=state->next_operation||!count||count>pairs.size()-cursor||operation==UINT64_MAX||(d!=Direction::BooleanToField&&d!=Direction::FieldToBoolean))fail();
        auto begin=cursor;cursor+=count;state->next_operation++;
        std::vector<MaskPair>v;v.reserve(count);for(size_t i=begin;i<cursor;i++)v.push_back(std::exchange(pairs[i],{}));
        return Lease(state,operation,begin,d,std::move(v));
    }
};
}
