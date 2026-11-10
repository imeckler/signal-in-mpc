#pragma once
// Runtime-sized layer over the validated-v3 Boolean engine.
//
// The typed session API fixes every wire width at compile time, which does not
// suit a long-lived worker whose record and transcript sizes are public but
// only known at run time. This layer drives the same protocol core
// (AG2PCProtocol: authenticated inputs, directed openings; AG2PCEngine: the
// checked circuit passes) on runtime-sized wire bundles. It adds no
// cryptography and no gate logic: circuits are pinned Lean exports, and the
// only operations here are supplying inputs, selecting and concatenating
// wires, running a circuit, and opening.
//
// Security mode is a build-time choice and never a fallback. The default is the
// malicious-secure engine below. Defining EMP_HYBRID_SEMI_HONEST replaces it by
// the honest-but-curious session of sh_session.h under the same names, so every
// kernel and worker above this layer is shared between the two modes.
#include <emp-ag2pc/emp-ag2pc.h>
#include "lean_circuit.h"
#include <stdexcept>
#include <vector>
#ifdef EMP_HYBRID_SEMI_HONEST
#include "sh_session.h"
namespace emp_hybrid {
using Wires=ShWires;using DynSession=ShSession;
constexpr const char*SECURITY_MODE="semi-honest";
}
#else
namespace emp_hybrid {
constexpr const char*SECURITY_MODE="malicious-128";
using Wires=emp::SecureWires;
class DynSession {
    ::AG2PCProtocol proto;emp::AG2PCEngine engine;
public:
    DynSession(emp::NetIO*io,::ThreadPool*pool,int party,int ssp):proto(io,pool,party,ssp){engine.proto=&proto;}
    DynSession(const DynSession&)=delete;DynSession&operator=(const DynSession&)=delete;
    int party()const{return proto.party;}
    uint64_t and_gates()const{return engine.total_ands;}
    uint64_t sent_bytes()const{return proto.io->send_counter+proto.sib->send_counter;}
    ::AG2PCProtocol&protocol(){return proto;}
    // Both parties call with their own bits; returns (ALICE's wires, BOB's wires).
    std::pair<Wires,Wires> input_both(const std::vector<uint8_t>&mine){
        auto v=proto.process_inputs({emp::ALICE,emp::BOB},{mine,mine});return {std::move(v[0]),std::move(v[1])};
    }
    // One owner's private bits; the other party passes a same-length placeholder.
    Wires input_private(int owner,const std::vector<uint8_t>&bits){
        if(owner!=emp::ALICE&&owner!=emp::BOB)throw std::invalid_argument("input owner");
        return std::move(proto.process_inputs({owner},{bits})[0]);
    }
    Wires public_bits(const std::vector<uint8_t>&bits){for(auto b:bits)if(b>1)throw std::invalid_argument("public bit");return proto.public_wires(bits);}
    Wires run(const emp::circuit::BooleanProgram&program,const Wires&input){
        if(input.size()!=program.num_inputs)throw std::invalid_argument("circuit input width");
        return engine.run_program(program,input);
    }
    Wires run(const LeanCircuit&circuit,const Wires&input){return run(circuit.parallel(1),input);}
    // Open to both parties (two directed authenticated openings).
    std::vector<uint8_t> open(const Wires&w){return proto.decode(w,emp::PUBLIC);}
    static Wires concat(const std::vector<const Wires*>&parts){
        Wires out;for(auto*p:parts)emp::ag2pc_detail::append_bundle(out,*p);return out;
    }
    static Wires pick(const Wires&w,const std::vector<size_t>&indices){
        Wires out;const bool garbler=!w.label0.empty()||w.eval_label.empty();
        out.Lambda.reserve(indices.size());out.wire_bundle.reserve(indices.size());
        for(auto i:indices){
            if(i>=w.size())throw std::out_of_range("wire index");
            out.Lambda.push_back(w.Lambda[i]);out.wire_bundle.push_back(w.wire_bundle[i]);
            if(!w.label0.empty())out.label0.push_back(w.label0[i]);
            if(!w.eval_label.empty())out.eval_label.push_back(w.eval_label[i]);
        }
        (void)garbler;return out;
    }
    // Interleave two equal-length bundles as (a0,b0,a1,b1,...): the input order of
    // n parallel copies of a two-input Lean circuit such as xor-bit.
    static Wires interleave(const Wires&a,const Wires&b){
        if(a.size()!=b.size())throw std::invalid_argument("interleave width");
        Wires both=concat({&a,&b});std::vector<size_t>order;order.reserve(2*a.size());
        for(size_t i=0;i<a.size();i++){order.push_back(i);order.push_back(a.size()+i);}
        return pick(both,order);
    }
};
}
#endif
