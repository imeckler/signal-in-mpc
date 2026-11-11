#pragma once
// SEMI-HONEST Boolean session (explicit build mode EMP_HYBRID_SEMI_HONEST).
//
// Plain Yao garbling with free-XOR and half-gates (ZRE15) and semi-honest IKNP
// OT for the evaluator's inputs. It offers NO protection against a party that
// deviates from the protocol: no authenticated bits, no cut-and-choose, no
// output check. It exists so the same Lean circuits and the same runtime can be
// costed and run in the honest-but-curious model. It is never selected
// implicitly; a build must define EMP_HYBRID_SEMI_HONEST.
//
// Same surface as the malicious runtime-sized session (dyn_session.h): supply
// inputs, select and concatenate wires, run a pinned Lean circuit, open.
// ALICE garbles, BOB evaluates. A wire is one 128-bit label: the garbler holds
// the zero-label, the evaluator the active label.
#include <emp-tool/emp-tool.h>
#include <emp-ot/emp-ot.h>
#include "lean_circuit.h"
#include <memory>
#include <stdexcept>
#include <vector>
namespace emp_hybrid {
struct ShWires {
    std::vector<emp::block> label;
    size_t size()const{return label.size();}
    ShWires slice(size_t lo,size_t hi)const{if(lo>hi||hi>label.size())throw std::out_of_range("wire slice");ShWires r;r.label.assign(label.begin()+lo,label.begin()+hi);return r;}
};
class ShSession {
    emp::NetIO*io;int me;emp::block delta=emp::zero_block;emp::IKNP ot;emp::MITCCRH<8> hash;uint64_t ands=0;emp::PRG prg;
    bool garbler()const{return me==emp::ALICE;}
public:
    ShSession(emp::NetIO*channel,::ThreadPool*,int party,int):io(channel),me(party),ot(party,channel,false){
        if(me!=emp::ALICE&&me!=emp::BOB)throw std::invalid_argument("party");
        emp::block start;
        if(garbler()){prg.random_block(&delta,1);if(!emp::getLSB(delta))delta=delta^emp::makeBlock(0,1);prg.random_block(&start,1);io->send_block(&start,1);io->flush();}
        else io->recv_block(&start,1);
        hash.setS(start);
    }
    ShSession(const ShSession&)=delete;ShSession&operator=(const ShSession&)=delete;
    int party()const{return me;}
    // Plain garbling has no triples: nothing to mint ahead (same surface as the malicious session).
    void start_stock(unsigned,size_t,size_t){}
    uint64_t stock_minted()const{return 0;}
    double stock_seconds()const{return 0;}
    uint64_t and_gates()const{return ands;}
    uint64_t sent_bytes()const{return io->send_counter;}
    // One owner's private bits; the other party passes a same-length placeholder.
    ShWires input_private(int owner,const std::vector<uint8_t>&bits){
        const size_t n=bits.size();ShWires out;out.label.resize(n);if(!n)return out;
        if(owner==emp::ALICE){
            if(garbler()){
                prg.random_block(out.label.data(),n);std::vector<emp::block>active(n);
                for(size_t i=0;i<n;i++)active[i]=bits[i]?out.label[i]^delta:out.label[i];
                io->send_block(active.data(),n);io->flush();
            }else io->recv_block(out.label.data(),n);
        }else if(owner==emp::BOB){
            if(garbler()){
                prg.random_block(out.label.data(),n);std::vector<emp::block>one(n);for(size_t i=0;i<n;i++)one[i]=out.label[i]^delta;
                ot.send(out.label.data(),one.data(),int64_t(n));io->flush();
            }else{
                std::unique_ptr<bool[]>choice(new bool[n]);for(size_t i=0;i<n;i++)choice[i]=bits[i]!=0;
                ot.recv(out.label.data(),choice.get(),int64_t(n));io->flush();
            }
        }else throw std::invalid_argument("input owner");
        return out;
    }
    std::pair<ShWires,ShWires> input_both(const std::vector<uint8_t>&mine){auto a=input_private(emp::ALICE,mine);auto b=input_private(emp::BOB,mine);return {std::move(a),std::move(b)};}
    // Public constants cost nothing: the active label is zero for both values.
    ShWires public_bits(const std::vector<uint8_t>&bits){
        ShWires out;out.label.resize(bits.size(),emp::zero_block);
        for(size_t i=0;i<bits.size();i++){if(bits[i]>1)throw std::invalid_argument("public bit");if(garbler()&&bits[i])out.label[i]=delta;}
        return out;
    }
    ShWires run(const emp::circuit::BooleanProgram&program,const ShWires&input){
        if(input.size()!=program.num_inputs)throw std::invalid_argument("circuit input width");
        std::vector<emp::block>w(program.num_wires,emp::zero_block);std::copy(input.label.begin(),input.label.end(),w.begin());
        using Op=emp::circuit::Op;emp::block table[2];
        for(const auto&g:program.gates){
            switch(g.op){
            case Op::Xor:w[g.out]=w[g.in0]^w[g.in1];break;
            case Op::Not:w[g.out]=garbler()?w[g.in0]^delta:w[g.in0];break;
            case Op::And:
                if(garbler()){w[g.out]=emp::halfgates_garble(w[g.in0],w[g.in0]^delta,w[g.in1],w[g.in1]^delta,delta,table,&hash);io->send_block(table,2);}
                else{io->recv_block(table,2);w[g.out]=emp::halfgates_eval(w[g.in0],w[g.in1],table,&hash);}
                ands++;break;
            case Op::Const0:w[g.out]=emp::zero_block;break;
            case Op::Const1:w[g.out]=garbler()?delta:emp::zero_block;break;
            default:throw std::invalid_argument("gate kind");
            }
        }
        if(garbler())io->flush();
        ShWires out;out.label.reserve(program.outputs.size());for(auto id:program.outputs)out.label.push_back(w[id]);return out;
    }
    ShWires run(const LeanCircuit&circuit,const ShWires&input){return run(circuit.parallel(1),input);}
    // Open to both parties: decoding bits one way, values back the other way.
    std::vector<uint8_t> open(const ShWires&w){
        const size_t n=w.size();std::vector<uint8_t>out(n);if(!n)return out;std::unique_ptr<bool[]>bits(new bool[n]);
        if(garbler()){
            for(size_t i=0;i<n;i++)bits[i]=emp::getLSB(w.label[i]);io->send_bool(bits.get(),n);io->flush();
            io->recv_bool(bits.get(),n);for(size_t i=0;i<n;i++)out[i]=bits[i];
        }else{
            io->recv_bool(bits.get(),n);for(size_t i=0;i<n;i++){out[i]=uint8_t(bits[i]^emp::getLSB(w.label[i]));bits[i]=out[i];}
            io->send_bool(bits.get(),n);io->flush();
        }
        return out;
    }
    // Open to one party only: the other party sends its half of the decoding information.
    std::vector<uint8_t> open_to(const ShWires&w,int recipient){
        const size_t n=w.size();std::vector<uint8_t>out(n,0);if(!n)return out;std::unique_ptr<bool[]>bits(new bool[n]);
        if(recipient!=emp::ALICE&&recipient!=emp::BOB)throw std::invalid_argument("opening recipient");
        if(me!=recipient){for(size_t i=0;i<n;i++)bits[i]=emp::getLSB(w.label[i]);io->send_bool(bits.get(),n);io->flush();}
        else{io->recv_bool(bits.get(),n);for(size_t i=0;i<n;i++)out[i]=uint8_t(bits[i]^emp::getLSB(w.label[i]));}
        return out;
    }
    static ShWires concat(const std::vector<const ShWires*>&parts){ShWires out;for(auto*p:parts)out.label.insert(out.label.end(),p->label.begin(),p->label.end());return out;}
    static ShWires pick(const ShWires&w,const std::vector<size_t>&indices){
        ShWires out;out.label.reserve(indices.size());for(auto i:indices){if(i>=w.size())throw std::out_of_range("wire index");out.label.push_back(w.label[i]);}return out;
    }
    static ShWires interleave(const ShWires&a,const ShWires&b){
        if(a.size()!=b.size())throw std::invalid_argument("interleave width");
        ShWires out;out.label.reserve(2*a.size());for(size_t i=0;i<a.size();i++){out.label.push_back(a.label[i]);out.label.push_back(b.label[i]);}return out;
    }
};
}
