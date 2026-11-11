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
#include "profile.h"
#include <condition_variable>
#include <map>
#include <mutex>
#include <thread>
namespace emp_hybrid {
constexpr const char*SECURITY_MODE="malicious-128";
using Wires=emp::SecureWires;
// AND triples minted ahead of use. The engine's triple generation does not depend on the
// circuit (TRIPLE_POOL_AUDIT.md, steps 1-2), so it can run before the circuit that uses it,
// and beside it. Each factory is a further TriplePool of the SAME session: the session's
// Delta, its own two channels (siblings of the session's channel), its own COT sessions,
// thread pool and counter range. It runs TriplePool::mint unchanged, in batches of a fixed
// length (the bucket size follows from that length, as for any mint). Finished batches are
// used in index order, each triple once, only by this session, and are gone with it.
//
// Both parties must mint the same batches. Batch k (made by factory k mod F) is started when
// k*batch < requested + reserve, where `requested` counts the triples the circuits run so
// far have asked for: the same number on both sides, reached at different moments. So each
// side announces a batch on the factory's channel when its own count allows it, and the
// batch starts when both have; on shutdown a side announces the end instead, and both stop.
class TripleStock {
    struct Batch {emp::BlockVec mac,key;};   // region-major (a, b, c), stride `batch`
    struct Factory {
        std::unique_ptr<emp::NetIO>io,sib;std::unique_ptr<::ThreadPool>threads;std::unique_ptr<::TriplePool>pool;std::thread thread;
    };
    std::vector<std::unique_ptr<Factory>>factories;std::mutex m;std::condition_variable changed;
    std::map<uint64_t,Batch>ready;uint64_t requested=0,next=0;size_t offset=0;bool stopping=false;
    size_t batch=0,reserve=0;int party=0;
    void work(Factory&f,uint64_t first){
        for(uint64_t k=first;;k+=factories.size()){
            uint8_t mine=0,peer=0;
            {std::unique_lock<std::mutex>lock(m);changed.wait(lock,[&]{return stopping||k*batch<requested+reserve;});mine=stopping?0:1;}
            if(party==emp::ALICE){f.io->send_data(&mine,1);f.io->flush();f.io->recv_data(&peer,1);}
            else{f.io->recv_data(&peer,1);f.io->send_data(&mine,1);f.io->flush();}
            if(peer>1)emp::error("triple stock: announcement");
            if(!mine||!peer)return;
            Batch made;made.mac.resize(3*batch);made.key.resize(3*batch);
            f.pool->mint(int(batch),made.mac.data(),made.key.data());
            {std::lock_guard<std::mutex>lock(m);ready[k]=std::move(made);}
            changed.notify_all();
        }
    }
public:
    double waited=0;   // seconds circuits spent waiting for a batch (profile only)
    bool active()const{return !factories.empty();}
    // Called by both parties at the same point: the sibling channels pair up in order.
    void start(emp::NetIO*io,int party_,int ssp,const emp::block&delta,unsigned count,size_t batch_,size_t reserve_){
        if(active()||!count||count>8||batch_<1024||batch_>(size_t(1)<<24)||reserve_>(size_t(1)<<28))throw std::invalid_argument("triple stock parameters");
        batch=batch_;reserve=reserve_;party=party_;
        for(unsigned i=0;i<count;i++){
            auto f=std::make_unique<Factory>();f->io=io->make_sibling();f->sib=f->io->make_sibling();f->threads=std::make_unique<::ThreadPool>(2);
            // Counter range of its own: digest tags and hash-tweak seeds never coincide with
            // the session pool's or another factory's under the shared Delta.
            f->pool=std::make_unique<::TriplePool>(f->io.get(),f->sib.get(),f->threads.get(),party,ssp,&delta,uint64_t(i+1)<<56);
            factories.push_back(std::move(f));
        }
        for(unsigned i=0;i<count;i++)factories[i]->thread=std::thread([this,i]{work(*factories[i],i);});
    }
    // L finished triples into region-major buffers of stride L. Always from stock, in order.
    bool take(int count,emp::block*mac,emp::block*key){
        const auto started=std::chrono::steady_clock::now();const size_t L=size_t(count);
        std::unique_lock<std::mutex>lock(m);requested+=L;changed.notify_all();
        for(size_t done=0;done<L;){
            changed.wait(lock,[&]{return ready.count(next)!=0;});
            auto&from=ready[next];const size_t n=std::min(L-done,batch-offset);
            for(unsigned region=0;region<3;region++){
                std::memcpy(mac+region*L+done,from.mac.data()+region*batch+offset,n*sizeof(emp::block));
                std::memcpy(key+region*L+done,from.key.data()+region*batch+offset,n*sizeof(emp::block));
            }
            done+=n;offset+=n;
            if(offset==batch){ready.erase(next);next++;offset=0;}
        }
        waited+=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
        return true;
    }
    uint64_t sent_bytes()const{uint64_t n=0;for(auto&f:factories)n+=uint64_t(f->io->send_counter+f->sib->send_counter);return n;}
    uint64_t minted()const{uint64_t n=0;for(auto&f:factories)n+=f->pool->minted;return n;}
    double mint_seconds()const{double s=0;for(auto&f:factories)s+=1e-9*double(f->pool->mint_ns);return s;}
    void stop(){
        {std::lock_guard<std::mutex>lock(m);stopping=true;}
        changed.notify_all();
        for(auto&f:factories)if(f->thread.joinable())f->thread.join();
        for(auto&f:factories)f->pool.reset();   // closes its COT sessions with the peer's factory
        factories.clear();ready.clear();
    }
    ~TripleStock(){stop();}
};
class DynSession {
    ::AG2PCProtocol proto;emp::AG2PCEngine engine;TripleStock stock;
public:
    DynSession(emp::NetIO*io,::ThreadPool*pool,int party,int ssp):proto(io,pool,party,ssp){engine.proto=&proto;}
    ~DynSession(){proto.fpre->stock=nullptr;stock.stop();}
    DynSession(const DynSession&)=delete;DynSession&operator=(const DynSession&)=delete;
    // Mint AND triples ahead of use in `factories` background pools (see TripleStock). Both
    // parties call this with the same arguments before any circuit runs.
    void start_stock(unsigned factories,size_t batch,size_t reserve){
        stock.start(proto.io,proto.party,proto.fpre->ssp,proto.Delta,factories,batch,reserve);
        proto.fpre->stock=[this](int count,emp::block*mac,emp::block*key){return stock.take(count,mac,key);};
    }
    // Profile only: triples minted by the factories, their minting time (all factories), bytes.
    uint64_t stock_minted()const{return stock.minted();}
    double stock_seconds()const{return stock.mint_seconds();}
    int party()const{return proto.party;}
    uint64_t and_gates()const{return engine.total_ands;}
    uint64_t sent_bytes()const{return proto.io->send_counter+proto.sib->send_counter+stock.sent_bytes();}
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
        const uint64_t minted=proto.fpre->mint_ns;const double waited=stock.waited;
        auto out=engine.run_program(program,input);
        Profile::get().credit("boolean triples: minted inside the circuit run",1e-9*double(proto.fpre->mint_ns-minted));
        Profile::get().credit("boolean triples: circuit waiting for stock",stock.waited-waited);
        return out;
    }
    Wires run(const LeanCircuit&circuit,const Wires&input){return run(circuit.parallel(1),input);}
    // Open to both parties (two directed authenticated openings).
    std::vector<uint8_t> open(const Wires&w){return proto.decode(w,emp::PUBLIC);}
    // Open to one party only (one directed authenticated opening).
    std::vector<uint8_t> open_to(const Wires&w,int recipient){
        if(recipient!=emp::ALICE&&recipient!=emp::BOB)throw std::invalid_argument("opening recipient");
        auto out=proto.decode(w,recipient);if(proto.party!=recipient)out.assign(w.size(),0);return out;
    }
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
