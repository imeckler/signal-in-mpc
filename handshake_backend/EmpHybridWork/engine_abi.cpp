// The engines behind the C ABI of engine_abi.h (REORGANIZATION_PLAN.md 5.7, stage S8).
//
// This file adds no cryptography and no gate logic. It owns the two engines of one worker
// (the Boolean session, dyn_session.h, and the field engine, field_engine.h), keeps the
// values they hold in handle tables, and forwards each call to the engine unchanged. It never
// sends anything itself: the only bytes that leave here are the engines' own protocol messages
// on the engines' own links.
//
// ONE TRANSLATION UNIT. The EMP headers define AG2PCProtocol members out of class without
// `inline` (emp-ag2pc backend/protocol.h), so two objects that both include them cannot be
// linked together. The legacy library (legacy_abi.cpp) is therefore compiled as part of this
// file, included at its end; build_hybrid_v3.py --engine-abi compiles only this file.
#define EMP_HYBRID_ENGINE_ABI_TU 1
#include "engine_abi.h"
#include "dyn_session.h"
#include "dabit_generator.h"
#include "field_engine.h"
#include "lean_circuit.h"
#include "peer_link.h"
#include "profile.h"
#include <cstring>
#include <iostream>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#ifdef EMP_HYBRID_ENGINE_ABI_TEST
static constexpr int engine_abi_test_build=1;
#else
static constexpr int engine_abi_test_build=0;
#endif

namespace engine_abi {
thread_local std::string last_error;
// Runs `body`; a C++ exception becomes status 1 and the message of ea_error_message().
template<class F> int guard(F&&body){
    try{body();return 0;}
    catch(const std::exception&e){last_error=e.what();return 1;}
    catch(...){last_error="unknown failure";return 1;}
}
inline void need(bool ok,const char*what){if(!ok)throw std::runtime_error(what);}
// Values named by handles. Ids start at 1 and are never reused.
template<class T> struct Table {
    std::unordered_map<uint64_t,T>items;uint64_t next=1;
    uint64_t put(T value){need(next!=0,"handle space");items.emplace(next,std::move(value));return next++;}
    T&at(uint64_t id){auto it=items.find(id);need(it!=items.end(),"unknown handle");return it->second;}
    void drop(uint64_t id){need(items.erase(id)==1,"unknown handle");}
};
struct LegacyState;
struct LegacyDeleter {void operator()(LegacyState*)const;};   // defined in legacy_abi.cpp
}

struct ea_session {
    int party=0;   // emp::ALICE or emp::BOB
    // Declaration order is construction order, as in tls_worker_v3.cpp's `run`; destruction runs
    // in reverse (the legacy kernels first, then the challenge, field engine, Boolean session,
    // its thread pool, and last the Boolean channel).
    std::unique_ptr<emp::NetIO>io;
    std::unique_ptr<::ThreadPool>threads;
    std::unique_ptr<emp_hybrid::DynSession>mpc;
    std::unique_ptr<emp_hybrid::FieldEngine>field;
    std::unique_ptr<emp_hybrid::Challenge>channel;
    engine_abi::Table<emp_hybrid::Wires>bools;
    engine_abi::Table<emp_hybrid::FieldEngine::Handle>fields;
    engine_abi::Table<std::unique_ptr<emp_hybrid::LeanCircuit>>circuits;
    std::unique_ptr<engine_abi::LegacyState,engine_abi::LegacyDeleter>legacy;
    ~ea_session(){
        legacy.reset();
        // The profile reads the engines through callbacks: none may outlive them.
        auto&profile=emp_hybrid::Profile::get();profile.gates=nullptr;profile.products=nullptr;profile.boolean_bytes=nullptr;profile.field_bytes=nullptr;
    }
};

extern "C" {
const char*ea_security_mode(void){return emp_hybrid::SECURITY_MODE;}
int ea_test_build(void){return engine_abi_test_build;}
const char*ea_error_message(void){return engine_abi::last_error.c_str();}
void ea_bytes_free(ea_bytes*bytes){if(bytes){std::free(bytes->data);bytes->data=nullptr;bytes->len=0;}}

int ea_session_create(const ea_config*config,ea_session**out){
    using namespace engine_abi;
    return guard([&]{
        need(config&&out,"session arguments");*out=nullptr;
        need(config->party==0||config->party==1,"party");
        need(config->port>1024&&config->port<65536&&config->field_port>1024&&config->field_port<65536,"port");
        need(config->challenge_domain&&*config->challenge_domain,"challenge domain");
        auto s=std::make_unique<ea_session>();s->party=config->party+1;
        // The other worker's address and this one's listen address (peer_link.h, unchanged).
        const emp_hybrid::PeerLink link=emp_hybrid::PeerLink::make(config->peer,config->listen);
        s->io=link.open(s->party==emp::ALICE,config->port);
        s->threads=std::make_unique<::ThreadPool>(4);
        s->mpc=std::make_unique<emp_hybrid::DynSession>(s->io.get(),s->threads.get(),s->party,128);
        if(config->stock_factories)s->mpc->start_stock(config->stock_factories,config->stock_batch,config->stock_reserve);
        s->field=std::make_unique<emp_hybrid::FieldEngine>(unsigned(config->party),config->field_port,config->field_batch,nullptr,
            config->field_reserve,config->field_lines,config->field_peer,config->field_direct!=0);
        s->channel=std::make_unique<emp_hybrid::Challenge>(*s->io,s->party,std::string(config->challenge_domain));
        auto&profile=emp_hybrid::Profile::get();auto*mpc=s->mpc.get();auto*field=s->field.get();
        profile.gates=[mpc]{return mpc->and_gates();};profile.products=[field]{return field->products();};
        profile.boolean_bytes=[mpc]{return uint64_t(mpc->sent_bytes());};profile.field_bytes=[field]{return field->sent_bytes();};
        *out=s.release();
    });
}
void ea_session_destroy(ea_session*session){try{delete session;}catch(...){}}

int ea_counters_read(ea_session*s,ea_counters*out){
    return engine_abi::guard([&]{
        engine_abi::need(s&&out,"counters arguments");
        out->and_gates=s->mpc->and_gates();out->boolean_bytes=uint64_t(s->mpc->sent_bytes());
        out->field_bytes=s->field->sent_bytes();out->field_products=s->field->products();
        out->stock_minted=s->mpc->stock_minted();out->stock_seconds=s->mpc->stock_seconds();
    });
}
int ea_profile_report(ea_session*s,const char*prefix){
    return engine_abi::guard([&]{engine_abi::need(s&&prefix,"profile arguments");emp_hybrid::Profile::get().report(std::cerr,prefix);std::cerr.flush();});
}

// ---- loading
int ea_circuit_load(ea_session*s,const char*path,const char*sha,uint64_t*out){
    return engine_abi::guard([&]{
        engine_abi::need(s&&path&&sha&&out,"circuit arguments");
        *out=s->circuits.put(std::make_unique<emp_hybrid::LeanCircuit>(std::string(path),sha));
    });
}
int ea_circuit_shape(ea_session*s,uint64_t circuit,uint32_t*inputs,uint32_t*outputs){
    return engine_abi::guard([&]{
        engine_abi::need(s&&inputs&&outputs,"circuit arguments");auto&c=*s->circuits.at(circuit);
        *inputs=c.input_bits();*outputs=c.output_bits();
    });
}
int ea_circuit_free(ea_session*s,uint64_t circuit){return engine_abi::guard([&]{engine_abi::need(s,"session");s->circuits.drop(circuit);});}

}   // extern "C"

// ---- Boolean engine
namespace {
std::vector<uint8_t> bit_vector(const uint8_t*bits,size_t count){
    engine_abi::need(count==0||bits,"bits");std::vector<uint8_t>out(bits,bits+count);
    for(auto b:out)engine_abi::need(b<=1,"a bit is 0 or 1");
    return out;
}
void copy_bits(const std::vector<uint8_t>&from,uint8_t*to,size_t count){
    engine_abi::need(from.size()==count&&(count==0||to),"opened width");if(count)std::memcpy(to,from.data(),count);
}
}
extern "C" {
int ea_bool_input_private(ea_session*s,int owner,const uint8_t*bits,size_t count,uint64_t*out){
    return engine_abi::guard([&]{
        engine_abi::need(s&&out&&(owner==0||owner==1),"input arguments");
        *out=s->bools.put(s->mpc->input_private(owner+1,bit_vector(bits,count)));
    });
}
int ea_bool_input_both(ea_session*s,const uint8_t*bits,size_t count,uint64_t*out_a,uint64_t*out_b){
    return engine_abi::guard([&]{
        engine_abi::need(s&&out_a&&out_b,"input arguments");auto both=s->mpc->input_both(bit_vector(bits,count));
        *out_a=s->bools.put(std::move(both.first));*out_b=s->bools.put(std::move(both.second));
    });
}
int ea_bool_public(ea_session*s,const uint8_t*bits,size_t count,uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"public arguments");*out=s->bools.put(s->mpc->public_bits(bit_vector(bits,count)));});
}
int ea_bool_run(ea_session*s,uint64_t circuit,uint32_t copies,uint64_t input,uint64_t*out){
    return engine_abi::guard([&]{
        engine_abi::need(s&&out&&copies>=1,"run arguments");auto&c=*s->circuits.at(circuit);
        *out=s->bools.put(s->mpc->run(c.parallel(copies),s->bools.at(input)));
    });
}
int ea_bool_open(ea_session*s,uint64_t handle,uint8_t*bits,size_t count){
    return engine_abi::guard([&]{engine_abi::need(s,"session");copy_bits(s->mpc->open(s->bools.at(handle)),bits,count);});
}
int ea_bool_open_to(ea_session*s,uint64_t handle,int recipient,uint8_t*bits,size_t count){
    return engine_abi::guard([&]{
        engine_abi::need(s&&(recipient==0||recipient==1),"open arguments");
        copy_bits(s->mpc->open_to(s->bools.at(handle),recipient+1),bits,count);
    });
}
int ea_bool_concat(ea_session*s,const uint64_t*handles,size_t count,uint64_t*out){
    return engine_abi::guard([&]{
        engine_abi::need(s&&out&&(count==0||handles),"concat arguments");std::vector<const emp_hybrid::Wires*>parts;
        for(size_t i=0;i<count;i++)parts.push_back(&s->bools.at(handles[i]));
        *out=s->bools.put(emp_hybrid::DynSession::concat(parts));
    });
}
int ea_bool_pick(ea_session*s,uint64_t handle,const uint64_t*indices,size_t count,uint64_t*out){
    return engine_abi::guard([&]{
        engine_abi::need(s&&out&&(count==0||indices),"pick arguments");std::vector<size_t>order(indices,indices+count);
        *out=s->bools.put(emp_hybrid::DynSession::pick(s->bools.at(handle),order));
    });
}
int ea_bool_slice(ea_session*s,uint64_t handle,size_t lo,size_t hi,uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"slice arguments");*out=s->bools.put(s->bools.at(handle).slice(lo,hi));});
}
int ea_bool_interleave(ea_session*s,uint64_t a,uint64_t b,uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"interleave arguments");*out=s->bools.put(emp_hybrid::DynSession::interleave(s->bools.at(a),s->bools.at(b)));});
}
int ea_bool_width(ea_session*s,uint64_t handle,size_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"width arguments");*out=s->bools.at(handle).size();});
}
int ea_bool_free(ea_session*s,uint64_t handle){return engine_abi::guard([&]{engine_abi::need(s,"session");s->bools.drop(handle);});}

}   // extern "C"

// ---- field engine
namespace {
std::array<uint8_t,32> element(const uint8_t*bytes){engine_abi::need(bytes,"element");std::array<uint8_t,32>out{};std::memcpy(out.data(),bytes,32);return out;}
void put_all(ea_session&s,const std::vector<emp_hybrid::FieldEngine::Handle>&from,uint64_t*to,size_t count){
    engine_abi::need(from.size()==count&&(count==0||to),"field output count");for(size_t i=0;i<count;i++)to[i]=s.fields.put(from[i]);
}
}
extern "C" {
int ea_field_input_coins(ea_session*s,const uint64_t*local,size_t count,uint64_t*outs_a,uint64_t*outs_b){
    return engine_abi::guard([&]{
        engine_abi::need(s&&(count==0||local),"coin arguments");auto both=s->field->input_coins(std::vector<uint64_t>(local,local+count));
        put_all(*s,both[0],outs_a,count);put_all(*s,both[1],outs_b,count);
    });
}
int ea_field_input_elements(ea_session*s,const uint8_t*local,size_t count,uint64_t*outs_a,uint64_t*outs_b){
    return engine_abi::guard([&]{
        engine_abi::need(s&&(count==0||local),"element arguments");std::vector<std::array<uint8_t,32>>values;
        for(size_t i=0;i<count;i++)values.push_back(element(local+32*i));
        auto both=s->field->input_elements(values);put_all(*s,both[0],outs_a,count);put_all(*s,both[1],outs_b,count);
    });
}
int ea_field_constant(ea_session*s,uint64_t value,uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"constant arguments");*out=s->fields.put(s->field->constant(value));});
}
int ea_field_public(ea_session*s,const uint8_t value[32],uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"public arguments");*out=s->fields.put(s->field->public_element(element(value)));});
}
int ea_field_add(ea_session*s,uint64_t a,uint64_t b,uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"add arguments");*out=s->fields.put(s->field->add(s->fields.at(a),s->fields.at(b)));});
}
int ea_field_sub(ea_session*s,uint64_t a,uint64_t b,uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"sub arguments");*out=s->fields.put(s->field->sub(s->fields.at(a),s->fields.at(b)));});
}
int ea_field_scale(ea_session*s,uint64_t a,uint64_t constant,uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"scale arguments");*out=s->fields.put(s->field->scale(s->fields.at(a),constant));});
}
int ea_field_divide_public(ea_session*s,uint64_t a,const uint8_t c[32],uint64_t*out){
    return engine_abi::guard([&]{engine_abi::need(s&&out,"divide arguments");*out=s->fields.put(s->field->divide_public(s->fields.at(a),element(c)));});
}
int ea_field_mul(ea_session*s,const uint64_t*a,const uint64_t*b,size_t count,uint64_t*outs){
    return engine_abi::guard([&]{
        engine_abi::need(s&&(count==0||(a&&b)),"mul arguments");std::vector<emp_hybrid::FieldEngine::Handle>x,y;
        for(size_t i=0;i<count;i++){x.push_back(s->fields.at(a[i]));y.push_back(s->fields.at(b[i]));}
        put_all(*s,s->field->mul(x,y),outs,count);
    });
}
int ea_field_check(ea_session*s){return engine_abi::guard([&]{engine_abi::need(s,"session");s->field->check();});}
int ea_field_checked_open(ea_session*s,const uint64_t*handles,size_t count,uint8_t*out){
    return engine_abi::guard([&]{
        engine_abi::need(s&&(count==0||(handles&&out)),"open arguments");std::vector<emp_hybrid::FieldEngine::Handle>hs;
        for(size_t i=0;i<count;i++)hs.push_back(s->fields.at(handles[i]));
        auto opened=s->field->checked_open(hs);engine_abi::need(opened.size()==count,"opened count");
        for(size_t i=0;i<count;i++)std::memcpy(out+32*i,opened[i].data(),32);
    });
}
int ea_field_free(ea_session*s,uint64_t handle){return engine_abi::guard([&]{engine_abi::need(s,"session");s->fields.drop(handle);});}
}   // extern "C"

// The legacy library shares this translation unit (see the top of this file).
#include "legacy_abi.cpp"
