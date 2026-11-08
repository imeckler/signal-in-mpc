#pragma once
#include "NativeWorker.h"
#include <chrono>
#include <fstream>
#include <iostream>
#include <optional>
namespace tls_mpc_worker {
// Public work/communication metadata only. These are MP-SPDZ protocol payload
// counters, not link-layer bytes. Parallel communication operations are summed,
// not interpreted as critical-path network rounds. No share contents are read.
class PublicMetrics {
public:
    struct Counts {
        uint64_t worker_bytes=0,host_bytes=0,communication_operations=0;
        uint64_t external_tls_sent=0,external_tls_received=0;
        Counts operator+(const Counts& x) const {return{worker_bytes+x.worker_bytes,host_bytes+x.host_bytes,
            communication_operations+x.communication_operations,external_tls_sent+x.external_tls_sent,
            external_tls_received+x.external_tls_received};}
    };
    struct Token {Counts counts;std::chrono::steady_clock::time_point time;};
private:
    Machine<tls_mpc_worker::Share>& machine;unsigned party;
    Counts sealed,external;bool terminal=false;
    struct FunctionTotals {
        size_t calls=0,timed_calls=0;uint64_t verification_ns=0,machine_run_ns=0;bool initialized=false,declared_known=false,actual_available=true;
        DataPositions per_call,declared_total,actual_total;
    };
    std::map<std::string,FunctionTotals> functions;
    bool resources_complete=true;
    static uint64_t operations(const NamedCommStats& stats) {
        uint64_t result=0;for(const auto& item:stats)result+=item.second.rounds;return result;
    }
    template<class M> static std::optional<DataPositions> actual_usage(M& machine) {
        if constexpr(requires(M& value){value.public_function_usage();})return machine.public_function_usage();
        else return std::nullopt;
    }
    void usage(const char* source,const DataPositions& data) noexcept {
        try {
            for(size_t field=0;field<N_DATA_FIELD_TYPE;++field)for(size_t kind=0;kind<N_DTYPE;++kind)
                if(data.files[field][kind])std::cerr<<"TLS_RESOURCE {\"party\":"<<party<<",\"source\":\""<<source
                    <<"\",\"field\":"<<field<<",\"kind\":"<<kind<<",\"count\":"<<data.files[field][kind]<<"}\n";
        }catch(...){}
    }
public:
    explicit PublicMetrics(Machine<tls_mpc_worker::Share>& machine,unsigned party):machine(machine),party(party){}
    Counts snapshot() noexcept {
        if(terminal)return sealed+external;
        try {
            auto worker=machine.total_stats().comm_stats;
            auto host=machine.get_player().total_comm();
            return sealed+external+Counts{worker.sent,host.sent,operations(worker)+operations(host),0,0};
        }catch(...){return sealed+external;}
    }
    Token begin() noexcept {return{snapshot(),std::chrono::steady_clock::now()};}
    void finish(const char* stage,const Token& before,bool success=true) noexcept {
        try {
            auto after=snapshot();auto ns=std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now()-before.time).count();
            bool monotone=after.worker_bytes>=before.counts.worker_bytes&&after.host_bytes>=before.counts.host_bytes&&
                after.communication_operations>=before.counts.communication_operations&&after.external_tls_sent>=before.counts.external_tls_sent&&
                after.external_tls_received>=before.counts.external_tls_received;
            std::cerr<<"TLS_METRIC {\"party\":"<<party<<",\"stage\":\""<<stage<<"\",\"success\":"<<(success?"true":"false")
                <<",\"elapsed_ns\":"<<ns<<",\"counters_monotone\":"<<(monotone?"true":"false");
            if(monotone)std::cerr<<",\"worker_payload_bytes\":"<<after.worker_bytes-before.counts.worker_bytes
                <<",\"host_payload_bytes\":"<<after.host_bytes-before.counts.host_bytes
                <<",\"communication_operations\":"<<after.communication_operations-before.counts.communication_operations
                <<",\"external_tls_sent\":"<<after.external_tls_sent-before.counts.external_tls_sent
                <<",\"external_tls_received\":"<<after.external_tls_received-before.counts.external_tls_received;
            std::cerr<<"}\n";
        }catch(...){}
    }
    // Capture BEFORE cleanup destroys protocol owners. Final retirement checks,
    // TLS/socket overhead and transport setup are not in this payload snapshot.
    // Their time remains included in the epoch/stage wall-clock measurements.
    void committed_epoch(Counts before,bool is_terminal) noexcept {
        sealed=before;sealed.external_tls_sent=0;sealed.external_tls_received=0;terminal=is_terminal;
    }
    void failed_terminal() noexcept {terminal=true;}
    void external_record(bool sent,size_t bytes) noexcept {
        if(party==0){if(sent)external.external_tls_sent+=bytes;else external.external_tls_received+=bytes;}
    }
    void function_resources(const std::string& descriptor,uint64_t verify_ns=0,uint64_t run_ns=0,bool timed=false) noexcept {
        try {
            auto& total=functions[descriptor];
            if(!total.initialized){
                std::ifstream file(descriptor);std::string program;size_t tape;file>>program>>tape;
                if(!file||tape>=machine.progs.size()){resources_complete=false;return;}
                auto& selected=machine.progs[tape];total.per_call=selected.get_offline_data_used();
                total.declared_known=!selected.usage_unknown();total.initialized=true;
            }
            ++total.calls;total.declared_total.increase(total.per_call);
            if(timed){++total.timed_calls;total.verification_ns+=verify_ns;total.machine_run_ns+=run_ns;}
            if(auto actual=actual_usage(machine))total.actual_total.increase(*actual);
            else total.actual_available=false;
        }catch(...){resources_complete=false;}
    }
    void emit_resources() noexcept {
        try {
            for(auto& item:functions){
                std::cerr<<"TLS_RESOURCE_META {\"party\":"<<party<<",\"descriptor\":\""<<item.first
                    <<"\",\"calls\":"<<item.second.calls<<",\"timed_calls\":"<<item.second.timed_calls
                    <<",\"verification_ns\":"<<item.second.verification_ns<<",\"machine_run_ns\":"<<item.second.machine_run_ns<<",\"declared_known\":"<<(item.second.declared_known?"true":"false")
                    <<",\"actual_available\":"<<(item.second.actual_available?"true":"false")<<"}\n";
                usage("compiler_declared_demand",item.second.declared_total);
                if(item.second.actual_available)usage("runtime_function_consumed",item.second.actual_total);
            }
            std::cerr<<"TLS_RESOURCE_COMPLETE {\"party\":"<<party<<",\"complete\":"<<(resources_complete?"true":"false")<<"}\n";
        }catch(...){}
    }

};
}
