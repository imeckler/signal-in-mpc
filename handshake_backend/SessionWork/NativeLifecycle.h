#pragma once
#include "NativeWorker.h"
#include "SessionLifecycle.h"
#include "LifecycleWork/SecureGmp.h"
#include "SessionWork/ErasedHostCall.h"
#include "PublicMetrics.h"
#include <chrono>

namespace tls_mpc_worker {
class NativeLifecycle final : public SessionLifecycle {
    Machine<Share>& machine;
    bool closed=false, erased=false;
    uint64_t renewed_in=0;
    ApplicationEpochPolicy record_policy;
    uint64_t renewals_=0,renewal_ns_=0;
    PublicMetrics* metrics;
    void require_profile() const {
        public_require(ErasedHostCall::active() && SecureGmp::installed(),"erased host/GMP capability absent");
        public_require(machine.get_N().num_players()==5 && ShamirOptions::singleton.threshold==2 &&
            machine.opts.live_prep && machine.use_encryption && machine.opts.security_parameter==128 &&
            machine.opts.lg2==128 && machine.opts.lgp==255,"unsupported lifecycle profile");
    }
public:
    explicit NativeLifecycle(Machine<Share>& machine,ApplicationEpochPolicy policy=ApplicationEpochPolicy::explicit_boundaries,PublicMetrics* metrics=nullptr)
        :machine(machine),record_policy(policy),metrics(metrics) {require_profile();}
    ApplicationEpochPolicy application_epoch_policy() const noexcept override {return record_policy;}
    uint64_t renewal_count() const noexcept {return renewals_;}
    uint64_t renewal_nanoseconds() const noexcept {return renewal_ns_;}
    bool host_active() const noexcept override {return ErasedHostCall::active();}
    bool application_allowed() const noexcept override {
        return !closed && host_active() && ErasedHostCall::completed(renewed_in);
    }
    void renew_epoch() override {
        require_profile(); public_require(!closed,"terminal lifecycle");
        try {
            auto measurement=metrics?metrics->begin():PublicMetrics::Token{};
            auto started=std::chrono::steady_clock::now();
            machine.retire_worker_epoch();
            renewal_ns_+=std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now()-started).count();
            ++renewals_;renewed_in=ErasedHostCall::generation();
            if(metrics){metrics->committed_epoch(measurement.counts,false);metrics->finish("epoch.renew",measurement);}
        }
        catch(...) {closed=true;if(metrics)metrics->failed_terminal();throw;}
    }
    bool abort_epoch() noexcept override {
        if(closed)return erased;
        closed=true;
        try {require_profile();auto measurement=metrics?metrics->begin():PublicMetrics::Token{};
            machine.retire_worker_epoch(false);erased=true;
            if(metrics){metrics->committed_epoch(measurement.counts,true);metrics->finish("epoch.abort",measurement);}}
        catch(...) {erased=false;if(metrics)metrics->failed_terminal();}
        return erased;
    }
};
}
