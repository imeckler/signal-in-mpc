#pragma once
#include "NativeWorker.h"
#include "SessionLifecycle.h"
#include "LifecycleWork/SecureGmp.h"
#include "SessionWork/ErasedHostCall.h"

namespace tls_mpc_worker {
class NativeLifecycle final : public SessionLifecycle {
    Machine<Share>& machine;
    bool closed=false, erased=false;
    uint64_t renewed_in=0;
    void require_profile() const {
        public_require(ErasedHostCall::active() && SecureGmp::installed(),"erased host/GMP capability absent");
        public_require(machine.get_N().num_players()==5 && ShamirOptions::singleton.threshold==2 &&
            machine.opts.live_prep && machine.use_encryption && machine.opts.security_parameter==128 &&
            machine.opts.lg2==128 && machine.opts.lgp==255,"unsupported lifecycle profile");
    }
public:
    explicit NativeLifecycle(Machine<Share>& machine):machine(machine) {require_profile();}
    bool host_active() const noexcept override {return ErasedHostCall::active();}
    bool application_allowed() const noexcept override {
        return !closed && host_active() && ErasedHostCall::completed(renewed_in);
    }
    void renew_epoch() override {
        require_profile(); public_require(!closed,"terminal lifecycle");
        try {machine.retire_worker_epoch();renewed_in=ErasedHostCall::generation();}
        catch(...) {closed=true;throw;}
    }
    bool abort_epoch() noexcept override {
        if(closed)return erased;
        closed=true;
        try {require_profile();machine.retire_worker_epoch(false);erased=true;}
        catch(...) {erased=false;}
        return erased;
    }
};
}
