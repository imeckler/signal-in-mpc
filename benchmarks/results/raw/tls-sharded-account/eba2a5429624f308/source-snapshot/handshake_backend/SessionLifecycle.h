#pragma once
namespace tls_mpc_worker {
enum class ApplicationEpochPolicy { explicit_boundaries, every_record };
// Trusted embedding capability. Production workers supply none. The isolated
// candidate binds actual protocol/transport renewal plus a host-stack barrier.
// An external receipt may be sent only after that barrier completes.
class SessionLifecycle {
public:
    virtual ~SessionLifecycle()=default;
    virtual bool host_active() const noexcept=0;
    virtual bool application_allowed() const noexcept=0;
    virtual ApplicationEpochPolicy application_epoch_policy() const noexcept=0;
    virtual void renew_epoch()=0;
    virtual bool abort_epoch() noexcept=0;
};
}
