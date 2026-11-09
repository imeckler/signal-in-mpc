#pragma once
#include <cstdint>
#include <limits>
#include <stdexcept>

namespace tls_mpc_worker {
// Additional native guard; the Lean controller remains the protocol source.
// Reservation precedes effects. Any failed effect must abort the session.
class SessionPolicy {
public:
    enum class Phase { fresh, hello, handshake, authenticated, verified, application, aborted };
private:
    Phase phase_ = Phase::fresh;
    uint64_t receive_ = 0;
    bool exhausted_ = false;
    static void require(bool ok) { if (!ok) throw std::runtime_error("invalid TLS worker phase or sequence"); }
public:
    Phase phase() const { return phase_; }
    void begin() { require(phase_ == Phase::fresh); phase_ = Phase::hello; }
    void derive() { require(phase_ == Phase::hello); phase_ = Phase::handshake; }
    void receive(uint64_t sequence) {
        require((phase_ == Phase::handshake || phase_ == Phase::authenticated) && !exhausted_ && sequence == receive_);
        if (receive_ == std::numeric_limits<uint64_t>::max()) exhausted_ = true;
        else ++receive_;
    }
    void authenticate() { require(phase_ == Phase::handshake); phase_ = Phase::authenticated; }
    void verify() { require(phase_ == Phase::authenticated); phase_ = Phase::verified; }
    void finish() { require(phase_ == Phase::verified); phase_ = Phase::application; }
    void abort() noexcept { phase_ = Phase::aborted; }
};
}
