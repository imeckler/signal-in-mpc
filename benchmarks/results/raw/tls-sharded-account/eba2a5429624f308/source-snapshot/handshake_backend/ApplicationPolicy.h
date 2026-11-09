#pragma once
#include <cstdint>
#include <limits>
#include <stdexcept>

namespace tls_mpc_worker {
// Unverified native enforcement of TlsApplicationPolicy. Reservation precedes
// cryptography; send acknowledgement precedes key rotation. Any failed effect
// must abort through Session/Dispatch. Receive epoch needs no bounded counter.
class ApplicationPolicy {
public:
    static constexpr uint64_t record_limit=uint64_t(1)<<24;
    static constexpr uint64_t max_send_epoch=(uint64_t(1)<<48)-1;
    enum class Pending { none, application, close, update_sealed, update_sent };
    struct State {
        uint64_t send_epoch=0, send_next=0, receive_next=0;
        bool receive_exhausted=false, response_due=false, request_outstanding=false;
        bool send_closed=false, receive_closed=false, aborted=false;
        Pending pending=Pending::none;
        bool update_request=false, receive_update=false, receive_request=false;
    };
private:
    State state_;
    static void require(bool ok) { if(!ok) throw std::runtime_error("invalid native application phase/sequence"); }
    void idle() const { require(!state_.aborted && state_.pending==Pending::none && !state_.receive_update); }
    void sender(uint64_t seq) const { idle(); require(!state_.send_closed && seq==state_.send_next); }
public:
    ApplicationPolicy()=default;
    // Boundary-state injection is used only by the standalone public fixture.
    explicit ApplicationPolicy(State state):state_(state) {}
    const State& state() const { return state_; }
    void application(uint64_t seq) {
        sender(seq); require(!state_.response_due && seq<record_limit-1);
        ++state_.send_next; state_.pending=Pending::application;
    }
    void update(uint64_t seq,bool request) {
        sender(seq); require(state_.send_epoch<max_send_epoch && seq<record_limit &&
            !(request && (state_.request_outstanding || state_.response_due)));
        ++state_.send_next; state_.pending=Pending::update_sealed; state_.update_request=request;
    }
    void close(uint64_t seq) {
        sender(seq); require(seq<record_limit); ++state_.send_next;
        state_.send_closed=true; state_.pending=Pending::close;
    }
    void sent() {
        require(!state_.aborted && !state_.receive_update);
        switch(state_.pending) {
        case Pending::application: case Pending::close: state_.pending=Pending::none; break;
        case Pending::update_sealed: state_.pending=Pending::update_sent; break;
        default: throw std::runtime_error("unexpected application send acknowledgement");
        }
    }
    void rotated_send() {
        require(!state_.aborted && !state_.send_closed && state_.pending==Pending::update_sent);
        ++state_.send_epoch; state_.send_next=0; state_.pending=Pending::none;
        state_.response_due=false;
        state_.request_outstanding=state_.request_outstanding || state_.update_request;
    }
    void receive(uint64_t seq) {
        idle(); require(!state_.receive_closed && !state_.receive_exhausted && seq==state_.receive_next);
        if(seq==std::numeric_limits<uint64_t>::max()) state_.receive_exhausted=true;
        else ++state_.receive_next;
    }
    void event(unsigned kind,bool request) {
        require(!state_.aborted && !state_.receive_update);
        if(kind==3) { state_.receive_update=true; state_.receive_request=request; }
        else if(kind==4) state_.receive_closed=true;
        else require(kind==1 || kind==2);
    }
    void rotated_receive() {
        require(!state_.aborted && state_.receive_update);
        state_.receive_next=0; state_.receive_exhausted=false; state_.receive_update=false;
        state_.request_outstanding=false;
        state_.response_due=state_.response_due || (state_.receive_request && state_.send_epoch<max_send_epoch);
    }
    void abort() noexcept { state_.aborted=true; }
};
}
