#include "ApplicationPolicy.h"
#include <cassert>
#include <functional>
#include <iostream>
using P=tls_mpc_worker::ApplicationPolicy;
static bool rejects(const std::function<void()>& f) {try {f();return false;} catch(const std::runtime_error&) {return true;}}
int main() {
    size_t checks=0;
    auto reject=[&](auto f){assert(rejects(f));++checks;};
    P p;
    reject([&]{p.sent();});reject([&]{p.rotated_send();});reject([&]{p.rotated_receive();});
    p.application(0);reject([&]{p.application(0);});reject([&]{p.application(1);});
    reject([&]{p.receive(0);});p.sent();reject([&]{p.application(0);});
    p.update(1,true);reject([&]{p.rotated_send();});p.sent();
    reject([&]{p.application(2);});p.rotated_send();
    assert(p.state().send_epoch==1 && p.state().send_next==0 && p.state().request_outstanding);
    reject([&]{p.update(0,true);});
    p.receive(0);p.event(3,true);reject([&]{p.receive(1);});reject([&]{p.application(0);});p.rotated_receive();
    assert(p.state().response_due && !p.state().request_outstanding && p.state().receive_next==0);
    reject([&]{p.application(0);});reject([&]{p.update(0,true);});
    p.update(0,false);p.sent();p.rotated_send();p.application(0);p.sent();
    assert(!p.state().response_due && p.state().send_epoch==2);
    // Half-close permits the remaining direction and rejects the closed one.
    p.receive(0);p.event(4,false);reject([&]{p.receive(1);});
    p.application(1);p.sent();p.close(2);p.sent();reject([&]{p.application(3);});
    P q;q.close(0);q.sent();q.receive(0);q.event(1,false);q.receive(1);q.event(4,false);
    // Last available sending record is reserved for a control, not payload.
    for(uint64_t epoch:{uint64_t(0),P::max_send_epoch-1,P::max_send_epoch}) {
        P::State s;s.send_epoch=epoch;s.send_next=P::record_limit-1;
        P a(s);reject([&]{a.application(s.send_next);});
        P c(s);c.close(s.send_next);c.sent();
        P u(s);
        if(epoch==P::max_send_epoch) reject([&]{u.update(s.send_next,false);});
        else {u.update(s.send_next,false);u.sent();u.rotated_send();assert(u.state().send_next==0);}
        P::State exhausted=s;exhausted.send_next=P::record_limit;P e(exhausted);
        reject([&]{e.close(exhausted.send_next);});reject([&]{e.update(exhausted.send_next,false);});
    }
    // UINT64_MAX is usable exactly once; only authenticated KU resets it.
    P::State last;last.receive_next=UINT64_MAX;P r(last);
    r.receive(UINT64_MAX);r.event(2,false);reject([&]{r.receive(UINT64_MAX);});reject([&]{r.receive(0);});
    P k(last);k.receive(UINT64_MAX);k.event(3,false);k.rotated_receive();k.receive(0);k.event(1,false);
    P::State ceiling;ceiling.send_epoch=P::max_send_epoch;P e(ceiling);
    e.receive(0);e.event(3,true);e.rotated_receive();assert(!e.state().response_due);
    // Abort is terminal in every split-phase update state.
    for(int point=0;point<5;++point) {
        P a;if(point>0)a.update(0,true);if(point>1)a.sent();if(point>2)a.rotated_send();
        if(point>3){a.receive(0);a.event(3,true);}a.abort();a.abort();
        reject([&]{a.application(0);});reject([&]{a.update(0,false);});reject([&]{a.close(0);});
        reject([&]{a.receive(0);});reject([&]{a.sent();});reject([&]{a.rotated_send();});reject([&]{a.rotated_receive();});
    }
    std::cout<<checks<<" native rejection checks plus key-update/half-close/exhaustion transitions passed\n";
}
