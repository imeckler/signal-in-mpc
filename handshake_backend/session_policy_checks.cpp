#include "SessionPolicy.h"
#include <cassert>
#include <functional>
#include <iostream>
using P = tls_mpc_worker::SessionPolicy;
static bool rejects(const std::function<void()>& f) { try { f(); return false; } catch (const std::runtime_error&) { return true; } }
int main() {
    P p;
    assert(rejects([&]{ p.finish(); }));
    assert(rejects([&]{ p.derive(); }));
    p.begin(); assert(rejects([&]{ p.begin(); }));
    p.derive(); assert(rejects([&]{ p.derive(); }));
    assert(rejects([&]{ p.verify(); }));
    assert(rejects([&]{ p.finish(); }));
    assert(rejects([&]{ p.receive(1); }));
    p.receive(0); assert(rejects([&]{ p.receive(0); }));
    p.authenticate(); assert(rejects([&]{ p.authenticate(); }));
    p.receive(1); p.verify();
    assert(rejects([&]{ p.receive(2); }));
    p.finish(); assert(rejects([&]{ p.finish(); }));
    for (int point=0; point<7; ++point) {
        P q;
        if(point>=1) q.begin();
        if(point>=2) q.derive();
        if(point>=3) q.receive(0);
        if(point>=4) q.authenticate();
        if(point>=5) q.verify();
        if(point>=6) q.finish();
        q.abort(); q.abort();
        assert(rejects([&]{ q.begin(); })); assert(rejects([&]{ q.derive(); }));
        assert(rejects([&]{ q.receive(1); })); assert(rejects([&]{ q.authenticate(); }));
        assert(rejects([&]{ q.verify(); })); assert(rejects([&]{ q.finish(); }));
    }
    std::cout << "phase/order/sequence/replay checks passed; abort terminal at all seven checkpoints\n";
}
