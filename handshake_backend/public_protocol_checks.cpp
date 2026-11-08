#include "PublicProtocol.h"
#include <cassert>
#include <functional>
#include <iostream>
using namespace tls_mpc_worker;
static bool rejects(const std::function<void()>& f) { try { f(); return false; } catch(const std::runtime_error&) { return true; } }
int main() {
    size_t checks=0;
    for(unsigned op=1;op<=25;++op) for(uint64_t sequence:{uint64_t(0),uint64_t(1),UINT64_MAX}) {
        Request r{sequence,Opcode(op),{0,1,127,255}}; auto frame=encode_request(r); auto decoded=decode_request(frame);
        assert(decoded.sequence==sequence&&decoded.operation==r.operation&&decoded.payload==r.payload); ++checks;
        for(size_t n=0;n<frame.size();++n) { auto short_frame=frame;short_frame.resize(n);assert(rejects([&]{decode_request(short_frame);}));++checks; }
        frame.push_back(0);assert(rejects([&]{decode_request(frame);}));++checks;
    }
    for(unsigned op:{0,26,255}) { auto frame=encode_request({0,Opcode::begin,{}});frame[0]=op;assert(rejects([&]{decode_request(frame);}));++checks; }
    auto too_big=encode_request({0,Opcode::begin,{}});too_big[9]=255;
    assert(rejects([&]{decode_request(too_big);}));++checks;
    RequestSequence seq;assert(rejects([&]{seq.reserve(1);}));seq.reserve(0);
    assert(rejects([&]{seq.reserve(0);}));seq.reserve(1);++checks;
    PublicBytes auth{0,1,'x',0,1,0,0,1,42,8,7};auth.resize(auth.size()+32,0);
    auth.insert(auth.end(),{0,1,99,1});assert(authentication_decision(auth));++checks;
    auto rejected=auth;rejected.back()=0;assert(!authentication_decision(rejected));++checks;
    auto bad=auth;bad.back()=2;assert(rejects([&]{authentication_decision(bad);}));++checks;
    for(size_t n=0;n<auth.size();++n) { auto cut=auth;cut.resize(n);assert(rejects([&]{authentication_decision(cut);}));++checks; }
    auth.push_back(0);assert(rejects([&]{authentication_decision(auth);}));++checks;
    std::cout<<checks<<" public framing, bounds, replay and authentication encoding checks passed\n";
}
