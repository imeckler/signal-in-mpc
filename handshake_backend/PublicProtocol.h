#pragma once
#include <cstdint>
#include <vector>
#include <stdexcept>
#include <limits>

namespace tls_mpc_worker {
using PublicBytes = std::vector<uint8_t>;
enum class Opcode : uint8_t { begin=1, derive=2, open=3, authenticate=4, verify=5, finish=6, retire=7, abort=8, connect=9, send=10, receive=11,
    open_application=12, seal_application=13, seal_control=14, rotate_send=15, rotate_receive=16, poll_receive=17, process_websocket=18, provider_catalogue=19, provider_upgrade=20, provider_produce=21, mux_catalogue=22, mux_upgrade=23, mux_produce=24, mux_process=25, mux_produce_batch=26 };
constexpr size_t max_request_bytes = 2 * 1024 * 1024;
inline void public_require(bool ok, const char* reason) { if (!ok) throw std::runtime_error(reason); }
struct Cursor {
    const PublicBytes& data; size_t offset=0;
    PublicBytes take(size_t n) {
        public_require(n <= data.size()-offset, "truncated public request");
        PublicBytes result(data.begin()+offset,data.begin()+offset+n); offset+=n; return result;
    }
    uint64_t number(size_t n) {
        public_require(n<=8,"oversized integer"); uint64_t value=0;
        for(auto byte:take(n)) value=(value<<8)|byte;
        return value;
    }
    void done() const { public_require(offset==data.size(),"trailing public request data"); }
};
inline void put_number(PublicBytes& out, uint64_t value, size_t n) {
    public_require(n<=8,"oversized integer");
    for(size_t i=n;i>0;--i) out.push_back((value>>(8*(i-1)))&255);
}
struct Request { uint64_t sequence; Opcode operation; PublicBytes payload; };
inline PublicBytes encode_request(const Request& request) {
    public_require(request.payload.size()<=max_request_bytes,"public request too large");
    auto op=static_cast<uint8_t>(request.operation);
    public_require(op>=1 && op<=26,"unknown worker operation");
    PublicBytes out{op}; put_number(out,request.sequence,8); put_number(out,request.payload.size(),4);
    out.insert(out.end(),request.payload.begin(),request.payload.end()); return out;
}
inline Request decode_request(const PublicBytes& frame) {
    public_require(frame.size()<=max_request_bytes+13,"public frame too large");
    Cursor in{frame}; auto op=in.number(1); public_require(op>=1&&op<=26,"unknown worker operation");
    auto sequence=in.number(8); auto size=in.number(4);
    public_require(size<=max_request_bytes,"public payload too large");
    auto payload=in.take(size); in.done(); return {sequence,Opcode(op),std::move(payload)};
}
// Parse the exact public certificate-validation request emitted by Lean.
// Certificate cryptography remains local to each Lean controller's auth helper.
inline bool authentication_decision(const PublicBytes& payload) {
    Cursor in{payload}; auto host=in.take(in.number(2));
    public_require(!host.empty(),"empty authentication hostname");
    auto count=in.number(2); public_require(count>0,"empty server certificate chain");
    for(size_t i=0;i<count;++i) { auto n=in.number(3); public_require(n>0,"empty server certificate"); in.take(n); }
    in.number(2); in.take(32); auto n=in.number(2);
    public_require(n>0,"empty CertificateVerify signature"); in.take(n);
    auto decision=in.number(1); public_require(decision<=1,"invalid authentication decision"); in.done();
    return decision==1;
}
class RequestSequence {
    uint64_t next=0; bool exhausted=false;
public:
    void reserve(uint64_t sequence) {
        public_require(!exhausted && sequence==next,"worker request replay/gap");
        if(next==std::numeric_limits<uint64_t>::max()) exhausted=true; else ++next;
    }
};
}
