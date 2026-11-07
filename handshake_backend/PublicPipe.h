#pragma once
#include "PublicProtocol.h"
#include <istream>
#include <ostream>
#include <optional>
namespace tls_mpc_worker {
inline PublicBytes read_exact(std::istream& input, size_t size) {
    public_require(size<=max_request_bytes,"pipe read exceeds bound");
    PublicBytes data(size);
    if(size) { input.read(reinterpret_cast<char*>(data.data()),size); public_require(size_t(input.gcount())==size,"truncated pipe frame"); }
    return data;
}
inline std::optional<Request> read_request(std::istream& input) {
    int first=input.get(); if(first==std::char_traits<char>::eof()) return std::nullopt;
    auto header=read_exact(input,12); header.insert(header.begin(),uint8_t(first));
    Cursor in{header}; in.number(1); in.number(8); auto size=in.number(4);
    public_require(size<=max_request_bytes,"oversized pipe payload");
    auto payload=read_exact(input,size); header.insert(header.end(),payload.begin(),payload.end());
    return decode_request(header);
}
inline void write_reply(std::ostream& output, bool success, const PublicBytes& data) {
    public_require(data.size()<=max_request_bytes,"oversized pipe response");
    PublicBytes header{uint8_t(success?0:1)}; put_number(header,data.size(),4);
    output.write(reinterpret_cast<const char*>(header.data()),header.size());
    output.write(reinterpret_cast<const char*>(data.data()),data.size()); output.flush();
    public_require(bool(output),"worker reply write failed");
}
}
