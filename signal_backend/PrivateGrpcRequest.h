#pragma once
#include <cstdint>
#include <string>
#include <vector>
#include <stdexcept>
#include <utility>

namespace signal_mpc {
// Fixed-shape HTTP/2+gRPC framing. PublicBits creates constants only. Header
// VALUES, authorization, and protobuf request content remain owned shares.
// Each header uses HPACK's never-indexed literal form without Huffman coding,
// so no dynamic compression state stores secret values. Public lengths leak.
// Connection preface/SETTINGS, flow control, response routing, and stream-ID
// allocation are transport responsibilities; this is one already-open stream.
template<class SharedBits,class PublicBits>
SharedBits frame_grpc_request(uint32_t stream,SharedBits authority,SharedBits path,
    SharedBits authorization,SharedBits protobuf,PublicBits&& public_bits) {
    auto require=[](bool ok,const char* why){if(!ok)throw std::runtime_error(why);};
    auto size=[&](const SharedBits& b){require(b.size()%8==0,"unaligned private request");return b.size()/8;};
    require(stream>0 && stream<=0x7fffffff && (stream&1),"invalid client HTTP/2 stream");
    auto an=size(authority),pn=size(path),un=size(authorization),bn=size(protobuf);
    require(an>0&&an<=255&&pn>0&&pn<=2048&&un>0&&un<=2048&&bn>0&&bn<=12000,
        "private request exceeds bounded profile");
    using Bytes=std::vector<uint8_t>;
    auto append=[](SharedBits& out,const SharedBits& in){out.insert(out.end(),in.begin(),in.end());};
    auto integer=[](size_t n,unsigned prefix,uint8_t tag){
        Bytes out;size_t mask=(size_t(1)<<prefix)-1;
        if(n<mask){out.push_back(tag|n);return out;}
        out.push_back(tag|mask);n-=mask;
        while(n>=128){out.push_back((n&127)|128);n>>=7;}out.push_back(n);return out;
    };
    auto literal=[&](SharedBits& headers,const std::string& name,const SharedBits& value){
        auto encoded=integer(name.size(),7,0);encoded.insert(encoded.begin(),0x10);
        encoded.insert(encoded.end(),name.begin(),name.end());
        append(headers,public_bits(encoded));append(headers,public_bits(integer(value.size()/8,7,0)));
        append(headers,value);
    };
    auto headers=public_bits(Bytes{0x83,0x87}); // :method POST, :scheme https
    literal(headers,":authority",authority);literal(headers,":path",path);
    literal(headers,"content-type",public_bits(Bytes{'a','p','p','l','i','c','a','t','i','o','n','/','g','r','p','c'}));
    literal(headers,"te",public_bits(Bytes{'t','r','a','i','l','e','r','s'}));
    literal(headers,"authorization",authorization);
    auto frame_header=[&](size_t length,uint8_t type,uint8_t flags){
        require(length<=16384,"HTTP/2 frame exceeds initial maximum");
        return public_bits(Bytes{uint8_t(length>>16),uint8_t(length>>8),uint8_t(length),type,flags,
          uint8_t(stream>>24),uint8_t(stream>>16),uint8_t(stream>>8),uint8_t(stream)});
    };
    size_t hn=size(headers);
    // A single opaque TLS payload; no splitting or private lengths exposed.
    require(9+hn+9+5+bn<=16384,"private request requires stream fragmentation");
    auto result=frame_header(hn,1,4); // HEADERS / END_HEADERS
    append(result,headers);append(result,frame_header(5+bn,0,1)); // DATA / END_STREAM
    append(result,public_bits(Bytes{0,uint8_t(bn>>24),uint8_t(bn>>16),uint8_t(bn>>8),uint8_t(bn)}));
    append(result,protobuf);return result;
}

// The serializer must assemble the actual service protobuf from shared request
// metadata and shared Signal wire. Retain returns a same-worker opaque TLS
// handle. Any handoff failure destroys this in-memory chain; no rollback/retry.
template<class Store,class Shape,class SharedBits,class Evaluate,class Serialize,class Frame,class Retain>
uint64_t produce_private_request(Store& store,const Shape& shape,SharedBits payload,
    Evaluate&& evaluate,Serialize&& serialize,Frame&& frame,Retain&& retain) {
    try {
        auto produced=store.produce(shape,std::move(payload),std::forward<Evaluate>(evaluate));
        auto request=serialize(std::move(produced.wire));
        auto handle=retain(frame(std::move(request)));
        store.transport_complete(produced.ticket);return handle;
    } catch(...) {store.close();throw;}
}
}
