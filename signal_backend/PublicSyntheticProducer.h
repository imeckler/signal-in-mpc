#pragma once
// TEST FIXTURE ONLY: publicly known disposable chain/identity material.
// Never expose this initializer through a production RPC or use it for live sends.
#include "EstablishedSendStore.h"
#include "PrivateGrpcRequest.h"
#include <memory>

namespace signal_mpc {
template<class SharedBits> class PublicSyntheticProducer {
    using Bytes=std::vector<uint8_t>;
    std::unique_ptr<EstablishedSendStore<SharedBits>> store_;
    uint64_t pending_ticket_=0;
    bool closed_=false;
    unsigned completed_=0;
    static Bytes initial_state() {
        // check_lean_signal_spqr_send.cases(): consecutive-coupled-state-0.
        const std::string hex=
          "04000000000000000061495c6d3b3215b0b6d10a73415f8e271852515c5808f7fbb970e1156e87ba50c"
          "901e6b2fedd436fa6c9b4b6261a785f01af17571d8b0e0cd5527366e55da368e449b8b68b121f83e2c864b88cdf7db05280c5f32914349361bb349f28e89dfd"
          "0000000000000000000000015b35ffb674f0db142cb10efc2d17f9c978945501f00204ad7abafe5e71afdcc00b2a60078e4ad01bfea5b45a6dcf767afdd8f7846ad1b54ddb686726d94363f3";
        Bytes result;
        for(size_t i=0;i<hex.size();i+=2)result.push_back(std::stoul(hex.substr(i,2),nullptr,16));
        return result;
    }
public:
    static constexpr size_t payload_bytes=228;
    static SendShape shape(){return {0,1,1,1,1,0,false,false};}
    PublicSyntheticProducer()=default;
    PublicSyntheticProducer(const PublicSyntheticProducer&)=delete;
    PublicSyntheticProducer& operator=(const PublicSyntheticProducer&)=delete;
    template<class Evaluate,class PublicBits>
    SharedBits produce(Evaluate&& evaluate,PublicBits&& public_bits) {
        try {
            if(closed_ || pending_ticket_ || completed_>=3)throw std::runtime_error("synthetic producer unavailable/pending");
            if(!store_)store_=std::make_unique<EstablishedSendStore<SharedBits>>(public_bits(initial_state()),SharedBits{});
            auto output=store_->produce(shape(),public_bits(Bytes{0}),std::forward<Evaluate>(evaluate));
            pending_ticket_=output.ticket;
            // Fixture request proto: field1 bytes containing the actual shared
            // Signal wire. This is NOT Signal's service request protobuf.
            auto protobuf=public_bits(Bytes{0x0a,72});
            protobuf.insert(protobuf.end(),output.wire.begin(),output.wire.end());
            auto text=[&](const std::string& value){return public_bits(Bytes(value.begin(),value.end()));};
            auto framed=frame_grpc_request(uint32_t(2*completed_+1),text("fixture.invalid"),
                text("/fixture.Signal/Send"),text("Basic fixture"),std::move(protobuf),public_bits);
            if(framed.size()!=payload_bytes*8)throw std::runtime_error("synthetic frame size mismatch");
            return framed;
        } catch(...) {close();throw;}
    }
    void transport_complete() {
        try {
            if(closed_ || !store_ || !pending_ticket_)throw std::runtime_error("no synthetic send pending");
            store_->transport_complete(pending_ticket_);pending_ticket_=0;++completed_;
        } catch(...) {close();throw;}
    }
    void close() noexcept {closed_=true;pending_ticket_=0;if(store_)store_->close();}
};
}
