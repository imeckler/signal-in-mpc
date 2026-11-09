#pragma once
#include "SendShape.h"
#include <cstdint>
#include <utility>
#include <type_traits>

namespace signal_mpc {
// A single already-selected active Signal/SPQR sending chain. SharedBits must
// own and wipe its shares (native instantiation: tls_mpc_worker::Bits). This
// class never opens data or inspects a shared value. Public sizes/tickets only.
// No disk durability, session initialization, epoch selection or DH/KEM update
// is implied. The caller serializes access on the same worker as TLS.
template<class SharedBits> class EstablishedSendStore {
    static_assert(std::is_nothrow_move_assignable_v<SharedBits> &&
        std::is_nothrow_move_constructible_v<SharedBits>, "share ownership moves must not throw");
    SharedBits state_,addresses_,last_status_;
    bool poisoned_=false,pending_=false;
    uint64_t ticket_=0;
    static void require(bool ok,const char* reason) {if(!ok)throw std::runtime_error(reason);}
    static SharedBits bytes(const SharedBits& bits,size_t offset,size_t count) {
        require(bits.size()%8==0 && offset<=bits.size()/8 && count<=bits.size()/8-offset,
            "invalid Signal shared slice");
        return SharedBits(bits.begin()+offset*8,bits.begin()+(offset+count)*8);
    }
    static void append(SharedBits& out,const SharedBits& bits) {
        out.insert(out.end(),bits.begin(),bits.end());
    }
    void live() const {require(!poisoned_,"Signal send store is closed");}
public:
    // state181: version1,counter4,previous4,ratchet32,chain32,PQchain32,
    // PQcounter4,epoch8,senderIdentity32,recipientIdentity32.
    // addresses0/36 are bound to this state, not supplied afresh per send.
    explicit EstablishedSendStore(SharedBits state,SharedBits addresses)
        :state_(std::move(state)),addresses_(std::move(addresses)) {
        require(state_.size()==181*8 && (addresses_.empty() || addresses_.size()==36*8),
            "invalid established Signal state dimensions");
    }
    ~EstablishedSendStore(){close();}
    EstablishedSendStore(const EstablishedSendStore&)=delete;
    EstablishedSendStore& operator=(const EstablishedSendStore&)=delete;
    struct Produced {uint64_t ticket;SharedBits wire;};
    // Payload: secret kind1, optional chunkIndex2+chunkData32, plaintext.
    // Evaluate must validate/pin shape.descriptor(), collectively agree its
    // program closure before private execution, and return owned shared bits.
    template<class Evaluate> Produced produce(const SendShape& shape,SharedBits payload,Evaluate&& evaluate) {
        live();require(!pending_,"Signal send already awaits transport completion");
        require(ticket_!=UINT64_MAX,"Signal send ticket exhausted");
        require(shape.address_bytes()*8==addresses_.size() &&
            payload.size()==8*(1+shape.chunk_bytes()+shape.plaintext_bytes()),
            "Signal send payload/profile mismatch");
        // Reserve before invoking a stateful private runtime. Any exception
        // poisons this chain; there is no retry with possibly consumed state.
        pending_=true;++ticket_;
        try {
            auto input=bytes(state_,0,117);
            append(input,bytes(payload,0,1+shape.chunk_bytes()));
            append(input,bytes(state_,117,64));
            append(input,bytes(payload,1+shape.chunk_bytes(),shape.plaintext_bytes()));
            append(input,addresses_);
            require(input.size()==shape.input_bytes()*8,"Signal send input assembly mismatch");
            auto output=evaluate(shape,std::move(input));
            require(output.size()==shape.output_bytes()*8,"Signal send output size mismatch");
            // Allocate every output before committing. The circuit has already
            // selected old state on rejection and zeroed its wire; acceptance
            // stays shared and is never used for a host branch.
            auto status=bytes(output,0,1);
            auto next=bytes(state_,0,1);
            append(next,bytes(output,33,4));
            append(next,bytes(state_,5,36));
            append(next,bytes(output,1,32));
            append(next,bytes(output,37,32));
            append(next,bytes(output,69,4));
            append(next,bytes(state_,109,72));
            auto wire=bytes(output,73,shape.wire_bytes());
            state_=std::move(next);last_status_=std::move(status);
            // State is committed before any wire becomes eligible for TLS.
            return {ticket_,std::move(wire)};
        } catch(...) {close();throw;}
    }
    // Call only once the immutable wire is handed to the transport's pending
    // ciphertext mechanism. A failed handoff must close(), never re-encrypt.
    void transport_complete(uint64_t ticket) {
        live();require(pending_ && ticket==ticket_,"stale Signal transport ticket");pending_=false;
    }
    void close() noexcept {
        poisoned_=true;pending_=false;state_.clear();addresses_.clear();last_status_.clear();
    }
};
}
