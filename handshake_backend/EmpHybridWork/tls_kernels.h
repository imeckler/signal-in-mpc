#pragma once
// TLS 1.3 client on the two engines. All secret state is held here as named
// private wire bundles; every circuit is a Lean kernel (TlsMpc/HybridKernels.lean)
// bound by field name through kernel.h. This file sequences kernels, runs the
// key-agreement protocol in the field engine, and holds handles. It contains no
// circuit layout: it never slices a key out of a block or assembles an input.
// Only outputs Lean marks as openable are opened.
#include "kernel.h"
#include "dyn_word_mask.h"
#include "x25519_fast.h"
#include "split_ecdh.h"
namespace emp_hybrid {
class TlsKernels {
public:   // engine references and shared resources are also used by service_kernels.h
    DynSession&s;FE&f;Challenge&channel;int party;WordCircuits circuits;X25519Fast curve;KernelCache cache;
    std::vector<DynMask>masks;size_t next_mask=0;std::vector<H>swaps;SplitEcdh split;
    // Key agreement route. Default: additively shared scalar, local scalar
    // multiplications, one point addition in the field engine (split_ecdh.h).
    // true: the shared-scalar Montgomery ladder proved against RFC 7748 in Lean.
    bool ladder_agreement=false;
    // Named private values: clientHandshake, serverHandshake, mainSecret,
    // clientApplication, serverApplication, parser.
    Values state;
    TlsKernels(DynSession&session,FE&field,Challenge&c,int p,const std::string&cache_script):s(session),f(field),channel(c),party(p),cache(cache_script,c){}
    uint64_t and_gates()const{return s.and_gates();}
    Wires constant(const std::vector<uint8_t>&bytes){return s.public_bits(byte_bits(bytes));}
    const Wires&held(const std::string&name)const{auto it=state.find(name);if(it==state.end()||it->second.size()==0)throw std::runtime_error("no private value "+name);return it->second;}
    void keep(Values&out,const std::string&name,const std::string&as=""){state[as.empty()?name:as]=std::move(out.at(name));}
    void prepare(){masks=generate_masks(s,f,channel,party,circuits,16);}
    // Next unused conversion mask; a fresh verified batch is generated when the current one is spent.
    DynMask&take_mask(){
        if(next_mask>=masks.size()){masks=generate_masks(s,f,channel,party,circuits,16);next_mask=0;}
        return masks[next_mask++];
    }
    // Ladder swap bits (as field-bit shares) of the X25519 scalar whose bits are
    // the XOR of both parties' `share` arguments. Every contribution is checked to be a bit.
    std::vector<H> shared_scalar(const std::array<uint8_t,32>&share){
        auto bit=[&](unsigned i){return uint64_t((share[i/8]>>(i%8))&1);};
        std::vector<uint64_t>local(252);
        for(unsigned step=2;step<=253;step++)local[step-2]=step==2?bit(3):step==253?(bit(253)^uint64_t(party==emp::ALICE)):(bit(step+1)^bit(step));
        auto shares=f.input_coins(local);f.check();
        std::vector<H>all=shares[0];all.insert(all.end(),shares[1].begin(),shares[1].end());
        for(auto&v:f.checked_open(circuits.field_bit_checks(f,all)))for(auto byte:v)if(byte)throw std::runtime_error("non-bit scalar contribution");
        return circuits.field_bit_xor(f,shares[0],shares[1]);
    }
    // Private 255-bit word (value reduced mod p) -> one field share, consuming one mask.
    H word_to_field(const Wires&value){
        if(value.size()!=255)throw std::runtime_error("word width");
        auto&mask=take_mask();if(mask.used)throw std::runtime_error("word mask reuse");mask.used=true;
        auto opened=bits_to_bytes(s.open(s.run(circuits.into_field,DynSession::concat({&value,&mask.bits}))),0);   // ((u mod p)+r) mod p
        if(!canonical(opened))throw std::runtime_error("noncanonical masked word");
        std::array<uint8_t,32>peer{};channel.transfer(opened.data(),peer.data(),32);if(opened!=peer)throw std::runtime_error("public masked value disagreement");
        return f.sub(f.public_element(opened),mask.field);
    }
    // X25519 of a shared scalar and a field-shared point, as the private 255-bit word kernels take.
    Wires agreement_word(const std::vector<H>&scalar,H point){
        bool zero=false;auto result=curve.evaluate(f,channel,scalar,point,zero);
        return field_to_word(s,f,channel,circuits,take_mask(),result);
    }
    // Client key share. Split route: public sum of two locally computed shares.
    // Ladder route: X25519 of a shared scalar with the base point, then opened.
    std::array<uint8_t,32> begin(){
        if(!ladder_agreement)return split.begin(channel,party);
        std::array<uint8_t,32>seed{};{emp::PRG prg;prg.random_data_unaligned(seed.data(),32);}
        swaps=shared_scalar(seed);
        bool zero=false;auto public_key=curve.evaluate(f,channel,swaps,f.constant(9),zero);
        if(zero)throw std::runtime_error("degenerate public key");
        return f.checked_open({public_key}).at(0);
    }
    // Agreement with the server's public key share, then the handshake key
    // schedule on the unopened result. An all-zero agreement aborts, as TLS requires.
    void derive(std::array<uint8_t,32>peer,const std::vector<uint8_t>&hello_hash){
        if((ladder_agreement&&swaps.size()!=252)||hello_hash.size()!=32)throw std::runtime_error("derive state");
        peer[31]&=127;
        if(!canonical(peer)){unsigned carry=19;for(auto&b:peer){unsigned v=b+carry;b=uint8_t(v);carry=v>>8;}peer[31]&=127;}   // public value reduced mod p
        bool zero=false;auto agreement=ladder_agreement?curve.evaluate(f,channel,swaps,f.public_element(peer),zero):split.agree(f,channel,curve,peer,zero);
        if(zero)throw std::runtime_error("all-zero key agreement");
        auto word=field_to_word(s,f,channel,circuits,take_mask(),agreement),hash=constant(hello_hash);
        auto out=cache.get("tls-derive").run(s,{{"agreement",&word},{"helloHash",&hash}});
        keep(out,"clientHandshake");keep(out,"serverHandshake");keep(out,"mainSecret");swaps.clear();
    }
    std::vector<uint8_t> open_handshake(const std::vector<uint8_t>&sequence,const std::vector<uint8_t>&wire){
        auto&kernel=cache.get("tls-open-handshake "+std::to_string(wire.size()));auto seq=constant(sequence),record=constant(wire);
        return kernel.open(s,kernel.run(s,{{"serverHandshake",&held("serverHandshake")},{"sequence",&seq},{"record",&record}}),"result");
    }
    bool verify_finished(const std::vector<uint8_t>&hash,const std::vector<uint8_t>&message){
        auto&kernel=cache.get("tls-verify-finished");auto h=constant(hash),m=constant(message);
        auto out=kernel.open(s,kernel.run(s,{{"serverHandshake",&held("serverHandshake")},{"transcriptHash",&h},{"message",&m}}),"accepted");
        if(out.size()!=1||(out[0]!=0&&out[0]!=255))throw std::runtime_error("acceptance byte");return out[0]==255;
    }
    std::vector<uint8_t> finish(const std::vector<uint8_t>&server_hash,const std::vector<uint8_t>&client_hash,const std::vector<uint8_t>&certificate){
        auto&kernel=cache.get("tls-finish "+std::to_string(certificate.size()));auto sh=constant(server_hash),ch=constant(client_hash),cert=constant(certificate);
        auto out=kernel.run(s,{{"mainSecret",&held("mainSecret")},{"serverHash",&sh},{"clientHandshake",&held("clientHandshake")},{"clientHash",&ch},{"certificate",&cert}});
        keep(out,"clientApplication");keep(out,"serverApplication");return kernel.open(s,out,"record");
    }
    // Drop the handshake-phase wire handles (not an erasure receipt).
    void retire(){state.erase("clientHandshake");state.erase("serverHandshake");state.erase("mainSecret");swaps.clear();}
    void abort(){state.clear();swaps.clear();buffers.clear();}
    // ---- Application phase. Plaintext lives only in private buffers named by public handles.
    // `length` empty: the whole content is the payload (public size). `length` present: private
    // length within the public capacity, with `valid` the buffer's computed validity byte.
    // `sealer` set: the buffer is sealed by that kernel instead, with `content` bound to its
    // `frame` input and `extra` bound by name (a request assembled in the clear around private slots).
    struct PrivateBuffer {Wires length,content,valid;std::string sealer;Values extra;};
    std::map<uint64_t,PrivateBuffer>buffers;uint64_t next_buffer=1;
    uint64_t retain(PrivateBuffer buffer){if(next_buffer==0)throw std::runtime_error("handle space");buffers[next_buffer]=std::move(buffer);return next_buffer++;}
    // Authenticate, decrypt and classify one record; only the event bytes are opened.
    std::vector<uint8_t> open_application(const std::vector<uint8_t>&sequence,const std::vector<uint8_t>&wire){
        if(!state.count("parser")){auto unused=constant({0});auto initial=cache.get("tls-parser-initial").run(s,{{"unused",&unused}});keep(initial,"parser");}
        auto&kernel=cache.get("tls-open-application "+std::to_string(wire.size()));auto seq=constant(sequence),record=constant(wire);
        auto out=kernel.run(s,{{"parser",&held("parser")},{"serverApplication",&held("serverApplication")},{"sequence",&seq},{"record",&record}});
        auto event=kernel.open(s,out,"event");keep(out,"parser");
        if(event.size()!=2||event[0]>4||event[1]>1)throw std::runtime_error("application event");
        if(event[0]!=1)return event;
        auto id=retain({std::move(out.at("length")),std::move(out.at("content")),Wires{}});
        std::vector<uint8_t>reply{1,0};for(int i=7;i>=0;i--)reply.push_back(uint8_t(id>>(8*i)));return reply;
    }
    // Seal a private buffer; only ciphertext (and, for private-length buffers, the acceptance byte) is opened.
    std::vector<uint8_t> seal_application(const std::vector<uint8_t>&sequence,uint64_t id,size_t size,size_t padding){
        auto it=buffers.find(id);if(it==buffers.end()||8*size!=it->second.content.size())throw std::runtime_error("application seal request");
        auto seq=constant(sequence);auto&buffer=it->second;
        if(!buffer.sealer.empty()){
            if(padding)throw std::runtime_error("request padding");
            auto&kernel=cache.get(buffer.sealer);Binding bound{{"clientApplication",&held("clientApplication")},{"sequence",&seq},{"frame",&buffer.content}};
            for(auto&entry:buffer.extra)bound.push_back({entry.first,&entry.second});
            auto out=kernel.run(s,bound);
            if(kernel.open(s,out,"accepted")!=std::vector<uint8_t>{255})throw std::runtime_error("private request rejected");
            return kernel.open(s,out,"record");
        }
        if(buffer.length.size()){
            if(padding)throw std::runtime_error("private buffer padding");
            auto&kernel=cache.get("tls-seal-private "+std::to_string(size));auto valid=buffer.valid.size()?buffer.valid:constant({255});
            auto out=kernel.run(s,{{"clientApplication",&held("clientApplication")},{"sequence",&seq},{"valid",&valid},{"length",&buffer.length},{"content",&buffer.content}});
            if(kernel.open(s,out,"accepted")!=std::vector<uint8_t>{255})throw std::runtime_error("private payload rejected");
            return kernel.open(s,out,"record");
        }
        auto&kernel=cache.get("tls-seal "+std::to_string(size)+" "+std::to_string(padding));
        return kernel.open(s,kernel.run(s,{{"clientApplication",&held("clientApplication")},{"sequence",&seq},{"content",&buffer.content}}),"record");
    }
    // Public TLS control content (KeyUpdate or close_notify) under the private keys.
    std::vector<uint8_t> seal_control(const std::vector<uint8_t>&sequence,unsigned kind,const std::vector<uint8_t>&content){
        auto&kernel=cache.get("tls-seal-control "+std::to_string(kind)+" "+std::to_string(content.size()));auto seq=constant(sequence),body=constant(content);
        return kernel.open(s,kernel.run(s,{{"clientApplication",&held("clientApplication")},{"sequence",&seq},{"content",&body}}),"record");
    }
    // Public-receive profile: the length of an authenticated received buffer, and the
    // byte at `offset` if it lies within that length. Nothing else of the buffer is opened.
    std::vector<uint8_t> reveal_byte(uint64_t id,size_t offset){
        auto it=buffers.find(id);if(it==buffers.end()||it->second.length.size()==0)throw std::runtime_error("reveal handle");
        const size_t capacity=it->second.content.size()/8;std::vector<uint8_t>select(capacity,0);if(offset<capacity)select[offset]=255;
        auto&kernel=cache.get("tls-reveal "+std::to_string(capacity));auto chosen=constant(select);
        auto out=kernel.run(s,{{"length",&it->second.length},{"content",&it->second.content},{"select",&chosen}});
        auto reply=kernel.open(s,out,"length");const size_t length=size_t(reply.at(0))*256+reply.at(1);if(length>capacity)throw std::runtime_error("revealed length");
        if(offset<length)reply.push_back(kernel.open(s,out,"byte").at(0));
        return reply;
    }
    // Public bytes as a sendable buffer (control replies in the public-receive profile).
    uint64_t public_buffer(const std::vector<uint8_t>&bytes){
        if(bytes.empty()||bytes.size()>16384)throw std::runtime_error("public buffer size");
        return retain({Wires{},constant(bytes),Wires{}});
    }
    void rotate(bool sending){
        const std::string name=sending?"clientApplication":"serverApplication";
        auto out=cache.get("tls-update").run(s,{{"traffic",&held(name)}});keep(out,"traffic",name);
    }
    // Bytes neither party knows: XOR of both parties' random contributions.
    Wires fresh(size_t bytes){
        std::vector<uint8_t>raw(bytes);{emp::PRG prg;prg.random_data_unaligned(raw.data(),int(bytes));}
        auto shares=s.input_both(byte_bits(raw));return s.run(circuits.xor_bit.parallel(8*bytes),DynSession::interleave(shares.first,shares.second));
    }
    // ---- TEST FIXTURE ONLY (enabled by the worker's environment).
    uint64_t test_produce(size_t bytes){return retain({Wires{},fresh(bytes),Wires{}});}
    // Diagnostic: opens the received length and the XOR of the echoed bytes with what was sent.
    // Returns -1 if the record is not an echo of `bytes` bytes after `prefix`.
    int test_echo(uint64_t sent,uint64_t received,size_t prefix,size_t bytes){
        auto&a=buffers.at(sent);auto&b=buffers.at(received);auto length=bits_bytes(s.open(b.length));
        if(size_t(length[0])*256+length[1]!=prefix+bytes||b.content.size()<8*(prefix+bytes)||a.content.size()<8*bytes)return -1;
        auto x=a.content.slice(0,8*bytes),y=b.content.slice(8*prefix,8*(prefix+bytes));
        for(auto bit:s.open(s.run(circuits.xor_bit.parallel(8*bytes),DynSession::interleave(x,y))))if(bit)return 0;
        return 1;
    }
};
}
