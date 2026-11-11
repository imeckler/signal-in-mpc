#pragma once
// TLS 1.3 client on the two engines. All secret state is held here as named
// private wire bundles; every circuit is a Lean kernel (TlsMpc/HybridKernels.lean)
// bound by field name through kernel.h. This file sequences kernels, runs the
// key-agreement protocol in the field engine, and holds handles. It contains no
// circuit layout: it never slices a key out of a block or assembles an input.
// Only outputs Lean marks as openable are opened.
#include "kernel.h"
#include "gcm_shares.h"
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
    // Received application records: true opens one bit first (authenticated handshake record or
    // not) and runs the post-handshake framing scan only for handshake records (tls-open-typed,
    // tls-frame); false runs it on every record (tls-open-application-class). Set by the worker.
    bool typed_open=false;
    // Named private values: clientHandshake, serverHandshake, mainSecret,
    // clientApplication, serverApplication, parser.
    Values state;
    TlsKernels(DynSession&session,FE&field,Challenge&c,int p,const std::string&cache_script):s(session),f(field),channel(c),party(p),cache(cache_script,c){}
    // The capacity of a size class (`RecordClass.capacity` in TlsMpc/RecordClassKernels.lean): up to
    // 32, then rounded up to a multiple of a quarter of the power of two below (40, 48, 56, 64, 80, ...).
    // A public function of a public size; a deployment's manifest holds one circuit per capacity.
    static size_t record_capacity(size_t n){if(n<=32)return 32;size_t step=1;while(8*step<n)step*=2;return (n+step-1)/step*step;}
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
    // Swap bit of ladder step `step` (2..253) for a clamped scalar; `top` is scalar bit 254.
    static uint64_t swap_bit(const std::array<uint8_t,32>&scalar,unsigned step,bool top){
        auto bit=[&](unsigned i){return uint64_t((scalar[i/8]>>(i%8))&1);};
        return step==2?bit(3):step==253?(bit(253)^uint64_t(top)):(bit(step+1)^bit(step));
    }
    // The same swap bits for a scalar BOTH parties know (one of our own prekeys), as constants.
    std::vector<H> public_scalar(const std::array<uint8_t,32>&scalar){
        std::vector<H>out;for(unsigned step=2;step<=253;step++)out.push_back(f.constant(swap_bit(scalar,step,true)));return out;
    }
    // n private Boolean bits -> n field shares holding the same bits, each through one single-bit
    // pair: open bit xor rho, then select rho or 1-rho.
    std::vector<DynBitPair>pairs;size_t next_pair=0;
    std::vector<H> bits_to_field(const Wires&bits){
        ProfileScope scope("conversion: boolean bits to field bits");
        const size_t n=bits.size();if(!n||n>16*255)throw std::runtime_error("bit conversion size");
        if(pairs.size()-next_pair<n){
            const unsigned blocks=unsigned((n-(pairs.size()-next_pair)+254)/255);std::vector<DynBitPair>more;
            auto extra=generate_masks(s,f,channel,party,circuits,16,blocks,&more);
            pairs.erase(pairs.begin(),pairs.begin()+next_pair);next_pair=0;pairs.insert(pairs.end(),more.begin(),more.end());
            masks.erase(masks.begin(),masks.begin()+std::min(next_mask,masks.size()));next_mask=0;masks.insert(masks.end(),extra.begin(),extra.end());
        }
        std::vector<const Wires*>parts;for(size_t i=0;i<n;i++)parts.push_back(&pairs[next_pair+i].bit);
        auto rho=DynSession::concat(parts);
        auto opened=s.open(s.run(circuits.xor_bit.parallel(uint32_t(n)),DynSession::interleave(bits,rho)));
        auto one=f.constant(1);std::vector<H>out;for(size_t i=0;i<n;i++)out.push_back(opened.at(i)?f.sub(one,pairs[next_pair+i].field):pairs[next_pair+i].field);
        next_pair+=n;return out;
    }
    std::vector<H> shared_scalar(const std::array<uint8_t,32>&share){
        std::vector<uint64_t>local(252);
        for(unsigned step=2;step<=253;step++)local[step-2]=swap_bit(share,step,party==emp::ALICE);
        auto shares=f.input_coins(local);f.check();
        std::vector<H>all=shares[0];all.insert(all.end(),shares[1].begin(),shares[1].end());
        for(auto&v:f.checked_open(circuits.field_bit_checks(f,all)))for(auto byte:v)if(byte)throw std::runtime_error("non-bit scalar contribution");
        return circuits.field_bit_xor(f,shares[0],shares[1]);
    }
    // Private 255-bit word (value reduced mod p) -> one field share, consuming one mask.
    H word_to_field(const Wires&value){
        ProfileScope scope("conversion: boolean word to field value");
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
    // Several independent agreements (scalar, point) in the same field rounds.
    std::vector<Wires> agreement_words(const std::vector<std::pair<const std::vector<H>*,H>>&jobs){
        std::vector<bool>zero;auto results=curve.evaluate_many(f,channel,jobs,zero);
        std::vector<Wires>out;for(auto result:results)out.push_back(field_to_word(s,f,channel,circuits,take_mask(),result));
        return out;
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
    void abort(){state.clear();swaps.clear();buffers.clear();send_shares.clear();receive_shares.clear();}
    GcmShares send_shares,receive_shares;   // this party's shares of the GHASH key powers, per direction
    // ---- Several TLS connections in one worker (tls_worker_v3.cpp, operation 90, one per Tor
    // circuit). What belongs to ONE connection: the named TLS secrets in `state` (handshake and
    // traffic keys, the record parser), the key-agreement scalar between begin and derive, and the
    // GHASH key-power shares. `exchange` swaps them with a parked copy. Engines, circuits,
    // conversion masks and private buffers (public handles) are shared by every connection.
    struct Parked {Values state;std::vector<H>swaps;std::array<uint8_t,32>split_scalar{};bool split_ready=false;GcmShares send_shares,receive_shares;};
    void exchange(Parked&other){
        std::swap(state,other.state);std::swap(swaps,other.swaps);std::swap(split.scalar,other.split_scalar);std::swap(split.ready,other.split_ready);
        std::swap(send_shares,other.send_shares);std::swap(receive_shares,other.receive_shares);
    }
    // ---- Application phase. Plaintext lives only in private buffers named by public handles.
    // `length` empty: the whole content is the payload (public size). `length` present: private
    // length within the public capacity, with `valid` the buffer's computed validity byte.
    // `sealer` set: the buffer is sealed by that kernel instead, with `content` bound to its
    // `frame` input and `extra` bound by name (a request assembled in the clear around private slots).
    // `revealable`: the length-masked content from tls-reveal-masked, computed on first reveal.
    struct PrivateBuffer {Wires length,content,valid;std::string sealer;Values extra;Wires revealable;size_t revealed_length=0;};
    std::map<uint64_t,PrivateBuffer>buffers;uint64_t next_buffer=1;
    uint64_t retain(PrivateBuffer buffer){if(next_buffer==0)throw std::runtime_error("handle space");buffers[next_buffer]=std::move(buffer);return next_buffer++;}
    // Authenticate, decrypt and classify one record; only the event bytes are opened.
    std::vector<uint8_t> open_application(const std::vector<uint8_t>&sequence,const std::vector<uint8_t>&wire){
        if(!state.count("parser")){auto unused=constant({0});auto initial=cache.get("tls-parser-initial").run(s,{{"unused",&unused}});keep(initial,"parser");}
        if(wire.size()<22||wire.size()!=5+size_t(wire[3])*256+wire[4])throw std::runtime_error("application record size");
        // Size class (TlsMpc/RecordClassKernels.lean): the record followed by zero bytes up to its
        // class's capacity, and its length field as a public value. The kernel masks what lies beyond.
        std::vector<uint8_t>padded(wire);padded.resize(record_capacity(wire.size()),0);
        auto seq=constant(sequence),record=constant(padded),size=constant({wire[3],wire[4]});
        // Tag check from the parties' local halves over the public ciphertext; the result is a private mask.
        const std::vector<uint8_t>header(wire.begin(),wire.begin()+5),ciphertext(wire.begin()+5,wire.end()-16);
        receive_shares.ensure(s,cache,party,held("serverApplication"),GcmShares::blocks(header.size(),ciphertext.size()));
        auto halves=receive_shares.supply(s,party,header,ciphertext);auto tag=constant(std::vector<uint8_t>(wire.end()-16,wire.end()));
        auto check=cache.get("gcm-check").run(s,{{"traffic",&held("serverApplication")},{"sequence",&seq},{"halfA",&halves.first},{"halfB",&halves.second},{"tag",&tag}});
        const Binding inputs{{"parser",&held("parser")},{"serverApplication",&held("serverApplication")},{"sequence",&seq},{"record",&record},{"size",&size},{"accepted",&check.at("accepted")}};
        const std::string capacity=std::to_string(padded.size());const Kernel*opener=nullptr;Values out;
        if(typed_open){
            // Two steps (TlsMpc/TypedOpenKernels.lean): the first kernel decrypts and parses the record and
            // opens one bit, "authenticated and a handshake record" (0 for every record whose tag check
            // failed: TypedOpenProofs.tlsOpenTyped_gated). Bit 0: its own event and fields are the result.
            // Bit 255: the framing scan runs on the private parse (tls-frame) and gives the result.
            opener=&cache.get("tls-open-typed "+capacity);out=opener->run(s,inputs);
            const auto bit=opener->open(s,out,"handshake");
            if(bit.size()!=1||(bit[0]!=0&&bit[0]!=255))throw std::runtime_error("record type bit");
            if(bit[0]==255){
                const Wires parsed=std::move(out.at("parsed"));opener=&cache.get("tls-frame "+capacity);
                out=opener->run(s,{{"parser",&held("parser")},{"parsed",&parsed}});
            }
        }else{opener=&cache.get("tls-open-application-class "+capacity);out=opener->run(s,inputs);}
        auto event=opener->open(s,out,"event");keep(out,"parser");
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
            return tagged(kernel,out);
        }
        if(buffer.length.size()){
            if(padding)throw std::runtime_error("private buffer padding");
            auto&kernel=cache.get("tls-seal-private-ctr "+std::to_string(size));auto valid=buffer.valid.size()?buffer.valid:constant({255});
            auto out=kernel.run(s,{{"clientApplication",&held("clientApplication")},{"sequence",&seq},{"valid",&valid},{"length",&buffer.length},{"content",&buffer.content}});
            if(kernel.open(s,out,"accepted")!=std::vector<uint8_t>{255})throw std::runtime_error("private payload rejected");
            return tagged(kernel,out);
        }
        if(padding==0){
            // Size class (TlsMpc/RecordClassKernels.lean): the content followed by public zero bytes up
            // to its class's capacity, and the record's length field (content, type byte, tag) as a
            // public value. The record is the exact-size one: nothing beyond it is encrypted or kept.
            const size_t capacity=record_capacity(size),length=size+17;
            auto filler=constant(std::vector<uint8_t>(capacity-size+1,0)).slice(0,8*(capacity-size));
            auto content=DynSession::concat({&buffer.content,&filler}),field=constant({uint8_t(length>>8),uint8_t(length)});
            auto&kernel=cache.get("tls-seal-class "+std::to_string(capacity));
            auto out=kernel.run(s,{{"clientApplication",&held("clientApplication")},{"sequence",&seq},{"content",&content},{"size",&field}});
            if(kernel.open(s,out,"accepted")!=std::vector<uint8_t>{255})throw std::runtime_error("sealed record size");
            return tagged(kernel,out,size+1);
        }
        auto&kernel=cache.get("tls-seal-ctr 23 "+std::to_string(size)+" "+std::to_string(padding));
        return tagged(kernel,kernel.run(s,{{"clientApplication",&held("clientApplication")},{"sequence",&seq},{"content",&buffer.content}}));
    }
    // Finish a record from a CTR kernel's outputs: the header and ciphertext are public; the
    // tag is the private pad combined with the parties' local halves (gcm_shares.h).
    std::vector<uint8_t> tagged(const Kernel&kernel,Values out,size_t keep=SIZE_MAX){
        auto record=kernel.open(s,out,"header"),ciphertext=kernel.open(s,out,"ciphertext");
        if(keep<ciphertext.size())ciphertext.resize(keep);   // a size-class kernel: zero bytes follow the record's own
        send_shares.ensure(s,cache,party,held("clientApplication"),GcmShares::blocks(record.size(),ciphertext.size()));
        auto halves=send_shares.supply(s,party,record,ciphertext);auto&tagger=cache.get("gcm-tag");
        auto tag=tagger.open(s,tagger.run(s,{{"pad",&out.at("pad")},{"halfA",&halves.first},{"halfB",&halves.second}}),"tag");
        record.insert(record.end(),ciphertext.begin(),ciphertext.end());record.insert(record.end(),tag.begin(),tag.end());
        return record;
    }
    // Public TLS control content (KeyUpdate or close_notify) under the private keys.
    std::vector<uint8_t> seal_control(const std::vector<uint8_t>&sequence,unsigned kind,const std::vector<uint8_t>&content){
        auto&kernel=cache.get("tls-seal-ctr "+std::to_string(kind)+" "+std::to_string(content.size())+" 0");auto seq=constant(sequence),body=constant(content);
        return tagged(kernel,kernel.run(s,{{"clientApplication",&held("clientApplication")},{"sequence",&seq},{"content",&body}}));
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
    // The same for a range: the length, then the bytes at [offset, offset+count) that lie within
    // it. The masked content is computed once per buffer; each call only opens wires.
    std::vector<uint8_t> reveal_range(uint64_t id,size_t offset,size_t count){
        auto it=buffers.find(id);if(it==buffers.end()||it->second.length.size()==0||count==0)throw std::runtime_error("reveal handle");
        auto&buffer=it->second;const size_t capacity=buffer.content.size()/8;
        if(buffer.revealable.size()==0){
            auto&kernel=cache.get("tls-reveal-masked "+std::to_string(capacity));
            auto out=kernel.run(s,{{"length",&buffer.length},{"content",&buffer.content}});
            auto opened=kernel.open(s,out,"length");buffer.revealed_length=size_t(opened.at(0))*256+opened.at(1);
            if(buffer.revealed_length>capacity)throw std::runtime_error("revealed length");
            buffer.revealable=std::move(out.at("bytes"));
        }
        ProfileScope scope("open revealed server bytes");
        const size_t length=buffer.revealed_length;std::vector<uint8_t>reply{uint8_t(length>>8),uint8_t(length)};
        if(offset<length){
            const size_t end=std::min(length,offset+count);
            auto bytes=bits_bytes(s.open(buffer.revealable.slice(8*offset,8*end)));reply.insert(reply.end(),bytes.begin(),bytes.end());
        }
        return reply;
    }
    // A range of an authenticated record as private wires, nothing opened (the record's length
    // was opened by an earlier reveal_range call, which every caller makes first).
    Wires take_range(uint64_t id,size_t offset,size_t count){
        auto it=buffers.find(id);
        if(it==buffers.end()||it->second.revealable.size()==0||count==0||offset+count>it->second.revealed_length)throw std::runtime_error("take range");
        return it->second.revealable.slice(8*offset,8*(offset+count));
    }
    // Public bytes as a sendable buffer (control replies in the public-receive profile).
    uint64_t public_buffer(const std::vector<uint8_t>&bytes){
        if(bytes.empty()||bytes.size()>16384)throw std::runtime_error("public buffer size");
        return retain({Wires{},constant(bytes),Wires{}});
    }
    void rotate(bool sending){
        const std::string name=sending?"clientApplication":"serverApplication";
        auto out=cache.get("tls-update").run(s,{{"traffic",&held(name)}});keep(out,"traffic",name);
        (sending?send_shares:receive_shares).clear();   // key power shares belong to the old key
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
