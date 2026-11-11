#pragma once
// Signal service path on the two engines: authenticated WebSocket upgrade,
// private receive parsing and the established sealed-sender text send.
//
// Every circuit is a Lean kernel (TlsMpc/HybridKernels.lean) bound by field
// name. This file holds named private state, sequences kernels, and runs the
// X25519 agreements in the field engine. It has no knowledge of any record or
// state layout, and opens only what Lean marks as openable:
//   - send: the gated producer status (must be 255 before the frame is retained);
//   - receive: chunk acceptance, parser status flags at the end of a chunk, the
//     control queue's validity, count and reply kinds.
//
// X25519 for sealed sender uses the shared-scalar ladder on a PRIVATE recipient
// point. The sender's long-term results (its public key and the static
// agreement with the recipient) are computed once per conversation.
//
// State admission is the TEST FIXTURE only: public disposable sender states
// from signal_backend/TextNotificationWork are entered as private wires by one
// party. It is not authenticated provisioning and not durable.
#include <deque>
#include "tls_kernels.h"
#include "edwards_points.h"
#include "../../signal_backend/TextNotificationWork/PublicTextFixture.h"
#include <openssl/evp.h>
#include <openssl/sha.h>
namespace emp_hybrid {
class ServiceKernels {
    TlsKernels&k;DynSession&s;FE&f;
    static constexpr size_t PASSWORD=22;
    static constexpr size_t CONTACT=319;   // one contact's record: session block and metadata
    size_t CERT=260;   // sender certificate bytes (the fixture's; set by account admission)
public:
    using ContactId=std::array<uint8_t,16>;   // u128, big-endian
private:
    // `record` is the contact's private state (empty while not loaded); `key` is its storage key
    // (contact-key kernel). The derived values and the offset table are an in-memory cache only.
    struct Account {std::vector<H>identity;Wires certificate,sender_public;};
    struct Conversation {Wires record,static_agreement,key;H recipient;bool ready=false;OffsetAgreement offset;Account*fixture=nullptr;};
    // The account: our identity key (shared scalar) and sender certificate, the same for every
    // contact and never part of a contact's stored record. The Lean kernels take the certificate
    // followed by the contact record as one `conversation` value; `whole` only joins the wires and
    // `keep` takes the contact part back.
    // TEST FIXTURE: its two conversations have different senders, so each carries its own account.
    Account account;std::deque<Account>fixture_accounts;Wires credentials_a,credentials_b,envelope;
    Account&of(const Conversation&c){return c.fixture?*c.fixture:account;}
    Wires whole(const Conversation&c){return DynSession::concat({&of(c).certificate,&c.record});}
    void keep(Conversation&c,const Wires&conversation){need(conversation.size()==8*(CERT+CONTACT),"conversation shape");c.record=conversation.slice(8*CERT,8*(CERT+CONTACT));}
    void prepare(Conversation&c){
        if(c.ready)return;
        auto w=whole(c);auto out=view().run(s,{{"conversation",&w}});c.recipient=k.word_to_field(out.at("recipient"));
        auto&a=of(c);if(!a.sender_public.size())a.sender_public=k.agreement_word(a.identity,f.constant(9));
        c.static_agreement=k.agreement_word(a.identity,c.recipient);c.ready=true;
    }
    // A message being received: what steps 13-17 need from steps 1-12, all private except the widths.
    struct Rejected {};
    struct Arrival {Wires message,prekey_valid,verified,sender_identity,uuid,device,ours;H sender_point,base,ratchet;std::string widths;bool one_time=false,held=false;};
    struct ReceivePrograms {
        FieldProgram recover{std::string(EMP_WORD_CIRCUIT_DIR)+"/xeddsa-recover.flat",XEDDSA_RECOVER_SHA};
        FieldProgram check{std::string(EMP_WORD_CIRCUIT_DIR)+"/xeddsa-check.flat",XEDDSA_CHECK_SHA};
        FieldProgram torsion{std::string(EMP_WORD_CIRCUIT_DIR)+"/receive-torsion.flat",RECEIVE_TORSION_SHA};
        ReceivePrograms(){
            if(recover.input_count()!=1||recover.output_count()!=3||check.input_count()!=512||check.output_count()!=2||torsion.input_count()!=2||torsion.output_count()!=2)throw std::runtime_error("receive program shape");
        }
    };
    Arrival arrival;ReceivePrograms programs;
    // The sealed-sender server key as an Edwards point (xeddsa-recover on a public value, so its
    // outputs are public): once per key.
    std::vector<uint8_t>server_key;H server_x,server_y;Wires server_x_word,server_y_word;
    void server(const std::vector<uint8_t>&key){
        if(key==server_key)return;
        std::array<uint8_t,32>u{};std::copy_n(key.begin(),32,u.begin());u[31]&=127;need(canonical(u),"server key range");
        auto point=f.checked_open(programs.recover.evaluate_all(f,{{f.public_element(u)}}).at(0));
        std::array<uint8_t,32>one{};one[0]=1;need(point.size()==3&&point[0]==one,"server key is not a curve point");
        server_x=f.public_element(point[1]);server_y=f.public_element(point[2]);
        server_x_word=public_word(point[1]);server_y_word=public_word(point[2]);server_key=key;
    }
    Wires public_word(const std::array<uint8_t,32>&value){std::vector<uint8_t>bits(255);for(unsigned i=0;i<255;i++)bits[i]=(value[i/8]>>(i%8))&1;return s.public_bits(bits);}
    Wires public_word(uint8_t small){std::array<uint8_t,32>value{};value[0]=small;return public_word(value);}
    Wires word(H value){return field_to_word(s,f,k.channel,k.circuits,k.take_mask(),value);}
    // A kernel whose parameters came from a message: parameters Lean does not accept refuse the message.
    const Kernel&shaped(const std::string&name){
        try{return k.cache.get(name);}catch(const std::runtime_error&e){if(std::string(e.what())=="kernel cache failed")throw Rejected{};throw;}
    }
    static bool flag(uint8_t byte){if(byte!=0&&byte!=255)throw Rejected{};return byte==255;}
    // 1 + the index of the single set flag among five.
    static unsigned width(const std::vector<uint8_t>&flags,size_t at){
        unsigned found=0,count=0;for(unsigned i=0;i<5;i++)if(flag(flags.at(at+i))){found=i+1;count++;}
        if(count!=1)throw Rejected{};return found;
    }
    OffsetPrograms offset_programs;
    std::map<ContactId,Conversation>conversations;std::vector<std::pair<ContactId,Wires>>inputs;std::vector<bool>consumed;
    static ContactId fixture_id(unsigned slot){ContactId id{};id[15]=uint8_t(slot+1);return id;}
    Values ws;   // upgrade, accept, frame, control, responseTemplate, response, requestId
    bool admitted=false,started=false,upgraded=false,pending=false,closed=false;
    Wires entered(const std::vector<uint8_t>&bytes){return s.input_private(emp::ALICE,byte_bits(bytes));}   // one party supplies; private from then on
    void need(bool ok,const char*what){if(!ok){closed=true;throw std::runtime_error(what);}}
    const Kernel&view(){return k.cache.get("signal-conversation-view "+std::to_string(CERT));}
public:
    explicit ServiceKernels(TlsKernels&kernels):k(kernels),s(kernels.s),f(kernels.f){}
    // Public-receive profile: server records are parsed in the clear by the controllers,
    // which then also track upgrade completion and pending responses. Set before `upgrade`.
    bool public_receive=false;std::vector<uint8_t>accept_bytes,last_request_id;
    // TEST FIXTURE admission: two conversations, two texts each.
    void admit_fixture(){
        need(!admitted,"service admission repeated");admitted=true;
        for(unsigned slot=0;slot<2;slot++){
            auto native=signal_mpc::PublicTextFixture::initial(slot);need(native.size()==32+CERT+CONTACT,"fixture state shape");
            std::array<uint8_t,32>secret{};if(k.party==emp::ALICE)std::copy_n(native.begin(),32,secret.begin());
            fixture_accounts.push_back({k.shared_scalar(secret),entered({native.begin()+32,native.begin()+32+CERT}),Wires{}});
            Conversation c;c.fixture=&fixture_accounts.back();c.record=entered({native.begin()+32+CERT,native.end()});
            if(slot==0){auto w=whole(c);auto out=view().run(s,{{"conversation",&w}});ws["requestId"]=std::move(out.at("requestId"));}   // one request-id sequence per connection
            conversations[fixture_id(slot)]=std::move(c);
        }
        for(unsigned round=0;round<2;round++)for(unsigned slot=0;slot<2;slot++)inputs.push_back({fixture_id(slot),entered(signal_mpc::PublicTextFixture::text_input(slot,round))});
        consumed.assign(inputs.size(),false);
    }
    // TEST admission of the account from a local-server export: both controllers hold the same
    // disposable test state and one party enters it as private wires, as for the fixture. The
    // certificate is the sender's own, at its exact length.
    void admit_account(const std::vector<uint8_t>&secret_key,const std::vector<uint8_t>&sender_certificate){
        need(!closed&&!started&&!admitted&&secret_key.size()==32&&!sender_certificate.empty()&&sender_certificate.size()<=1024,"account admission");
        CERT=sender_certificate.size();admitted=true;
        std::array<uint8_t,32>secret{};if(k.party==emp::ALICE)std::copy_n(secret_key.begin(),32,secret.begin());
        account.identity=k.shared_scalar(secret);account.certificate=entered(sender_certificate);
    }
    // TEST admission of one contact's record (session block and metadata) in the clear, the same way.
    // Stored contacts are loaded with contact_key and contact_open instead.
    void admit_contact(const ContactId&id,const std::vector<uint8_t>&record){
        need(!closed&&admitted&&account.certificate.size()&&record.size()==CONTACT&&!conversations.count(id),"contact admission");
        Conversation c;c.record=entered(record);conversations[id]=std::move(c);
    }
    // The account's socket credentials (account id 16, password) as XOR shares: each party's
    // share is its own private input, and the upgrade kernel combines them.
    void account_credentials(const std::vector<uint8_t>&share){
        need(!started&&!closed&&share.size()==16+PASSWORD&&!credentials_a.size(),"account credentials");
        const std::vector<uint8_t>none(share.size(),0);
        credentials_a=s.input_private(emp::ALICE,byte_bits(k.party==emp::ALICE?share:none));
        credentials_b=s.input_private(emp::BOB,byte_bits(k.party==emp::BOB?share:none));
    }
    // A delivered envelope's sealed content, collected unopened from the records that carried it.
    // Reply: the number of bytes held so far (4).
    std::vector<uint8_t> envelope_take(uint64_t handle,size_t offset,size_t count){
        need(public_receive&&!closed&&envelope.size()/8+count<=16384,"envelope take");
        auto part=k.take_range(handle,offset,count);envelope=envelope.size()?DynSession::concat({&envelope,&part}):part;
        const size_t n=envelope.size()/8;return {uint8_t(n>>24),uint8_t(n>>16),uint8_t(n>>8),uint8_t(n)};
    }
    void envelope_drop(){envelope=Wires{};arrival=Arrival{};}
    // ---- A new contact's first message (TlsMpc/ReceiveKernels.lean lists the steps and what each
    // opens). This only sequences those kernels and field programs: every shape it opens is one
    // Lean marks as public, and it selects the next kernel by passing the opened numbers on as
    // that kernel's parameters. A message that fails any check is refused (reply 0) with nothing
    // else released; the connection carries on.
    // Step 1-12: sealed sender, the sender certificate and the prekey message's public part.
    // Reply: 0, or 255, one-time prekey named (1), its id (4), signed prekey id (4), Kyber prekey
    // id (4), Kyber ciphertext.
    std::vector<uint8_t> envelope_open(const std::vector<uint8_t>&identity_public,const std::vector<uint8_t>&now,const std::vector<uint8_t>&server_key,
            const std::vector<uint8_t>&signer_certificate,const std::vector<uint8_t>&signer_id){
        need(public_receive&&!closed&&account.identity.size()&&envelope.size()&&!arrival.held&&identity_public.size()==32&&now.size()==8&&server_key.size()==32,"envelope open");
        Wires sealed=std::move(envelope);envelope=Wires{};
        try{
            server(server_key);
            const std::string size=std::to_string(sealed.size()/8);
            auto point=shaped("receive-envelope-point "+size).run(s,{{"envelope",&sealed}});
            auto agreement=k.agreement_word(account.identity,k.word_to_field(point.at("ephemeralPoint")));
            auto ours=k.constant(identity_public);
            auto opened=shaped("receive-unseal-static "+size).run(s,{{"envelope",&sealed},{"ourIdentity",&ours},{"agreement",&agreement}});
            Arrival a;a.sender_point=k.word_to_field(opened.at("senderPoint"));
            auto second=k.agreement_word(account.identity,a.sender_point);
            auto&unseal=shaped("receive-unseal-message "+size);
            auto unsealed=unseal.run(s,{{"envelope",&sealed},{"staticValid",&opened.at("staticValid")},{"chain",&opened.at("chain")},{"agreement",&second}});
            auto prefix=unseal.open(s,unsealed,"certificateLength");if(prefix.size()!=2)throw Rejected{};
            const std::string content=std::to_string(unsealed.at("content").size()/8)+" "+std::to_string(prefix[0])+" "+std::to_string(prefix[1]);
            auto&layout=shaped("receive-content-shape "+content);
            auto shape=layout.open(s,layout.run(s,{{"content",&unsealed.at("content")},{"valid",&unsealed.at("valid")}}),"shape");
            if(shape.size()!=4||flag(shape[0])==flag(shape[1]))throw Rejected{};
            auto parts=shaped("receive-content "+content+(flag(shape[1])?" 1":" 0")).run(s,{{"content",&unsealed.at("content")},{"valid",&unsealed.at("valid")}});
            // Sender certificate: everything but the signature in the Boolean engine, the
            // signature's curve equation in the field engine.
            auto&certificate=shaped("receive-certificate "+std::to_string(prefix[0])+" "+std::to_string(prefix[1])+" "+std::to_string(shape[2])+" "+std::to_string(shape[3]));
            auto embedded=k.constant(signer_certificate),reference=k.constant(signer_id),time=k.constant(now);
            const size_t wanted=certificate.input_bits("signer");
            const Wires*signer=wanted==embedded.size()?&embedded:wanted==reference.size()?&reference:nullptr;if(!signer)throw Rejected{};
            auto checked=certificate.run(s,{{"certificate",&parts.at("certificate")},{"valid",&parts.at("valid")},{"senderIdentity",&opened.at("senderIdentity")},
                {"signer",signer},{"now",&time},{"serverX",&server_x_word},{"serverY",&server_y_word}});
            std::vector<H>challenge{server_x,server_y};
            for(auto h:k.bits_to_field(DynSession::concat({&checked.at("flip"),&checked.at("challenge"),&checked.at("scalar")})))challenge.push_back(h);
            auto r=programs.check.evaluate_all(f,{challenge}).at(0);
            auto rx=word(r.at(0)),ry=word(r.at(1)),valid=public_word(1);
            auto verified=shaped("receive-certificate-verified").run(s,{{"certificateValid",&checked.at("certificateValid")},{"signature",&checked.at("signature")},
                {"serverValid",&valid},{"rx",&rx},{"ry",&ry}});
            // The prekey message: widths, then our prekey ids and the Kyber ciphertext.
            const std::string n=std::to_string(parts.at("message").size()/8);
            auto&widths=shaped("receive-prekey-shape "+n);
            auto flags=widths.open(s,widths.run(s,{{"message",&parts.at("message")},{"valid",&parts.at("valid")}}),"shape");if(flags.size()!=21)throw Rejected{};
            a.one_time=flag(flags[0]);
            a.widths=n+" "+std::to_string(a.one_time?width(flags,1):0)+" "+std::to_string(width(flags,6))+" "+std::to_string(width(flags,11))+" "+std::to_string(width(flags,16));
            auto&prekey=shaped("receive-prekey-open "+a.widths);
            auto named=prekey.run(s,{{"message",&parts.at("message")},{"valid",&parts.at("valid")},{"messageType",&parts.at("messageType")},{"senderIdentity",&opened.at("senderIdentity")}});
            std::vector<uint8_t>reply{255,uint8_t(a.one_time)};
            for(auto field:{"oneTimePrekeyId","signedPrekeyId","kyberPrekeyId","kyberCiphertext"}){auto bytes=prekey.open(s,named,field);reply.insert(reply.end(),bytes.begin(),bytes.end());}
            a.base=k.word_to_field(named.at("basePoint"));a.ratchet=k.word_to_field(named.at("ratchetPoint"));
            a.message=std::move(parts.at("message"));a.prekey_valid=std::move(named.at("prekeyValid"));a.verified=std::move(verified.at("verified"));
            a.sender_identity=std::move(opened.at("senderIdentity"));a.uuid=std::move(checked.at("uuid"));a.device=std::move(checked.at("deviceId"));
            a.ours=std::move(ours);a.held=true;arrival=std::move(a);
            return reply;
        }catch(const Rejected&){arrival=Arrival{};return {0};}
    }
    // Step 13-17: the agreements, the session, the message text, the contact's access key; the
    // new contact's record is kept under `id`. `signed_prekey` and `one_time_prekey` are the
    // private keys of OUR prekeys the message named and `kem_secret` the decapsulated Kyber
    // secret: values both parties hold. Reply: 0, or 255, text length (2), text.
    std::vector<uint8_t> envelope_session(const ContactId&id,const std::vector<uint8_t>&local_address,const std::array<uint8_t,32>&signed_prekey,
            const std::array<uint8_t,32>&one_time_prekey,const std::vector<uint8_t>&kem_secret,const std::vector<uint8_t>&request_id){
        need(public_receive&&!closed&&arrival.held&&!conversations.count(id)&&local_address.size()==17&&kem_secret.size()==32&&request_id.size()==8,"envelope session");
        Arrival a=std::move(arrival);arrival=Arrival{};
        try{
            // The base key as an Edwards point, and its multiple by the group order (zero when torsion free).
            auto lifted=programs.recover.evaluate_all(f,{{a.base}}).at(0);
            auto order=programs.torsion.evaluate_all(f,{{lifted.at(1),lifted.at(2)}}).at(0);
            auto base_valid=word(lifted.at(0)),torsion_x=word(order.at(0)),torsion_y=word(order.at(1));
            auto ours=k.public_scalar(signed_prekey);
            auto dh1=k.agreement_word(ours,a.sender_point),dh2=k.agreement_word(account.identity,a.base),dh3=k.agreement_word(ours,a.base);
            Wires dh4;if(a.one_time)dh4=k.agreement_word(k.public_scalar(one_time_prekey),a.base);
            auto receiving=k.agreement_word(ours,a.ratchet);
            // Our new ratchet key: a scalar neither party knows.
            std::array<uint8_t,32>seed{};{emp::PRG prg;prg.random_data_unaligned(seed.data(),32);}
            auto ratchet=k.shared_scalar(seed);
            auto sending=k.agreement_word(ratchet,a.ratchet),ratchet_public=k.agreement_word(ratchet,f.constant(9));
            auto&layout=shaped("receive-signal-shape "+a.widths);
            auto shape=layout.open(s,layout.run(s,{{"message",&a.message},{"valid",&a.prekey_valid}}),"shape");if(shape.size()!=13)throw Rejected{};
            auto&session=shaped("receive-session "+std::to_string(CERT)+" "+a.widths+" "+std::to_string(width(shape,0))+" "+std::to_string(width(shape,5))+" "+
                std::to_string(shape[10])+" "+std::to_string(shape[11])+(flag(shape[12])?" 1":" 0")+" 0");
            auto address=k.constant(local_address),secret=k.constant(kem_secret),access=k.constant(std::vector<uint8_t>(16,0)),request=k.constant(request_id);
            Binding bound{{"message",&a.message},{"prekeyValid",&a.prekey_valid},{"verified",&a.verified},{"senderIdentity",&a.sender_identity},{"ourIdentity",&a.ours},
                {"localAddress",&address},{"uuid",&a.uuid},{"deviceId",&a.device},{"dh1",&dh1},{"dh2",&dh2},{"dh3",&dh3},{"kemSecret",&secret},
                {"receiveAgreement",&receiving},{"sendAgreement",&sending},{"ratchetPublic",&ratchet_public},{"baseValid",&base_valid},{"torsionX",&torsion_x},
                {"torsionY",&torsion_y},{"certificate",&account.certificate},{"accessKey",&access},{"requestId",&request}};
            if(a.one_time)bound.push_back({"dh4",&dh4});
            auto out=session.run(s,bound);
            if(session.open(s,out,"status")!=std::vector<uint8_t>{255})throw Rejected{};
            // The text, and the access key from the profile key that follows it.
            const size_t ciphertext=out.at("plaintext").size()/8-8;if(ciphertext<16)throw Rejected{};
            auto&text=shaped("receive-text "+std::to_string(ciphertext)+" "+std::to_string(ciphertext-6));
            auto body=text.run(s,{{"plaintext",&out.at("plaintext")}});
            if(text.open(s,body,"status")!=std::vector<uint8_t>{255})throw Rejected{};
            auto length=text.open(s,body,"length"),content=text.open(s,body,"text"),starts=text.open(s,body,"layout");
            if(length.size()!=2||starts.size()!=3)throw Rejected{};
            const size_t count=size_t(length[0])*256+length[1];unsigned start=0,set=0;
            for(unsigned i=0;i<3;i++)if(flag(starts[i])){start=4+i;set++;}
            if(set!=1||count>content.size())throw Rejected{};
            auto&key=shaped("receive-access-key "+std::to_string(CERT)+" "+std::to_string(ciphertext)+" "+std::to_string(start+count));
            auto keyed=key.run(s,{{"conversation",&out.at("conversation")},{"plaintext",&out.at("plaintext")}});
            if(key.open(s,keyed,"status")!=std::vector<uint8_t>{255})throw Rejected{};
            Conversation c;keep(c,keyed.at("conversation"));conversations[id]=std::move(c);
            std::vector<uint8_t>reply{255,length[0],length[1]};reply.insert(reply.end(),content.begin(),content.begin()+count);return reply;
        }catch(const Rejected&){return {0};}
    }
    // Unauthenticated chat socket: the upgrade request has no secrets and is built by the
    // controllers; this only fixes the expected Sec-WebSocket-Accept for the public nonce.
    std::vector<uint8_t> upgrade_public(const std::vector<uint8_t>&nonce){
        need(!started&&!closed&&nonce.size()==16,"upgrade unavailable");started=true;public_receive=true;
        unsigned char key[25]={},digest[20],encoded[29]={};EVP_EncodeBlock(key,nonce.data(),16);
        std::string material(reinterpret_cast<char*>(key),24);material+="258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
        SHA1(reinterpret_cast<const unsigned char*>(material.data()),material.size(),digest);EVP_EncodeBlock(encoded,digest,20);
        accept_bytes.assign(encoded,encoded+28);
        std::vector<uint8_t>out=nonce;out.insert(out.end(),accept_bytes.begin(),accept_bytes.end());return out;
    }
    // ---- Contact state at rest (kernels contact-key, contact-seal, contact-open).
    // The storage key from the two parties' additive shares (mod 2^255-19) of the contact's
    // stored scalar. Each party's share is its own private input.
    void contact_key(const ContactId&id,const std::array<uint8_t,32>&share){
        need(!closed,"contact key unavailable");
        const std::vector<uint8_t>mine(share.begin(),share.end()),none(32,0);
        auto a=s.input_private(emp::ALICE,byte_bits(k.party==emp::ALICE?mine:none)),b=s.input_private(emp::BOB,byte_bits(k.party==emp::BOB?mine:none));
        auto out=k.cache.get("contact-key").run(s,{{"shareA",&a},{"shareB",&b}});conversations[id].key=std::move(out.at("traffic"));
    }
    static void version_ok(const std::vector<uint8_t>&version){
        if(version.size()!=8||version==std::vector<uint8_t>(8,255))throw std::runtime_error("contact version");
    }
    // Encrypt the contact's current state for storage. Reply: check16, ciphertext.
    std::vector<uint8_t> contact_seal(const ContactId&id,const std::vector<uint8_t>&version){
        auto it=conversations.find(id);need(!closed&&it!=conversations.end()&&it->second.key.size()&&it->second.record.size(),"contact seal unavailable");version_ok(version);
        auto&c=it->second;auto&kernel=k.cache.get("contact-seal "+std::to_string(c.record.size()/8));auto v=k.constant(version);
        auto out=kernel.run(s,{{"traffic",&c.key},{"version",&v},{"content",&c.record}});
        auto reply=kernel.open(s,out,"check");auto ciphertext=kernel.open(s,out,"ciphertext");reply.insert(reply.end(),ciphertext.begin(),ciphertext.end());return reply;
    }
    // Load a contact's state from its stored ciphertext. A wrong key (bad or stale share from
    // either side) fails the public check value and aborts without revealing anything else.
    void contact_open(const ContactId&id,const std::vector<uint8_t>&version,const std::vector<uint8_t>&check,const std::vector<uint8_t>&ciphertext){
        auto it=conversations.find(id);need(!closed&&it!=conversations.end()&&it->second.key.size()&&it->second.record.size()==0&&check.size()==16&&ciphertext.size()==CONTACT,"contact open unavailable");version_ok(version);
        auto&c=it->second;auto&kernel=k.cache.get("contact-open "+std::to_string(ciphertext.size()));auto v=k.constant(version),sum=k.constant(check),body=k.constant(ciphertext);
        auto out=kernel.run(s,{{"traffic",&c.key},{"version",&v},{"ciphertext",&body},{"check",&sum}});
        need(kernel.open(s,out,"accepted")==std::vector<uint8_t>{255},"contact key does not match the stored state");
        c.record=std::move(out.at("content"));c.ready=false;c.offset=OffsetAgreement{};
    }
    // Drop a contact's loaded state, key and cached derived values.
    // TEST FIXTURE: the sender identity admitted with the fixture stays (it is the client's own key, not contact state).
    void contact_evict(const ContactId&id){
        auto it=conversations.find(id);need(it!=conversations.end(),"contact evict unavailable");
        auto&c=it->second;c.record=Wires{};c.key=Wires{};c.static_agreement=Wires{};c.ready=false;c.offset=OffsetAgreement{};
    }
    std::vector<uint8_t> catalogue()const{
        if(!admitted||closed)throw std::runtime_error("no admitted provider");
        std::vector<uint8_t>out{0,0,0,0,0,0,0,1,0,uint8_t(inputs.size())};
        for(size_t i=0;i<inputs.size();i++){for(int b=0;b<7;b++)out.push_back(0);out.push_back(uint8_t(i+1));}
        return out;
    }
    // Authenticated upgrade request with private credentials and a public nonce.
    // Returns the request's handle and its public size.
    std::pair<uint64_t,size_t> upgrade(const std::vector<uint8_t>&nonce){
        need((admitted||credentials_a.size())&&!started&&!closed&&nonce.size()==16,"upgrade unavailable");started=true;
        auto open_nonce=k.constant(nonce);Values request;
        if(credentials_a.size())request=k.cache.get("signal-upgrade-shared "+std::to_string(PASSWORD)).run(s,{{"credentialsA",&credentials_a},{"credentialsB",&credentials_b},{"nonce",&open_nonce}});
        else{
            // TEST FIXTURE credentials.
            std::vector<uint8_t>credentials{0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff};credentials.insert(credentials.end(),PASSWORD,'x');
            auto secret=entered(credentials);
            request=k.cache.get("signal-upgrade "+std::to_string(PASSWORD)).run(s,{{"credentials",&secret},{"nonce",&open_nonce}});
        }
        // Expected Sec-WebSocket-Accept: a public function of the public nonce.
        unsigned char key[25]={},digest[20],encoded[29]={};EVP_EncodeBlock(key,nonce.data(),16);
        std::string material(reinterpret_cast<char*>(key),24);material+="258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
        SHA1(reinterpret_cast<const unsigned char*>(material.data()),material.size(),digest);EVP_EncodeBlock(encoded,digest,20);
        accept_bytes.assign(encoded,encoded+28);ws["accept"]=k.constant(accept_bytes);
        auto unused=k.constant({0});auto initial=k.cache.get("ws-initial").run(s,{{"unused",&unused}});
        for(auto name:{"upgrade","frame","control","responseTemplate"})ws[name]=std::move(initial.at(name));
        const size_t bytes=request.at("content").size()/8;
        return {k.retain({Wires{},std::move(request.at("content")),Wires{}}),bytes};
    }
    // One established sealed-sender text send. Returns the handle of the masked
    // WebSocket frame (private length within a public capacity) and that capacity.
    std::pair<uint64_t,size_t> produce(uint64_t input){
        need((public_receive?started:(upgraded&&!pending))&&!closed&&input>=1&&input<=inputs.size()&&!consumed[input-1],"send unavailable");consumed[input-1]=true;
        auto&c=conversations.at(inputs[input-1].first);
        prepare(c);
        std::array<uint8_t,32>seed{};{emp::PRG prg;prg.random_data_unaligned(seed.data(),32);}
        auto ephemeral=k.shared_scalar(seed);
        auto ephemeral_public=k.agreement_word(ephemeral,f.constant(9)),ephemeral_agreement=k.agreement_word(ephemeral,c.recipient),mask=k.fresh(4);
        auto&kernel=k.cache.get(std::string(public_receive?"signal-send-open ":"signal-send ")+std::to_string(CERT));
        auto w=whole(c);
        auto out=kernel.run(s,{{"conversation",&w},{"text",&inputs[input-1].second},{"requestId",&ws.at("requestId")},
            {"ephemeralPublic",&ephemeral_public},{"senderPublic",&of(c).sender_public},{"ephemeralAgreement",&ephemeral_agreement},
            {"staticAgreement",&c.static_agreement},{"mask",&mask},{"responseTemplate",&ws.at("responseTemplate")}});
        // Nothing is retained or sealed unless the gated status opens to 255.
        need(kernel.open(s,out,"status")==std::vector<uint8_t>{255},"private send rejected");
        keep(c,out.at("conversation"));ws["requestId"]=std::move(out.at("requestId"));
        if(public_receive)last_request_id=kernel.open(s,out,"requestIdUsed");   // correlated in the clear by the controllers
        else{ws["response"]=std::move(out.at("response"));pending=true;}
        const size_t capacity=out.at("content").size()/8;
        return {k.retain({std::move(out.at("length")),std::move(out.at("content")),std::move(out.at("valid"))}),capacity};
    }
    // Open-envelope send, step 1: session encryption and sealed sender. Opens the gated status,
    // then the timestamp and the envelope (what the Signal server will receive).
    // Reply: timestamp8, length2, envelope bytes (public capacity).
    std::vector<uint8_t> seal_open(uint64_t input){
        need(public_receive&&started&&!closed&&input>=1&&input<=inputs.size()&&!consumed[input-1],"send unavailable");consumed[input-1]=true;
        return seal_open(inputs[input-1].first,inputs[input-1].second);
    }
    // The same for a contact by id and a PUBLIC text (the notify path): `text` is the 90-byte
    // message content the controllers built in the clear (the kernel named signal-seal-built).
    std::vector<uint8_t> seal_open(const ContactId&id,const std::vector<uint8_t>&text){
        need(public_receive&&started&&!closed&&text.size()==90&&conversations.count(id),"send unavailable");
        return seal_open(id,k.constant(text));
    }
    std::vector<uint8_t> seal_open(const ContactId&id,const Wires&text){
        auto&c=conversations.at(id);need(c.record.size()!=0,"contact state not loaded");
        prepare(c);
        // Ephemeral pair by the offset agreement (edwards_points.h): no ladder per message.
        if(!c.offset.prepared())c.offset.prepare(offset_programs,f,k.channel,k.party,c.recipient);
        std::array<uint8_t,32>offset{};{
            // Joint public offset: commit, then open, then XOR.
            std::array<uint8_t,32>mine{},peer{},commit{},peer_commit{},check{};{emp::PRG prg;prg.random_data_unaligned(mine.data(),32);}
            SHA256(mine.data(),32,commit.data());k.channel.transfer(commit.data(),peer_commit.data(),32);k.channel.transfer(mine.data(),peer.data(),32);
            SHA256(peer.data(),32,check.data());need(check==peer_commit,"offset commitment");
            for(unsigned i=0;i<32;i++)offset[i]=mine[i]^peer[i];
        }
        auto pair=c.offset.step(offset_programs,f,offset);
        std::vector<uint8_t>public_bits(255);for(unsigned i=0;i<255;i++)public_bits[i]=(pair.first[i/8]>>(i%8))&1;
        auto ephemeral_public=s.public_bits(public_bits);
        auto ephemeral_agreement=field_to_word(s,f,k.channel,k.circuits,k.take_mask(),pair.second);
        // Lengths are public under the policy: open the counters' varint widths and use the
        // fixed-width kernel for exactly those widths (it rejects if the widths are not exact).
        auto&widths=k.cache.get("signal-widths "+std::to_string(CERT));auto w=whole(c);auto flags=widths.run(s,{{"conversation",&w}});
        std::string name=std::string(text.size()==8*90?"signal-seal-built ":"signal-seal-fixed ")+std::to_string(CERT);
        for(auto field:{"counter","previous","epoch","index"}){
            unsigned width=1;for(auto flag:widths.open(s,flags,field)){need(flag==0||flag==255,"width flag");width+=flag==255;}
            name+=" "+std::to_string(width);
        }
        auto&kernel=k.cache.get(name);
        Wires body=text;
        auto out=kernel.run(s,{{"conversation",&w},{"text",&body},{"ephemeralPublic",&ephemeral_public},
            {"senderPublic",&of(c).sender_public},{"ephemeralAgreement",&ephemeral_agreement},{"staticAgreement",&c.static_agreement}});
        need(kernel.open(s,out,"status")==std::vector<uint8_t>{255},"private send rejected");
        keep(c,out.at("conversation"));
        auto reply=kernel.open(s,out,"timestamp");auto envelope=kernel.open(s,out,"envelope");
        reply.push_back(uint8_t(envelope.size()>>8));reply.push_back(uint8_t(envelope.size()));reply.insert(reply.end(),envelope.begin(),envelope.end());
        return reply;
    }
    // Step 2: a request frame assembled in the clear, to be sealed with this conversation's
    // private recipient fields inserted at the given public offsets.
    uint64_t request(uint64_t input,const std::vector<size_t>&offsets,const std::vector<uint8_t>&mask,const std::vector<uint8_t>&frame){
        need(input>=1&&input<=inputs.size()&&consumed[input-1],"request unavailable");
        return request(inputs[input-1].first,offsets,mask,frame);
    }
    uint64_t request(const ContactId&id,const std::vector<size_t>&offsets,const std::vector<uint8_t>&mask,const std::vector<uint8_t>&frame){
        auto it=conversations.find(id);
        need(public_receive&&!closed&&it!=conversations.end()&&it->second.record.size()!=0&&offsets.size()==4&&mask.size()==4&&!frame.empty(),"request unavailable");
        TlsKernels::PrivateBuffer buffer;buffer.content=k.constant(frame);
        buffer.sealer="signal-request-ctr "+std::to_string(CERT)+" "+std::to_string(frame.size());for(auto at:offsets)buffer.sealer+=" "+std::to_string(at);
        buffer.extra["conversation"]=whole(it->second);buffer.extra["mask"]=k.constant(mask);
        return k.retain(std::move(buffer));
    }
    // One received application chunk through the parsers.
    // Reply: upgraded, response complete, n, n x (kind, handle8, capacity2).
    std::vector<uint8_t> process(uint64_t handle){
        need(started&&!closed,"WebSocket unavailable");
        auto it=k.buffers.find(handle);need(it!=k.buffers.end()&&it->second.length.size()!=0,"receive handle");
        auto chunk=std::move(it->second);k.buffers.erase(it);const size_t capacity=chunk.content.size()/8;need(capacity>=1&&capacity<=128,"receive profile");
        auto&activity=k.cache.get("ws-activity "+std::to_string(capacity));auto valid=k.constant({255});
        auto masks=activity.run(s,{{"valid",&valid},{"length",&chunk.length}});
        need(activity.open(s,masks,"accepted")==std::vector<uint8_t>{255},"invalid private receive chunk");
        const bool upgrading=!upgraded,responding=pending;
        auto&step=k.cache.get(upgrading?"ws-upgrade-byte":responding?"ws-response-byte":"ws-idle-byte");Values out;
        for(size_t i=0;i<capacity;i++){
            auto active=masks.at("masks").slice(8*i,8*i+8),byte=chunk.content.slice(8*i,8*i+8);   // i-th element of each array
            Binding bound{{"frame",&ws.at("frame")},{"control",&ws.at("control")},{"active",&active},{"byte",&byte}};
            if(upgrading){bound.push_back({"upgrade",&ws.at("upgrade")});bound.push_back({"accept",&ws.at("accept")});}
            else if(responding)bound.push_back({"response",&ws.at("response")});
            out=step.run(s,bound);
            ws["frame"]=std::move(out.at("frame"));ws["control"]=std::move(out.at("control"));
            if(upgrading)ws["upgrade"]=std::move(out.at("upgrade"));else if(responding)ws["response"]=std::move(out.at("response"));
        }
        auto flags=step.open(s,out,"status");bool complete=false;
        if(upgrading){
            need(flags.size()==3&&flags[0]==255&&(flags[1]==0||flags[1]==255)&&flags[2]==255,"WebSocket upgrade rejected");
            if(flags[1]==255){upgraded=true;ws.erase("upgrade");}
        }else if(responding){
            need(flags.size()==4&&flags[0]==255&&flags[1]==255&&(flags[2]==0||flags[2]==255)&&(flags[3]==0||flags[3]==255)&&(flags[2]==255||flags[3]==0),"private response rejected");
            if(flags[2]==255){need(flags[3]==255,"service response was not a success");complete=true;pending=false;ws.erase("response");}
        }else need(flags.size()==1&&flags[0]==255,"WebSocket frame rejected");
        // Control queue: validity, then count and kinds; lengths and payloads stay private.
        auto&status=k.cache.get("ws-control-status");auto queue_out=status.run(s,{{"control",&ws.at("control")}});
        need(status.open(s,queue_out,"valid")==std::vector<uint8_t>{255},"private controls rejected");
        auto queue=status.open(s,queue_out,"queue");need(queue.size()==5&&queue[0]<=4,"control queue");
        for(unsigned i=0;i<4;i++)need(i<queue[0]?(queue[i+1]==8||queue[i+1]==10):queue[i+1]==0,"control kind");
        std::vector<uint8_t>reply{uint8_t(upgraded),uint8_t(complete),queue[0]};
        for(unsigned i=0;i<queue[0];i++){
            auto mask=k.fresh(4);auto frame=k.cache.get("ws-control-reply "+std::to_string(i)).run(s,{{"control",&ws.at("control")},{"mask",&mask}});
            const size_t bytes=frame.at("content").size()/8;
            auto id=k.retain({std::move(frame.at("length")),std::move(frame.at("content")),std::move(frame.at("valid"))});
            reply.push_back(queue[i+1]);for(int b=7;b>=0;b--)reply.push_back(uint8_t(id>>(8*b)));reply.push_back(uint8_t(bytes>>8));reply.push_back(uint8_t(bytes));
            if(queue[i+1]==8)closed=true;
        }
        ws["control"]=std::move(queue_out.at("control"));
        return reply;
    }
    void close(){closed=true;conversations.clear();inputs.clear();ws.clear();}
};
}
