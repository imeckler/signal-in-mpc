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
    // `scalar`: the identity key's 256 bits as private wires (what is stored); `identity`: its
    // ladder swap bits in the field engine (what the agreements use).
    struct Account {std::vector<H>identity;Wires certificate,sender_public,scalar;};
    // A contact with a device LIST (MULTI_DEVICE.md) holds one entry per device: its record and,
    // for a session we started that the device has not answered, the `pending` record its
    // messages are built from (kind 1: no one-time prekey was used; 2: one was; 0: established).
    // `devices` empty: the contact is the single record below. Otherwise `record` is a copy of the
    // first device's (the contact's identity key, UUID and access key are the same in every one).
    struct Device {Wires record,pending;unsigned kind=0;};
    struct Conversation {Wires record,static_agreement,key;H recipient;bool ready=false;OffsetAgreement offset;Account*fixture=nullptr;std::vector<Device>devices;};
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
        // Likewise a shape outside the deployment's circuit manifest (strict mode, kernel.h).
        try{return k.cache.get(name);}catch(const KernelRefused&){throw Rejected{};}
        catch(const std::runtime_error&e){if(std::string(e.what())=="kernel cache failed")throw Rejected{};throw;}
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
    // Several connections in one worker (tls_worker_v3.cpp, operation 90): the WebSocket state of
    // ONE connection, swapped with a parked copy when the worker switches connections. Contacts,
    // the account and the envelope or bundle being collected are shared by every connection.
    struct Socket {Values ws;bool started=false,upgraded=false,pending=false,closed=false,public_receive=false;std::vector<uint8_t>accept_bytes,last_request_id;};
    void exchange(Socket&other){
        std::swap(ws,other.ws);std::swap(started,other.started);std::swap(upgraded,other.upgraded);std::swap(pending,other.pending);std::swap(closed,other.closed);
        std::swap(public_receive,other.public_receive);std::swap(accept_bytes,other.accept_bytes);std::swap(last_request_id,other.last_request_id);
    }
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
        account.scalar=entered(std::vector<uint8_t>(secret.begin(),secret.end()));
    }
    // ---- The account's own record at rest: identity key (32), socket credentials (account id
    // 16, password), sender certificate. Sealed and opened by the same kernels as a contact's
    // state, under a key from the two parties' shares of the account's stored scalar.
    Wires account_traffic,credentials;
    void account_key(const std::array<uint8_t,32>&share){
        need(!closed,"account key unavailable");
        const std::vector<uint8_t>mine(share.begin(),share.end()),none(32,0);
        auto a=s.input_private(emp::ALICE,byte_bits(k.party==emp::ALICE?mine:none)),b=s.input_private(emp::BOB,byte_bits(k.party==emp::BOB?mine:none));
        auto out=k.cache.get("contact-key").run(s,{{"shareA",&a},{"shareB",&b}});account_traffic=std::move(out.at("traffic"));
    }
    // Reply: check16, ciphertext. Needs the admitted account and its credentials (both shares).
    std::vector<uint8_t> account_seal(const std::vector<uint8_t>&version){
        need(!closed&&account_traffic.size()&&account.scalar.size()==256&&account.certificate.size()&&(credentials.size()||credentials_a.size()),"account seal unavailable");version_ok(version);
        if(!credentials.size())credentials=s.run(k.circuits.xor_bit.parallel(uint32_t(credentials_a.size())),DynSession::interleave(credentials_a,credentials_b));
        auto content=DynSession::concat({&account.scalar,&credentials,&account.certificate});
        auto&kernel=k.cache.get("contact-seal "+std::to_string(content.size()/8));auto v=k.constant(version);
        auto out=kernel.run(s,{{"traffic",&account_traffic},{"version",&v},{"content",&content}});
        auto reply=kernel.open(s,out,"check");auto ciphertext=kernel.open(s,out,"ciphertext");reply.insert(reply.end(),ciphertext.begin(),ciphertext.end());return reply;
    }
    // Load the account from its stored ciphertext: nothing is opened but the key check.
    void account_open(const std::vector<uint8_t>&version,const std::vector<uint8_t>&check,const std::vector<uint8_t>&ciphertext){
        const size_t fixed=32+16+PASSWORD;
        need(!closed&&!started&&!admitted&&account_traffic.size()&&check.size()==16&&ciphertext.size()>fixed&&ciphertext.size()<=fixed+1024,"account open unavailable");version_ok(version);
        auto&kernel=k.cache.get("contact-open "+std::to_string(ciphertext.size()));auto v=k.constant(version),sum=k.constant(check),body=k.constant(ciphertext);
        auto out=kernel.run(s,{{"traffic",&account_traffic},{"version",&v},{"ciphertext",&body},{"check",&sum}});
        need(kernel.open(s,out,"accepted")==std::vector<uint8_t>{255},"account key does not match the stored state");
        const auto&content=out.at("content");CERT=ciphertext.size()-fixed;admitted=true;
        account.scalar=content.slice(0,256);credentials=content.slice(256,8*fixed);account.certificate=content.slice(8*fixed,content.size());
        // The ladder's swap bits from the scalar's bits (Lean circuit), then into the field engine.
        account.identity=k.bits_to_field(s.run(k.curve.swap_bits,account.scalar));
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
            // Our new ratchet key: a scalar neither party knows.
            std::array<uint8_t,32>seed{};{emp::PRG prg;prg.random_data_unaligned(seed.data(),32);}
            auto ratchet=k.shared_scalar(seed);
            // The agreements do not depend on one another: they run in the same field rounds.
            const auto one_time=a.one_time?k.public_scalar(one_time_prekey):std::vector<H>{};
            std::vector<std::pair<const std::vector<H>*,H>>jobs{{&ours,a.sender_point},{&account.identity,a.base},{&ours,a.base},{&ours,a.ratchet},
                {&ratchet,a.ratchet},{&ratchet,f.constant(9)}};
            if(a.one_time)jobs.push_back({&one_time,a.base});
            auto agreed=k.agreement_words(jobs);
            auto&dh1=agreed[0],&dh2=agreed[1],&dh3=agreed[2],&receiving=agreed[3],&sending=agreed[4],&ratchet_public=agreed[5];
            Wires dh4;if(a.one_time)dh4=agreed[6];
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
        auto&c=it->second;
        // A device list is stored as its entries one after the other (record, then pending if any).
        const Wires joined=c.devices.empty()?Wires{}:entries(c);const Wires&content=c.devices.empty()?c.record:joined;
        auto&kernel=k.cache.get("contact-seal "+std::to_string(content.size()/8));auto v=k.constant(version);
        auto out=kernel.run(s,{{"traffic",&c.key},{"version",&v},{"content",&content}});
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
    // Give a contact received under a provisional id its real id (named by the message it
    // sent). Reply 255, or 0 (and the contact is dropped) if that id is already present.
    std::vector<uint8_t> contact_assign(const ContactId&from,const ContactId&to){
        auto it=conversations.find(from);need(!closed&&it!=conversations.end(),"contact assign unavailable");
        Conversation moved=std::move(it->second);conversations.erase(it);
        if(conversations.count(to))return {0};
        conversations[to]=std::move(moved);return {255};
    }
    // Drop a contact's loaded state, key and cached derived values.
    // TEST FIXTURE: the sender identity admitted with the fixture stays (it is the client's own key, not contact state).
    void contact_evict(const ContactId&id){
        auto it=conversations.find(id);need(it!=conversations.end(),"contact evict unavailable");
        auto&c=it->second;c.record=Wires{};c.key=Wires{};c.static_agreement=Wires{};c.ready=false;c.offset=OffsetAgreement{};c.devices.clear();
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
        if(credentials.size())request=k.cache.get("signal-upgrade "+std::to_string(PASSWORD)).run(s,{{"credentials",&credentials},{"nonce",&open_nonce}});
        else if(credentials_a.size())request=k.cache.get("signal-upgrade-shared "+std::to_string(PASSWORD)).run(s,{{"credentialsA",&credentials_a},{"credentialsB",&credentials_b},{"nonce",&open_nonce}});
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
        // Size class c in 1..4: validity, kind, 80c padded content bytes, timestamp8 (10+80c bytes).
        need(public_receive&&started&&!closed&&text.size()>=90&&text.size()<=330&&(text.size()-10)%80==0&&conversations.count(id),"send unavailable");
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
        // A private text input is 59 bytes (signal-seal-fixed); built public content is 10+80c bytes and names its size class c.
        std::string name=text.size()>=8*90&&(text.size()-8*10)%(8*80)==0?"signal-seal-built "+std::to_string(CERT)+" "+std::to_string((text.size()-8*10)/(8*80)):"signal-seal-fixed "+std::to_string(CERT);
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
        auto chunk=std::move(it->second);k.buffers.erase(it);const size_t capacity=chunk.content.size()/8;need(capacity>=1&&capacity<=139,"receive profile");   // the size class of a 149-byte record
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
    // ---- A contact with several devices (MULTI_DEVICE.md; kernels in TlsMpc/BundleKernels.lean,
    // EstablishKernels.lean and MlKemFastKernels.lean). As everywhere in this file: kernels are
    // sequenced and their named fields bound; nothing is parsed or computed here. Opened: the
    // prekey response's punctuation shape, one status byte per device, and per send what a
    // single-device send opens (status, timestamp, envelope). The response body, every bundle
    // field, the device ids and why an establishment failed stay private.
private:
    static constexpr size_t PENDING=1616;   // EstablishKernel.pendingBytes
    Wires bundle;   // a prekey response's body, collected unopened
    // One device's establishment in progress, between its steps; `done` and `statuses` over the devices so far.
    struct Establishing {
        size_t index=0;unsigned step=0;bool one_time=false;
        Values fields,bound,hash,ntt,parts,kem;std::vector<Wires>agreements;
        H identity_point,signed_point,one_time_point;std::vector<H>lifted;Wires identity_valid,identity_x,identity_y;
        std::vector<Device>done;std::vector<uint8_t>statuses;
    };
    Establishing establishing;
    Wires entries(const Conversation&c){
        std::vector<const Wires*>parts;for(auto&d:c.devices){parts.push_back(&d.record);if(d.kind)parts.push_back(&d.pending);}
        return DynSession::concat(parts);
    }
    // A new ephemeral pair for a message to this contact (public key word, agreement word), by the
    // offset agreement with a joint public offset, exactly as in seal_open.
    std::pair<Wires,Wires> ephemeral(Conversation&c){
        if(!c.offset.prepared())c.offset.prepare(offset_programs,f,k.channel,k.party,c.recipient);
        std::array<uint8_t,32>offset{},mine{},peer{},commit{},peer_commit{},check{};{emp::PRG prg;prg.random_data_unaligned(mine.data(),32);}
        SHA256(mine.data(),32,commit.data());k.channel.transfer(commit.data(),peer_commit.data(),32);k.channel.transfer(mine.data(),peer.data(),32);
        SHA256(peer.data(),32,check.data());need(check==peer_commit,"offset commitment");
        for(unsigned i=0;i<32;i++)offset[i]=mine[i]^peer[i];
        auto pair=c.offset.step(offset_programs,f,offset);
        std::vector<uint8_t>public_bits(255);for(unsigned i=0;i<255;i++)public_bits[i]=(pair.first[i/8]>>(i%8))&1;
        return {s.public_bits(public_bits),field_to_word(s,f,k.channel,k.circuits,k.take_mask(),pair.second)};
    }
public:
    // The prekey fetch for a contact: a frame built in the clear; the sealer inserts the contact's
    // UUID and access key from its record. Returns the handle of the request to seal.
    uint64_t bundle_fetch(const ContactId&id,size_t payload_at,size_t uuid_at,size_t key_at,const std::vector<uint8_t>&mask,const std::vector<uint8_t>&frame){
        auto it=conversations.find(id);
        need(public_receive&&!closed&&it!=conversations.end()&&it->second.record.size()!=0&&mask.size()==4&&!frame.empty(),"bundle fetch unavailable");
        TlsKernels::PrivateBuffer buffer;buffer.content=k.constant(frame);
        buffer.sealer="bundle-fetch-ctr "+std::to_string(frame.size())+" "+std::to_string(payload_at)+" "+std::to_string(uuid_at)+" "+std::to_string(key_at);
        buffer.extra["record"]=it->second.record;buffer.extra["mask"]=k.constant(mask);
        return k.retain(std::move(buffer));
    }
    // The response body, collected unopened from the records that carried it. Reply: bytes held (4).
    std::vector<uint8_t> bundle_take(uint64_t handle,size_t offset,size_t count){
        need(public_receive&&!closed&&bundle.size()/8+count<=65536,"bundle take");
        auto part=k.take_range(handle,offset,count);bundle=bundle.size()?DynSession::concat({&bundle,&part}):part;
        const size_t n=bundle.size()/8;return {uint8_t(n>>24),uint8_t(n>>16),uint8_t(n>>8),uint8_t(n)};
    }
    void bundle_drop(){bundle=Wires{};establishing=Establishing{};}
    // Opens one flag per body byte: whether it is JSON punctuation (the output Lean marks public).
    std::vector<uint8_t> bundle_shape(){
        need(public_receive&&!closed&&bundle.size()>=8*2540,"bundle shape");
        // In a size class (TlsMpc/BundleItemKernels.lean): the body followed by public zero bytes up to
        // the class's capacity; their flags are zero and are dropped from the reply.
        const size_t size=bundle.size()/8,capacity=TlsKernels::record_capacity(size);
        auto filler=k.constant(std::vector<uint8_t>(capacity-size+1,0)).slice(0,8*(capacity-size));
        auto padded=DynSession::concat({&bundle,&filler});
        auto&kernel=k.cache.get("bundle-shape "+std::to_string(capacity));
        auto flags=kernel.open(s,kernel.run(s,{{"body",&padded}}),"shape");flags.resize(size);return flags;
    }
    // One step (0..8) of one device's establishment from the held body. The controllers call the
    // steps of device 0, then of device 1, ... in order (and may keep the connection alive in
    // between; a step is at most a few million gates or two dozen thousand field products).
    //   0: the device's fields, its signatures (identity key lifted once per response), binding to the contact
    //   1: the key agreements, with a new base scalar and a new ratchet scalar neither party knows
    //   2..7: Kyber-1024 encapsulation to the device's Kyber prekey (each party supplies 32 private bytes)
    //   8: the session; opens its one status byte
    // `layout`: the item's offset and digit counts, from Lean's `layout?` on the opened shape.
    // Reply: 255 after steps 0..7, the status after step 8; 0 if Lean refuses the layout. When
    // the last device's status and all before it are 255 the contact's device list is replaced
    // by the new one; otherwise it is left as it was.
    std::vector<uint8_t> bundle_establish(const ContactId&id,size_t index,size_t count,unsigned step,const std::array<size_t,6>&layout,
            const std::vector<uint8_t>&local_registration,const std::vector<uint8_t>&request_id){
        auto it=conversations.find(id);
        need(public_receive&&!closed&&it!=conversations.end()&&it->second.record.size()!=0&&bundle.size()&&count>=1&&count<=6&&index<count&&step<=8&&
            local_registration.size()==4&&request_id.size()==8,"bundle establish");
        if(index==0&&step==0)establishing=Establishing{};
        auto&e=establishing;need(e.index==index&&e.step==step,"bundle establish order");
        auto&c=it->second;auto&a=of(c);const std::string flag=layout[4]?"1":"0";
        try{
            switch(step){
            case 0:{
                prepare(c);
                // The item and the bytes around it (TlsMpc/BundleItemKernels.lean), cut from the held body at
                // the item's offset with the widths the kernel declares for its inputs. Its shape depends
                // on the item alone, not on the size of the body or where the item lies in it.
                std::string name=std::string("bundle-item ")+(index==0?"1":"0")+(index+1==count?" 1":" 0");
                for(size_t i=1;i<6;i++)name+=" "+std::to_string(layout[i]);
                auto&cut=shaped(name);
                const size_t total=bundle.size()/8,start=layout[0],head=cut.input_bits("head")/8,width=cut.input_bits("item")/8;
                if(start<head||(index==0)!=(start==head)||start+width+2>total)throw Rejected{};
                auto head_bytes=bundle.slice(0,8*head),item_bytes=bundle.slice(8*start,8*(start+width)),end_bytes=bundle.slice(8*(total-2),8*total);
                auto before=bundle.slice(8*(start-1),8*start),after=bundle.slice(8*(start+width),8*(start+width+1));
                Binding pieces{{"head",&head_bytes},{"item",&item_bytes},{"end",&end_bytes}};
                if(index!=0)pieces.push_back({"before",&before});
                if(index+1!=count)pieces.push_back({"after",&after});
                e.fields=cut.run(s,pieces);e.one_time=layout[4]!=0;
                Binding keys{{"identityKey",&e.fields.at("identityKey")},{"signedPrekey",&e.fields.at("signedPrekey")}};
                if(e.one_time)keys.push_back({"oneTimePrekey",&e.fields.at("oneTimePrekey")});
                auto points=k.cache.get("establish-points "+flag).run(s,keys);
                if(index==0){
                    // The identity key is the same bytes for every device of a response.
                    e.identity_point=k.word_to_field(points.at("identityPoint"));
                    e.lifted=programs.recover.evaluate_all(f,{{e.identity_point}}).at(0);
                    e.identity_valid=word(e.lifted.at(0));e.identity_x=word(e.lifted.at(1));e.identity_y=word(e.lifted.at(2));
                }
                e.signed_point=k.word_to_field(points.at("signedPrekeyPoint"));
                if(e.one_time)e.one_time_point=k.word_to_field(points.at("oneTimePrekeyPoint"));
                auto challenges=k.cache.get("establish-challenges").run(s,{{"identityX",&e.identity_x},{"identityY",&e.identity_y},{"signedPrekey",&e.fields.at("signedPrekey")},
                    {"signedPrekeySignature",&e.fields.at("signedPrekeySignature")},{"kyberPrekey",&e.fields.at("kyberPrekey")},{"kyberPrekeySignature",&e.fields.at("kyberPrekeySignature")}});
                auto instance=[&](const char*flip,const char*challenge,const char*scalar){
                    std::vector<H>in{e.lifted.at(1),e.lifted.at(2)};
                    for(auto h:k.bits_to_field(DynSession::concat({&challenges.at(flip),&challenges.at(challenge),&challenges.at(scalar)})))in.push_back(h);
                    return in;
                };
                auto ec=instance("ecFlip","ecChallenge","ecScalar"),pq=instance("pqFlip","pqChallenge","pqScalar");
                auto r=programs.check.evaluate_all(f,{ec,pq});   // both signatures in the same rounds
                auto ec_rx=word(r.at(0).at(0)),ec_ry=word(r.at(0).at(1)),pq_rx=word(r.at(1).at(0)),pq_ry=word(r.at(1).at(1));
                auto verified=k.cache.get("establish-verified").run(s,{{"identityValid",&e.identity_valid},{"ecRx",&ec_rx},{"ecRy",&ec_ry},{"pqRx",&pq_rx},{"pqRy",&pq_ry},
                    {"signedPrekeySignature",&e.fields.at("signedPrekeySignature")},{"kyberPrekeySignature",&e.fields.at("kyberPrekeySignature")}});
                e.bound=k.cache.get("bundle-bind").run(s,{{"record",&c.record},{"valid",&e.fields.at("valid")},{"verified",&verified.at("verified")},{"identityKey",&e.fields.at("identityKey")}});
                break;
            }
            case 1:{
                std::array<uint8_t,32>seed{};{emp::PRG prg;prg.random_data_unaligned(seed.data(),32);}
                auto base=k.shared_scalar(seed);{emp::PRG prg;prg.random_data_unaligned(seed.data(),32);}
                auto ratchet=k.shared_scalar(seed);
                // dh1, dh2, dh3, ratchetAgreement, basePublic, ratchetPublic, (dh4): EstablishKernels.lean, step 6.
                std::vector<std::pair<const std::vector<H>*,H>>jobs{{&a.identity,e.signed_point},{&base,e.identity_point},{&base,e.signed_point},{&ratchet,e.signed_point},
                    {&base,f.constant(9)},{&ratchet,f.constant(9)}};
                if(e.one_time)jobs.push_back({&base,e.one_time_point});
                e.agreements=k.agreement_words(jobs);
                break;
            }
            case 2:{
                auto entropy=[&](int owner){std::vector<uint8_t>mine(32,0);if(k.party==owner){emp::PRG prg;prg.random_data_unaligned(mine.data(),32);}return s.input_private(owner,byte_bits(mine));};
                auto mine=entropy(emp::ALICE),theirs=entropy(emp::BOB);
                e.hash=k.cache.get("kem-hash kyber").run(s,{{"kyberPrekey",&e.fields.at("kyberPrekey")},{"entropyA",&mine},{"entropyB",&theirs}});
                e.ntt=k.cache.get("kem-ntt").run(s,{{"coins",&e.hash.at("coins")}});
                break;
            }
            case 3:case 4:case 5:case 6:{
                const std::string row=std::to_string(step-3);
                auto matrix=k.cache.get("kem-matrix "+row).run(s,{{"kyberPrekey",&e.fields.at("kyberPrekey")}});
                auto u=k.cache.get("kem-u "+row).run(s,{{"row"+row,&matrix.at("row"+row)},{"rhat",&e.ntt.at("rhat")},{"coins",&e.hash.at("coins")}});
                e.parts["u"+row]=std::move(u.at("u"+row));e.parts["ok"+row]=std::move(matrix.at("ok"+row));
                break;
            }
            case 7:{
                auto v=k.cache.get("kem-v").run(s,{{"kyberPrekey",&e.fields.at("kyberPrekey")},{"rhat",&e.ntt.at("rhat")},{"coins",&e.hash.at("coins")},{"message",&e.hash.at("message")}});
                Binding bound{{"v",&v.at("v")},{"kbar",&e.hash.at("kbar")},{"keyValid",&e.hash.at("keyValid")}};
                for(auto&part:e.parts)bound.push_back({part.first,&part.second});
                e.kem=k.cache.get("kem-finish kyber").run(s,bound);
                break;
            }
            default:{
                need(e.agreements.size()==(e.one_time?7u:6u),"bundle establish agreements");
                auto&session=k.cache.get("establish-session "+std::to_string(CERT)+" "+flag);
                auto request=k.constant(request_id),local=k.constant(local_registration);
                Binding bound{{"verified",&e.bound.at("verified")},{"kemStatus",&e.kem.at("kemStatus")},{"dh1",&e.agreements[0]},{"dh2",&e.agreements[1]},{"dh3",&e.agreements[2]},
                    {"ratchetAgreement",&e.agreements[3]},{"kemSecret",&e.kem.at("kemSecret")},{"kemCiphertext",&e.kem.at("kemCiphertext")},
                    {"basePublic",&e.agreements[4]},{"ratchetPublic",&e.agreements[5]},{"senderPublic",&a.sender_public},
                    {"identityKey",&e.fields.at("identityKey")},{"signedPrekey",&e.fields.at("signedPrekey")},{"certificate",&a.certificate},
                    {"uuid",&e.bound.at("uuid")},{"accessKey",&e.bound.at("accessKey")},{"requestId",&request},{"deviceId",&e.fields.at("deviceId")},
                    {"registrationId",&e.fields.at("registrationId")},{"localRegistrationId",&local},
                    {"signedPrekeyId",&e.fields.at("signedPrekeyId")},{"kyberPrekeyId",&e.fields.at("kyberPrekeyId")}};
                if(e.one_time){bound.push_back({"dh4",&e.agreements[6]});bound.push_back({"oneTimePrekeyId",&e.fields.at("oneTimePrekeyId")});}
                auto out=session.run(s,bound);auto status=session.open(s,out,"status");need(status.size()==1,"establish status");
                need(out.at("conversation").size()==8*(CERT+CONTACT)&&out.at("pending").size()==8*PENDING,"establish shape");
                Device device;device.record=out.at("conversation").slice(8*CERT,8*(CERT+CONTACT));device.pending=std::move(out.at("pending"));device.kind=e.one_time?2:1;
                e.done.push_back(std::move(device));e.statuses.push_back(status[0]);
                e.fields.clear();e.bound.clear();e.hash.clear();e.ntt.clear();e.parts.clear();e.kem.clear();e.agreements.clear();
                if(index+1==count){
                    bool all=true;for(auto value:e.statuses)all=all&&value==255;
                    if(all){c.devices=std::move(e.done);c.record=c.devices[0].record;}
                    bundle_drop();
                }else{e.index=index+1;e.step=0;}
                return {status[0]};
            }
            }
        }catch(const Rejected&){bundle_drop();return {0};}
        e.step=step+1;return {255};
    }
    // One send to every device of a contact with a device list: per device a new ephemeral pair
    // and the kernel for its kind (0: signal-seal-built, as a single-device send; 1, 2:
    // bundle-seal, a PreKey message built from `pending`). All devices get the same built text.
    // The new records are kept only when every status opened to 255.
    // Reply: timestamp8, then per device length2 and its envelope.
    std::vector<uint8_t> seal_devices(const ContactId&id,const std::vector<uint8_t>&local_address,const std::vector<uint8_t>&text){
        auto it=conversations.find(id);
        need(public_receive&&started&&!closed&&it!=conversations.end()&&!it->second.devices.empty()&&local_address.size()==17&&
            text.size()>=90&&text.size()<=330&&(text.size()-10)%80==0,"send unavailable");
        auto&c=it->second;prepare(c);
        auto body=k.constant(text),address=k.constant(local_address);const size_t classes=(text.size()-10)/80;
        std::vector<Wires>next;std::vector<uint8_t>reply;
        for(auto&d:c.devices){
            auto pair=ephemeral(c);
            auto w=DynSession::concat({&of(c).certificate,&d.record});
            auto&widths=k.cache.get("signal-widths "+std::to_string(CERT));auto flags=widths.run(s,{{"conversation",&w}});
            std::string name=d.kind==0?"signal-seal-built "+std::to_string(CERT)+" "+std::to_string(classes)
                :"bundle-seal "+std::to_string(CERT)+(d.kind==2?" 1 ":" 0 ")+std::to_string(80*classes);
            for(auto field:{"counter","previous","epoch","index"}){
                unsigned width=1;for(auto flag:widths.open(s,flags,field)){need(flag==0||flag==255,"width flag");width+=flag==255;}
                name+=" "+std::to_string(width);
            }
            auto&kernel=k.cache.get(name);
            Binding bound{{"conversation",&w},{"text",&body},{"ephemeralPublic",&pair.first},{"senderPublic",&of(c).sender_public},
                {"ephemeralAgreement",&pair.second},{"staticAgreement",&c.static_agreement}};
            if(d.kind!=0){bound.push_back({"pending",&d.pending});bound.push_back({"localAddress",&address});}
            auto out=kernel.run(s,bound);
            need(kernel.open(s,out,"status")==std::vector<uint8_t>{255},"private send rejected");
            need(out.at("conversation").size()==8*(CERT+CONTACT),"conversation shape");
            if(reply.empty())reply=kernel.open(s,out,"timestamp");
            auto envelope=kernel.open(s,out,"envelope");
            reply.push_back(uint8_t(envelope.size()>>8));reply.push_back(uint8_t(envelope.size()));reply.insert(reply.end(),envelope.begin(),envelope.end());
            next.push_back(out.at("conversation").slice(8*CERT,8*(CERT+CONTACT)));
        }
        for(size_t i=0;i<next.size();i++)c.devices[i].record=std::move(next[i]);
        c.record=c.devices[0].record;
        return reply;
    }
    // Its request frame: one message per device, assembled in the clear; the sealer inserts the
    // contact's UUID and access key and each device's id and registration id from the records.
    uint64_t request_devices(const ContactId&id,size_t payload_at,size_t uuid_at,size_t key_at,const std::vector<std::pair<size_t,size_t>>&slots,
            const std::vector<uint8_t>&mask,const std::vector<uint8_t>&frame){
        auto it=conversations.find(id);
        need(public_receive&&!closed&&it!=conversations.end()&&!it->second.devices.empty()&&slots.size()==it->second.devices.size()&&mask.size()==4&&!frame.empty(),"request unavailable");
        TlsKernels::PrivateBuffer buffer;buffer.content=k.constant(frame);
        buffer.sealer="bundle-request-ctr "+std::to_string(frame.size())+" "+std::to_string(payload_at)+" "+std::to_string(uuid_at)+" "+std::to_string(key_at);
        for(auto&slot:slots)buffer.sealer+=" "+std::to_string(slot.first)+" "+std::to_string(slot.second);
        std::vector<const Wires*>records;for(auto&d:it->second.devices)records.push_back(&d.record);
        buffer.extra["records"]=DynSession::concat(records);buffer.extra["mask"]=k.constant(mask);
        return k.retain(std::move(buffer));
    }
    // Load a contact's device list from its stored ciphertext. `kinds` are public (stored next to
    // the ciphertext) and say how the content splits into entries; a wrong key fails as in contact_open.
    void contact_open_devices(const ContactId&id,const std::vector<uint8_t>&kinds,const std::vector<uint8_t>&version,const std::vector<uint8_t>&check,const std::vector<uint8_t>&ciphertext){
        auto it=conversations.find(id);size_t total=0;for(auto kind:kinds){need(kind<=2,"device kind");total+=CONTACT+(kind?PENDING:0);}
        need(!closed&&it!=conversations.end()&&it->second.key.size()&&it->second.record.size()==0&&check.size()==16&&!kinds.empty()&&kinds.size()<=6&&ciphertext.size()==total,"contact open unavailable");version_ok(version);
        auto&c=it->second;auto&kernel=k.cache.get("contact-open "+std::to_string(ciphertext.size()));auto v=k.constant(version),sum=k.constant(check),body=k.constant(ciphertext);
        auto out=kernel.run(s,{{"traffic",&c.key},{"version",&v},{"ciphertext",&body},{"check",&sum}});
        need(kernel.open(s,out,"accepted")==std::vector<uint8_t>{255},"contact key does not match the stored state");
        const auto&content=out.at("content");c.devices.clear();size_t at=0;
        for(auto kind:kinds){
            Device device;device.kind=kind;device.record=content.slice(8*at,8*(at+CONTACT));at+=CONTACT;
            if(kind){device.pending=content.slice(8*at,8*(at+PENDING));at+=PENDING;}
            c.devices.push_back(std::move(device));
        }
        c.record=c.devices[0].record;c.ready=false;c.offset=OffsetAgreement{};
    }
    void close(){closed=true;conversations.clear();inputs.clear();ws.clear();}
};
}
