#pragma once
#include "NativeWorker.h"
#include "SessionLifecycle.h"
#include "PayloadWork/PrivatePayload.h"
#include "PayloadWork/StatusGate.h"
#include "PublicMetrics.h"
#include "RestoreAdmissionWork/PrivateRequestCursor.h"
#include "../signal_backend/SealedSenderWork/NativeService.h"
#include "../signal_backend/SealedSenderWork/NativeUpgrade.h"
#include "../signal_backend/SealedSenderWork/NativePayload.h"
#include "../signal_backend/VariableServiceWork/NativeVariableService.h"
#include "BatchThroughputWork/NativeBatchService.h"
#include "../signal_backend/TextNotificationWork/NativeTextNotification.h"
#include "WebSocketWork/NativeWebSocket.h"
#include "WebSocketWork/NativeWebSocketMux.h"
#include "SessionPolicy.h"
#include "ApplicationPolicy.h"
#include "ShapeCompiler.h"
#include "Protocols/Opener.h"
#include <cstdint>
#include <initializer_list>
#include <map>

namespace tls_mpc_worker {
using Bytes = std::vector<uint8_t>;
class Session {
    Machine<Share>& machine;
    Worker worker;
    ShapeCompiler* shapes;
    SessionLifecycle* lifecycle;
    const PinnedPrograms& pinned_programs;
    PublicMetrics* metrics;
    SessionPolicy policy;
    struct Traffic { Bits secret, key, iv; };
    Traffic client_hs, server_hs, client_app, server_app;
    Bits main_secret;
    ApplicationPolicy application_policy;
    bool application_ready=false;
    Bits parser_state;
    PrivateRequestCursor<Bits> request_ids;
    enum class Origin {producer,authenticated_receive,websocket_close};
    struct Buffer { Bits data, private_length, validity; size_t capacity; bool fixed_length; Origin origin=Origin::producer; };
    std::map<uint64_t,Buffer> buffers;
    std::unique_ptr<NativeWebSocket> websocket;
    std::unique_ptr<NativeWebSocketMux> websocket_mux;
    bool websocket_closing=false;
    uint64_t next_buffer=1;
    Bytes pending_wire;
    bool pending_send=false;
    static void require(bool ok, const char* reason) { if (!ok) throw std::runtime_error(reason); }
    static Bits concat(std::initializer_list<Bits> parts) {
        Bits result;
        for (const auto& part : parts) result.insert(result.end(), part.begin(), part.end());
        return result;
    }
    static Bits bytes(const Bits& input, size_t offset, size_t length) {
        require((offset + length) * 8 <= input.size(), "secret slice out of bounds");
        return Bits(input.begin() + offset * 8, input.begin() + (offset + length) * 8);
    }
    Bits public_bits(const Bytes& input) {
        auto result = worker.allocate(input.size() * 8);
        for (size_t i = 0; i < input.size(); ++i)
            for (size_t j = 0; j < 8; ++j)
                result[8*i+j][0] = Bit::constant((input[i] >> (7-j)) & 1,
                    machine.get_N().my_num(), machine.get_bit_mac_key());
        return result;
    }
    Bits eval(const std::string& name, Bits input, size_t output_bytes) {
        return worker.binary(name, std::move(input), output_bytes * 8);
    }
    Bits eval_shape(const KernelShape& shape, Bits input) {
        if(shapes)shapes->prepare(shape);
        return eval(shape.stem(),std::move(input),shape.output_bytes());
    }
    Traffic traffic(Bits secret) {
        auto output = eval("tls-traffic-keys", secret, 28);
        return {std::move(secret), bytes(output, 0, 16), bytes(output, 16, 12)};
    }
    void require_application() const {
        require(policy.phase()==SessionPolicy::Phase::application && application_ready &&
            lifecycle && lifecycle->application_allowed(),
            "application unavailable before actual handshake-state retirement");
    }
    static Bytes sequence_bytes(uint64_t sequence) {
        Bytes result(8); for(int i=7;i>=0;--i) {result[i]=sequence&255;sequence>>=8;} return result;
    }
    uint64_t retain(Buffer buffer) {
        require(next_buffer!=0 && buffers.size()<4096,"application handle capacity exhausted");
        uint64_t id=next_buffer++; buffers.emplace(id,std::move(buffer)); return id;
    }
    Bytes pending(Bytes wire) {
        require(!pending_send,"application ciphertext already pending");
        pending_wire=wire;pending_send=true;return wire;
    }
    // Private opening primitive: call sites release only authenticated public
    // handshake data, ciphertext, public key/Finished, or application event2.
    Bytes release(const Bits& input) {
        require(input.size() % 8 == 0, "unaligned public output");
        Opener<Bit> opener(machine.get_player(), machine.get_bit_mac_key());
        opener.init_open();
        for (const auto& bit : input) { require(bit.size() == 1, "invalid bit register"); opener.prepare_open(bit[0]); }
        opener.exchange();
        Bytes result(input.size()/8, 0);
        for (size_t i = 0; i < input.size(); ++i)
            result[i/8] |= (opener.finalize_open().get() & 1) << (7-i%8);
        opener.Check(); // Authenticate/check BEFORE returning public bytes.
        return result;
    }
    template<class F> auto guarded(F&& operation) -> decltype(operation()) {
        try { require(!lifecycle || lifecycle->host_active(),"private work requires erased host call"); return operation(); }
        catch (...) { abort(); throw; }
    }
    template<class F> auto measured(const char* stage,F&& operation) -> decltype(operation()) {
        if(!metrics)return operation();auto before=metrics->begin();
        try {auto result=operation();metrics->finish(stage,before);return result;}
        catch(...){metrics->finish(stage,before,false);throw;}
    }
public:
    explicit Session(Machine<Share>& machine, const PinnedPrograms& pinned,ShapeCompiler* shapes=nullptr,SessionLifecycle* lifecycle=nullptr,PublicMetrics* metrics=nullptr)
        : machine(machine), worker(machine, pinned,{},metrics?PublicFunctionObserver(
            [this](const std::string& descriptor,uint64_t verify_ns,uint64_t run_ns){this->metrics->function_resources(descriptor,verify_ns,run_ns,true);}):PublicFunctionObserver{}),
          shapes(shapes),lifecycle(lifecycle),pinned_programs(pinned),metrics(metrics) {}
    Session(const Session&)=delete;
    Session& operator=(const Session&)=delete;
    ~Session(){abort();}
    Bytes begin() { return guarded([&] { policy.begin(); return release(worker.begin()); }); }
    void derive(const Bytes& peer, const Bytes& hello_hash) {
        guarded([&] {
            policy.derive();
            require(peer.size() == 32 && hello_hash.size() == 32, "invalid agreement/hash length");
            bigint u = 0;
            for (int i = 31; i >= 0; --i) { u <<= 8; u += i == 31 ? peer[i] & 127 : peer[i]; }
            Field coordinate(u);
            auto agreement = worker.agreement(coordinate);
            auto output = eval("tls-handshake-secrets", concat({agreement, public_bits(hello_hash)}), 128);
            client_hs = traffic(bytes(output, 32, 32));
            server_hs = traffic(bytes(output, 64, 32));
            main_secret = bytes(output, 96, 32);
        });
    }
    Bytes open_handshake(uint64_t sequence, const Bytes& wire) {
        return guarded([&] {
            policy.receive(sequence);
            // AES-128-GCM profile: at most 16385 inner bytes + 16 tag + 5 header,
            // matching TlsReceive.openChecked. The generic transport limit is larger.
            require(wire.size() >= 22 && wire.size() <= 16406, "invalid AES-GCM record size");
            Bytes seq(8); for (int i = 7; i >= 0; --i) { seq[i] = sequence & 255; sequence >>= 8; }
            auto result = eval("tls-open-handshake-record-" + std::to_string(wire.size()),
                concat({server_hs.key, server_hs.iv, public_bits(seq), public_bits(wire)}), wire.size()-17);
            auto output = release(result); // PROVED handshake-only gate is inside this kernel.
            require(output[0] == 255, "handshake record authentication/type rejected");
            return output;
        });
    }
    // The service must first agree the EXACT authentication request and all
    // parties' local validation results. This method does not validate X.509.
    void certificate_authenticated() { guarded([&] { policy.authenticate(); }); }
    bool verify_finished(const Bytes& hash, const Bytes& message) {
        return guarded([&] {
            policy.verify();
            require(hash.size() == 32 && message.size() == 36, "invalid Finished dimensions");
            auto output = release(eval("tls-verify-finished",
                concat({server_hs.secret, public_bits(hash), public_bits(message)}), 1));
            require(output[0] == 255, "server Finished rejected");
            return true;
        });
    }
    Bytes finish(const Bytes& server_hash, const Bytes& client_hash, const Bytes& certificate) {
        return guarded([&] {
            policy.finish();
            require(server_hash.size() == 32 && client_hash.size() == 32, "invalid transcript hash");
            require(certificate.empty() || certificate == Bytes({11,0,0,4,0,0,0,0}), "invalid empty client certificate");
            auto applications = eval("tls-application-secrets", concat({main_secret, public_bits(server_hash)}), 64);
            client_app = traffic(bytes(applications, 0, 32));
            server_app = traffic(bytes(applications, 32, 32));
            auto verify_data = eval("tls-finished", concat({client_hs.secret, public_bits(client_hash)}), 32);
            auto content = concat({public_bits(certificate), public_bits({20,0,0,32}), verify_data});
            size_t length = certificate.size() + 36;
            return release(eval("tls-seal-record-22-"+std::to_string(length)+"-0",
                concat({client_hs.key, client_hs.iv, public_bits(Bytes(8,0)), content}), length+22));
        });
    }
    void retire() {
        guarded([&] {
            require(policy.phase()==SessionPolicy::Phase::application && !application_ready,
                "invalid or repeated retirement phase");
            require(lifecycle,"native VM retirement/erasure capability unavailable");
            worker.erase_owned_scalar();
            for(auto* traffic:{&client_hs,&server_hs}) {
                traffic->secret.clear();traffic->key.clear();traffic->iv.clear();
            }
            main_secret.clear();
            lifecycle->renew_epoch();
            // application_allowed stays false until the host-call stack wipe
            // barrier completes. The dispatcher replies only after that barrier.
            application_ready=true;
        });
    }
    // Internal same-worker producer interface, never a public RPC importing or
    // opening bytes. Trusted producers may retain their fixed-shape output here.
    uint64_t retain_fixed_payload(Bits payload) {
        return guarded([&] { require_application(); require(payload.size()%8==0 && payload.size()<=16384*8,"invalid fixed payload");
            require(!websocket_closing,"WebSocket closing; producer payload forbidden");
            size_t size=payload.size()/8;
            return retain({std::move(payload),{},{},size,true}); });
    }
    // Actual producer validity must remain attached through transport sealing.
    // Capacity is an agreed public workload profile, never an opened length.
    uint64_t retain_private_payload(PrivatePayload payload) {
        return guarded([&] { require_application();
            require(!websocket_closing,"WebSocket closing; producer payload forbidden");
            payload.validate_shape();
            require(payload.capacity<=16384,"private outgoing capacity exceeds record limit");
            return retain({std::move(payload.data),std::move(payload.private_length),
                std::move(payload.validity),payload.capacity,false}); });
    }
    uint64_t retain_private_result(Bits encoded,size_t capacity) {
        return guarded([&] {require_application();
            require(request_ids.committed(),"private account reservation incomplete");
            return retain_private_payload(PrivatePayload::from_result(std::move(encoded),capacity));});
    }
    // Embedding-only public constants and computed private validity. Neither is
    // a public RPC input/import path. Unpatched/unsupported sessions fail here.
    Bits share_public_constants(const Bytes& value) {
        return guarded([&] {require_application();return public_bits(value);});
    }
    uint64_t retain_validated_upgrade(Bits payload,Bits computed_validity) {
        return guarded([&] {require_application();require(payload.size()%8==0&&payload.size()<=16384*8&&computed_validity.size()==8,
            "invalid private upgrade dimensions");
            size_t capacity=payload.size()/8;
            return retain_private_payload(PrivatePayload(std::move(payload),
                public_bits({uint8_t(capacity>>8),uint8_t(capacity)}),std::move(computed_validity),capacity));});
    }
    Bits combine_private_validity(Bits producer,Bits upstream) {
        return guarded([&] {require_application();require(producer.size()==8&&upstream.size()==8,"invalid private validity dimensions");
            return eval("tls-provider-validity",concat({producer,upstream}),1);});
    }
    void initialize_private_request_ids(const Bytes& public_nonce) {
        guarded([&] {require_application();require(public_nonce.size()==16,"private request allocator initialization rejected");
            request_ids.initialize(eval("tls-private-request-id-init",public_bits(public_nonce),8));});
    }
    // Trusted same-worker admission only. Account authorization/coherence must
    // supply the computed flag; actual account Reserve must commit its staged
    // range before producer evaluation. No RPC import exists.
    // TLS sequence numbers, traffic keys and nonce state are always fresh.
    void restore_private_request_ids(Bits cursor,Bits computed_validity) {
        guarded([&] {require_application();require(cursor.size()==64&&computed_validity.size()==8,
                "restored request allocator admission rejected");
            auto checked=eval("tls-private-request-id-next",Bits(cursor),9);
            auto accepted=eval("tls-provider-validity",concat({bytes(checked,0,1),computed_validity}),1);
            require(release(std::move(accepted))==Bytes{255},"restored request allocator admission rejected");
            request_ids.initialize(std::move(cursor),true);});
    }
    // Invoked inside the actual staged-group Reserve hook. The callback binds
    // this cursor range and ALL staged callinputs in one account certificate.
    template<class Commit> void commit_private_request_ids(Commit&& commit) {
        guarded([&]{require_application();request_ids.commit_pending(std::forward<Commit>(commit));});
    }
    Bits reserve_private_request_id() {
        return guarded([&] {require_application();return request_ids.reserve([&](Bits current){
            auto output=measured("request.id",[&]{return eval("tls-private-request-id-next",std::move(current),9);});
            require(release(bytes(output,0,1))==Bytes{255},"private request admission rejected");
            return bytes(output,1,8);
        });}); // Restored IDs are quarantined until whole-account Reserve completes.
    }
    // Consume exactly once into an internal HTTP/WebSocket/Signal processor.
    // No plaintext bytes or actual length are returned over RPC.
    PrivatePayload take_private_payload(uint64_t handle) {
        return guarded([&] { require_application();
            auto found=buffers.find(handle);require(found!=buffers.end(),"unknown private payload handle");
            auto& source=found->second;
            auto length=source.fixed_length ? public_bits({uint8_t(source.capacity>>8),uint8_t(source.capacity)}) : std::move(source.private_length);
            auto valid=source.fixed_length ? public_bits({255}) : std::move(source.validity);
            PrivatePayload result(std::move(source.data),std::move(length),std::move(valid),source.capacity);
            buffers.erase(found);return result;
        });
    }
    // Caller must first commit selected producer state and discard old owned
    // inputs. New TLS/app/producer shares and retained outputs deliberately live.
    // Further application work waits for this host call's complete wipe barrier.
    void checkpoint_private_computation() {
        guarded([&] {require_application();require(!pending_send&&request_ids.committed(),"private checkpoint with pending ciphertext/account reservation");
            lifecycle->renew_epoch();});
    }
    Bits evaluate_signal(const signal_mpc::SendShape& shape,Bits input) {
        return guarded([&] { require_application();return worker.signal(shape,std::move(input)); });
    }
    Bits evaluate_service(const signal_mpc::ServiceShape& shape,Bits input) {
        return guarded([&] {require_application();
            signal_mpc::NativeService service(machine,worker,pinned_programs);
            require(request_ids.committed(),"private account reservation incomplete");return service.evaluate(shape,std::move(input));});
    }
    uint64_t retain_service_result(const signal_mpc::ServiceShape& shape,Bits result) {
        return guarded([&] {require_application();
            signal_mpc::NativePayload adapter(machine,worker,pinned_programs);
            return retain_private_result(adapter.wrap(shape,std::move(result)),shape.output_bytes()-1);});
    }
    Bits evaluate_upgrade(const signal_mpc::UpgradeShape& shape,Bits input) {
        return guarded([&] {require_application();
            signal_mpc::NativeUpgrade upgrade(machine,worker,pinned_programs);
            auto result=measured("upgrade.builder",[&]{return upgrade.evaluate(shape,std::move(input));});
            if(metrics)metrics->function_resources(shape.descriptor());return result;});
    }
    Bits evaluate_variable(const signal_mpc::VariableShape& shape,Bits input) {
        return guarded([&] {require_application();
            signal_mpc::NativeVariableService service(machine,worker,pinned_programs);
            auto result=measured("provider.crypto",[&]{require(request_ids.committed(),"private account reservation incomplete");return service.evaluate(shape,std::move(input));});
            if(metrics)metrics->function_resources(shape.descriptor());return result;});
    }
    std::vector<Bits> evaluate_variable_batch(const std::vector<signal_mpc::VariableShape>& shapes,std::vector<Bits> inputs) {
        return guarded([&] {require_application();require(!shapes.empty(),"empty conversation batch");
            NativeBatchService service(machine,worker,pinned_programs);
            auto result=measured("provider.crypto.batch",[&]{require(request_ids.committed(),"private account reservation incomplete");return service.evaluate(shapes,std::move(inputs));});
            if(metrics)metrics->function_resources(VariableBatchShape(shapes.front(),shapes.size()).descriptor());
            return result;});
    }
    Bits evaluate_text_notification(Bits input) {
        return guarded([&] {require_application();
            signal_mpc::NativeTextNotification builder(machine,worker,pinned_programs);
            auto result=measured("content.builder",[&]{return builder.evaluate(std::move(input));});
            if(metrics)metrics->function_resources("Programs/Functions/signal_private_text_notification_48_80-sbv:[472x1]-sbv:[720x1]");
            return result;});
    }
    void start_websocket(const Bytes& expected_accept) {
        guarded([&] {require_application();require(!websocket&&!websocket_mux,"WebSocket already initialized");
            websocket.reset(new NativeWebSocket(worker,pinned_programs,expected_accept,
                [&](const Bytes& value){return public_bits(value);}));});
    }
    void expect_websocket_response(Bits request_id) {
        guarded([&] {require_application();require(bool(websocket),"WebSocket unavailable");
            websocket->expect(std::move(request_id),[&](const Bytes& value){return public_bits(value);});});
    }
    struct WebSocketReceipt {bool upgraded,response_complete;std::vector<std::pair<unsigned,uint64_t>> controls;};
    WebSocketReceipt process_websocket(uint64_t handle) {
        return guarded([&] {require_application();require(bool(websocket)&&!pending_send,"WebSocket unavailable/pending send");
            auto found=buffers.find(handle);
            require(found!=buffers.end()&&found->second.origin==Origin::authenticated_receive,
                "WebSocket requires authenticated receive handle");
            auto result=websocket->feed(take_private_payload(handle),
                [&](const Bits& value){return release(value);},[&](const Bytes& value){return public_bits(value);});
            WebSocketReceipt receipt{result.upgraded,result.response_complete,{}};
            bool closing=false;
            for(auto& control:result.controls) {
                auto id=retain_private_result(std::move(control.payload),131);
                if(control.kind==8)buffers.at(id).origin=Origin::websocket_close;
                receipt.controls.push_back({control.kind,id});closing=closing||control.kind==8;
            }
            websocket_closing=websocket_closing||closing;
            // Partial selected protocol state survives; discarded TLS plaintext,
            // parser history and control buffers precede the erasure barrier.
            lifecycle->renew_epoch();return receipt;});
    }
    void start_websocket_mux(const Bytes& expected_accept) {
        guarded([&]{require_application();require(!websocket&&!websocket_mux,"WebSocket already initialized");
            websocket_mux.reset(new NativeWebSocketMux(worker,pinned_programs,expected_accept,
                [&](const Bytes& value){return public_bits(value);}));});
    }
    void expect_websocket_mux_response(size_t slot,Bits assigned_id,Bits computed_validity) {
        guarded([&]{require_application();require(bool(websocket_mux)&&!websocket_closing,"WebSocket mux unavailable");
            websocket_mux->expect(slot,std::move(assigned_id),std::move(computed_validity),
                [&](const Bytes& value){return public_bits(value);},[&](const Bits& value){return release(value);});});
    }
    struct WebSocketMuxReceipt {bool upgraded;Bytes completed_slots;std::vector<std::pair<unsigned,uint64_t>> controls;};
    WebSocketMuxReceipt process_websocket_mux(uint64_t handle) {
        return guarded([&]{require_application();require(bool(websocket_mux)&&!pending_send,"WebSocket mux unavailable/pending send");
            auto found=buffers.find(handle);require(found!=buffers.end()&&found->second.origin==Origin::authenticated_receive,
                "WebSocket mux requires authenticated receive handle");
            auto result=measured("receive.response",[&]{return websocket_mux->feed(take_private_payload(handle),
                [&](const Bits& value){return release(value);},[&](const Bytes& value){return public_bits(value);});});
            WebSocketMuxReceipt receipt{result.upgraded,std::move(result.completed_slots),{}};
            for(auto& control:result.controls){
                auto id=retain_private_result(std::move(control.payload),131);
                if(control.kind==8){buffers.at(id).origin=Origin::websocket_close;websocket_closing=true;}
                receipt.controls.push_back({control.kind,id});
            }
            lifecycle->renew_epoch();return receipt;});
    }
    Bytes seal_application(uint64_t sequence,uint64_t handle,size_t size,size_t padding) {
        return guarded([&] { require_application();
            require(size<=16384 && padding<=16384-size,"invalid application dimensions");
            auto found=buffers.find(handle);require(found!=buffers.end(),"unknown application handle");
            const auto& buffer=found->second;
            require(!websocket_closing||buffer.origin==Origin::websocket_close,"WebSocket closing; service send forbidden");
            require(buffer.capacity==size,"private payload capacity mismatch");
            require(buffer.fixed_length || padding==0,"private capacity already includes TLS padding");
            application_policy.application(sequence);
            Bytes wire;
            if(buffer.fixed_length) {
                wire=release(eval_shape(KernelShape::seal(23,size,padding),
                    concat({client_app.key,client_app.iv,public_bits(sequence_bytes(sequence)),buffer.data})));
            } else {
                auto sealed=eval_shape(KernelShape::seal_private(size),
                    concat({client_app.key,client_app.iv,public_bits(sequence_bytes(sequence)),
                        buffer.validity,buffer.private_length,buffer.data}));
                // Authenticate status before disclosing any ciphertext. A rejected
                // producer/bounds result is terminal, never a normal empty request.
                wire=release_private_seal(sealed,size,[&](const Bits& value) {return release(value);});
            }
            // The reserved public ciphertext is sufficient for the one pending
            // send. Consume plaintext once and erase runtime history before the
            // host-call barrier makes the ciphertext receipt eligible for send.
            // A failed send remains terminal; it cannot roll back producer state.
            buffers.erase(found);
            auto result=pending(std::move(wire));
            if(lifecycle->application_epoch_policy()==ApplicationEpochPolicy::every_record)
                lifecycle->renew_epoch();
            return result;
        });
    }
    Bytes seal_control(uint64_t sequence,unsigned kind,const Bytes& content) {
        return guarded([&] { require_application();
            if(kind==22 && (content==Bytes({24,0,0,1,0}) || content==Bytes({24,0,0,1,1})))
                application_policy.update(sequence,content.back()==1);
            else {require(kind==21 && content==Bytes({1,0}),"invalid public application control");application_policy.close(sequence);}
            return pending(release(eval_shape(KernelShape::seal(kind,content.size(),0),
                concat({client_app.key,client_app.iv,public_bits(sequence_bytes(sequence)),public_bits(content)}))));
        });
    }
    Bytes open_application(uint64_t sequence,const Bytes& wire) {
        return guarded([&] { require_application();require(wire.size()>=22 && wire.size()<=16406,"invalid application wire size");
            application_policy.receive(sequence);
            const size_t capacity=wire.size()-21;
            if(parser_state.empty()) parser_state=public_bits(Bytes(11,0));
            auto opened=eval_shape(KernelShape::open(wire.size()),
                concat({server_app.key,server_app.iv,public_bits(sequence_bytes(sequence)),public_bits(wire)}));
            // Keep both ORIGINAL shared inputs until the DEFER decision.
            auto input=concat({parser_state,opened});
            auto result=eval_shape(KernelShape::route(capacity),input);
            auto event=release(bytes(result,0,2));
            if(event==Bytes({5,0})) {
                result=eval_shape(KernelShape::post_handshake(capacity),std::move(input));
                event=release(bytes(result,0,2));
            }
            require(event.size()==2 && event[0]>=1 && event[0]<=4 &&
                (event[0]==3?event[1]<=1:event[1]==0),"application authentication/control rejected");
            parser_state=bytes(result,2,11);
            application_policy.event(event[0],event[1]==1);
            if(event[0]==1) {
                auto id=retain({bytes(result,15,capacity),bytes(result,13,2),public_bits({255}),capacity,false,Origin::authenticated_receive});
                auto encoded=sequence_bytes(id);event.insert(event.end(),encoded.begin(),encoded.end());
            }
            return event; // No plaintext, length, state or ticket is opened.
        });
    }
    void before_send(const Bytes& wire) {
        guarded([&] { if(policy.phase()==SessionPolicy::Phase::application && application_ready) {
            require_application();
            require(pending_send && pending_wire==wire,"send does not match reserved ciphertext");
        }});
    }
    void after_send() {
        guarded([&] { if(policy.phase()==SessionPolicy::Phase::application && application_ready) {
            require_application();
            application_policy.sent();pending_wire.clear();pending_send=false;
        }});
    }
    void rotate_send() {
        guarded([&] { require_application();application_policy.rotated_send();
            auto next=traffic(eval("tls-update-traffic",client_app.secret,32));
            client_app=std::move(next);lifecycle->renew_epoch(); });
    }
    void rotate_receive() {
        guarded([&] { require_application();application_policy.rotated_receive();
            auto next=traffic(eval("tls-update-traffic",server_app.secret,32));
            server_app=std::move(next);lifecycle->renew_epoch(); });
    }
    bool abort() noexcept {
        if(websocket){websocket->close();websocket.reset();}
        if(websocket_mux){websocket_mux->close();websocket_mux.reset();}
        policy.abort();application_policy.abort();application_ready=false;
        worker.erase_owned_scalar();
        for(auto* traffic:{&client_hs,&server_hs,&client_app,&server_app}) {
            traffic->secret.clear();traffic->key.clear();traffic->iv.clear();
        }
        main_secret.clear();parser_state.clear();request_ids.close();buffers.clear();
        pending_wire.clear();pending_send=false;
        return lifecycle && lifecycle->abort_epoch();
    }
    // A missing/failed lifecycle capability never acknowledges runtime erasure.
};
}
