#pragma once
#include "NativeSession.h"
#include "NativeCollective.h"
#include "TcpRecords.h"
#include "ShapeCompiler.h"
namespace tls_mpc_worker {
class Dispatch {
    Session& session;
    Collective& collective;
    bool failed=false;
    TcpRecords transport;
    ShapeCompiler* shapes;
public:
    Dispatch(Session& session, Collective& collective, ShapeCompiler* shapes=nullptr) : session(session), collective(collective),shapes(shapes) {}
    bool fail_from_private_producer() noexcept {failed=true;transport.close();return session.abort();}
    template<class Extension> Bytes private_extension(const Request& request,Extension&& extension) {
        try {public_require(!failed,"worker already aborted");collective.agree(request);return extension();}
        catch(...) {failed=true;transport.close();session.abort();throw;}
    }
    Bytes call(const Request& request) {
        try {
            // A completed terminal cleanup can be acknowledged again without
            // touching the already-discarded MPC transport. No other operation
            // can run or disclose output after the terminal transition.
            if(failed && request.operation==Opcode::abort) {
                Cursor terminal{request.payload};terminal.done();
                public_require(session.abort(),"terminal cleanup unavailable");return {};
            }
            public_require(!failed,"worker already aborted");
            collective.agree(request); // BEFORE private work or output.
            Cursor in{request.payload};
            switch(request.operation) {
            case Opcode::begin: {
                in.done(); auto key=session.begin(); auto random=collective.public_random();
                key.insert(key.end(),random.begin(),random.end()); return key;
            }
            case Opcode::derive: {
                auto peer=in.take(32), hash=in.take(32); in.done(); session.derive(peer,hash); return {};
            }
            case Opcode::open: {
                auto sequence=in.number(8); auto wire=in.take(request.payload.size()-8); in.done();
                if(shapes)shapes->prepare(wire.size());
                return session.open_handshake(sequence,wire);
            }
            case Opcode::authenticate: {
                public_require(authentication_decision(request.payload),"public server authentication rejected");
                session.certificate_authenticated(); return {};
            }
            case Opcode::verify: {
                auto hash=in.take(32), message=in.take(36); in.done();
                return {uint8_t(session.verify_finished(hash,message)?255:0)};
            }
            case Opcode::finish: {
                auto server=in.take(32), client=in.take(32); auto cert=in.take(request.payload.size()-64); in.done();
                return session.finish(server,client,cert);
            }
            case Opcode::connect: {
                auto host=in.take(in.number(2));auto port=in.number(2);in.done();
                return collective.leader([&] {transport.connect(std::string(host.begin(),host.end()),port);return Bytes{};});
            }
            case Opcode::send: {
                session.before_send(request.payload);
                auto result=collective.leader([&] {transport.send(request.payload);return Bytes{};});
                session.after_send();return result;
            }
            case Opcode::receive:
                in.done();return collective.leader([&] {return transport.receive();});
            case Opcode::poll_receive:
                in.done();return collective.leader([&] {return transport.poll_receive();});
            case Opcode::retire:
                in.done(); session.retire();return {};
            case Opcode::open_application: {
                auto seq=in.number(8);auto wire=in.take(request.payload.size()-8);in.done();
                return session.open_application(seq,wire);
            }
            case Opcode::seal_application: {
                auto seq=in.number(8),handle=in.number(8),size=in.number(2),padding=in.number(2);in.done();
                return session.seal_application(seq,handle,size,padding);
            }
            case Opcode::seal_control: {
                auto seq=in.number(8);auto kind=in.number(1);auto content=in.take(request.payload.size()-9);in.done();
                return session.seal_control(seq,kind,content);
            }
            case Opcode::rotate_send: in.done();session.rotate_send();return {};
            case Opcode::rotate_receive: in.done();session.rotate_receive();return {};
            case Opcode::process_websocket: {
                auto handle=in.number(8);in.done();auto receipt=session.process_websocket(handle);
                Bytes out{uint8_t(receipt.upgraded),uint8_t(receipt.response_complete),uint8_t(receipt.controls.size())};
                for(const auto& control:receipt.controls) {
                    out.push_back(control.first);put_number(out,control.second,8);put_number(out,131,2);
                }
                return out;
            }
            case Opcode::provider_catalogue:
            case Opcode::provider_upgrade:
            case Opcode::provider_produce:
                throw std::runtime_error("private provider launch profile unavailable");
            case Opcode::abort:
                in.done(); {bool erased=session.abort();failed=true;transport.close();
                    public_require(erased,"native VM erasure capability failed or unavailable");return {};}
            }
            throw std::runtime_error("unknown worker operation");
        } catch(...) { failed=true; transport.close(); session.abort(); throw; }
    }
};
}
