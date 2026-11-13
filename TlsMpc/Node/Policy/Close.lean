import TlsMpc.Node.Policy.Receive

/-!
# The client's WebSocket Close (libsignal profile; CLIENT_FINGERPRINT.md (b), ranking row 10)

When libsignal-net lets a chat connection go, it sends one Close frame with status code 1000
(normal closure) and an empty reason, and finishes: it does not wait for the server's Close
(libsignal v0.106.1, `rust/net/infra/src/ws/connection.rs` lines 328-346, `Event::ClientDisconnect`:
`Message::Close(Some(CloseFrame { code: CloseCode::Normal, reason: Default::default() }))`, then
`Outcome::Finished(Ok(FinishReason::LocalDisconnect))`; its test `sends_outgoing_messages`, lines
669-678, reads exactly that frame and then the end of the stream). `close` is that frame as a client sends it (FIN, opcode 8,
masked, 2-byte payload); `Session/Common.lean` (`closeWebSocket`) sends it at the orderly end of a
session under the libsignal profile.

A public control frame built here in the clear, like `ping` (`Policy/Receive.lean`); it is sealed
through the path that seals public buffers (`Flow.Tls.publicBuffer`, size class 32), not a request
kernel. Proved: `CloseProofs.lean` (`close_reference`, `close_decode`). No emitter imports this
module.
-/

open TlsMpc

namespace PublicReceive

/-- The Close payload libsignal sends: status code 1000 (RFC 6455 section 7.4.1, normal closure),
big-endian, and no reason. -/
def normalClosure : List Byte := [0x03, 0xe8]

/-- A masked WebSocket Close (FIN, opcode 8) with status code 1000 and an empty reason, masked with
`mask` (4 bytes of joint randomness, a fresh one per frame). -/
def close (mask : List Byte) : List Byte :=
  [0x88, 0x82] ++ mask ++ [0x03 ^^^ get mask 0, 0xe8 ^^^ get mask 1]

end PublicReceive
