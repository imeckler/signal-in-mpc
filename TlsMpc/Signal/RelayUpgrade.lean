import TlsMpc.Signal.RelayEncoding

/-! Secret Basic credentials in the actual HTTP/1.1 WebSocket upgrade route.
The WebSocket key is a public fresh nonce represented as input bytes. Server
HTTP101/Upgrade/Connection/Sec-WebSocket-Accept validation is not supplied here. -/
namespace TlsMpc.Signal.RelayUpgrade
open Std.Tactic.BVDecide RelayEncoding

/-- The `User-Agent` of the model client (handshake_backend/EmpHybridWork/CLIENT_FINGERPRINT.md):
Signal-Android passes `"Signal-Android/" + versionName + " Android/" + SDK_INT` to libsignal's
`Network`, which appends `" libsignal/" + version` (Signal-Android b8544a8,
StandardUserAgentInterceptor.java; libsignal rust/net/src/env.rs `UserAgent`). A deployment
constant: it must follow the current Android release (8.36.0 with libsignal 0.107.0 at
Signal-Android b8544a8), or the version itself becomes the fingerprint. -/
def userAgent : String := "Signal-Android/8.36.0 Android/35 libsignal/0.107.0"

/-- The request head as libsignal-net writes it over HTTP/1.1 (`connect_http1` in
rust/net/infra/src/ws.rs builds the request; tungstenite 0.29 `generate_request` writes
`Host`, `Connection`, `Upgrade`, `Sec-WebSocket-Version`, `Sec-WebSocket-Key` first, in that
case, then libsignal's own headers in insertion order with their lowercase names). -/
def head : String :=
  "GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nConnection: Upgrade\r\nUpgrade: websocket\r\nSec-WebSocket-Version: 13\r\nSec-WebSocket-Key: "

/-- The authenticated socket. libsignal's headers (`AuthenticatedChatHeaders`): `authorization`
with the username `"{aci}.{deviceId}"` (this account is the primary device, 1),
`x-signal-receive-stories`, no `accept-language` (Signal-Android passes no languages), then
`user-agent`. -/
def request (a : ByteAuth.Ops B) (passwordBytes : Nat) (raw : List B) : List B :=
  literal a head ++
  base64 a ((raw.drop (16+passwordBytes)).take 16) ++
  literal a "\r\nauthorization: Basic " ++
  base64 a (uuid a (raw.take 16) ++ literal a ".1:" ++ (raw.drop 16).take passwordBytes) ++
  literal a ("\r\nx-signal-receive-stories: false\r\nuser-agent: " ++ userAgent ++ "\r\n\r\n")

/-- The upgrade request for an UNAUTHENTICATED chat socket: libsignal's request with
no headers of its own but the user agent. It contains no secret; the only input is the
public WebSocket nonce. Sealed-sender sends go on this socket, because on an
authenticated socket the server treats every send as identified. -/
def anonymousRequest (a : ByteAuth.Ops B) (nonce : List B) : List B :=
  literal a head ++
  base64 a (nonce.take 16) ++
  literal a ("\r\nuser-agent: " ++ userAgent ++ "\r\n\r\n")

/-- The original requests (`SIGNAL_CLIENT_PROFILE=legacy`). -/
def legacyAnonymousRequest (a : ByteAuth.Ops B) (nonce : List B) : List B :=
  literal a "GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: " ++
  base64 a (nonce.take 16) ++
  literal a "\r\nSec-WebSocket-Version: 13\r\nX-Signal-Receive-Stories: false\r\nAccept-Language: en\r\nUser-Agent: tls-mpc\r\n\r\n"

theorem request_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
    (ha : ByteAuth.Hom a a' f) (passwordBytes : Nat) (raw : List B) :
    (request a passwordBytes raw).map f = request a' passwordBytes (raw.map f) := by
  simp only [request,List.map_append,literal_map ha,base64_map ha,uuid_map ha,List.map_take,List.map_drop]

theorem compiled_request_correct (passwordBytes : Nat) (raw : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat) (hi : index<8*(request ByteAuth.symbolic passwordBytes raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (request ByteAuth.symbolic passwordBytes raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (request ByteAuth.symbolic passwordBytes raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (request ByteAuth.concrete passwordBytes (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,request_map (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.RelayUpgrade
