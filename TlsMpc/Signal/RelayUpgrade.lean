import TlsMpc.Signal.RelayEncoding

/-! Secret Basic credentials in the actual HTTP/1.1 WebSocket upgrade route.
The WebSocket key is a public fresh nonce represented as input bytes. Server
HTTP101/Upgrade/Connection/Sec-WebSocket-Accept validation is not supplied here. -/
namespace TlsMpc.Signal.RelayUpgrade
open Std.Tactic.BVDecide RelayEncoding

def request (a : ByteAuth.Ops B) (passwordBytes : Nat) (raw : List B) : List B :=
  literal a "GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: " ++
  base64 a ((raw.drop (16+passwordBytes)).take 16) ++
  literal a "\r\nSec-WebSocket-Version: 13\r\nAuthorization: Basic " ++
  base64 a (uuid a (raw.take 16) ++ literal a ":" ++ (raw.drop 16).take passwordBytes) ++
  literal a "\r\nX-Signal-Receive-Stories: false\r\nAccept-Language: en\r\nUser-Agent: tls-mpc\r\n\r\n"

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
