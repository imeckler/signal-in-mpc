import TlsMpc.Node.Policy.Close
import TlsMpc.Node.Policy.RequestProofs

/-!
# The client's Close frame is RFC 6455's Close with status code 1000 (beside T8)

New file (2026-11-12). It changes no definition; no emitter imports it. About `PublicReceive.close`
(`Policy/Close.lean`), the frame the libsignal profile sends at the orderly end of a session
(`Session/Common.lean`, `closeWebSocket`), against the RFC 6455 references of `RequestSpec.lean`
(`clientFrame`, `decodeFrame`), as `RequestProofs.lean` does for `ping` and `keepalive`.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):
* `close_reference`: `close mask` is the masked client frame (FIN, opcode 8, minimal length) whose
  payload is a Close body (section 5.5.1: the status code, two bytes in network order, then the
  reason) with code 1000 and an empty reason; `normalClosure_eq`: that body is libsignal's
  `normalClosure` (`03 e8`), `closeBody_code`: its code reads back as 1000.
* `close_decode`: RFC 6455's reading of the frame (`decodeFrame`) is one FIN Close frame, masked
  with the key, with a minimal length, carrying exactly that body.

NOT PROVED: that the C++/Rust worker seals the public buffer unchanged (the same trusted hypothesis
as every public frame: `RequestProofs.lean`, header).
-/

namespace TlsMpc.Node.CloseProofs
open TlsMpc TlsMpc.Node.RequestSpec
open TlsMpc.Node.RequestProofs (sentFrame decode_clientFrame)

/-- RFC 6455 section 5.2: opcode 8, a connection Close. -/
def closeOpcode : Nat := 8

/-- RFC 6455 section 5.5.1: a Close body is a 2-byte unsigned status code in network byte order,
then the UTF-8 reason. -/
def closeBody (code : Nat) (reason : List (BitVec 8)) : List (BitVec 8) :=
  [BitVec.ofNat 8 (code / 256), BitVec.ofNat 8 (code % 256)] ++ reason

/-- The body libsignal's Close carries (code 1000, no reason) is `PublicReceive.normalClosure`. -/
theorem normalClosure_eq : PublicReceive.normalClosure = closeBody 1000 [] := rfl

/-- The status code of the body reads back as 1000 (big-endian, its first two bytes). -/
theorem closeBody_code : bigEndian ((closeBody 1000 []).take 2) = 1000 := by decide

/-- **`close`** is RFC 6455's masked client Close frame (FIN, opcode 8) with status code 1000 and an
empty reason. -/
theorem close_reference (mask : List (BitVec 8)) :
    PublicReceive.close mask = clientFrame closeOpcode mask (closeBody 1000 []) := rfl

/-- **The Close frame, read by RFC 6455**: FIN, opcode 8, masked with the key, minimal length,
payload the status code 1000 and nothing else. -/
theorem close_decode (mask : List (BitVec 8)) (hmask : mask.length = 4) :
    decodeFrame (PublicReceive.close mask) = some (sentFrame closeOpcode mask (closeBody 1000 [])) := by
  rw [close_reference]
  exact decode_clientFrame closeOpcode mask _ (by decide) hmask (by decide)

#print axioms normalClosure_eq
#print axioms closeBody_code
#print axioms close_reference
#print axioms close_decode

end TlsMpc.Node.CloseProofs
