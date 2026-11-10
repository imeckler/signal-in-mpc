import TlsMpc.TlsKdf
import TlsMpc.TlsRecord
import TlsMpc.TlsPublicHandshake
import TlsMpc.TlsHandshake
import TlsMpc.TlsKdfPrepared
import TlsMpc.TlsPostHandshake
import TlsMpc.Signal.DhRatchet

/-!
Key-derivation circuits that take the X25519 result exactly as it leaves the
field conversion: one 255-bit word, bit `i` weighing `2^i`.

The word is zero-extended to 256 bits and split into 32 little-endian bytes
inside the circuit, so the runtime hands over the conversion's wires in order
and does no bit or byte rearrangement of its own. Variable 0 is the word;
variables 1..32 are the other 32-byte input.
-/
namespace TlsMpc.HybridKdf
open Std.Tactic.BVDecide

/-- The 32 little-endian bytes of a 255-bit word (top bit of the last byte zero). -/
def wordBytes (w : BVExpr 255) : List (BVExpr 8) :=
  let wide : BVExpr 256 := .append (.const (0 : BitVec 1)) w (by rfl)
  (List.range 32).map (fun i => .extract (8 * i) 8 wide)

theorem wordBytes_length (w : BVExpr 255) : (wordBytes w).length = 32 := by simp [wordBytes]

/-- Byte `i` is `(w / 256^i) mod 256`: the RFC 7748 little-endian encoding. -/
theorem wordBytes_toNat (w : BVExpr 255) (assign : BVExpr.Assignment) (i : Nat) (hi : i < 32) :
    (((wordBytes w)[i]'(by rw [wordBytes_length]; exact hi)).eval assign).toNat =
      (w.eval assign).toNat / 256 ^ i % 256 := by
  have hw : ∀ v : BitVec 255, ((0#1) ++ v).toNat = v.toNat := by
    intro v
    rw [BitVec.toNat_append]
    simp
  simp only [wordBytes, List.getElem_map, List.getElem_range]
  show (BitVec.extractLsb' (8 * i) 8 ((0#1) ++ w.eval assign)).toNat = _
  rw [BitVec.extractLsb'_toNat, hw, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- TLS 1.3 handshake secrets from the DH word and a 32-byte transcript hash. -/
def tlsHandshakeSecrets : List (BVExpr 8) :=
  let secrets := TlsKdf.handshakeSecretsFast Sha256.symbolic (wordBytes (.var 0)) (ByteCircuit.inputBytes 1 32)
  secrets.handshake ++ secrets.client ++ secrets.server ++ secrets.main

/-- Signal `RootKey::create_chain` from a 32-byte root key and the DH word. -/
def signalDhRatchet : List (BVExpr 8) :=
  Signal.DhRatchet.createCore Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 1 32) (wordBytes (.var 0))

/-! ### TLS 1.3 client handshake kernels

One circuit per worker operation, so the runtime keeps named private outputs
and passes them back in order. Layout of a traffic block: secret32, key16, iv12. -/

def trafficBlock (secret : List (BVExpr 8)) : List (BVExpr 8) :=
  let keys := TlsKdf.trafficKeysFast Sha256.symbolic secret
  secret ++ keys.1 ++ keys.2

/-- Inputs: DH word (variable 0), hello transcript hash (32 bytes).
Outputs: client handshake traffic block (60), server handshake traffic block
(60), main secret (32). -/
def tlsDerive : List (BVExpr 8) :=
  let secrets := TlsKdf.handshakeSecretsFast Sha256.symbolic (wordBytes (.var 0)) (ByteCircuit.inputBytes 1 32)
  trafficBlock secrets.client ++ trafficBlock secrets.server ++ secrets.main

/-- Inputs: server handshake key16, iv12, sequence8, complete record.
Output: acceptance, type, length2, content; only authenticated handshake or
alert content is released, application data is zeroed inside the circuit. -/
def tlsOpenHandshake (size : Nat) : List (BVExpr 8) :=
  TlsPublicHandshake.openCore Gcm.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 16)
    (ByteCircuit.inputBytes 16 12) (ByteCircuit.inputBytes 28 8) (ByteCircuit.inputBytes 36 size)

/-- Inputs: server handshake traffic secret32, transcript hash32, received
Finished message (36). Output: one acceptance byte. -/
def tlsVerifyFinished : List (BVExpr 8) :=
  [TlsHandshake.verifyHash Sha256.symbolic ByteAuth.symbolic (ByteCircuit.inputBytes 0 32)
    (ByteCircuit.inputBytes 32 32) (ByteCircuit.inputBytes 64 36)]

/-- Inputs: main secret32, server-Finished transcript hash32, client handshake
traffic block (secret32, key16, iv12), client-Finished transcript hash32, then
`certificateSize` public bytes of an (empty) client Certificate message.
Outputs: client application traffic block (60), server application traffic
block (60), then the sealed client Finished record. -/
def tlsFinish (certificateSize : Nat) : List (BVExpr 8) :=
  let main := ByteCircuit.inputBytes 0 32
  let serverHash := ByteCircuit.inputBytes 32 32
  let clientSecret := ByteCircuit.inputBytes 64 32
  let clientKey := ByteCircuit.inputBytes 96 16
  let clientIv := ByteCircuit.inputBytes 112 12
  let clientHash := ByteCircuit.inputBytes 124 32
  let certificate := ByteCircuit.inputBytes 156 certificateSize
  let application := TlsKdf.applicationSecretsFast Sha256.symbolic main serverHash
  let verifyData := TlsKdf.finished Sha256.symbolic clientSecret clientHash
  let header : List (BVExpr 8) := [20, 0, 0, 32].map (fun n => .const (BitVec.ofNat 8 n))
  let zeroSequence : List (BVExpr 8) := List.replicate 8 (.const 0)
  let wire := TlsRecord.sealCore Gcm.symbolic clientKey clientIv zeroSequence
    (certificate ++ header ++ verifyData) 22 0
  trafficBlock application.1 ++ trafficBlock application.2 ++ wire

/-! ### Application-phase kernels -/

/-- KeyUpdate. Input: a traffic secret (32). Output: the next traffic block
(secret32, key16, iv12). -/
def tlsUpdateTraffic : List (BVExpr 8) :=
  trafficBlock (TlsKdf.expandLabelFast Sha256.symbolic (ByteCircuit.inputBytes 0 32) "traffic upd" [] 32)

theorem tlsUpdateTraffic_secret :
    TlsKdf.expandLabelFast Sha256.symbolic (ByteCircuit.inputBytes 0 32) "traffic upd" [] 32 =
      TlsKdf.updateTraffic Sha256.symbolic (ByteCircuit.inputBytes 0 32) :=
  TlsKdf.expandLabelFast_correct _ _ _ _ _

/-- Application receive. Inputs: post-handshake parser state (11), server
application key16, iv12, sequence8, complete record. Output: event byte and
request byte (the only two bytes that may be opened), next parser state (11),
then private length2 and content buffer (released only for application data). -/
def tlsOpenApplication (size : Nat) : List (BVExpr 8) :=
  TlsPostHandshake.openCore Gcm.symbolic Signal.Word64.symbolic ByteAuth.symbolic
    (ByteCircuit.inputBytes 0 11) (ByteCircuit.inputBytes 11 16) (ByteCircuit.inputBytes 27 12)
    (ByteCircuit.inputBytes 39 8) (ByteCircuit.inputBytes 47 size)

/-- Seal one record of the given inner content type. Inputs: key16, iv12,
sequence8, content. Output: the complete TLSCiphertext record. -/
def tlsSeal (size kind padding : Nat) : List (BVExpr 8) :=
  TlsRecord.sealCore Gcm.symbolic (ByteCircuit.inputBytes 0 16) (ByteCircuit.inputBytes 16 12)
    (ByteCircuit.inputBytes 28 8) (ByteCircuit.inputBytes 36 size) kind padding

#print axioms wordBytes_toNat

end TlsMpc.HybridKdf
