import TlsMpc.Signal.PrivateBootstrapKeysV1
import TlsMpc.Signal.PrivateInitialSpqrV1
import TlsMpc.Signal.PrivatePreKeyMessageV1

/-! Bounded genuine initial PreKey sends with full retained state. This composes
internally computed bootstrap keys, ML-KEM768 generation and validated text.
The native orchestrator must bind the real private bundle/trust/signature/DH/KEM
stages. It never accepts caller-supplied agreements or verification assertions.
Only the first two initial KeysSampled sends are implemented here; continuation
must route the returned phase into later legitimate SPQR entries, not reset it. -/
namespace TlsMpc.Signal.PrivateBootstrapSendV1
open Std.Tactic.BVDecide

def part (raw : List B) (offset size : Nat) : List B := (raw.drop offset).take size

def senderAfter (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (old chain : List B) : List B :=
 old.take 96 ++ chain ++ ChainSend.nextCounter s a (part old 128 4) ++ part old 132 4

def inner (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
 (sender own peer addresses plaintext pqWire pqKey : List B) : PrivateBuffer.Buffer B × List B :=
 let derived := Symmetric.deriveFast s (part sender 96 32) pqKey
 let pq := PrivateBuffer.fromPublic a 37 pqWire
 let message := PrivateSignalMessage.message o s a true true (a.const 4)
  (part sender 128 4) (part sender 132 4) (part sender 64 32)
  derived.material.cipherKey derived.material.iv derived.material.macKey own peer plaintext addresses pq
 (PrivateBuffer.resize a 256 message,senderAfter s a sender derived.nextChainKey)

-- Retained initial-send state6039 (not a whole SessionRecord): ownIK32||peerIK32||base32||taggedKyberCT1569||
-- localRegistration/oneTime/signed/PQ IDs16||addresses36||sender136||
-- receivers345||full initial-SPQR typed state3841.
def first (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
 (keys generated own peer metadata addresses plaintext ciphertext : List B) (textValid : B) : List B :=
 let shape := if keys.length=546 ∧ generated.length=3585 ∧ own.length=32 ∧ peer.length=32 ∧
  metadata.length=16 ∧ addresses.length=36 ∧ plaintext.length=80 ∧ ciphertext.length=1569
  then a.const 255 else a.const 0
 let pq := PrivateInitialSpqrV1.start s a (part keys 514 32) generated
 let status := a.and shape (a.and (OpenResult.get a keys 0)
  (a.and (OpenResult.get a pq 0) (ByteAuth.eqMask a textValid (a.const 255))))
 let output := inner o s a (part keys 33 136) own peer addresses plaintext (part pq 3842 37) (part pq 3879 32)
 let wire := PrivatePreKeyMessageV1.message s a status
  (metadata.take 4) (part metadata 4 4) (part metadata 8 4) (part metadata 12 4)
  (part keys 1 32) own ciphertext output.1
 let state := own ++ peer ++ part keys 1 32 ++ ciphertext ++ metadata ++ addresses ++
  output.2 ++ part keys 169 345 ++ part pq 1 3841
 wire.valid :: (ByteAuth.release a wire.valid state ++ PrivateBuffer.output a wire)

/-- Input exact previous valid||initial-send-state6040, then a new validated text. No
new KEM/base/ratchet keys are sampled. Rejection retains the full old state. -/
def second (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
 (old plaintext : List B) (textValid : B) : List B :=
 let state := old.drop 1
 let pq := PrivateInitialSpqrV1.second s a (OpenResult.get a old 0 :: part state 2198 3841)
 let shape := if old.length=6040 ∧ plaintext.length=80 then a.const 255 else a.const 0
 let status := a.and shape (a.and (OpenResult.get a old 0)
  (a.and (OpenResult.get a pq 0) (ByteAuth.eqMask a textValid (a.const 255))))
 let own := state.take 32
 let peer := part state 32 32
 let metadata := part state 1665 16
 let output := inner o s a (part state 1717 136) own peer (part state 1681 36) plaintext
  (part pq 3842 37) (part pq 3879 32)
 let wire := PrivatePreKeyMessageV1.message s a status
  (metadata.take 4) (part metadata 4 4) (part metadata 8 4) (part metadata 12 4)
  (part state 64 32) own (part state 96 1569) output.1
 let candidate := state.take 1717 ++ output.2 ++ part state 1853 345 ++ part pq 1 3841
 wire.valid :: (ChainSend.selectState a wire.valid candidate state ++ PrivateBuffer.output a wire)
end TlsMpc.Signal.PrivateBootstrapSendV1
