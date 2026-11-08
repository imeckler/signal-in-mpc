import TlsMpc.Signal.PrivateProtoParseV1
import TlsMpc.Signal.PrivateMessageMac
import TlsMpc.Signal.ActiveSpqrReceive
import TlsMpc.Signal.RatchetStep
import TlsMpc.Signal.ReceiverStore
import TlsMpc.Signal.CbcOpen
import TlsMpc.Signal.SliceAt

/-! Bounded new-DH/active-PQ receiving transaction, text bucket80. All acceptance
conditions are computed from the actual original private wire, derived keys and
retained state. No supplied authentication/PQ-key flags. Native composition must
compute the fresh pair and both DH agreements using the SAME parsed remote key;
that mixed field conversion boundary remains separate. The private parser's
source/semantic proof is being completed in its separately owned versioned module.
No artifact/implementation agreement is claimed merely from this draft model. -/
namespace TlsMpc.Signal.PrivateNewDhReceive
open Std.Tactic.BVDecide

def conjunction (a : ByteAuth.Ops B) : List B → B
  | [] => a.const 255
  | x::xs => a.and x (conjunction a xs)

def pqWire (o : Word64.Ops B V) (a : ByteAuth.Ops B)
    (wire : List B) (parsed : PrivateProtoParseV1.Parsed B V) : List B :=
  let field := ProtoParse.getField o a parsed.state 4
  let valid := a.and parsed.valid (a.and field.present (o.ule field.length (o.const 32)))
  valid :: ((Word64.bytes o field.length).drop 6 ++
    SliceAt.readCore o a 32 (wire.drop 1) field.offset field.length)

def listBytes (a : ByteAuth.Ops B) (raw : List B) : SkippedKeys.Bytes B n :=
  fun i => OpenResult.get a raw i.val

def nextEntry (a : ByteAuth.Ops B) (remote chain : List B) : ReceiverStore.Entry B 0 :=
  ⟨a.const 255,listBytes a remote,listBytes a chain,
    listBytes a [a.const 0,a.const 0,a.const 0,a.const 1],fun i => Fin.elim0 i⟩

def selectResult (a : ByteAuth.Ops B) (accepted : B) (old : RatchetStep.State B)
    (receivers : List (ReceiverStore.Entry B 0)) (oldPq : List B) (next : RatchetStep.State B)
    (remote nextReceiverChain pqCandidate plaintext : List B) : List B :=
  let retained := ReceiverStore.insert a accepted (nextEntry a remote nextReceiverChain) receivers
  accepted :: (ChainSend.selectState a accepted next.bytes old.bytes ++ ReceiverStore.bytes retained ++
    ChainSend.selectState a accepted (pqCandidate.take 44) oldPq ++
    ByteAuth.release a accepted ([a.const 0,a.const 80] ++ plaintext.take 80))

/-- A rejected authenticated transaction preserves root/private/sender bytes,
every retained receiving slot and the receiving PQ epoch/key/counter. -/
theorem selectResult_reject (old : RatchetStep.State (BitVec 8))
    (receivers : List (ReceiverStore.Entry (BitVec 8) 0)) (oldPq : List (BitVec 8))
    (next : RatchetStep.State (BitVec 8)) (remote nextReceiverChain pqCandidate plaintext : List (BitVec 8)) :
    selectResult ByteAuth.concrete 0 old receivers oldPq next remote nextReceiverChain pqCandidate plaintext=
      0 :: (old.bytes ++ ReceiverStore.bytes receivers ++ oldPq ++
        List.replicate (2+(plaintext.take 80).length) 0) := by
  unfold selectResult
  rw [ChainSend.selectState_reject,ReceiverStore.insert_reject 0 _ receivers (by decide),
    ChainSend.selectState_reject,ByteAuth.release_reject]
  simp only [List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_zero]

/-- Output status || sender/root136 || retained receivers(69*count) ||
selected receivePQ44 || private plaintextBE16+bucket80. Root/private/PQ bytes
are never opened. Rejection selects all old state and zero application output.
First profile: five retained slots, unknown ratchet, Signal counter0, V4, no addresses, ciphertext96,
valid PKCS7 yielding80 bytes, active-epoch/in-order kind0 receiving PQ message. -/
def receive (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (old : RatchetStep.State B)
    (receivers : List (ReceiverStore.Entry B 0)) (oldPq sender receiver : List B)
    (newPrivate newPublic receiveAgreement sendAgreement encodedWire : List B) : List B :=
  let wire := encodedWire.drop 3
  let parsed := PrivateProtoParseV1.parse d o a wire (OpenResult.get a encodedWire 1)
    (OpenResult.get a encodedWire 2) (OpenResult.get a encodedWire 0)
  let remote := parsed.metadata.take 32
  let pq := ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
    ((oldPq.drop 40).take 4) (pqWire o a wire parsed)
  let derived := RatchetStep.derive s old.root receiveAgreement sendAgreement
  let material := Symmetric.deriveFast s derived.2.1 (pq.drop 45)
  let field := ProtoParse.getField o a parsed.state 3
  let ciphertext := SliceAt.readCore o a 96 (wire.drop 1) field.offset field.length
  let opened := CbcOpen.openCore aes a material.material.cipherKey material.material.iv ciphertext
  let known := ReceiverStore.lookup a (listBytes a remote) receivers
  let shape := if receivers.length=5 ∧ oldPq.length=44 ∧ encodedWire.length=259 ∧
      old.root.length=32 ∧ old.privateKey.length=32 ∧ old.publicKey.length=32 ∧ old.chain.length=32 ∧
      old.index.length=4 ∧ old.previous.length=4 ∧ sender.length=32 ∧ receiver.length=32 ∧
      newPrivate.length=32 ∧ newPublic.length=32 ∧ receiveAgreement.length=32 ∧ sendAgreement.length=32
    then a.const 255 else a.const 0
  let accepted := conjunction a [shape,parsed.valid,OpenResult.get a pq 0,
    PrivateMessageMac.verify o s a wire.length material.material.macKey sender receiver encodedWire,
    OpenResult.get a opened 0,
    Word64.eq o a (o.band (ProtoParse.getField o a parsed.state 1).scalar (o.const 4294967295)) (o.const 0),
    Word64.eq o a field.length (o.const 96),
    a.not (ProtoParse.getField o a parsed.state 5).present,
    ByteAuth.equalMask a ((opened.drop 1).take 8) (OpenResult.encodeLength a 80),
    a.not (ByteAuth.eqMask a known.valid (a.const 255)),
    ByteAuth.eqMask a (OpenResult.get a wire 0) (a.const 68),
    DhRatchet.agreementMask a receiveAgreement,DhRatchet.agreementMask a sendAgreement]
  let next : RatchetStep.State B := ⟨derived.1,newPrivate,newPublic,derived.2.2,
    List.replicate 4 (a.const 0),RatchetStep.previousCounter s a old.index⟩
  selectResult a accepted old receivers oldPq next remote material.nextChainKey (pq.drop 1) (opened.drop 9)

end TlsMpc.Signal.PrivateNewDhReceive
