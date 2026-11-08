import TlsMpc.Signal.PrivateNewDhReceiveSplit

/-! Selected active-PQ in-order receive, with one symmetric/MAC/CBC computation.
Known ratchet: retain own root/private/sending state, update first matching receiver.
New ratchet: counter0 only, insert new receiver and select computed DH state.
No skipped-key retention, KEM epoch evolution, bootstrap or durable store claim. -/
namespace TlsMpc.Signal.PrivateSessionReceiveV1
open PrivateNewDhReceive PrivateNewDhReceiveSplit

-- Pinned PublicKey::ct_eq compares key type and raw key_data bytes. X25519
-- agreement normalization is separate and must NOT alter ratchet identity lookup.
def pointMatch (a : ByteAuth.Ops B) (remote : List B) (e : ReceiverStore.Entry B 0) : B :=
 ReceiverStore.matchMask a (listBytes a remote) e
def lookup (a : ByteAuth.Ops B) (remote : List B) (old : List (ReceiverStore.Entry B 0)) : ReceiverStore.Entry B 0 :=
 ReceiverStore.lookup a (listBytes a remote) old
def replace (a : ByteAuth.Ops B) (allow : B) (remote : List B) (next : ReceiverStore.Entry B 0)
    (old : List (ReceiverStore.Entry B 0)) : List (ReceiverStore.Entry B 0) :=
 ReceiverStore.replaceFirst a allow (listBytes a remote) next old

def finish (a : ByteAuth.Ops B) (accepted known : B) (old next : RatchetStep.State B)
    (receivers : List (ReceiverStore.Entry B 0)) (oldPq remote chain counter pq plain : List B)
    (selected : ReceiverStore.Entry B 0) : List B :=
 let newEntry := PrivateNewDhReceive.nextEntry a remote chain
 let knownEntry : ReceiverStore.Entry B 0 := ⟨a.const 255,selected.ratchet,listBytes a chain,listBytes a counter,fun j => Fin.elim0 j⟩
 let inserted := ReceiverStore.insert a accepted newEntry receivers
 let replaced := replace a accepted remote knownEntry receivers
 let store := List.zipWith (ReceiverStore.choose a known) replaced inserted
 let sender := ChainSend.selectState a known old.bytes next.bytes
 accepted :: (ChainSend.selectState a accepted sender old.bytes ++ ReceiverStore.bytes store ++
   ChainSend.selectState a accepted (pq.take 44) oldPq ++
   ByteAuth.release a accepted ([a.const 0,a.const 80] ++ plain.take 80))

def receiveSummary (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (old : RatchetStep.State B)
    (receivers : List (ReceiverStore.Entry B 0)) (oldPq sender receiver : List B)
    (newPrivate newPublic receiveAgreement sendAgreement encodedWire : List B) (summary : Summary B V) : List B :=
 let wire := encodedWire.drop 3
 let selected := lookup a summary.remote receivers
 let known := ByteAuth.eqMask a selected.valid (a.const 255)
 let counter := (Word64.bytes o (o.band summary.counter (o.const 4294967295))).drop 4
 let pq := ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
   ((oldPq.drop 40).take 4) (pqWireSummary o a wire summary)
 let derived := RatchetStep.derive s old.root receiveAgreement sendAgreement
 let chain := ChainSend.selectState a known (List.ofFn selected.chain) derived.2.1
 let material := Symmetric.deriveFast s chain (pq.drop 45)
 let ciphertext := SliceAt.readCore o a 96 (wire.drop 1) summary.cipherOffset summary.cipherLength
 let opened := CbcOpen.openCore aes a material.material.cipherKey material.material.iv ciphertext
 let inOrder := a.and (ByteAuth.equalMask a counter (List.ofFn selected.counter))
   (ChainSend.counterMask a (List.ofFn selected.counter))
 let fresh := conjunction a [ByteAuth.equalMask a counter (List.replicate 4 (a.const 0)),
   DhRatchet.agreementMask a receiveAgreement,DhRatchet.agreementMask a sendAgreement]
 let path := Unpad.chooseByte a known inOrder fresh
 let shape := if receivers.length=5 ∧ oldPq.length=44 ∧ encodedWire.length=259 ∧
   old.root.length=32 ∧ old.privateKey.length=32 ∧ old.publicKey.length=32 ∧ old.chain.length=32 ∧
   old.index.length=4 ∧ old.previous.length=4 ∧ sender.length=32 ∧ receiver.length=32 ∧
   newPrivate.length=32 ∧ newPublic.length=32 ∧ receiveAgreement.length=32 ∧ sendAgreement.length=32
   then a.const 255 else a.const 0
 let accepted := conjunction a [shape,summary.valid,OpenResult.get a pq 0,path,
   PrivateMessageMac.verify o s a wire.length material.material.macKey sender receiver encodedWire,
   OpenResult.get a opened 0,Word64.eq o a summary.cipherLength (o.const 96),a.not summary.addressPresent,
   ByteAuth.equalMask a ((opened.drop 1).take 8) (OpenResult.encodeLength a 80),
   ByteAuth.eqMask a (OpenResult.get a wire 0) (a.const 68)]
 let next : RatchetStep.State B := ⟨derived.1,newPrivate,newPublic,derived.2.2,
   List.replicate 4 (a.const 0),RatchetStep.previousCounter s a old.index⟩
 finish a accepted known old next receivers oldPq summary.remote material.nextChainKey
   (ChainSend.nextCounter s a counter) (pq.drop 1) (opened.drop 9) selected
end TlsMpc.Signal.PrivateSessionReceiveV1
