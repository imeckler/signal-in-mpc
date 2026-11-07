import TlsMpc.Signal.SpqrChain
import TlsMpc.Signal.SpqrMessage

/-! Send from an already selected active SPQR epoch. The newly incremented
SPQR chain counter is both the HKDF counter and the encoded message index;
the derived SPQR message key feeds Signal key derivation in this circuit.
The caller must supply the chain selected for `message.epoch - 1` and the
payload selected by the SPQR state machine. Epoch selection, KEM/chunk state
transitions and atomic storage commit are not implemented here.

This bounded profile rejects zero epochs, exhausted counters, noncanonical
public widths and invalid typed addresses/kinds. Rejection preserves both old
chain states and zeros the wire. All values and the status remain shared.
Compiler equality is proved against the executable Lean definition; full
equivalence to translated SPQR/Signal/RustCrypto remains separate. -/

namespace TlsMpc.Signal.SpqrSend
open Std.Tactic.BVDecide

structure Input (B : Type) where
  version : B
  counter : List B
  previous : List B
  ratchet : List B
  chainKey : List B
  pqChainKey : List B
  pqCounter : List B
  epoch : List B
  kind : B
  chunkIndex : List B
  chunkData : List B
  sender : List B
  receiver : List B
  plaintext : List B
  addresses : List B

def Input.map (f : B → B') (i : Input B) : Input B' :=
  ⟨f i.version, i.counter.map f, i.previous.map f, i.ratchet.map f,
    i.chainKey.map f, i.pqChainKey.map f, i.pqCounter.map f, i.epoch.map f,
    f i.kind, i.chunkIndex.map f, i.chunkData.map f, i.sender.map f,
    i.receiver.map f, i.plaintext.map f, i.addresses.map f⟩

def epochMask (a : ByteAuth.Ops B) (epoch : List B) : B :=
  a.not (ByteAuth.equalMask a epoch (List.replicate 8 (a.const 0)))

def acceptedMask (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) : B :=
  a.and (ChainSend.acceptedMask s a shape (a.const 1) i.counter i.previous i.addresses)
    (a.and (ChainSend.counterMask a i.pqCounter)
      (a.and (epochMask a i.epoch)
        (SpqrMessage.acceptedMask v s a pqShape (Varint64.pack v a i.epoch)
          (Varint.pack s a (ChainSend.nextCounter s a i.pqCounter)) i.kind i.chunkIndex)))

structure Prepared (B : Type) where
  nextChainKey : List B
  nextCounter : List B
  nextPqChainKey : List B
  nextPqCounter : List B
  wire : List B

def Prepared.map (f : B → B') (p : Prepared B) : Prepared B' :=
  ⟨p.nextChainKey.map f, p.nextCounter.map f, p.nextPqChainKey.map f,
    p.nextPqCounter.map f, p.wire.map f⟩

/-- One SPQR derivation, with the resulting key and counter bound to the same
Signal message. The expanded HMAC states are shared by the optimized KDFs. -/
def prepare (o : Aes.Ops B) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) : Prepared B :=
  let pqOutput := SpqrChain.materialFast s a i.pqChainKey i.pqCounter
  let nextPqCounter := ChainSend.nextCounter s a i.pqCounter
  let pq := SpqrMessage.content v s a pqShape (Varint64.pack v a i.epoch)
    (Varint.pack s a nextPqCounter) i.kind i.chunkIndex i.chunkData
  let derived := Symmetric.deriveFast s i.chainKey (pqOutput.drop 32)
  let wire := Send.message o s a shape i.version i.counter i.previous i.ratchet
    derived.material.cipherKey derived.material.iv derived.material.macKey
    i.sender i.receiver i.plaintext pq i.addresses
  ⟨derived.nextChainKey, ChainSend.nextCounter s a i.counter,
    pqOutput.take 32, nextPqCounter, wire⟩

def sealCore (o : Aes.Ops B) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) : List B :=
  let accepted := acceptedMask v s a shape pqShape i
  let p := prepare o v s a shape pqShape i
  accepted :: (ChainSend.selectState a accepted p.nextChainKey i.chainKey ++
    ChainSend.selectState a accepted p.nextCounter i.counter ++
    ChainSend.selectState a accepted p.nextPqChainKey i.pqChainKey ++
    ChainSend.selectState a accepted p.nextPqCounter i.pqCounter ++
    ByteAuth.release a accepted p.wire)

def inputShape (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) : Prop :=
  shape.valid ∧ pqShape.valid ∧ i.counter.length = 4 ∧ i.previous.length = 4 ∧
  i.ratchet.length = 32 ∧ i.chainKey.length = 32 ∧ i.pqChainKey.length = 32 ∧
  i.pqCounter.length = 4 ∧ i.epoch.length = 8 ∧
  i.chunkIndex.length = (if pqShape.hasChunk then 2 else 0) ∧
  i.chunkData.length = (if pqShape.hasChunk then 32 else 0) ∧
  i.sender.length = 32 ∧ i.receiver.length = 32 ∧
  i.addresses.length = (if shape.withAddresses then 36 else 0) ∧ i.plaintext.length ≤ 1024

instance (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) :
    Decidable (inputShape shape pqShape i) := inferInstanceAs (Decidable (_ ∧ _))

def sealChecked (o : Aes.Ops B) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) : Option (List B) :=
  if inputShape shape pqShape i then some (sealCore o v s a shape pqShape i) else none

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} {fv : V → V'}
  (ho : Aes.Hom o o' f) (hv : Varint64.Hom v v' f fv)
  (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem epochMask_map (epoch : List B) :
    f (epochMask a epoch) = epochMask a' (epoch.map f) := by
  simp only [epochMask, ha.not, ByteAuth.equalMask_map ha, List.map_replicate, ha.const]

include hv hs

theorem acceptedMask_map (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) :
    f (acceptedMask v s a shape pqShape i) = acceptedMask v' s' a' shape pqShape (i.map f) := by
  simp only [acceptedMask, Input.map, ha.and, ChainSend.acceptedMask_map hs ha, ha.const,
    ChainSend.counterMask_map ha, epochMask_map ha, SpqrMessage.acceptedMask_map hv hs ha,
    Varint64.pack_map hv ha, Varint.pack_map hs ha, ChainSend.nextCounter_map hs ha]

include ho

theorem prepare_map (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) :
    (prepare o v s a shape pqShape i).map f = prepare o' v' s' a' shape pqShape (i.map f) := by
  have hd := ChainSend.deriveFast_map hs (chainKey := i.chainKey)
    (pqKey := (SpqrChain.materialFast s a i.pqChainKey i.pqCounter).drop 32)
  simp only [Symmetric.Step.map, Symmetric.Material.map, List.map_drop,
    SpqrChain.materialFast_map hs ha] at hd
  have hk := congrArg Symmetric.Step.nextChainKey hd
  have hc := congrArg (fun d => d.material.cipherKey) hd
  have hm := congrArg (fun d => d.material.macKey) hd
  have hi := congrArg (fun d => d.material.iv) hd
  simp only at hk hc hm hi
  simp only [prepare, Prepared.map, Input.map, Send.message_map ho hs ha, hk, hc, hm, hi,
    List.map_take, SpqrChain.materialFast_map hs ha, ChainSend.nextCounter_map hs ha,
    SpqrMessage.content_map hv hs ha, Varint64.pack_map hv ha, Varint.pack_map hs ha]

theorem sealCore_map (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) :
    (sealCore o v s a shape pqShape i).map f = sealCore o' v' s' a' shape pqShape (i.map f) := by
  have hp := prepare_map ho hv hs ha shape pqShape i
  have hk := congrArg Prepared.nextChainKey hp
  have hc := congrArg Prepared.nextCounter hp
  have hpk := congrArg Prepared.nextPqChainKey hp
  have hpc := congrArg Prepared.nextPqCounter hp
  have hw := congrArg Prepared.wire hp
  simp only [Prepared.map] at hk hc hpk hpc hw
  simp only [sealCore, List.map_cons, List.map_append, ChainSend.selectState_map ha,
    ByteAuth.release_map ha, acceptedMask_map hv hs ha, hk, hc, hpk, hpc, hw, Input.map]

theorem sealChecked_map (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input B) :
    (sealChecked o v s a shape pqShape i).map (List.map f) =
      sealChecked o' v' s' a' shape pqShape (i.map f) := by
  simp only [sealChecked, inputShape, Input.map, List.length_map]
  split <;> simp [sealCore_map ho hv hs ha, Input.map]

end Refinement

theorem epochMask_value (epoch : List (BitVec 8)) :
    epochMask ByteAuth.concrete epoch = if epoch ≠ List.replicate 8 0 then 255 else 0 := by
  simp only [epochMask, ByteAuth.equalMask_value]
  change (~~~(if epoch = List.replicate 8 0 then 255 else 0)) = _
  split <;> simp_all

def accepted (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input (BitVec 8)) : Prop :=
  ChainSend.accepted shape 1 i.counter i.previous i.addresses ∧
  i.pqCounter ≠ List.replicate 4 255 ∧ i.epoch ≠ List.replicate 8 0 ∧
  SpqrMessage.accepted pqShape (Varint64.pack Varint64.concrete ByteAuth.concrete i.epoch)
    (Varint.pack Sha256.concrete ByteAuth.concrete
      (ChainSend.nextCounter Sha256.concrete ByteAuth.concrete i.pqCounter)) i.kind i.chunkIndex

instance (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input (BitVec 8)) :
    Decidable (accepted shape pqShape i) := inferInstanceAs (Decidable (_ ∧ _))

theorem acceptedMask_value (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input (BitVec 8)) :
    acceptedMask Varint64.concrete Sha256.concrete ByteAuth.concrete shape pqShape i =
      if accepted shape pqShape i then 255 else 0 := by
  simp only [acceptedMask, ChainSend.acceptedMask_value, ChainSend.counterMask_value,
    epochMask_value, SpqrMessage.acceptedMask_value, Receive.mask_and, accepted]
  rfl

/-- Canonical material functions replace the optimized prepared-HMAC variants. -/
def canonical (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input (BitVec 8)) : Prepared (BitVec 8) :=
  let pqOutput := SpqrChain.material Sha256.concrete ByteAuth.concrete i.pqChainKey i.pqCounter
  let nextPqCounter := ChainSend.nextCounter Sha256.concrete ByteAuth.concrete i.pqCounter
  let pq := SpqrMessage.content Varint64.concrete Sha256.concrete ByteAuth.concrete pqShape
    (Varint64.pack Varint64.concrete ByteAuth.concrete i.epoch)
    (Varint.pack Sha256.concrete ByteAuth.concrete nextPqCounter) i.kind i.chunkIndex i.chunkData
  let derived := Symmetric.derive Sha256.concrete i.chainKey (pqOutput.drop 32)
  ⟨derived.nextChainKey, ChainSend.nextCounter Sha256.concrete ByteAuth.concrete i.counter,
    pqOutput.take 32, nextPqCounter,
    Send.message Aes.concrete Sha256.concrete ByteAuth.concrete shape i.version i.counter i.previous i.ratchet
      derived.material.cipherKey derived.material.iv derived.material.macKey
      i.sender i.receiver i.plaintext pq i.addresses⟩

theorem prepare_concrete_correct (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input (BitVec 8)) :
    prepare Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete shape pqShape i =
      canonical shape pqShape i := by
  simp only [prepare, SpqrChain.materialFast_correct, Symmetric.deriveFast_correct, canonical]

def spec (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input (BitVec 8)) : List (BitVec 8) :=
  let p := canonical shape pqShape i
  if accepted shape pqShape i then
    255 :: (p.nextChainKey ++ p.nextCounter ++ p.nextPqChainKey ++ p.nextPqCounter ++ p.wire)
  else 0 :: (i.chainKey ++ i.counter ++ i.pqChainKey ++ i.pqCounter ++ List.replicate p.wire.length 0)

theorem sealCore_concrete_correct (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input (BitVec 8))
    (hkey : i.chainKey.length = 32) (hcounter : i.counter.length = 4)
    (hpkey : i.pqChainKey.length = 32) (hpcounter : i.pqCounter.length = 4) :
    sealCore Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete shape pqShape i = spec shape pqShape i := by
  have hk : (canonical shape pqShape i).nextChainKey.length = i.chainKey.length := by
    simp [canonical, Symmetric.derive, Symmetric.nextChainKey, Sha256.hmac_length, hkey]
  have hc : (canonical shape pqShape i).nextCounter.length = i.counter.length := by
    simp [canonical, ChainSend.nextCounter, hcounter]
  have hpk : (canonical shape pqShape i).nextPqChainKey.length = i.pqChainKey.length := by
    simp [canonical, SpqrChain.material_length, hpkey]
  have hpc : (canonical shape pqShape i).nextPqCounter.length = i.pqCounter.length := by
    simp [canonical, ChainSend.nextCounter, hpcounter]
  simp only [sealCore, acceptedMask_value, prepare_concrete_correct, spec]
  split
  · rw [ChainSend.selectState_accept _ _ hk, ChainSend.selectState_accept _ _ hc,
      ChainSend.selectState_accept _ _ hpk, ChainSend.selectState_accept _ _ hpc, ByteAuth.release_accept]
  · rw [ChainSend.selectState_reject, ChainSend.selectState_reject,
      ChainSend.selectState_reject, ChainSend.selectState_reject, ByteAuth.release_reject]

theorem reject_preserves_both_states (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : Input (BitVec 8))
    (bad : ¬ accepted shape pqShape i) :
    sealCore Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete shape pqShape i =
      0 :: (i.chainKey ++ i.counter ++ i.pqChainKey ++ i.pqCounter ++
        List.replicate (canonical shape pqShape i).wire.length 0) := by
  simp only [sealCore, acceptedMask_value, if_neg bad, prepare_concrete_correct,
    ChainSend.selectState_reject, ByteAuth.release_reject]

theorem compiled_sealCore_correct (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (i : Input (BVExpr 8)) (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (sealCore Aes.symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape pqShape i).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape pqShape i))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape pqShape i))).vec.get bit hi)) =
      (ByteCircuit.joinValue (sealCore Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete shape pqShape
        (i.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct, sealCore_map (Aes.evaluationHom assign)
    (Varint64.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_sealCore_spec (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (i : Input (BVExpr 8)) (hkey : i.chainKey.length = 32) (hcounter : i.counter.length = 4)
    (hpkey : i.pqChainKey.length = 32) (hpcounter : i.pqCounter.length = 4)
    (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (sealCore Aes.symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape pqShape i).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape pqShape i))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic shape pqShape i))).vec.get bit hi)) =
      (ByteCircuit.joinValue (spec shape pqShape (i.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [compiled_sealCore_correct, sealCore_concrete_correct _ _ _
    (by simpa [Input.map] using hkey) (by simpa [Input.map] using hcounter)
    (by simpa [Input.map] using hpkey) (by simpa [Input.map] using hpcounter)]

end TlsMpc.Signal.SpqrSend
