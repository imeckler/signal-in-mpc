import TlsMpc.Signal.Send
import TlsMpc.Signal.Symmetric

/-! Bounded established-chain send. Message keys, IV, ciphertext and MAC are
derived inside MPC. The optional SPQR message-key flag is secret (0/1); an
absent key selects the HKDF zero salt inside the circuit. A successful result
returns a candidate next chain key/counter. Rejection preserves the supplied
old chain state and zeros the wire output. Atomic persistence, the SPQR
transition and complete ratchet/session policy remain separate obligations. -/

namespace TlsMpc.Signal.ChainSend
open Std.Tactic.BVDecide

def salt (a : ByteAuth.Ops B) (present : B) (key : List B) : List B :=
  ByteAuth.release a (ByteAuth.eqMask a present (a.const 1)) key

def flagMask (a : ByteAuth.Ops B) (present : B) : B :=
  a.xor (ByteAuth.eqMask a present (a.const 0)) (ByteAuth.eqMask a present (a.const 1))

def counterMask (a : ByteAuth.Ops B) (counter : List B) : B :=
  a.not (ByteAuth.equalMask a counter (List.replicate 4 (a.const 255)))

def nextCounter (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (counter : List B) : List B :=
  let next := s.add (Varint.pack s a counter) (s.wordConst 1)
  (List.range 4).map (s.unpack next)

def selectState (a : ByteAuth.Ops B) (accepted : B) (next old : List B) : List B :=
  (List.range old.length).map (fun i => Unpad.chooseByte a accepted
    (OpenResult.get a next i) (OpenResult.get a old i))

def acceptedMask (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (shape : Serialization.Shape)
    (present : B) (counter previous addresses : List B) : B :=
  a.and (Serialization.acceptedMask s a shape counter previous addresses)
    (a.and (flagMask a present) (counterMask a counter))

def sealCore (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (version present : B)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List B) : List B :=
  let accepted := acceptedMask s a shape present counter previous addresses
  let derived := Symmetric.deriveFast s chainKey (salt a present pqKey)
  let wire := Send.message o s a shape version counter previous ratchet
    derived.material.cipherKey derived.material.iv derived.material.macKey
    sender receiver plaintext pq addresses
  accepted :: (selectState a accepted derived.nextChainKey chainKey ++
    selectState a accepted (nextCounter s a counter) counter ++ ByteAuth.release a accepted wire)

def sealChecked (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (shape : Serialization.Shape) (version present : B)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List B) : Option (List B) :=
  if Serialization.inputShape shape counter previous ratchet plaintext pq addresses ∧
      chainKey.length = 32 ∧ pqKey.length = 32 ∧ sender.length = 32 ∧ receiver.length = 32 ∧
      plaintext.length + pq.length + 256 < 2 ^ 61 then
    some (sealCore o s a shape version present counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses)
  else none

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem salt_map (present : B) (key : List B) :
    (salt a present key).map f = salt a' (f present) (key.map f) := by
  simp only [salt, ByteAuth.release_map ha, ByteAuth.eqMask_map ha, ha.const]

theorem flagMask_map (present : B) : f (flagMask a present) = flagMask a' (f present) := by
  simp only [flagMask, ha.xor, ByteAuth.eqMask_map ha, ha.const]

theorem counterMask_map (counter : List B) :
    f (counterMask a counter) = counterMask a' (counter.map f) := by
  simp only [counterMask, ha.not, ByteAuth.equalMask_map ha, List.map_replicate, ha.const]

theorem selectState_map (accepted : B) (next old : List B) :
    (selectState a accepted next old).map f =
      selectState a' (f accepted) (next.map f) (old.map f) := by
  simp only [selectState, List.map_map, Function.comp_def, List.length_map,
    Unpad.chooseByte_map ha, OpenResult.get_map ha]

include hs

theorem nextCounter_map (counter : List B) :
    (nextCounter s a counter).map f = nextCounter s' a' (counter.map f) := by
  simp only [nextCounter, List.map_map, Function.comp_def, hs.unpack, hs.add,
    Varint.pack_map hs ha, hs.wordConst]

theorem acceptedMask_map (shape : Serialization.Shape) (present : B)
    (counter previous addresses : List B) :
    f (acceptedMask s a shape present counter previous addresses) =
      acceptedMask s' a' shape (f present) (counter.map f) (previous.map f) (addresses.map f) := by
  simp only [acceptedMask, ha.and, Serialization.acceptedMask_map hs ha,
    flagMask_map ha, counterMask_map ha]

omit ha in
theorem deriveFast_map (chainKey pqKey : List B) :
    (Symmetric.deriveFast s chainKey pqKey).map f =
      Symmetric.deriveFast s' (chainKey.map f) (pqKey.map f) := by
  rw [Symmetric.deriveFast_correct, Symmetric.deriveFast_correct, Symmetric.derive_map hs]

include ho

theorem sealCore_map (shape : Serialization.Shape) (version present : B)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List B) :
    (sealCore o s a shape version present counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses).map f =
      sealCore o' s' a' shape (f version) (f present)
        (counter.map f) (previous.map f) (ratchet.map f) (chainKey.map f) (pqKey.map f)
        (sender.map f) (receiver.map f) (plaintext.map f) (pq.map f) (addresses.map f) := by
  have hd := deriveFast_map hs (chainKey := chainKey) (pqKey := salt a present pqKey)
  simp only [Symmetric.Step.map, Symmetric.Material.map, salt_map ha] at hd
  have hk := congrArg Symmetric.Step.nextChainKey hd
  have hc := congrArg (fun d => d.material.cipherKey) hd
  have hm := congrArg (fun d => d.material.macKey) hd
  have hi := congrArg (fun d => d.material.iv) hd
  simp only at hk hc hm hi
  simp only [sealCore, List.map_cons, List.map_append, selectState_map ha,
    acceptedMask_map hs ha, nextCounter_map hs ha, ByteAuth.release_map ha,
    Send.message_map ho hs ha, hk, hc, hm, hi]

theorem sealChecked_map (shape : Serialization.Shape) (version present : B)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List B) :
    (sealChecked o s a shape version present counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses).map (List.map f) =
      sealChecked o' s' a' shape (f version) (f present)
        (counter.map f) (previous.map f) (ratchet.map f) (chainKey.map f) (pqKey.map f)
        (sender.map f) (receiver.map f) (plaintext.map f) (pq.map f) (addresses.map f) := by
  simp only [sealChecked, Serialization.inputShape, List.length_map]
  split <;> simp [sealCore_map ho hs ha]

end Refinement

theorem salt_present (key : List (BitVec 8)) : salt ByteAuth.concrete 1 key = key := by
  simp only [salt, ByteAuth.eqMask_value]
  exact ByteAuth.release_accept key

theorem salt_absent (key : List (BitVec 8)) :
    salt ByteAuth.concrete 0 key = List.replicate key.length 0 := by
  simp only [salt, ByteAuth.eqMask_value]
  exact ByteAuth.release_reject key

theorem flagMask_value (present : BitVec 8) :
    flagMask ByteAuth.concrete present = if present = 0 ∨ present = 1 then 255 else 0 :=
  Receive.serviceKindMask_value present

theorem counterMask_value (counter : List (BitVec 8)) :
    counterMask ByteAuth.concrete counter = if counter ≠ List.replicate 4 255 then 255 else 0 := by
  simp only [counterMask, ByteAuth.equalMask_value]
  change (~~~(if counter = List.replicate 4 255 then 255 else 0)) = _
  split <;> simp_all

def accepted (shape : Serialization.Shape) (present : BitVec 8)
    (counter previous addresses : List (BitVec 8)) : Prop :=
  Serialization.accepted shape counter previous addresses ∧
  (present = 0 ∨ present = 1) ∧ counter ≠ List.replicate 4 255

instance (shape : Serialization.Shape) (present : BitVec 8)
    (counter previous addresses : List (BitVec 8)) : Decidable (accepted shape present counter previous addresses) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem acceptedMask_value (shape : Serialization.Shape) (present : BitVec 8)
    (counter previous addresses : List (BitVec 8)) :
    acceptedMask Sha256.concrete ByteAuth.concrete shape present counter previous addresses =
      if accepted shape present counter previous addresses then 255 else 0 := by
  simp only [acceptedMask, Serialization.acceptedMask_value, flagMask_value, counterMask_value,
    Receive.mask_and, accepted]
  split <;> simp_all

theorem selectState_reject (next old : List (BitVec 8)) :
    selectState ByteAuth.concrete 0 next old = old := by
  simp only [selectState]
  have hb := Unpad.chooseByte_reject
  simp only [hb]
  apply List.ext_getElem
  · simp
  · intro i hi hright
    simp only [List.getElem_map, List.getElem_range]
    simp [OpenResult.get, hright]

theorem selectState_accept (next old : List (BitVec 8)) (hlength : next.length = old.length) :
    selectState ByteAuth.concrete 255 next old = next := by
  simp only [selectState]
  have hb := Unpad.chooseByte_accept
  simp only [hb]
  apply List.ext_getElem
  · simp [hlength]
  · intro i hi hright
    simp only [List.getElem_map, List.getElem_range]
    simp [OpenResult.get, hright]

/-- Canonical pure behavior: derive the selected SPQR salt and next message
material; on success return next state and the same-content ciphertext/MAC;
on rejection return old state and a zero wire buffer. -/
def spec (shape : Serialization.Shape) (version present : BitVec 8)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List (BitVec 8)) : List (BitVec 8) :=
  let derived := Symmetric.derive Sha256.concrete chainKey (salt ByteAuth.concrete present pqKey)
  let wire := Send.message Aes.concrete Sha256.concrete ByteAuth.concrete shape version counter previous ratchet
    derived.material.cipherKey derived.material.iv derived.material.macKey sender receiver plaintext pq addresses
  if accepted shape present counter previous addresses then
    255 :: (derived.nextChainKey ++ nextCounter Sha256.concrete ByteAuth.concrete counter ++ wire)
  else 0 :: (chainKey ++ counter ++ List.replicate wire.length 0)

theorem sealCore_concrete_correct (shape : Serialization.Shape) (version present : BitVec 8)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List (BitVec 8))
    (hkey : chainKey.length = 32) (hcounter : counter.length = 4) :
    sealCore Aes.concrete Sha256.concrete ByteAuth.concrete shape version present
      counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses =
      spec shape version present counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses := by
  have hk : (Symmetric.derive Sha256.concrete chainKey (salt ByteAuth.concrete present pqKey)).nextChainKey.length = chainKey.length := by
    simp [Symmetric.derive, Symmetric.nextChainKey, Sha256.hmac_length, hkey]
  have hc : (nextCounter Sha256.concrete ByteAuth.concrete counter).length = counter.length := by
    simp [nextCounter, hcounter]
  simp only [sealCore, acceptedMask_value, Symmetric.deriveFast_correct, spec]
  split
  · rw [selectState_accept _ _ hk, selectState_accept _ _ hc, ByteAuth.release_accept]
  · rw [selectState_reject, selectState_reject, ByteAuth.release_reject]

theorem reject_preserves_state (shape : Serialization.Shape) (version present : BitVec 8)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List (BitVec 8))
    (bad : ¬ accepted shape present counter previous addresses) :
    (sealCore Aes.concrete Sha256.concrete ByteAuth.concrete shape version present
      counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses).take
        (1 + chainKey.length + counter.length) = 0 :: (chainKey ++ counter) := by
  simp only [sealCore, acceptedMask_value, if_neg bad, selectState_reject, ByteAuth.release_reject]
  have take_prefix (leading rest : List (BitVec 8)) :
      (leading ++ rest).take leading.length = leading := by simp
  have hn : 1 + chainKey.length + counter.length = (0 :: (chainKey ++ counter)).length := by
    simp
    omega
  rw [hn]
  simpa only [List.cons_append, List.append_assoc] using
    take_prefix (0 :: (chainKey ++ counter)) _

theorem compiled_sealCore_correct (shape : Serialization.Shape) (version present : BVExpr 8)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version present
      counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version present
          counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version present
          counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses))).vec.get index hi)) =
      (ByteCircuit.joinValue (sealCore Aes.concrete Sha256.concrete ByteAuth.concrete shape
        (version.eval assign) (present.eval assign)
        (counter.map (BVExpr.eval assign)) (previous.map (BVExpr.eval assign)) (ratchet.map (BVExpr.eval assign))
        (chainKey.map (BVExpr.eval assign)) (pqKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign))
        (receiver.map (BVExpr.eval assign)) (plaintext.map (BVExpr.eval assign)) (pq.map (BVExpr.eval assign))
        (addresses.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, sealCore_map (Aes.evaluationHom assign)
    (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_sealCore_spec (shape : Serialization.Shape) (version present : BVExpr 8)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List (BVExpr 8))
    (hkey : chainKey.length = 32) (hcounter : counter.length = 4)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version present
      counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version present
          counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version present
          counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses))).vec.get index hi)) =
      (ByteCircuit.joinValue (spec shape (version.eval assign) (present.eval assign)
        (counter.map (BVExpr.eval assign)) (previous.map (BVExpr.eval assign)) (ratchet.map (BVExpr.eval assign))
        (chainKey.map (BVExpr.eval assign)) (pqKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign))
        (receiver.map (BVExpr.eval assign)) (plaintext.map (BVExpr.eval assign)) (pq.map (BVExpr.eval assign))
        (addresses.map (BVExpr.eval assign)))).getLsbD index := by
  rw [compiled_sealCore_correct, sealCore_concrete_correct _ _ _ _ _ _ _ _ _ _ _ _ _
    (by simpa using hkey) (by simpa using hcounter)]

end TlsMpc.Signal.ChainSend
