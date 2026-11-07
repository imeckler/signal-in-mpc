import TlsMpc.Signal.SpqrChain
import TlsMpc.Signal.Varint64

/-! SPQR chain initialization and next-epoch key material. The two HKDF domains
and directional splits follow pinned Chain::new/add_epoch. Direction0=A2B,
direction1=B2A; direction and epochs stay shared. An accepted add produces one
candidate epoch record; insertion into retained links and atomic commit are
separate. Epoch secrets must come from the KEM state machine, not a caller's
claimed public result. Full translated HKDF/SPQR correspondence remains open.

Output is status || root32 || epochBE8 || sendKey32 || sendCounterBE4 ||
recvKey32 || recvCounterBE4. Failed add preserves old root/epoch and zeroes the
candidate chains. An invalid initialization direction zeroes all113 bytes.
Counter overflow is rejected explicitly rather than modeled as Rust panic. -/
namespace TlsMpc.Signal.SpqrEpoch
open Std.Tactic.BVDecide

structure Ops (B V : Type) where
  increment : V → V
  unpack : V → Nat → B

def concrete : Ops (BitVec 8) (BitVec 64) where
  increment x := x + 1
  unpack x i := x.extractLsb' (8 * (7 - i)) 8

def symbolic : Ops (BVExpr 8) (BVExpr 64) where
  increment x := BvConstruct.bin x .add (.const 1)
  unpack x i := BvConstruct.extract (8 * (7 - i)) 8 x

structure Hom (o : Ops B V) (o' : Ops B' V') (f : B → B') (fv : V → V') : Prop where
  increment : ∀ x, fv (o.increment x) = o'.increment (fv x)
  unpack : ∀ x i, f (o.unpack x i) = o'.unpack (fv x) i

def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [symbolic, concrete]

def nextEpoch (o : Ops B V) (v : Varint64.Ops B V) (a : ByteAuth.Ops B) (epoch : List B) : List B :=
  (List.range 8).map (o.unpack (o.increment (Varint64.pack v a epoch)))

def info (adding : Bool) : List Nat :=
  TlsKdf.ascii (if adding then "Signal PQ Ratchet V1 Chain Add Epoch" else "Signal PQ Ratchet V1 Chain  Start")

def material (s : Sha256.Ops B W) (adding : Bool) (root secret : List B) : List B :=
  TlsKdf.expandCore s (TlsKdf.extract s root secret) ((info adding).map s.byteConst) 96

def materialFast (s : Sha256.Ops B W) (adding : Bool) (root secret : List B) : List B :=
  TlsKdf.expandFast s (TlsKdf.extract s root secret) ((info adding).map s.byteConst) 96

theorem materialFast_correct (s : Sha256.Ops B W) (adding : Bool) (root secret : List B) :
    materialFast s adding root secret = material s adding root secret := by
  simp only [materialFast, material, TlsKdf.expandFast_correct]

theorem material_length (s : Sha256.Ops B W) (adding : Bool) (root secret : List B) :
    (material s adding root secret).length = 96 := by simp [material, TlsKdf.expandCore_length]

def chains (a : ByteAuth.Ops B) (direction : B) (output : List B) : List B :=
  let reverse := ByteAuth.eqMask a direction (a.const 1)
  let ab := (output.drop 32).take 32
  let ba := (output.drop 64).take 32
  Unpad.choose a reverse ba ab ++ List.replicate 4 (a.const 0) ++
    Unpad.choose a reverse ab ba ++ List.replicate 4 (a.const 0)

def addMask (o : Ops B V) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (direction : B) (epoch proposed : List B) : B :=
  a.and (ChainSend.flagMask a direction)
    (a.and (a.not (ByteAuth.equalMask a epoch (List.replicate 8 (a.const 255))))
      (ByteAuth.equalMask a proposed (nextEpoch o v a epoch)))

def newCore (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (direction : B) (secret : List B) : List B :=
  let accepted := ChainSend.flagMask a direction
  let output := materialFast s false (TlsKdf.zeros s 32) secret
  accepted :: ByteAuth.release a accepted
    (output.take 32 ++ List.replicate 8 (a.const 0) ++ chains a direction output)

def addCore (o : Ops B V) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (direction : B) (root epoch proposed secret : List B) : List B :=
  let accepted := addMask o v a direction epoch proposed
  let output := materialFast s true root secret
  accepted :: (ChainSend.selectState a accepted (output.take 32) root ++
    ChainSend.selectState a accepted proposed epoch ++ ByteAuth.release a accepted (chains a direction output))

def newChecked (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (direction : B) (secret : List B) : Option (List B) :=
  if secret.length = 32 then some (newCore s a direction secret) else none

def addChecked (o : Ops B V) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (direction : B) (root epoch proposed secret : List B) : Option (List B) :=
  if root.length = 32 ∧ epoch.length = 8 ∧ proposed.length = 8 ∧ secret.length = 32 then
    some (addCore o v s a direction root epoch proposed secret) else none

theorem chains_length (a : ByteAuth.Ops B) (direction : B) (output : List B) (hl : output.length = 96) :
    (chains a direction output).length = 72 := by simp [chains, Unpad.choose, hl]

theorem newCore_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (direction : B) (secret : List B) :
    (newCore s a direction secret).length = 113 := by
  simp [newCore, materialFast_correct, ByteAuth.release, material_length,
    chains_length _ _ _ (material_length _ _ _ _)]

theorem addCore_length (o : Ops B V) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (direction : B) (root epoch proposed secret : List B) :
    (addCore o v s a direction root epoch proposed secret).length = 1 + root.length + epoch.length + 72 := by
  simp [addCore, materialFast_correct, ChainSend.selectState, ByteAuth.release,
    chains_length _ _ _ (material_length _ _ _ _)]; omega

section Refinement
variable {o : Ops B V} {o' : Ops B' V'} {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (ho : Hom o o' f fv) (hv : Varint64.Hom v v' f fv)
  (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

include ho hv ha in
theorem nextEpoch_map (epoch : List B) :
    (nextEpoch o v a epoch).map f = nextEpoch o' v' a' (epoch.map f) := by
  simp only [nextEpoch, List.map_map, Function.comp_def, ho.unpack, ho.increment, Varint64.pack_map hv ha]

include hs in
theorem material_map (adding : Bool) (root secret : List B) :
    (material s adding root secret).map f = material s' adding (root.map f) (secret.map f) := by
  simp only [material, TlsKdf.expandCore_map hs, TlsKdf.extract_map hs,
    List.map_map, Function.comp_def, hs.byteConst]

include hs in
theorem materialFast_map (adding : Bool) (root secret : List B) :
    (materialFast s adding root secret).map f = materialFast s' adding (root.map f) (secret.map f) := by
  rw [materialFast_correct, materialFast_correct, material_map hs]

include ha in
theorem chains_map (direction : B) (output : List B) :
    (chains a direction output).map f = chains a' (f direction) (output.map f) := by
  simp only [chains, List.map_append, Unpad.choose_map ha, ByteAuth.eqMask_map ha,
    ha.const, List.map_take, List.map_drop, List.map_replicate]

include ho hv ha in
theorem addMask_map (direction : B) (epoch proposed : List B) :
    f (addMask o v a direction epoch proposed) = addMask o' v' a' (f direction) (epoch.map f) (proposed.map f) := by
  simp only [addMask, ha.and, ha.not, ChainSend.flagMask_map ha,
    ByteAuth.equalMask_map ha, List.map_replicate, ha.const, nextEpoch_map ho hv ha]

include hs ha in
theorem newCore_map (direction : B) (secret : List B) :
    (newCore s a direction secret).map f = newCore s' a' (f direction) (secret.map f) := by
  simp only [newCore, List.map_cons, ByteAuth.release_map ha, ChainSend.flagMask_map ha,
    List.map_append, List.map_take, List.map_replicate, ha.const, chains_map ha,
    materialFast_map hs, TlsKdf.zeros_map hs]

include ho hv hs ha in
theorem addCore_map (direction : B) (root epoch proposed secret : List B) :
    (addCore o v s a direction root epoch proposed secret).map f =
      addCore o' v' s' a' (f direction) (root.map f) (epoch.map f) (proposed.map f) (secret.map f) := by
  simp only [addCore, List.map_cons, List.map_append, addMask_map ho hv ha,
    ChainSend.selectState_map ha, List.map_take, materialFast_map hs,
    ByteAuth.release_map ha, chains_map ha]

include hs ha in
theorem newChecked_map (direction : B) (secret : List B) :
    (newChecked s a direction secret).map (List.map f) = newChecked s' a' (f direction) (secret.map f) := by
  simp only [newChecked, List.length_map]
  split <;> simp [newCore_map hs ha]

include ho hv hs ha in
theorem addChecked_map (direction : B) (root epoch proposed secret : List B) :
    (addChecked o v s a direction root epoch proposed secret).map (List.map f) =
      addChecked o' v' s' a' (f direction) (root.map f) (epoch.map f) (proposed.map f) (secret.map f) := by
  simp only [addChecked, List.length_map]
  split <;> simp [addCore_map ho hv hs ha]
end Refinement

def chainsSpec (direction : BitVec 8) (output : List (BitVec 8)) : List (BitVec 8) :=
  let ab := (output.drop 32).take 32
  let ba := (output.drop 64).take 32
  (if direction = 1 then ba else ab) ++ List.replicate 4 0 ++
    (if direction = 1 then ab else ba) ++ List.replicate 4 0

theorem chains_spec (direction : BitVec 8) (output : List (BitVec 8)) (hl : output.length = 96) :
    chains ByteAuth.concrete direction output = chainsSpec direction output := by
  have he : ((output.drop 64).take 32).length = ((output.drop 32).take 32).length := by simp [hl]
  have hc : ByteAuth.concrete.const 1 = (1 : BitVec 8) := rfl
  simp only [chains, hc, ByteAuth.eqMask_value, chainsSpec]
  split
  · rw [Unpad.choose_accept _ _ he, Unpad.choose_accept _ _ he.symm]; rfl
  · rw [Unpad.choose_reject _ _ he, Unpad.choose_reject _ _ he.symm]; rfl

def addAccepted (direction : BitVec 8) (epoch proposed : List (BitVec 8)) : Prop :=
  (direction = 0 ∨ direction = 1) ∧ epoch ≠ List.replicate 8 255 ∧
    proposed = nextEpoch concrete Varint64.concrete ByteAuth.concrete epoch

instance (direction : BitVec 8) (epoch proposed : List (BitVec 8)) : Decidable (addAccepted direction epoch proposed) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem addMask_value (direction : BitVec 8) (epoch proposed : List (BitVec 8)) :
    addMask concrete Varint64.concrete ByteAuth.concrete direction epoch proposed =
      if addAccepted direction epoch proposed then 255 else 0 := by
  have neg (p : Prop) [Decidable p] :
      ByteAuth.concrete.not (if p then 255 else 0) = if ¬p then 255 else 0 := by
    by_cases h : p <;> simp [h, ByteAuth.concrete]
  have hc : ByteAuth.concrete.const 255 = (255 : BitVec 8) := rfl
  simp only [addMask, ChainSend.flagMask_value, hc, ByteAuth.equalMask_value,
    neg, Receive.mask_and, addAccepted]
  rfl

def newSpec (direction : BitVec 8) (secret : List (BitVec 8)) : List (BitVec 8) :=
  let output := material Sha256.concrete false (List.replicate 32 0) secret
  if direction = 0 ∨ direction = 1 then
    255 :: (output.take 32 ++ List.replicate 8 0 ++ chainsSpec direction output)
  else List.replicate 113 0

def addSpec (direction : BitVec 8) (root epoch proposed secret : List (BitVec 8)) : List (BitVec 8) :=
  let output := material Sha256.concrete true root secret
  if addAccepted direction epoch proposed then
    255 :: (output.take 32 ++ proposed ++ chainsSpec direction output)
  else 0 :: (root ++ epoch ++ List.replicate 72 0)

theorem newCore_spec (direction : BitVec 8) (secret : List (BitVec 8)) :
    newCore Sha256.concrete ByteAuth.concrete direction secret = newSpec direction secret := by
  have hz : TlsKdf.zeros Sha256.concrete 32 = List.replicate 32 0 := rfl
  simp only [newCore, materialFast_correct, hz, ChainSend.flagMask_value, newSpec]
  split
  · rw [ByteAuth.release_accept, chains_spec _ _ (material_length _ _ _ _)]; rfl
  · rw [ByteAuth.release_reject]
    simp only [List.length_append, List.length_take, List.length_replicate,
      material_length, chains_length _ _ _ (material_length _ _ _ _)]
    rfl

theorem addCore_spec (direction : BitVec 8) (root epoch proposed secret : List (BitVec 8))
    (hr : root.length = 32) (he : proposed.length = epoch.length) :
    addCore concrete Varint64.concrete Sha256.concrete ByteAuth.concrete direction root epoch proposed secret =
      addSpec direction root epoch proposed secret := by
  have hm : ((material Sha256.concrete true root secret).take 32).length = root.length := by
    simp [material_length, hr]
  simp only [addCore, materialFast_correct, addMask_value, addSpec]
  split
  · rw [ChainSend.selectState_accept _ _ hm, ChainSend.selectState_accept _ _ he,
      ByteAuth.release_accept, chains_spec _ _ (material_length _ _ _ _)]
  · rw [ChainSend.selectState_reject, ChainSend.selectState_reject, ByteAuth.release_reject,
      chains_length _ _ _ (material_length _ _ _ _)]

theorem compiled_newCore_spec (direction : BVExpr 8) (secret : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (newCore Sha256.symbolic ByteAuth.symbolic direction secret).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (newCore Sha256.symbolic ByteAuth.symbolic direction secret))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (newCore Sha256.symbolic ByteAuth.symbolic direction secret))).vec.get index hi)) =
      (ByteCircuit.joinValue (newSpec (BVExpr.eval assign direction) (secret.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    newCore_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign), newCore_spec]

theorem compiled_addCore_spec (direction : BVExpr 8) (root epoch proposed secret : List (BVExpr 8))
    (hr : root.length = 32) (he : proposed.length = epoch.length)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (addCore symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic direction root epoch proposed secret).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (addCore symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic direction root epoch proposed secret))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (addCore symbolic Varint64.symbolic Sha256.symbolic ByteAuth.symbolic direction root epoch proposed secret))).vec.get index hi)) =
      (ByteCircuit.joinValue (addSpec (BVExpr.eval assign direction) (root.map (BVExpr.eval assign))
        (epoch.map (BVExpr.eval assign)) (proposed.map (BVExpr.eval assign)) (secret.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    addCore_map (evaluationHom assign) (Varint64.evaluationHom assign)
      (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign),
    addCore_spec _ _ _ _ _ (by simpa using hr) (by simpa using he)]

end TlsMpc.Signal.SpqrEpoch
