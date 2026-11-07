import TlsMpc.Signal.ChainSend

/-! The symmetric SPQR send-chain advance used by pinned
`spqr::chain::ChainEpochDirection::next_key_internal`. The counter is advanced
before it is encoded into HKDF info. The 64-byte output is split into the next
chain key and the message key. This component neither selects an epoch nor
implements ML-KEM, chunk processing, serialized SPQR state or persistence.

Compiler equality is proved against the executable Lean definition. Full
equivalence to the actual translated HKDF and SPQR wrapper remains separate.
The exhausted-counter profile rejects and preserves old state; this is not a
claim about Rust overflow behavior outside its stated precondition. -/

namespace TlsMpc.Signal.SpqrChain
open Std.Tactic.BVDecide

def info (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (counter : List B) : List B :=
  ChainSend.nextCounter s a counter ++
    (TlsKdf.ascii "Signal PQ Ratchet V1 Chain Next").map s.byteConst

def material (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (key counter : List B) : List B :=
  let prk := TlsKdf.extract s (TlsKdf.zeros s 32) key
  TlsKdf.expandCore s prk (info s a counter) 64

def materialFast (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (key counter : List B) : List B :=
  let prk := TlsKdf.extract s (TlsKdf.zeros s 32) key
  TlsKdf.expandFast s prk (info s a counter) 64

theorem materialFast_correct (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (key counter : List B) : materialFast s a key counter = material s a key counter := by
  simp only [materialFast, material, TlsKdf.expandFast_correct]

theorem material_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (key counter : List B) : (material s a key counter).length = 64 := by
  simp [material, TlsKdf.expandCore_length]

/-- Shared status, next key, next counter, message key. Rejection preserves the
old key/counter and zeroes the message key. -/
def stepCore (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (key counter : List B) : List B :=
  let accepted := ChainSend.counterMask a counter
  let output := materialFast s a key counter
  accepted :: (ChainSend.selectState a accepted (output.take 32) key ++
    ChainSend.selectState a accepted (ChainSend.nextCounter s a counter) counter ++
    ByteAuth.release a accepted (output.drop 32))

def stepChecked (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (key counter : List B) : Option (List B) :=
  if key.length = 32 ∧ counter.length = 4 then some (stepCore s a key counter) else none

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include hs ha

theorem info_map (counter : List B) :
    (info s a counter).map f = info s' a' (counter.map f) := by
  simp only [info, List.map_append, ChainSend.nextCounter_map hs ha,
    List.map_map, Function.comp_def, hs.byteConst]

theorem material_map (key counter : List B) :
    (material s a key counter).map f = material s' a' (key.map f) (counter.map f) := by
  simp only [material, TlsKdf.expandCore_map hs, TlsKdf.extract_map hs,
    TlsKdf.zeros_map hs, info_map hs ha]

theorem materialFast_map (key counter : List B) :
    (materialFast s a key counter).map f = materialFast s' a' (key.map f) (counter.map f) := by
  rw [materialFast_correct, materialFast_correct, material_map hs ha]

theorem stepCore_map (key counter : List B) :
    (stepCore s a key counter).map f = stepCore s' a' (key.map f) (counter.map f) := by
  simp only [stepCore, List.map_cons, List.map_append, ChainSend.counterMask_map ha,
    ChainSend.selectState_map ha, ByteAuth.release_map ha, List.map_take,
    List.map_drop, materialFast_map hs ha, ChainSend.nextCounter_map hs ha]

theorem stepChecked_map (key counter : List B) :
    (stepChecked s a key counter).map (List.map f) =
      stepChecked s' a' (key.map f) (counter.map f) := by
  simp only [stepChecked, List.length_map]
  split <;> simp [stepCore_map hs ha]

end Refinement

def spec (key counter : List (BitVec 8)) : List (BitVec 8) :=
  let output := material Sha256.concrete ByteAuth.concrete key counter
  if counter = List.replicate 4 255 then 0 :: (key ++ counter ++ List.replicate 32 0)
  else 255 :: (output.take 32 ++ ChainSend.nextCounter Sha256.concrete ByteAuth.concrete counter ++
    output.drop 32)

theorem stepCore_concrete_correct (key counter : List (BitVec 8))
    (hkey : key.length = 32) (hcounter : counter.length = 4) :
    stepCore Sha256.concrete ByteAuth.concrete key counter = spec key counter := by
  have hk : ((material Sha256.concrete ByteAuth.concrete key counter).take 32).length = key.length := by
    simp [material_length, hkey]
  have hc : (ChainSend.nextCounter Sha256.concrete ByteAuth.concrete counter).length = counter.length := by
    simp [ChainSend.nextCounter, hcounter]
  have hm : ((material Sha256.concrete ByteAuth.concrete key counter).drop 32).length = 32 := by
    simp [material_length]
  simp only [stepCore, materialFast_correct, ChainSend.counterMask_value]
  split
  · rename_i good
    rw [ChainSend.selectState_accept _ _ hk, ChainSend.selectState_accept _ _ hc,
      ByteAuth.release_accept]
    simp only [spec, if_neg good]
  · rename_i bad
    rw [ChainSend.selectState_reject, ChainSend.selectState_reject,
      ByteAuth.release_reject, hm]
    simp only [spec, if_pos (Classical.not_not.mp bad)]

theorem stepCore_length (key counter : List B) :
    (stepCore s a key counter).length = 1 + key.length + counter.length + 32 := by
  simp [stepCore, ChainSend.selectState, ByteAuth.release, materialFast_correct, material_length]
  omega

theorem exhausted_preserves_state (key : List (BitVec 8)) :
    stepCore Sha256.concrete ByteAuth.concrete key (List.replicate 4 255) =
      0 :: (key ++ List.replicate 4 255 ++ List.replicate 32 0) := by
  have hm : ChainSend.counterMask ByteAuth.concrete (List.replicate 4 255) = 0 := by
    rw [ChainSend.counterMask_value, if_neg (by simp)]
  simp only [stepCore, hm, materialFast_correct, ChainSend.selectState_reject,
    ByteAuth.release_reject, List.length_drop, material_length]

theorem compiled_stepCore_correct (key counter : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (stepCore Sha256.symbolic ByteAuth.symbolic key counter).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (stepCore Sha256.symbolic ByteAuth.symbolic key counter))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (stepCore Sha256.symbolic ByteAuth.symbolic key counter))).vec.get index hi)) =
      (ByteCircuit.joinValue (stepCore Sha256.concrete ByteAuth.concrete
        (key.map (BVExpr.eval assign)) (counter.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    stepCore_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_stepCore_spec (key counter : List (BVExpr 8))
    (hkey : key.length = 32) (hcounter : counter.length = 4)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (stepCore Sha256.symbolic ByteAuth.symbolic key counter).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (stepCore Sha256.symbolic ByteAuth.symbolic key counter))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (stepCore Sha256.symbolic ByteAuth.symbolic key counter))).vec.get index hi)) =
      (ByteCircuit.joinValue (spec
        (key.map (BVExpr.eval assign)) (counter.map (BVExpr.eval assign)))).getLsbD index := by
  rw [compiled_stepCore_correct, stepCore_concrete_correct _ _
    (by simpa using hkey) (by simpa using hcounter)]

end TlsMpc.Signal.SpqrChain
