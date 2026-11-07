import TlsMpc.Signal.ChainReceive
import TlsMpc.Signal.SkippedKeys

/-! Authenticated receive from a bounded skipped-seed store. Lookup key/counter
come only from the shared parser. The selected seed derives message keys inside
MPC, and removal commits only after authentication/address/padding checks. No
legacy expanded-key records, new ratchet creation, or host persistence here. -/
namespace TlsMpc.Signal.SkippedReceive
open Std.Tactic.BVDecide

def bytesAt (a : ByteAuth.Ops B) (bytes : List B) (start : Nat) : Fin n → B :=
  fun i => OpenResult.get a bytes (start + i.val)

def finish (a : ByteAuth.Ops B) (authentication : B) (parsed opened : List B)
    (slots : List (SkippedKeys.Slot B)) : List B :=
  let committed := SkippedKeys.consume a authentication (bytesAt a parsed 1) (bytesAt a parsed 33) slots
  committed.found :: (SkippedKeys.storeBytes committed.slots ++ ByteAuth.release a committed.found (opened.drop 1))

def openCore (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (present : B)
    (pqKey sender receiver wire expected : List B) (slots : List (SkippedKeys.Slot B)) : List B :=
  let parsed := ProtoParse.parseCore d o a wire
  let candidate := SkippedKeys.lookupCore a (bytesAt a parsed 1) (bytesAt a parsed 33) slots
  let material := Symmetric.messageMaterialFast s (List.ofFn candidate.seed) (ChainSend.salt a present pqKey)
  let opened := ProtoReceive.openCore d o aes s a material.cipherKey material.iv material.macKey sender receiver wire expected
  finish a (a.and (OpenResult.get a opened 0) (ChainSend.flagMask a present)) parsed opened slots

section
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'} {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha in
theorem bytesAt_map (bytes : List B) (start : Nat) :
    f ∘ (bytesAt a bytes start : Fin n → B) = bytesAt a' (bytes.map f) start := by
  funext i; simp only [Function.comp_def, bytesAt, OpenResult.get_map ha]
include ha in
theorem finish_map (authentication : B) (parsed opened : List B) (slots : List (SkippedKeys.Slot B)) :
    (finish a authentication parsed opened slots).map f =
      finish a' (f authentication) (parsed.map f) (opened.map f) (slots.map (SkippedKeys.Slot.map f)) := by
  have h := SkippedKeys.consume_map ha authentication (bytesAt a parsed 1) (bytesAt a parsed 33) slots
  simp only [bytesAt_map ha] at h
  have hf := congrArg SkippedKeys.Candidate.found h
  have ht := congrArg SkippedKeys.Candidate.slots h
  simp only [SkippedKeys.Candidate.map] at hf ht
  simp only [finish, List.map_cons, List.map_append, SkippedKeys.storeBytes_map, ByteAuth.release_map ha, List.map_drop, hf, ht]
include hs in
theorem materialFast_map (seed salt : List B) :
    (Symmetric.messageMaterialFast s seed salt).map f = Symmetric.messageMaterialFast s' (seed.map f) (salt.map f) := by
  rw [Symmetric.messageMaterialFast_correct, Symmetric.messageMaterialFast_correct, Symmetric.messageMaterial_map hs]
include hd ho he hs ha in
theorem openCore_map (present : B) (pqKey sender receiver wire expected : List B) (slots : List (SkippedKeys.Slot B)) :
    (openCore d o aes s a present pqKey sender receiver wire expected slots).map f =
      openCore d' o' aes' s' a' (f present) (pqKey.map f) (sender.map f) (receiver.map f) (wire.map f) (expected.map f)
        (slots.map (SkippedKeys.Slot.map f)) := by
  have hl (parsed : List B) := congrArg SkippedKeys.Candidate.seed
    (SkippedKeys.lookup_map ha (bytesAt a parsed 1) (bytesAt a parsed 33) slots)
  simp only [SkippedKeys.Candidate.map, bytesAt_map ha] at hl
  have h (parsed : List B) := materialFast_map hs
    (List.ofFn (SkippedKeys.lookupCore a (bytesAt a parsed 1) (bytesAt a parsed 33) slots).seed) (ChainSend.salt a present pqKey)
  simp only [Symmetric.Material.map, List.map_ofFn, hl, ChainSend.salt_map ha] at h
  have hc parsed := congrArg Symmetric.Material.cipherKey (h parsed)
  have hm parsed := congrArg Symmetric.Material.macKey (h parsed)
  have hi parsed := congrArg Symmetric.Material.iv (h parsed)
  simp only at hc hm hi
  simp only [openCore, finish_map ha, ha.and, OpenResult.get_map ha, ChainSend.flagMask_map ha,
    ProtoReceive.openCore_map hd ho he hs ha, ProtoParse.parseCore_map hd ho ha, hc, hm, hi]
end

theorem finish_reject (parsed opened : List (BitVec 8)) (slots : List (SkippedKeys.Slot (BitVec 8))) :
    finish ByteAuth.concrete 0 parsed opened slots =
      0 :: (SkippedKeys.storeBytes slots ++ List.replicate (opened.drop 1).length 0) := by
  simp only [finish, SkippedKeys.failed_auth_preserves 0 _ _ _ (by decide : (0 : BitVec 8) ≠ 255), ByteAuth.release_reject]

theorem compiled_openCore_correct (present : BVExpr 8)
    (pqKey sender receiver wire expected : List (BVExpr 8)) (slots : List (SkippedKeys.Slot (BVExpr 8)))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      present pqKey sender receiver wire expected slots).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      present pqKey sender receiver wire expected slots))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
        present pqKey sender receiver wire expected slots))).vec.get index hi)) =
      (ByteCircuit.joinValue (openCore VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        (BVExpr.eval assign present) (pqKey.map (BVExpr.eval assign)) (sender.map (BVExpr.eval assign))
        (receiver.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign)) (expected.map (BVExpr.eval assign))
        (slots.map (SkippedKeys.Slot.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, openCore_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.SkippedReceive
