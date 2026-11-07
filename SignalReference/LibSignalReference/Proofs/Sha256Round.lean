import LibSignalReference.Generated.Sha256Round.Funs
import TlsMpc.Sha256
import TlsMpc.ByteCircuit

/-!
Refinement of the scalar round function actually extracted from sha2 0.11.0's
wasm32 SIMD backend. The selected function itself contains no SIMD operations.
This does not establish the compression loop, byte loading, buffering or HMAC.
-/

namespace LibSignalReference.Proofs.Sha256Round

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std
open TlsMpc.Sha256

def encodeState (s : State (BitVec 32)) : Array U32 8#usize :=
  ⟨[⟨s.a⟩, ⟨s.b⟩, ⟨s.c⟩, ⟨s.d⟩, ⟨s.e⟩, ⟨s.f⟩, ⟨s.g⟩, ⟨s.h⟩], by simp⟩

def decodeState (xs : Array U32 8#usize) : State (BitVec 32) :=
  ⟨(xs.val[0]'(by simp)).bv, (xs.val[1]'(by simp)).bv,
   (xs.val[2]'(by simp)).bv, (xs.val[3]'(by simp)).bv,
   (xs.val[4]'(by simp)).bv, (xs.val[5]'(by simp)).bv,
   (xs.val[6]'(by simp)).bv, (xs.val[7]'(by simp)).bv⟩

theorem decode_encode (s : State (BitVec 32)) : decodeState (encodeState s) = s := by
  cases s
  rfl

theorem encode_decode (xs : Array U32 8#usize) : encodeState (decodeState xs) = xs := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [encodeState]
  · intro i hi hj
    have hi8 : i < 8 := by simpa [encodeState] using hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem choose_alternative (e f g : BitVec 32) :
    g ^^^ (e &&& (f ^^^ g)) = (e &&& f) ^^^ ((~~~e) &&& g) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> decide

theorem round_spec (s : State (BitVec 32)) (k : Nat) (w : BitVec 32) :
    RustCryptoSha256Round.sha256.wasm32_simd128.sha_round
      (encodeState s) ⟨BitVec.ofNat 32 k + w⟩
      ⦃ result => result = encodeState (round concrete k w s) ⦄ := by
  unfold RustCryptoSha256Round.sha256.wasm32_simd128.sha_round
  simp [encodeState, Array.index_usize, Array.update, lift]
  apply Subtype.ext
  simp only [round, concrete, big0, big1, choose,
    majority, xor3,
    core.num.U32.wrapping_add, UScalar.wrapping_add,
    core.num.U32.rotate_right, UScalar.rotate_right]
  simp only [List.cons.injEq, and_true, true_and]
  constructor
  all_goals
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simp only [UScalar.bv_xor, UScalar.bv_and, UScalar.ofNatCore_val_eq]
    dsimp only [UScalarTy.numBits]
    rw [choose_alternative]
    ac_rfl

theorem round_all_arrays (xs : Array U32 8#usize) (x : U32) :
    RustCryptoSha256Round.sha256.wasm32_simd128.sha_round xs x
      ⦃ result => decodeState result = round concrete 0 x.bv (decodeState xs) ⦄ := by
  obtain ⟨result, hr, hresult⟩ := WP.spec_imp_exists (round_spec (decodeState xs) 0 x.bv)
  have hx : (⟨BitVec.ofNat 32 0 + x.bv⟩ : U32) = x := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    change 0 + x.bv = x.bv
    exact BitVec.zero_add _
  rw [encode_decode, hx] at hr
  rw [hr, WP.spec_ok]
  rw [hresult, decode_encode]

def symbolicRoundBytes (k : Nat) (w : _root_.Std.Tactic.BVDecide.BVExpr 32)
    (s : State (_root_.Std.Tactic.BVDecide.BVExpr 32)) :=
  digest symbolic (round symbolic k w s)

theorem round_refines_artifact
    (k : Nat) (w : _root_.Std.Tactic.BVDecide.BVExpr 32)
    (s : State (_root_.Std.Tactic.BVDecide.BVExpr 32))
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment) :
    ∃ result,
      RustCryptoSha256Round.sha256.wasm32_simd128.sha_round
        (encodeState (s.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign)))
        ⟨BitVec.ofNat 32 k + w.eval assign⟩ = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * (symbolicRoundBytes k w s).length),
        TlsMpc.AigExport.evalRef
          (TlsMpc.AigExport.exportNodes (TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr (symbolicRoundBytes k w s))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (TlsMpc.AigExport.exportRef ((TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr (symbolicRoundBytes k w s))).vec.get index hi)) =
        (TlsMpc.ByteCircuit.joinValue (digest concrete (decodeState result))).getLsbD index := by
  obtain ⟨result, hr, hresult⟩ := WP.spec_imp_exists
    (round_spec (s.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign)) k (w.eval assign))
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [TlsMpc.ByteCircuit.compile_bytes_correct]
  rw [hresult, decode_encode]
  unfold symbolicRoundBytes
  rw [digest_map (evaluationHom assign), round_map (evaluationHom assign)]

end LibSignalReference.Proofs.Sha256Round
