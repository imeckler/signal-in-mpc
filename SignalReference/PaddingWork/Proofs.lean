import PaddingWork.Generated.ExcludeArraySize.Funs
import TlsMpc.Signal.Cbc

namespace SignalReference.PaddingWork

open Aeneas Aeneas.Std

def padByte (count : Nat) : U8 := ⟨BitVec.ofNat 8 count⟩

theorem raw_pad_spec (block : Slice U8) (pos : Usize)
    (hsize : block.length ≤ 255) (hpos : pos.val < block.length) :
    RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad block pos
      ⦃ result => result.val = block.val.take pos.val ++
          List.replicate (block.length - pos.val) (padByte (block.length - pos.val)) ⦄ := by
  unfold RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad
  step*
  have hn : n = padByte (block.length - pos.val) := by
    apply UScalar.eq_of_val_eq
    rw [n_post, UScalar.cast_val_eq]
    change i3.val % 256 = (block.length - pos.val) % 256
    rw [i3_post1, Slice.len_val]
  rw [s_post3, s1_post2, s_post2, hn]
  simp [List.setSlice!, Slice.length]
  omega

theorem raw_pad_too_large (block : Slice U8) (pos : Usize)
    (hsize : 255 < block.length) :
    RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad block pos =
      .fail .assertionFailure := by
  have h : block.len > 255#usize := by scalar_tac
  simp [RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad, h, massert]

theorem raw_pad_pos_out_of_bounds (block : Slice U8) (pos : Usize)
    (hpos : block.length ≤ pos.val) :
    RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad block pos =
      .fail .assertionFailure := by
  by_cases hsize : 255 < block.length
  · exact raw_pad_too_large block pos hsize
  have hs : ¬block.len > 255#usize := by scalar_tac
  have hp : pos ≥ block.len := by scalar_tac
  simp [RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad, hs, hp, massert]

theorem raw_pad_total (block : Slice U8) (pos : Usize) :
    if block.length ≤ 255 ∧ pos.val < block.length then
      ∃ result, RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad block pos = .ok result ∧
        result.val = block.val.take pos.val ++
          List.replicate (block.length - pos.val) (padByte (block.length - pos.val))
    else RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad block pos =
      .fail .assertionFailure := by
  split
  · rename_i h
    exact WP.spec_imp_exists (raw_pad_spec block pos h.1 h.2)
  · rename_i h
    by_cases hs : block.length ≤ 255
    · exact raw_pad_pos_out_of_bounds block pos (by omega)
    · exact raw_pad_too_large block pos (by omega)

/-- The final AES block padding in the CBC circuit equals the actual translated
    RustCrypto operation, for every byte value and every valid tail length. -/
theorem cbc_pad_refines_raw_pad (block : Slice U8) (pos : Usize)
    (hsize : block.length = 16) (hpos : pos.val < 16) :
    ∃ result, RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad block pos = .ok result ∧
      result.val.map (fun byte => byte.bv) =
        TlsMpc.Signal.Cbc.pad TlsMpc.Aes.concrete
          ((block.val.take pos.val).map (fun byte => byte.bv)) := by
  obtain ⟨result, hr, hv⟩ := WP.spec_imp_exists
    (raw_pad_spec block pos (by omega) (by omega))
  refine ⟨result, hr, ?_⟩
  rw [hv]
  have ht : (block.val.take pos.val).length = pos.val := by
    rw [List.length_take]
    change min pos.val block.length = pos.val
    omega
  simp only [List.map_append, List.map_replicate, TlsMpc.Signal.Cbc.pad,
    List.length_map, ht, Nat.mod_eq_of_lt hpos, hsize]
  rfl

/-- No secret bytes are opened by the bridge. The symbolic byte expressions
    may have any assignment equal to the selected Rust slice prefix. -/
theorem cbc_pad_refines_artifact (block : Slice U8) (pos : Usize)
    (hsize : block.length = 16) (hpos : pos.val < 16)
    (secret : List (_root_.Std.Tactic.BVDecide.BVExpr 8))
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) =
      (block.val.take pos.val).map (fun byte => byte.bv)) :
    ∃ result, RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad block pos = .ok result ∧
      ∀ (index : Nat)
        (hi : index < 8 * (TlsMpc.Signal.Cbc.pad TlsMpc.Aes.symbolic secret).length),
        TlsMpc.AigExport.evalRef
          (TlsMpc.AigExport.exportNodes (TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr (TlsMpc.Signal.Cbc.pad TlsMpc.Aes.symbolic secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (TlsMpc.AigExport.exportRef ((TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr (TlsMpc.Signal.Cbc.pad TlsMpc.Aes.symbolic secret))).vec.get index hi)) =
          (TlsMpc.ByteCircuit.joinValue (result.val.map (fun byte => byte.bv))).getLsbD index := by
  obtain ⟨result, hr, hv⟩ := cbc_pad_refines_raw_pad block pos hsize hpos
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [TlsMpc.ByteCircuit.compile_bytes_correct,
    TlsMpc.Signal.Cbc.pad_map (TlsMpc.Aes.evaluationHom assign), hsecret, hv]

theorem cbc_pad_append (o : TlsMpc.Aes.Ops B) (fullBlocks tail : List B)
    (hblocks : fullBlocks.length % 16 = 0) :
    TlsMpc.Signal.Cbc.pad o (fullBlocks ++ tail) =
      fullBlocks ++ TlsMpc.Signal.Cbc.pad o tail := by
  simp [TlsMpc.Signal.Cbc.pad, List.length_append, Nat.add_mod, hblocks, List.append_assoc]

/-- Complete message padding consists of unchanged full blocks followed by the
    translated final-block operation. This also covers an empty final tail. -/
theorem cbc_message_pad_refines_artifact (block : Slice U8) (pos : Usize)
    (hsize : block.length = 16) (hpos : pos.val < 16)
    (fullBlocks secret : List (_root_.Std.Tactic.BVDecide.BVExpr 8))
    (hblocks : fullBlocks.length % 16 = 0)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) =
      (block.val.take pos.val).map (fun byte => byte.bv)) :
    ∃ result, RustCryptoPadding.Pkcs7.Insts.Block_paddingPadding.raw_pad block pos = .ok result ∧
      ∀ (index : Nat)
        (hi : index < 8 * (TlsMpc.Signal.Cbc.pad TlsMpc.Aes.symbolic (fullBlocks ++ secret)).length),
        TlsMpc.AigExport.evalRef
          (TlsMpc.AigExport.exportNodes (TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr
              (TlsMpc.Signal.Cbc.pad TlsMpc.Aes.symbolic (fullBlocks ++ secret)))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (TlsMpc.AigExport.exportRef ((TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr
              (TlsMpc.Signal.Cbc.pad TlsMpc.Aes.symbolic (fullBlocks ++ secret)))).vec.get index hi)) =
          (TlsMpc.ByteCircuit.joinValue
            (fullBlocks.map (_root_.Std.Tactic.BVDecide.BVExpr.eval assign) ++
              result.val.map (fun byte => byte.bv))).getLsbD index := by
  obtain ⟨result, hr, hv⟩ := cbc_pad_refines_raw_pad block pos hsize hpos
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [TlsMpc.ByteCircuit.compile_bytes_correct,
    TlsMpc.Signal.Cbc.pad_map (TlsMpc.Aes.evaluationHom assign), List.map_append,
    cbc_pad_append _ _ _ (by simpa using hblocks), hsecret, hv]

end SignalReference.PaddingWork
