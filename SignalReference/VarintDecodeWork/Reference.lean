import VarintDecodeWork.Generated.spqr.Funs
import TlsMpc.Signal.VarintDecode.Spec

namespace LibSignalReference.Candidate.VarintDecode

open Aeneas Aeneas.Std TlsMpc
open TlsMpc.Signal.VarintDecode

set_option maxHeartbeats 2000000

def contents (bytes : Slice U8) : List (BitVec 8) := bytes.val.map UScalar.bv

theorem zero_add (i : Usize) : (0#usize + i : Result Usize) = .ok i := by
  have hb : (0#usize).val + i.val ≤ Usize.max := by scalar_tac
  obtain ⟨x, hx, hv⟩ := WP.spec_imp_exists (Usize.add_spec hb)
  have he : x = i := by scalar_tac
  simpa [he] using hx

theorem sub_zero (i : Usize) : (i - 0#usize : Result Usize) = .ok i := by
  obtain ⟨x, hx, hv⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i) (y := 0#usize) (by scalar_tac))
  have he : x = i := by scalar_tac
  simpa [he] using hx

theorem cast_index (i : Usize) (hi : i.val < 10) :
    (UScalar.hcast .I32 i).val = i.val := by
  have h := UScalar.hcast_inBounds_spec .I32 i (by scalar_tac : (i.val : Int) ≤ IScalar.max .I32)
  simpa only [lift, WP.spec_ok] using h

theorem payload_step (byte : U8) (i : Usize) (hi : i.val < 10) :
    (do
      let amount ← 7#i32 * UScalar.hcast .I32 i
      (UScalar.cast .U64 byte &&& 127#u64) <<< amount) =
      .ok (⟨Spqr.payload byte.bv i.val⟩ : U64) := by
  have hc := cast_index i hi
  obtain ⟨amount, ha, hv⟩ := WP.spec_imp_exists
    (I32.mul_spec (x := 7#i32) (y := UScalar.hcast .I32 i) (by scalar_tac) (by scalar_tac))
  rw [ha]
  simp only [bind_tc_ok]
  have hva : amount.val = 7 * (i.val : Int) := by scalar_tac
  have hn : amount.toNat = 7 * i.val := by
    simp only [IScalar.toNat, hva]
    rfl
  change UScalar.shiftLeft_IScalar _ amount = _
  simp only [UScalar.shiftLeft_IScalar, hva, Nat.cast_nonneg, Nat.ofNat_nonneg,
    Int.mul_nonneg, ge_iff_le, if_true, hn, UScalar.shiftLeft]
  have hs : 7 * i.val < UScalarTy.U64.numBits := by change 7 * i.val < 64; omega
  rw [if_pos hs]
  rfl

theorem loop_body_continue (bytes : Slice U8) (i maxIndex : Usize)
    (hi : i.val < maxIndex.val) (hm : maxIndex.val ≤ 10)
    (hlen : maxIndex.val ≤ bytes.length) (value : U64) :
    ∃ nextIndex,
      _root_.SpqrVarintDecode.decode_varint_loop.body bytes 0#usize maxIndex value i false =
        .ok (.cont ((⟨value.bv ||| Spqr.payload ((contents bytes)[i.val]?.getD 0) i.val⟩ : U64),
          nextIndex, Spqr.terminates ((contents bytes)[i.val]?.getD 0))) ∧
      nextIndex.val = i.val + 1 := by
  obtain ⟨byte, hbyte, hv⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec bytes i (by omega : i.val < bytes.length))
  obtain ⟨nextIndex, hnext, hnv⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
  refine ⟨nextIndex, ?_, by simpa using hnv⟩
  have hib : i < maxIndex := hi
  have hp := payload_step byte i (by omega : i.val < 10)
  have hil : i.val < bytes.val.length := by change i.val < bytes.length; omega
  have hb : (contents bytes)[i.val]?.getD 0 = byte.bv := by
    simp only [contents, List.getElem?_map, List.getElem?_eq_getElem hil,
      Option.map_some, Option.getD_some, hv]
  rw [_root_.SpqrVarintDecode.decode_varint_loop.body, if_pos hib]
  simp only [Bool.false_eq_true, if_false, zero_add, bind_tc_ok, hbyte, lift]
  rw [← bind_assoc_eq, hp]
  simp only [bind_tc_ok, hnext]
  rw [hb]
  have hterm : byte &&& 128#u8 = 0#u8 ↔ byte.bv &&& 128 = 0 := by
    constructor
    · intro h; exact congrArg UScalar.bv h
    · intro h; apply UScalar.eq_of_val_eq; exact congrArg BitVec.toNat h
  simp only [Spqr.terminates, hterm]
  rfl

def loopState (result : U64 × Usize × Bool) : Spqr.State :=
  ⟨result.1.bv, result.2.1.val, result.2.2⟩

/-- Every actual loop operation succeeds within the public prefix bound;
the comparison, value and consumed index are still arbitrary secret data. -/
theorem loop_reference (bytes : Slice U8) (maxIndex i : Usize)
    (hi : i.val ≤ maxIndex.val) (hm : maxIndex.val ≤ 10)
    (hlen : maxIndex.val ≤ bytes.length) (value : U64) (done : Bool) :
    ∃ result,
      _root_.SpqrVarintDecode.decode_varint_loop bytes 0#usize value i done maxIndex = .ok result ∧
      loopState result = Spqr.run (contents bytes) (maxIndex.val - i.val) i.val value.bv done := by
  generalize hf : maxIndex.val - i.val = fuel
  induction fuel generalizing i value done with
  | zero =>
      have hge : ¬i < maxIndex := by change ¬i.val < maxIndex.val; omega
      refine ⟨(value, i, done), ?_, rfl⟩
      unfold _root_.SpqrVarintDecode.decode_varint_loop
      rw [loop]
      simp [_root_.SpqrVarintDecode.decode_varint_loop.body, hge]
  | succ fuel ih =>
      have hit : i.val < maxIndex.val := by omega
      have hlt : i < maxIndex := hit
      cases done with
      | true =>
          refine ⟨(value, i, true), ?_, rfl⟩
          unfold _root_.SpqrVarintDecode.decode_varint_loop
          rw [loop]
          simp [_root_.SpqrVarintDecode.decode_varint_loop.body, hlt]
      | false =>
          obtain ⟨nextIndex, hbody, hnext⟩ := loop_body_continue bytes i maxIndex hit hm hlen value
          obtain ⟨result, hresult, hstate⟩ := ih nextIndex (by omega)
            (⟨value.bv ||| Spqr.payload ((contents bytes)[i.val]?.getD 0) i.val⟩ : U64)
            (Spqr.terminates ((contents bytes)[i.val]?.getD 0)) (by omega)
          refine ⟨result, ?_, ?_⟩
          · unfold _root_.SpqrVarintDecode.decode_varint_loop
            rw [loop]
            dsimp only
            rw [hbody]
            simpa only [bind_tc_ok, _root_.SpqrVarintDecode.decode_varint_loop] using hresult
          · simpa only [Spqr.run, Bool.false_eq_true, if_false, hnext] using hstate

def Matches (state : Spqr.State) (result : core.result.Result U64 _root_.SpqrVarintDecode.Error)
    (cursor : Usize) : Prop :=
  if state.done then result = .Ok ⟨state.value⟩ ∧ cursor.val = state.index
  else result = .Err .MsgDecode ∧ cursor = 0#usize

/-- Full actual prefix operation at start0. The only size bound is the Slice
model's own length≤Usize.max. Results/errors and the updated cursor are exact. -/
theorem decode_reference (bytes : Slice U8) :
    ∃ result cursor,
      _root_.SpqrVarintDecode.decode_varint bytes 0#usize = .ok (result, cursor) ∧
      Matches (Spqr.decode (contents bytes)) result cursor := by
  by_cases hz : bytes.length = 0
  · refine ⟨.Err .MsgDecode, 0#usize, ?_, ?_⟩
    · unfold _root_.SpqrVarintDecode.decode_varint
      have h : 0#usize ≥ Slice.len bytes := by change 0 ≥ bytes.length; omega
      simp only [if_pos h]
    · simp [Matches, Spqr.decode, contents, hz, Spqr.run, Slice.length] at *
  · let maxIndex := core.cmp.impls.OrdUsize.min 10#usize (Slice.len bytes)
    have hm : maxIndex.val = min 10 bytes.length := by simp [maxIndex]
    obtain ⟨⟨value, cursor, done⟩, hloop, hstate⟩ := loop_reference bytes maxIndex 0#usize
      (by scalar_tac) (by omega) (by omega) 0#u64 false
    have hs : loopState (value, cursor, done) = Spqr.decode (contents bytes) := by
      simpa [Spqr.decode, contents, hm, Slice.length] using hstate
    have hmin : core.cmp.min core.cmp.OrdUsize _root_.SpqrVarintDecode.MAX_VARINT_BYTES_LEN
        (Slice.len bytes) = .ok maxIndex := by
      with_unfolding_all rfl
    have hlt : ¬ 0#usize ≥ Slice.len bytes := by
      change ¬0 ≥ (Slice.len bytes).val
      simp only [Slice.len_val]
      omega
    have hd : _root_.SpqrVarintDecode.decode_varint bytes 0#usize =
        if done then .ok (.Ok value, cursor) else .ok (.Err .MsgDecode, 0#usize) := by
      unfold _root_.SpqrVarintDecode.decode_varint
      with_unfolding_all simp only [if_neg hlt, sub_zero, bind_tc_ok, hmin, hloop]
      cases done <;> simp [zero_add]
    cases done with
    | false =>
        refine ⟨.Err .MsgDecode, 0#usize, hd, ?_⟩
        rw [← hs]
        exact ⟨rfl, rfl⟩
    | true =>
        refine ⟨.Ok value, cursor, hd, ?_⟩
        rw [← hs]
        exact ⟨rfl, rfl⟩

def resultBytes (result : core.result.Result U64 _root_.SpqrVarintDecode.Error)
    (cursor : Usize) : List (BitVec 8) :=
  match result with
  | .Ok value => 255 :: BitVec.ofNat 8 cursor.val :: Spqr.valueBytes value.bv
  | .Err _ => List.replicate 10 0

theorem matches_bytes (state : Spqr.State) (result : core.result.Result U64 _root_.SpqrVarintDecode.Error)
    (cursor : Usize) (h : Matches state result cursor) :
    resultBytes result cursor = Spqr.encodeResult state := by
  unfold Matches at h
  unfold Spqr.encodeResult
  split at h <;> simp_all [resultBytes]

theorem decode_bytes_reference (bytes : Slice U8) :
    ∃ result cursor,
      _root_.SpqrVarintDecode.decode_varint bytes 0#usize = .ok (result, cursor) ∧
      Matches (Spqr.decode (contents bytes)) result cursor ∧
      resultBytes result cursor = Spqr.encodeResult (Spqr.decode (contents bytes)) := by
  obtain ⟨result, cursor, hd, hm⟩ := decode_reference bytes
  exact ⟨result, cursor, hd, hm, matches_bytes _ _ _ hm⟩

end LibSignalReference.Candidate.VarintDecode
