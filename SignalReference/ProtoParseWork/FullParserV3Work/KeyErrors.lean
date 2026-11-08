import ProtoParseWork.FullParserV3Work.ErrorProjection
import ProtoParseWork.FullParserV3Work.KeyCircuit
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem classify_invalid_range (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hk : key.ok = 255) (hr : 4294967295 < key.value.toNat) :
    classify Word64.concrete ByteAuth.concrete key payload state = ⟨2,key.value⟩ := by
  have hn : key.value.toNat &&& 7 = key.value.toNat % 8 := kind_nat key.value
  dsimp only [classify]
  rw [hk]
  change _ = _
  simp only [show Word64.concrete.const = BitVec.ofNat 64 from rfl,
    show Word64.concrete.band = (fun x y => x &&& y) from rfl,
    show Word64.concrete.shift = (fun x n => x >>> n) from rfl]
  simp [hn,Word64.select_accept,Word64.ule_value,show ¬key.value.toNat ≤ 4294967295 by omega,
    if_false,Word64.select_reject]
  simp [Word64.concrete,ByteAuth.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl,BitVec.allOnes_and]

theorem classify_invalid_wire (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hr : key.value.toNat ≤ 4294967295) (hw : 5 < key.value.toNat % 8) :
    classify Word64.concrete ByteAuth.concrete key payload state = ⟨3,key.value &&& 7⟩ := by
  have hn : key.value.toNat &&& 7 = key.value.toNat % 8 := kind_nat key.value
  dsimp only [classify]
  rw [hk]
  change _ = _
  simp only [show Word64.concrete.const = BitVec.ofNat 64 from rfl,
    show Word64.concrete.band = (fun x y => x &&& y) from rfl,
    show Word64.concrete.shift = (fun x n => x >>> n) from rfl]
  simp [hn,Word64.select_accept,Word64.ule_value,hr,if_true,kind_nat,
    show ¬key.value.toNat % 8 ≤ 5 by omega,if_false,Word64.select_reject]
  simp [Word64.concrete,ByteAuth.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl,BitVec.allOnes_and]

theorem classify_invalid_tag (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hr : key.value.toNat ≤ 4294967295) (hw : key.value.toNat % 8 ≤ 5)
    (ht : key.value.toNat < 8) :
    classify Word64.concrete ByteAuth.concrete key payload state = ⟨4,0⟩ := by
  have hn : key.value.toNat &&& 7 = key.value.toNat % 8 := kind_nat key.value
  dsimp only [classify]
  rw [hk]
  have hz : Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.shift key.value 3) (Word64.concrete.const 0) = 255 := by
    rw [word_eq_value]; exact if_pos ((shift_zero key.value).mpr ht)
  simp only [hz]
  change _ = _
  simp only [show Word64.concrete.const = BitVec.ofNat 64 from rfl,
    show Word64.concrete.band = (fun x y => x &&& y) from rfl,
    show Word64.concrete.shift = (fun x n => x >>> n) from rfl]
  simp [hn,Word64.select_accept,Word64.ule_value,hr,if_true,kind_nat,hw,
    word_eq_value,show key.value >>> 3 = 0 from (shift_zero key.value).mpr ht]

  simp [Word64.concrete,ByteAuth.concrete]

/-- Validation failures preserve the complete actual Rust constructor and
parameter, independently of payload decodes or preexisting message state. -/
theorem key_validation_error (value : U64) (error : LoopSupportSkip.error.DecodeError)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hk : key.ok = 255) (hv : key.value = value.bv)
    (he : keyResult value = .Err error) :
    statusView (.Err (SignalMessageIntegration.skipError error)) =
      some (classify Word64.concrete ByteAuth.concrete key payload state) := by
  by_cases hr : 4294967295 < value.val
  · simp only [keyResult,if_pos hr] at he
    cases he
    rw [classify_invalid_range key payload state hk (by simpa only [hv,UScalar.bv_toNat] using hr)]
    rw [hv]; rfl
  · have hb : value.val ≤ 4294967295 := by omega
    by_cases hw : 5 < value.val % 8
    · have hw' : 5 < (kindOf value).val := by simpa only [kind_value] using hw
      simp only [keyResult,if_neg hr,wire_error _ hw'] at he
      cases he
      rw [classify_invalid_wire key payload state hk (by simpa only [hv,UScalar.bv_toNat] using hb)
        (by simpa only [hv,UScalar.bv_toNat] using hw)]
      rw [hv]; rfl
    · have hkind : value.val % 8 ≤ 5 := by omega
      obtain ⟨kind,hwire⟩ := (wire_exists (kindOf value)).mpr (by rw [kind_value]; exact hkind)
      simp only [keyResult,if_neg hr,hwire] at he
      by_cases ht : (tagOf value).val < 1
      · simp only [if_pos ht] at he
        cases he
        have ht' : value.val < 8 := by rw [tag_value value hb] at ht; omega
        rw [classify_invalid_tag key payload state hk (by simpa only [hv,UScalar.bv_toNat] using hb)
          (by simpa only [hv,UScalar.bv_toNat] using hkind) (by simpa only [hv,UScalar.bv_toNat] using ht')]
        rfl
      · simp only [if_neg ht] at he
        cases he

/-- Actual full decode_key rejection agrees with private constructor/payload
metadata. This covers both varint dispatch paths and all key checks, with no
assumed decoder correctness or success-only restriction. -/
theorem actual_key_error (bytes after : Slice U8) (error : LoopSupportSkip.error.DecodeError)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hd : LoopSupportSkip.encoding.decode_key LibSignalReference.Candidate.ProstSkipBuf.sliceBuf bytes =
      .ok (.Err error,after)) :
    statusView (.Err (SignalMessageIntegration.skipError error)) = some (classify
      Word64.concrete ByteAuth.concrete
      (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (LibSignalReference.Candidate.ProstSkipSlice.contents bytes) 0) payload state) := by
  obtain ⟨result,remaining,_,hp,_,hk⟩ := decode_key_reference bytes
  rw [hd] at hk
  have he := congrArg Prod.fst (Result.ok.inj hk)
  cases result with
  | Err e =>
    have herr : e = error := by simpa only [finishResult,core.result.Result.Err.injEq] using he.symm
    subst error
    obtain ⟨rfl,hmask⟩ := hp
    rw [key_varint_error _ _ _ hmask]
    rfl
  | Ok value =>
    obtain ⟨count,_,_,hprefix,_⟩ := hp
    have hv : keyResult value = .Err error := he.symm
    exact key_validation_error value error _ payload state
      (by rw [hprefix]) (by rw [hprefix]) hv

#print axioms actual_key_error
#print axioms key_validation_error

#print axioms classify_invalid_range
#print axioms classify_invalid_wire
#print axioms classify_invalid_tag
end FullParserV3.Observed
