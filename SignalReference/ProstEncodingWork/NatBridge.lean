import ProstEncodingWork.Reference
import TlsMpc.Signal.Varint

namespace LibSignalReference.Candidate.ProstEncoding

open Aeneas Aeneas.Std
open _root_.ProstEncoding
open TlsMpc

set_option maxHeartbeats 2000000

theorem cast_byte (value : U64) :
    U8.bv (UScalar.cast .U8 value) = BitVec.ofNat 8 value.val := by rfl

theorem continuation_byte (value : U64) :
    U8.bv (UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64)) =
      BitVec.ofNat 8 (value.val % 128 + 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [U8.bv, UScalar.cast_bv_eq, UScalar.bv_or, UScalar.bv_and]
  have hm : value.val &&& 127 = value.val % 128 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod value.val 7
  have ho : (value.val % 128) ||| 128 = value.val % 128 + 128 := by
    have hh := Nat.two_pow_add_eq_or_of_lt (i := 7) (by omega : value.val % 128 < 2^7) 1
    simpa [Nat.or_comm, Nat.add_comm] using hh.symm
  change ((value.val &&& 127) ||| 128) % 256 = (value.val % 128 + 128) % 256
  rw [hm, ho]

theorem shifted_value (value : U64) :
    (⟨value.bv >>> 7⟩ : U64).val = value.val / 128 := by
  change (value.bv >>> 7).toNat = value.bv.toNat / 128
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A contract for a supplied buffer dictionary, not an axiom or a replacement
for its implementation. The concrete Vec proof discharges the bounded form. -/
def Appends (put : B → U8 → Result B) (contents : B → List (BitVec 8)) : Prop :=
  ∀ (buf : B) (byte : U8), ∃ after,
    put buf byte = .ok after ∧ contents after = contents buf ++ [byte.bv]

theorem run_appends (put : B → U8 → Result B) (contents : B → List (BitVec 8))
    (contract : Appends put contents) (fuel : Nat) (value : U64) (buf : B) :
    ∃ after, run put fuel value buf = .ok after ∧
      contents after = contents buf ++ Signal.Varint.publicNatLoop ByteAuth.concrete fuel value.val := by
  induction fuel generalizing value buf with
  | zero => exact ⟨buf, rfl, by simp [Signal.Varint.publicNatLoop]⟩
  | succ fuel ih =>
    by_cases hv : value < 128#u64
    · obtain ⟨after, ha, hc⟩ := contract buf (UScalar.cast .U8 value)
      refine ⟨after, ?_, ?_⟩
      · simpa only [run, if_pos hv] using ha
      · have hval : value.val < 128 := hv
        simpa only [Signal.Varint.publicNatLoop, if_pos hval, ByteAuth.concrete, cast_byte] using hc
    · obtain ⟨next, hn, hc⟩ := contract buf
        (UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64))
      obtain ⟨after, ha, hc'⟩ := ih ⟨value.bv >>> 7⟩ next
      refine ⟨after, ?_, ?_⟩
      · simp only [run, if_neg hv, hn, bind_tc_ok, shift_seven, ha]
      · have hval : ¬ value.val < 128 := hv
        rw [hc', hc]
        rw [continuation_byte value, shifted_value value]
        simp only [Signal.Varint.publicNatLoop, if_neg hval, ByteAuth.concrete,
          List.append_assoc, List.singleton_append]

theorem encode_appends (dictionary : bytes.buf.buf_mut.BufMut B)
    (contents : B → List (BitVec 8)) (contract : Appends dictionary.put_u8 contents)
    (value : U64) (buf : B) :
    ∃ after, encoding.varint.encode_varint dictionary value buf = .ok after ∧
      contents after = contents buf ++ Signal.Varint.publicNat ByteAuth.concrete value.val := by
  rw [encode_eq_run]
  exact run_appends dictionary.put_u8 contents contract 10 value buf

def AppendsWithin (put : B → U8 → Result B) (contents : B → List (BitVec 8))
    (maximum : Nat) : Prop :=
  ∀ (buf : B) (byte : U8), (contents buf).length < maximum →
    ∃ after, put buf byte = .ok after ∧ contents after = contents buf ++ [byte.bv]

theorem run_appends_within (put : B → U8 → Result B) (contents : B → List (BitVec 8))
    (maximum : Nat) (contract : AppendsWithin put contents maximum)
    (fuel : Nat) (value : U64) (buf : B) (hsize : (contents buf).length + fuel ≤ maximum) :
    ∃ after, run put fuel value buf = .ok after ∧
      contents after = contents buf ++ Signal.Varint.publicNatLoop ByteAuth.concrete fuel value.val := by
  induction fuel generalizing value buf with
  | zero => exact ⟨buf, rfl, by simp [Signal.Varint.publicNatLoop]⟩
  | succ fuel ih =>
    have hroom : (contents buf).length < maximum := by omega
    by_cases hv : value < 128#u64
    · obtain ⟨after, ha, hc⟩ := contract buf (UScalar.cast .U8 value) hroom
      refine ⟨after, ?_, ?_⟩
      · simpa only [run, if_pos hv] using ha
      · have hval : value.val < 128 := hv
        simpa only [Signal.Varint.publicNatLoop, if_pos hval, ByteAuth.concrete, cast_byte] using hc
    · obtain ⟨next, hn, hc⟩ := contract buf
        (UScalar.cast .U8 ((value &&& 127#u64) ||| 128#u64)) hroom
      have hnsize : (contents next).length + fuel ≤ maximum := by
        rw [hc]
        simp only [List.length_append, List.length_singleton]
        omega
      obtain ⟨after, ha, hc'⟩ := ih ⟨value.bv >>> 7⟩ next hnsize
      refine ⟨after, ?_, ?_⟩
      · simp only [run, if_neg hv, hn, bind_tc_ok, shift_seven, ha]
      · have hval : ¬ value.val < 128 := hv
        rw [hc', hc, continuation_byte value, shifted_value value]
        simp only [Signal.Varint.publicNatLoop, if_neg hval, ByteAuth.concrete,
          List.append_assoc, List.singleton_append]

theorem encode_appends_within (dictionary : bytes.buf.buf_mut.BufMut B)
    (contents : B → List (BitVec 8)) (maximum : Nat)
    (contract : AppendsWithin dictionary.put_u8 contents maximum)
    (value : U64) (buf : B) (hsize : (contents buf).length + 10 ≤ maximum) :
    ∃ after, encoding.varint.encode_varint dictionary value buf = .ok after ∧
      contents after = contents buf ++ Signal.Varint.publicNat ByteAuth.concrete value.val := by
  rw [encode_eq_run]
  exact run_appends_within dictionary.put_u8 contents maximum contract 10 value buf hsize

end LibSignalReference.Candidate.ProstEncoding
