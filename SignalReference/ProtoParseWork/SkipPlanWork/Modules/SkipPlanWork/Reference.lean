import SkipPlanWork.Fixed
import SkipTranslatorWork.SkipLeaf

namespace LibSignalReference.Candidate.ProstSkipPlan
open TlsMpc TlsMpc.Signal Aeneas Aeneas.Std LoopSupportSkip
open LibSignalReference.Candidate.ProstSkip LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 500000

/-- Exact actual-Rust outcome versus the existing numeric parser's fixed64 mask.
The byte slice starts after the key, within a group whose depth is below100. -/
theorem actual_fixed64_plan (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (bytes : Slice U8) (tag count : U32)
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 1)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hcount : count ≠ 0#u32) (hstart : key.stop.toNat ≤ capacity) (hcap : capacity ≤ 512)
    (hlen : bytes.length = capacity - key.stop.toNat) :
    encoding.skip_field sliceBuf .SixtyFourBit tag bytes ⟨count⟩ =
      .ok (if (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 255
        then (.Ok (),drop bytes 8) else (.Err (decodeError .BufferUnderflow),bytes)) := by
  rw [fixed64_reference _ _ _ hcount,
    fixed64_in_group _ _ _ _ hkey hvalue htag hkind hdepth hlimit]
  have hb := fixed_bounds key.stop capacity 8 hstart hcap (by decide)
  change Word64.concrete.ule (key.stop + 8) (BitVec.ofNat 64 capacity) = _ at hb
  rw [hb]
  unfold fixedResult
  by_cases h : 8 ≤ capacity - key.stop.toNat
  · simp [h,hlen,Nat.not_lt.mpr h]
  · have hh : capacity - key.stop.toNat < 8 := by omega
    simp [h,hlen,hh]

/-- Exact actual-Rust outcome versus the existing numeric parser's fixed32 mask.
The byte slice starts after the key, within a group whose depth is below100. -/
theorem actual_fixed32_plan (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (bytes : Slice U8) (tag count : U32)
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 5)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hcount : count ≠ 0#u32) (hstart : key.stop.toNat ≤ capacity) (hcap : capacity ≤ 512)
    (hlen : bytes.length = capacity - key.stop.toNat) :
    encoding.skip_field sliceBuf .ThirtyTwoBit tag bytes ⟨count⟩ =
      .ok (if (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 255
        then (.Ok (),drop bytes 4) else (.Err (decodeError .BufferUnderflow),bytes)) := by
  rw [fixed32_reference _ _ _ hcount,
    fixed32_in_group _ _ _ _ hkey hvalue htag hkind hdepth hlimit]
  have hb := fixed_bounds key.stop capacity 4 hstart hcap (by decide)
  change Word64.concrete.ule (key.stop + 4) (BitVec.ofNat 64 capacity) = _ at hb
  rw [hb]
  unfold fixedResult
  by_cases h : 4 ≤ capacity - key.stop.toNat
  · simp [h,hlen,Nat.not_lt.mpr h]
  · have hh : capacity - key.stop.toNat < 4 := by omega
    simp [h,hlen,hh]


/-- Length-delimited success and underflow preserve the exact post-varint suffix. -/
theorem actual_length_plan (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (value : U64) (tag count : U32)
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 2)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hcount : count ≠ 0#u32) (hstart : payload.stop.toNat ≤ capacity) (hcap : capacity ≤ 512)
    (hlen : after.length = capacity - payload.stop.toNat)
    (hpayload : payload.ok = 255) (hdecoded : payload.value.toNat = value.val)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
    encoding.skip_field sliceBuf .LengthDelimited tag before ⟨count⟩ =
      .ok (if (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 255
        then (.Ok (),drop after value.val) else (.Err (decodeError .BufferUnderflow),after)) := by
  rw [length_delimited_after _ _ _ _ _ hcount hdecode,
    length_in_group _ _ _ _ hkey hvalue htag hkind hdepth hlimit,hpayload]
  have hb := length_bounds payload.stop payload.value capacity hstart hcap
  rw [hb]
  simp only [show (255 : BitVec 8) = BitVec.allOnes 8 by rfl,BitVec.allOnes_and,hdecoded]
  unfold fixedResult
  by_cases h : value.val ≤ capacity - payload.stop.toNat
  · simp [h,hlen,Nat.not_lt.mpr h]
  · have hh : capacity - payload.stop.toNat < value.val := by omega
    simp [h,hlen,hh]

/-- A successfully decoded varint has no further payload bytes to skip. -/
theorem actual_varint_plan (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (value : U64) (tag count : U32)
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 0)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hcount : count ≠ 0#u32) (hpayload : payload.ok = 255)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 255 ∧
    encoding.skip_field sliceBuf .Varint tag before ⟨count⟩ = .ok (.Ok (),after) := by
  constructor
  · rw [varint_in_group _ _ _ _ hkey hvalue htag hkind hdepth hlimit,hpayload]
  · exact skip_varint_after _ _ _ _ _ hcount hdecode


theorem actual_varint_error_plan (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (error : error.DecodeError) (tag count : U32)
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 0)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hcount : count ≠ 0#u32) (hpayload : payload.ok = 0)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 ∧
    encoding.skip_field sliceBuf .Varint tag before ⟨count⟩ = .ok (.Err error,after) := by
  constructor
  · rw [varint_in_group _ _ _ _ hkey hvalue htag hkind hdepth hlimit,hpayload]
  · exact skip_varint_error _ _ _ _ _ hcount hdecode

theorem actual_length_error_plan (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (error : error.DecodeError) (tag count : U32)
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 2)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hcount : count ≠ 0#u32) (hpayload : payload.ok = 0)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 ∧
    encoding.skip_field sliceBuf .LengthDelimited tag before ⟨count⟩ = .ok (.Err error,after) := by
  constructor
  · rw [length_in_group _ _ _ _ hkey hvalue htag hkind hdepth hlimit,hpayload]
    exact BitVec.zero_and
  · exact length_delimited_error _ _ _ _ _ hcount hdecode

/-- A non-closing child at depth100 reaches the actual zero-count limit before
reading its payload. Closing tags belong to the parent group body instead. -/
theorem actual_limit_plan (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (bytes : Slice U8)
    (tag : U32) (kind : encoding.wire_type.WireType)
    (hdepth : state.depth.toNat = 100) (hkind : key.value &&& 7 ≠ 4) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 ∧
    encoding.skip_field sliceBuf kind tag bytes ⟨0#u32⟩ =
      .ok (.Err (decodeError .RecursionLimitReached),bytes) := by
  exact ⟨recursion_reject _ _ _ _ (by omega) hkind,recursion_limit_first _ _ _ _⟩

#print axioms actual_fixed64_plan
#print axioms actual_fixed32_plan
#print axioms actual_length_plan
#print axioms actual_varint_plan
#print axioms actual_varint_error_plan
#print axioms actual_length_error_plan
#print axioms actual_limit_plan

end LibSignalReference.Candidate.ProstSkipPlan
