import ProtoParseWork.DispatcherIntegrationWork.ContiguousReference
import TlsMpc.Signal.ProtoParseProofs
open Aeneas Aeneas.Std Result TlsMpc TlsMpc.Signal
open SignalMessageIntegration
set_option linter.unusedSimpArgs false
namespace DispatcherIntegration
set_option maxHeartbeats 1000000

/-- Numeric scalar metadata stores the decoded uint64; Prost stores its low32
bits. This projection is required for arbitrary noncanonical-width inputs. -/
def scalarView (f : ProtoParse.Field (BitVec 8) (BitVec 64)) : Option U32 :=
  if f.present = 255 then some (UScalar.cast .U32 (⟨f.scalar⟩ : U64)) else none

/-- Exact numeric scalar representation, including truncation above 32 bits. -/
theorem scalar_view_value (value : U64) (stop : BitVec 64) :
    scalarView ⟨255,stop,value.bv,value.bv⟩ = some (UScalar.cast .U32 value) := by
  cases value
  rfl

theorem select_full (yes no : ProtoParse.Field (BitVec 8) (BitVec 64)) :
    ProtoParse.selectField Word64.concrete ByteAuth.concrete 255 yes no = yes := by
  cases yes
  simp [ProtoParse.selectField, Word64.concrete, Unpad.chooseByte, ByteAuth.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,
    BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, and_self]

/-- The actual numeric metadata write at the counter slot has precisely the
representation consumed by the generated dispatcher's scalar projection. -/
theorem counter_write_view (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (hi : 1 < fields.length) (stop : BitVec 64) (value : U64) :
    scalarView ((ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 2
      ⟨255,stop,value.bv⟩ fields)[1]'(by simpa [ProtoParse.writeFields] using hi)) =
      some (UScalar.cast .U32 value) := by
  simp only [ProtoParse.writeFields, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have hm : Word64.eq Word64.concrete ByteAuth.concrete (2 : BitVec 64) (Word64.concrete.const (1+1)) = 255 := by decide
  rw [hm]
  change scalarView (ProtoParse.selectField Word64.concrete ByteAuth.concrete 255 _ _) = _
  rw [select_full]
  exact scalar_view_value value stop

/-- A successful actual counter merge agrees with the projected numeric field
record. The decoder result remains explicit here; total input coverage is
counter_full_reference, which supplies it without caller assumptions. -/
theorem counter_numeric_value (m : proto.wire.SignalMessage) (before after : Slice U8)
    (value : U64) (ctx : prost.encoding.DecodeContext)
    (hd : ProstFieldCandidate.encoding.varint.decode_varint
      LibSignalReference.Candidate.ProstFieldBuf.sliceBuf before = ok (.Ok value,after)) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      sliceBuf m 2#u32 .Varint before ctx =
      ok (.Ok (),{m with counter := scalarView ⟨255,0,value.bv,value.bv⟩},after) := by
  rw [counter_dispatch,scalar_view_value]
  unfold prost.encoding.uint32.merge
  rw [field_slice_adapter]
  simp only [toFieldWire]
  rw [LibSignalReference.Candidate.ProstField.uint32_after _ _ _ _ _ hd]
  rfl

theorem counter_numeric_write (m : proto.wire.SignalMessage) (before after : Slice U8)
    (value : U64) (ctx : prost.encoding.DecodeContext) (stop : BitVec 64)
    (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) (hi : 1 < fields.length)
    (hd : ProstFieldCandidate.encoding.varint.decode_varint
      LibSignalReference.Candidate.ProstFieldBuf.sliceBuf before = ok (.Ok value,after)) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      sliceBuf m 2#u32 .Varint before ctx =
      ok (.Ok (), {m with counter := (scalarView
        ((ProtoParse.writeFields Word64.concrete ByteAuth.concrete 255 2
          ⟨255,stop,value.bv⟩ fields)[1]'(by simpa [ProtoParse.writeFields] using hi)))},after) := by
  rw [counter_write_view fields hi stop value]
  simpa only [scalar_view_value] using counter_numeric_value m before after value ctx hd

/-- Malformed scalar input keeps the exact rejection and consumed suffix. A
missing Option is initialized to zero before Prost attempts the field merge. -/
theorem counter_numeric_error (m : proto.wire.SignalMessage) (before after : Slice U8)
    (error : ProstFieldCandidate.error.DecodeError) (ctx : prost.encoding.DecodeContext)
    (hd : ProstFieldCandidate.encoding.varint.decode_varint
      LibSignalReference.Candidate.ProstFieldBuf.sliceBuf before = ok (.Err error,after)) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      sliceBuf m 2#u32 .Varint before ctx =
      ok (.Err (fieldError error),{m with counter := some (m.counter.getD 0#u32)},after) := by
  rw [counter_dispatch]
  unfold prost.encoding.uint32.merge
  rw [field_slice_adapter]
  simp only [toFieldWire]
  rw [LibSignalReference.Candidate.ProstField.uint32_error _ _ _ _ _ hd]
  rfl

/-- Byte metadata denotes a content slice of the same bounded plaintext body. -/
def bytesView (body : Slice U8) (f : ProtoParse.Field (BitVec 8) (BitVec 64)) :
    Option (alloc.vec.Vec U8) :=
  if f.present = 255 then
    some (LibSignalReference.Candidate.ProstVecAdapter.fromSlice
      (ProstBytesCandidate.ContentModel.take
        (ProstBytesCandidate.ContentModel.drop body f.offset.toNat) f.length.toNat))
  else none

theorem bytes_view_value (body : Slice U8) (offset : Nat) (ho : offset < 2^64)
    (value : U64) :
    bytesView body ⟨255,BitVec.ofNat 64 offset,value.bv,value.bv⟩ =
    some (LibSignalReference.Candidate.ProstVecAdapter.fromSlice
      (ProstBytesCandidate.ContentModel.take
        (ProstBytesCandidate.ContentModel.drop body offset) value.val)) := by
  simp only [bytesView, if_pos rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  rfl

/-- Actual ciphertext replacement agrees with the secret offset/length content
view; duplicate bytes replace rather than append, including an empty value. -/
theorem ciphertext_numeric_value (m : proto.wire.SignalMessage)
    (body before after : Slice U8) (offset : Nat) (ho : offset < 2^64)
    (value : U64) (ctx : prost.encoding.DecodeContext)
    (hd : ProstBytesCandidate.encoding.varint.decode_varint
      LibSignalReference.Candidate.ProstBytesBuf.sliceBuf before = ok (.Ok value,after))
    (hrest : after = ProstBytesCandidate.ContentModel.drop body offset)
    (hn : value.val ≤ after.length) :
    proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
      sliceBuf m 4#u32 .LengthDelimited before ctx =
      ok (.Ok (),{m with ciphertext := (bytesView body
        ⟨255,BitVec.ofNat 64 offset,value.bv,value.bv⟩)},
        LibSignalReference.Candidate.ProstBytesBuf.drop after value.val) := by
  rw [ciphertext_dispatch,bytes_view_value body offset ho]
  unfold prost.encoding.bytes.merge
  rw [bytes_slice_adapter,bytes_actual_adapter]
  simp only [toBytesWire]
  rw [LibSignalReference.Candidate.ProstBytes.bytes_after_actual_vec _ _ _ _ _ _ hd hn]
  simp only [bind_tc_ok, hrest]
  rfl

#print axioms bytes_view_value
#print axioms ciphertext_numeric_value
#print axioms scalar_view_value
#print axioms counter_numeric_value
#print axioms counter_numeric_error
#print axioms counter_write_view
#print axioms counter_numeric_write
end DispatcherIntegration
