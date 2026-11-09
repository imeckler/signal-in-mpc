import ChatResponseReferenceWork.StreamingUnknownV1.Resume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Unknown tag classification is independent of validity, depth and inner flag:
none of the actual response or envelope known-field clauses may fire. -/
theorem unknown_schema_masks (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) (tag : U32)
    (unknown : 5 < tag.val)
    (newTag : Word64.concrete.shift (coreDecoded state byte) 3 = BitVec.ofNat 64 tag.val) :
    scalarKeyMask state byte = 0 ∧ bytesKeyMask state byte = 0 := by
  have one : tag.val ≠ 1 := by omega
  have two : tag.val ≠ 2 := by omega
  have three : tag.val ≠ 3 := by omega
  have four : tag.val ≠ 4 := by omega
  have five : tag.val ≠ 5 := by omega
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have xorZero : ByteAuth.concrete.xor 0 0 = 0 := rfl
  simp only [scalarKeyMask,bytesKeyMask,newTag,TlsChatResponse.wmember,List.map_cons,List.map_nil,
    TlsWebSocketUpgrade.any,List.foldl_cons,List.foldl_nil,native_tag_equality tag 1 (by decide),
    native_tag_equality tag 2 (by decide),native_tag_equality tag 3 (by decide),native_tag_equality tag 4 (by decide),
    native_tag_equality tag 5 (by decide),if_neg one,if_neg two,if_neg three,if_neg four,if_neg five]
  have eitherZero : TlsWebSocketUpgrade.either ByteAuth.concrete 0 0 = 0 := rfl
  have seed : ByteAuth.concrete.const 0 = 0 := rfl
  simp only [seed,eitherZero,TlsInner.select,xorZero,andZero]
  simp

theorem unknown_schema_wire (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) (tag : U32)
    (unknown : 5 < tag.val)
    (newTag : Word64.concrete.shift (coreDecoded state byte) 3 = BitVec.ofNat 64 tag.val) :
    schemaWireMask state byte = 255 := by
  obtain ⟨scalar,bytes⟩ := unknown_schema_masks state byte tag unknown newTag
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [schemaWireMask,scalar,bytes,zeroAnd]
  rfl

/-- Accepted native unknown keys retain all common key checks and actual group
recursion guard. Top-level EndGroup is deliberately excluded: source rejects it. -/
theorem unknown_inner_native_key_good (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (wire : WireType)
    (unknown : 5 < tag.val) (notEnd : wire ≠ .EndGroup)
    (depth : state.depth = 0) (inner : state.inner = 255)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,wire)) :
    actualKeyGood state byte = 255 := by
  have nativeKind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have nativeTag : Word64.concrete.shift (coreDecoded state byte) 3 = BitVec.ofNat 64 tag.val := by
    rw [decoded]; exact native_key_tag native tag wire accepted
  have schema := unknown_schema_wire state byte tag unknown nativeTag
  have notGroup : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4 = 0 := by
    rw [nativeKind]
    cases wire <;> first | contradiction | rfl
  have common : commonKey (coreDecoded state byte) = 255 := by
    rw [decoded,common_key_exact]
    exact if_pos (key_success_fields native tag wire accepted).1
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  have rightHot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  dsimp only [actualKeyGood]
  rw [schema,notGroup,TlsInner.select_reject,depth,inner]
  have depthAllowed : Word64.concrete.ule 0 (Word64.concrete.select 255 98 99) = 255 := rfl
  rw [depthAllowed]
  simp only [hotAnd,rightHot]
  simpa only [commonKey,keyFields,hotAnd,TlsChatResponse.weq] using common

#print axioms unknown_schema_masks
#print axioms unknown_schema_wire
#print axioms unknown_inner_native_key_good
end ChatResponseReference.StreamingUnknownV1
