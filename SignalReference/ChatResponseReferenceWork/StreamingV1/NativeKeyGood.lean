import ChatResponseReferenceWork.StreamingV1.MessageUnderflow
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- Exact executable keyGood expression from actual Core.step. -/
def actualKeyGood (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) : BitVec 8 :=
  let decoded := coreDecoded state byte
  let kind := Word64.concrete.band decoded (Word64.concrete.const 7)
  let tag := Word64.concrete.shift decoded 3
  ByteAuth.concrete.and (Word64.concrete.ule decoded (Word64.concrete.const 4294967295))
    (ByteAuth.concrete.and (ByteAuth.concrete.not (TlsChatResponse.weq Word64.concrete ByteAuth.concrete tag 0))
      (ByteAuth.concrete.and (Word64.concrete.ule kind (Word64.concrete.const 5))
        (ByteAuth.concrete.and (schemaWireMask state byte)
          (TlsInner.select ByteAuth.concrete (TlsChatResponse.weq Word64.concrete ByteAuth.concrete kind 4)
            (ByteAuth.concrete.and (ByteAuth.concrete.not (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0))
              (Word64.eq Word64.concrete ByteAuth.concrete tag
                (TlsChatResponse.lookup Word64.concrete ByteAuth.concrete (Word64.concrete.sub state.depth 1) 0 state.stack)))
            (Word64.concrete.ule state.depth (Word64.concrete.select state.inner 98 99))))))

/-- Actual native key acceptance plus the actual supported schema wire relation
establishes the complete Core key guard, not an assumed parser-validity mask. -/
theorem known_inner_native_key_good (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (wire : WireType)
    (depth : state.depth = 0) (inner : state.inner = 255)
    (decoded : coreDecoded state byte = native.bv)
    (accepted : keyResult native = .Ok (tag,wire))
    (known : (tag.val = 1 ∨ tag.val = 2) ∧ wire = .Varint ∨
      (tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5) ∧ wire = .LengthDelimited) :
    actualKeyGood state byte = 255 := by
  have nativeKind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have nativeTag : Word64.concrete.shift (coreDecoded state byte) 3 = Word64.concrete.const tag.val := by
    rw [decoded]; exact native_key_tag native tag wire accepted
  have schema : schemaWireMask state byte = 255 := by
    rcases known with ⟨tags,wireEq⟩ | ⟨tags,wireEq⟩
    · have result := scalar_wire_mask state byte true tag.val wire tags depth inner nativeTag nativeKind
      rw [wireEq] at result
      exact result
    · have result := bytes_wire_mask state byte true tag.val wire tags depth inner nativeTag nativeKind
      rw [wireEq] at result
      exact result
  have notGroup : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4 = 0 := by
    rw [nativeKind]
    rcases known with ⟨_,wireEq⟩ | ⟨_,wireEq⟩ <;> rw [wireEq] <;> rfl
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

#print axioms known_inner_native_key_good
end ChatResponseReference.StreamingV1
