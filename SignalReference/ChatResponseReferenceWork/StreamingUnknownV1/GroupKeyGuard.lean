import ChatResponseReferenceWork.StreamingUnknownV1.KeyGuard
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Every tag inside a group is schema-opaque, including tags 1 through 5. -/
theorem nested_schema_masks (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (notTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0) :
    scalarKeyMask state byte = 0 ∧ bytesKeyMask state byte = 0 := by
  simp only [scalarKeyMask,bytesKeyMask,notTop]
  exact ⟨BitVec.zero_and,BitVec.zero_and⟩

theorem nested_schema_wire (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (notTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0) :
    schemaWireMask state byte = 255 := by
  obtain ⟨scalar,bytes⟩ := nested_schema_masks state byte notTop
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [schemaWireMask,scalar,bytes,zeroAnd]
  rfl

theorem nested_depth_not_top (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (depth : Nat)
    (positive : 0 < depth) (bound : depth ≤ 100) (depthEq : state.depth = BitVec.ofNat 64 depth) :
    TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0 := by
  unfold TlsChatResponse.weq
  rw [depthEq,word_eq_value]
  apply if_neg
  intro equal
  have numeric := congrArg BitVec.toNat equal
  have small : depth < 2^64 := by omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
  change depth = 0 at numeric
  omega

/-- Actual accepted non-end group key passes the complete native/schema/depth
check exactly within the inner response recursion budget. Schema-known tag
numbers do not invoke response mergers inside the skipped group. -/
theorem nested_inner_native_key_good (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (wire : WireType) (depth : Nat)
    (positive : 0 < depth) (bound : depth ≤ 98) (depthEq : state.depth = BitVec.ofNat 64 depth)
    (notEnd : wire ≠ .EndGroup) (inner : state.inner = 255)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,wire)) :
    actualKeyGood state byte = 255 := by
  have nativeKind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have notTop := nested_depth_not_top state depth positive (by omega) depthEq
  have schema := nested_schema_wire state byte notTop
  have notGroup : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4 = 0 := by
    rw [nativeKind]
    cases wire <;> first | contradiction | rfl
  have common : commonKey (coreDecoded state byte) = 255 := by
    rw [decoded,common_key_exact]
    exact if_pos (key_success_fields native tag wire accepted).1
  have depthAllowed : Word64.concrete.ule state.depth (Word64.concrete.select state.inner 98 99) = 255 := by
    rw [depthEq,inner,Word64.select_accept,Word64.ule_value]
    have small : depth < 2^64 := by omega
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    exact if_pos bound
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  have rightHot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  dsimp only [actualKeyGood]
  rw [schema,notGroup,TlsInner.select_reject,depthAllowed]
  simp only [hotAnd,rightHot]
  simpa only [commonKey,keyFields,hotAnd,TlsChatResponse.weq] using common

/-- A closing group key is accepted exactly when its actual native tag equals
the current stack top. Closing does not consume recursion budget and therefore
remains possible at maximum depth; mismatched end tags retain rejection. -/
theorem nested_end_native_key_guard (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32)
    (notTop : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,.EndGroup)) :
    actualKeyGood state byte = Word64.eq Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 tag.val)
      (TlsChatResponse.lookup Word64.concrete ByteAuth.concrete (Word64.concrete.sub state.depth 1) 0 state.stack) := by
  have nativeKind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const 4 := by
    rw [decoded]; exact native_key_kind native tag .EndGroup accepted
  have nativeTag : Word64.concrete.shift (coreDecoded state byte) 3 = BitVec.ofNat 64 tag.val := by
    rw [decoded]; exact native_key_tag native tag .EndGroup accepted
  have schema := nested_schema_wire state byte notTop
  have common : commonKey (coreDecoded state byte) = 255 := by
    rw [decoded,common_key_exact]
    exact if_pos (key_success_fields native tag .EndGroup accepted).1
  have isEnd : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4 = 255 := by rw [nativeKind]; rfl
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have factored : actualKeyGood state byte = ByteAuth.concrete.and (commonKey (coreDecoded state byte))
      (Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.shift (coreDecoded state byte) 3)
        (TlsChatResponse.lookup Word64.concrete ByteAuth.concrete (Word64.concrete.sub state.depth 1) 0 state.stack)) := by
    dsimp only [actualKeyGood]
    rw [schema,isEnd,TlsInner.select_accept,notTop,notZero]
    simp only [commonKey,keyFields,hotAnd,TlsChatResponse.weq]
    simp only [ByteAuth.concrete,BitVec.and_assoc]
  rw [factored,common,hotAnd,nativeTag]

#print axioms nested_end_native_key_guard
#print axioms nested_schema_masks
#print axioms nested_schema_wire
#print axioms nested_depth_not_top
#print axioms nested_inner_native_key_good
end ChatResponseReference.StreamingUnknownV1
