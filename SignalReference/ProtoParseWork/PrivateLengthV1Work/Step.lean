import ProtoParseWork.PrivateLengthV1Work.Lookup
import ProtoParseWork.PrivateLengthV1Work.Stack
import ProtoParseWork.PrivateLengthV1Work.Select
namespace PrivateLengthV1.Step
open TlsMpc TlsMpc.Signal

theorem private_shapes (ending : BitVec 64) (position : Nat)
    (p : ProtoParse.Plan (BitVec 8) (BitVec 64)) (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    (PrivateProtoParseV1.applyPlan Word64.concrete ByteAuth.concrete ending position p state).stack.length = state.stack.length ∧
    (PrivateProtoParseV1.applyPlan Word64.concrete ByteAuth.concrete ending position p state).fields.length = state.fields.length := by
  simp [PrivateProtoParseV1.applyPlan,ProtoParse.writeStack,ProtoParse.writeFields,ProtoParse.initializeFields]

theorem public_stack_length (capacity position : Nat) (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state position).stack.length = state.stack.length := by
  simp [ProtoParse.step,ProtoParse.applyPlan,ProtoParse.writeStack]

/-- Every public scan slot past the secret end is an exact state stutter,
including error states and caller-supplied noncanonical state masks. -/
theorem past (ending position : Nat) (capacity : position ≤ 512) (after : ending ≤ position)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    PrivateProtoParseV1.step Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) rows state position = state := by
  have mask : Word64.concrete.ule (Word64.concrete.const (position+1)) (BitVec.ofNat 64 ending) = 0 := by
    change Word64.concrete.ule (BitVec.ofNat 64 (position+1)) (BitVec.ofNat 64 ending) = 0
    rw [Plan.nat_ule _ _ (by omega) (by omega)]
    simp [show ¬position+1 ≤ ending by omega]
  unfold PrivateProtoParseV1.step
  rw [mask]
  apply Select.state_reject
  · exact (private_shapes _ _ _ _).1
  · exact (private_shapes _ _ _ _).2

/-- A real scan step agrees with the accepted parser on take n. Only the
unaddressable, zero stack tail differs in representation. -/
theorem inside (bytes : List (BitVec 8)) (ending position count : Nat)
    (within : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) (before : position < ending)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (shape : state.stack.length = min 100 ending) (size : state.stack.length+count ≤ 100) :
    PrivateProtoParseV1.step Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending)
      (PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) bytes)
      (Stack.pad state count) position =
    Stack.pad (ProtoParse.step Word64.concrete ByteAuth.concrete ending
      (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending)) state position) count := by
  let newRows := PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) bytes
  let oldRows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending)
  let key := oldRows[position]?.getD ⟨ByteAuth.concrete.const 0,Word64.concrete.const position,Word64.concrete.const 0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((oldRows.drop (position+1)).take 10)
  let lastClear := (oldRows[ending-1]?.getD ⟨ByteAuth.concrete.const 0,Word64.concrete.const (ending-1),Word64.concrete.const 0⟩).ok
  let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete ending position lastClear key payload state
  have keyEq : newRows[position]?.getD ⟨ByteAuth.concrete.const 0,Word64.concrete.const position,Word64.concrete.const 0⟩ = key :=
    Lookup.key_get bytes ending position within capacity before
  have payloadEq : ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1)
      ((newRows.drop (position+1)).take 10) = payload := Lookup.payload_lookup bytes ending (position+1) within capacity key.stop
  have lastEq : (ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete
      (Word64.concrete.sub (BitVec.ofNat 64 ending) (Word64.concrete.const 1)) 0 newRows).ok = lastClear :=
    Lookup.last_ok bytes ending within capacity (by omega)
  have planEq : PrivateProtoParseV1.planWithCursor Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending)
      position lastClear key payload (Stack.pad state count) = p := by
    rw [Plan.cursor_const ending position (by omega) before]
    exact Stack.cursor_pad ending position lastClear key payload state count
  have mask : Word64.concrete.ule (Word64.concrete.const (position+1)) (BitVec.ofNat 64 ending) = 255 := by
    change Word64.concrete.ule (BitVec.ofNat 64 (position+1)) (BitVec.ofNat 64 ending) = 255
    rw [Plan.nat_ule _ _ (by omega) (by omega)]
    simp [show position+1 ≤ ending by omega]
  change PrivateProtoParseV1.step Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending)
      newRows (Stack.pad state count) position = Stack.pad (ProtoParse.step Word64.concrete ByteAuth.concrete ending oldRows state position) count
  unfold PrivateProtoParseV1.step
  rw [keyEq]
  dsimp only
  rw [payloadEq,lastEq,planEq,mask]
  rw [Select.state_accept _ _ (private_shapes _ _ _ _).1 (private_shapes _ _ _ _).2]
  rw [Stack.apply_pad ending position count (by omega) state shape size]
  rfl

#print axioms past
#print axioms inside
end PrivateLengthV1.Step
