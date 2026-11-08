import ProtoParseWork.PrivateLengthV1Work.Step
namespace PrivateLengthV1.Scan
open TlsMpc TlsMpc.Signal

theorem fold_inside (bytes : List (BitVec 8)) (ending count : Nat)
    (within : ending ≤ bytes.length) (capacity : bytes.length ≤ 512)
    (positions : List Nat) (before : ∀ position ∈ positions, position < ending)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (shape : state.stack.length = min 100 ending) (size : state.stack.length+count ≤ 100) :
    positions.foldl (PrivateProtoParseV1.step Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending)
      (PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) bytes))
      (Stack.pad state count) =
    Stack.pad (positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete ending
      (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending))) state) count := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
    simp only [List.foldl_cons]
    rw [Step.inside bytes ending position count within capacity (before position (by simp)) state shape size]
    apply ih
    · intro index member
      exact before index (by simp [member])
    · rw [Step.public_stack_length]
      exact shape
    · rw [Step.public_stack_length]
      exact size

theorem fold_past (ending : Nat) (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (positions : List Nat) (after : ∀ position ∈ positions, ending ≤ position ∧ position ≤ 512)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    positions.foldl (PrivateProtoParseV1.step Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 ending) rows) state = state := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
    have bounds := after position (by simp)
    simp only [List.foldl_cons,Step.past ending position bounds.2 bounds.1]
    apply ih
    intro index member
    exact after index (by simp [member])

theorem range_split (capacity ending : Nat) (inside : ending ≤ capacity) :
    List.range capacity = List.range ending ++ List.range' ending (capacity-ending) := by
  simpa only [List.range_eq_range',Nat.zero_add,Nat.add_sub_of_le inside] using
    (List.range'_append_1 (s:=0) (m:=ending) (n:=capacity-ending)).symm

/-- Complete all-outcomes private-end scan agreement. Exact fields, success or
rejection, cursor and group depth are preserved. The sole representation
extension is a proved-zero, unaddressable stack tail. No parser correctness,
termination or successful-input hypothesis is assumed. -/
theorem parseBody_take (bytes : List (BitVec 8)) (ending : Nat)
    (within : ending ≤ bytes.length) (capacity : bytes.length ≤ 512) :
    PrivateProtoParseV1.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 ending) bytes =
    Stack.pad (ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (bytes.take ending))
      (min 100 bytes.length-min 100 ending) := by
  let count := min 100 bytes.length-min 100 ending
  have first := fold_inside bytes ending count within capacity (List.range ending)
    (by intro position member; exact List.mem_range.mp member)
    (ProtoParse.initial Word64.concrete ByteAuth.concrete ending) (by simp [ProtoParse.initial])
    (by simp only [ProtoParse.initial,List.length_replicate]; dsimp [count]; omega)
  have rest (state : ProtoParse.State (BitVec 8) (BitVec 64)) :=
    fold_past ending
      (PrivateProtoParseV1.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) bytes)
      (List.range' ending (bytes.length-ending)) (by
        intro position member
        have bound := List.mem_range'.mp member
        omega) state
  unfold PrivateProtoParseV1.parseBody ProtoParse.parseBody
  simp only [List.length_take,Nat.min_eq_left within]
  rw [range_split bytes.length ending within,List.foldl_append,Stack.initial_pad bytes.length ending within]
  rw [first,rest]


/-- Capacity padding is functionally irrelevant for every outcome. This
includes malformed messages whose native failure cursor is before the end. -/
theorem padding_noninterference (left right : List (BitVec 8)) (ending : Nat)
    (shape : left.length = right.length) (within : ending ≤ left.length) (capacity : left.length ≤ 512)
    (same : left.take ending = right.take ending) :
    PrivateProtoParseV1.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) left =
    PrivateProtoParseV1.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 ending) right := by
  rw [parseBody_take left ending within capacity,
    parseBody_take right ending (by omega) (by omega),same,shape]

#print axioms fold_inside
#print axioms fold_past
#print axioms parseBody_take
#print axioms padding_noninterference
end PrivateLengthV1.Scan
