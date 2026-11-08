import TlsMpc.Signal.PrivateBufferWireSemantics

/-! Record-level arithmetic closure for compositional private-length packing.
No wire-length reconstruction or public width selector is introduced. -/
namespace TlsMpc.Signal.PrivateBuffer
open Semantics

theorem bits_value_injective (xs ys : List Bool) (hlen : xs.length=ys.length) (hv : value xs=value ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => exact (List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)).symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have head : x=y := by cases x <;> cases y <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv ⊢ <;> omega
      subst y
      have tail : value xs=value ys := by simp only [value] at hv;omega
      have length : xs.length=ys.length := by simpa using hlen
      exact congrArg (List.cons x) (ih ys length tail)

theorem decode_encode_masks (bits : List Bool) (hlen : bits.length=16) :
    decodeLength ByteAuth.concrete (encodeLength ByteAuth.concrete (bits.map mask))=bits.map mask := by
  rw [encodeLength_masks_eq bits hlen,decodeLength_masks]
  apply congrArg (List.map mask)
  apply bits_value_injective
  · simp [byteBits,hlen]
  · rw [bytePair_value,public_length_value (value bits) (by have h:=value_lt_pow bits;rw [hlen]at h;exact h)]

theorem add_public_length (left right : Nat) (fits : left+right<65536) :
    (addLoop ByteAuth.concrete (publicLength ByteAuth.concrete left) (publicLength ByteAuth.concrete right)
      (List.range 16) 0).1=publicLength ByteAuth.concrete (left+right) := by
  let lb := byteBits (BitVec.ofNat 8 left)++byteBits (BitVec.ofNat 8 (left/256))
  let rb := byteBits (BitVec.ofNat 8 right)++byteBits (BitVec.ofNat 8 (right/256))
  let pairs := (List.range 16).map (fun i => (lb[i]?.getD false,rb[i]?.getD false))
  let result := Semantics.add pairs false
  have rep : (addLoop ByteAuth.concrete (publicLength ByteAuth.concrete left) (publicLength ByteAuth.concrete right)
      (List.range 16) 0).1=result.1.map mask := by
    unfold publicLength
    rw [decodeLength_masks,decodeLength_masks]
    exact congrArg Prod.fst (addLoop_masks lb rb (List.range 16) false)
  have resultLen : result.1.length=16 := by simp [result,add_length,pairs]
  have encoded:=encode_added_decoded_of_fits 65535 (by omega)
    (BitVec.ofNat 8 (left/256)) (BitVec.ofNat 8 left)
    (BitVec.ofNat 8 (right/256)) (BitVec.ofNat 8 right)
    (by rw [public_length_value left (by omega),public_length_value right (by omega)];omega)
  rw [public_length_value left (by omega),public_length_value right (by omega)]at encoded
  change encodeLength ByteAuth.concrete (addLoop ByteAuth.concrete
    (publicLength ByteAuth.concrete left) (publicLength ByteAuth.concrete right) (List.range 16) 0).1=
      [BitVec.ofNat 8 ((left+right)/256),BitVec.ofNat 8 (left+right)] at encoded
  calc
    _=decodeLength ByteAuth.concrete (encodeLength ByteAuth.concrete (addLoop ByteAuth.concrete
      (publicLength ByteAuth.concrete left) (publicLength ByteAuth.concrete right) (List.range 16) 0).1) := by
      rw [rep,decode_encode_masks _ resultLen]
    _=publicLength ByteAuth.concrete (left+right) := by rw [encoded];rfl

theorem prefix_indexed (capacity count : Nat) (raw : List (BitVec 8)) :
    prefixData ByteAuth.concrete capacity count ((List.range capacity).map (OpenResult.get ByteAuth.concrete raw)) =
      prefixData ByteAuth.concrete capacity count raw := by
  unfold prefixData
  apply List.map_congr_left
  intro i hi
  have bound:=List.mem_range.mp hi
  simp [OpenResult.get,bound]

theorem resize_public (capacity count : Nat) (hc : capacity<65536) (fit : count≤capacity) (raw : List (BitVec 8)) :
    resize ByteAuth.concrete capacity ⟨255,publicLength ByteAuth.concrete count,raw⟩ =
      ⟨255,publicLength ByteAuth.concrete count,prefixData ByteAuth.concrete capacity count raw⟩ := by
  let indexed:=(List.range capacity).map (OpenResult.get ByteAuth.concrete raw)
  have made : make ByteAuth.concrete capacity (publicLength ByteAuth.concrete count) indexed =
      ⟨255,publicLength ByteAuth.concrete count,prefixData ByteAuth.concrete capacity count raw⟩ := by
    have h:=make_decoded capacity hc (BitVec.ofNat 8 (count/256)) (BitVec.ofNat 8 count) indexed (by simp [indexed])
    rw [public_length_value count (by omega),if_pos fit]at h
    change make ByteAuth.concrete capacity (publicLength ByteAuth.concrete count) indexed=
      ⟨255,publicLength ByteAuth.concrete count,prefixData ByteAuth.concrete capacity count indexed⟩ at h
    simpa only [indexed,prefix_indexed] using h
  unfold resize
  rw [made]
  change finish ByteAuth.concrete (255 &&& ByteAuth.eqMask ByteAuth.concrete 255 255) _ _=_
  rw [show (255 : BitVec 8) &&& ByteAuth.eqMask ByteAuth.concrete 255 255=255 from by decide]
  exact finish_accept _ _

theorem prefix_contents (capacity : Nat) (raw : List (BitVec 8)) (fit : raw.length≤capacity) :
    prefixData ByteAuth.concrete capacity raw.length raw = raw++List.replicate (capacity-raw.length) 0 := by
  have eq : prefixData ByteAuth.concrete capacity raw.length raw =
      joinedData ByteAuth.concrete capacity raw.length 0 raw [] := by
    unfold prefixData joinedData
    apply List.map_congr_left
    intro i hi
    by_cases h : i<raw.length <;> simp [h]
  rw [eq,joinedData_as_append ByteAuth.concrete capacity raw.length 0 raw [] (by omega) (by simp) (by omega)]
  simp [ByteAuth.concrete]

theorem prefix_append_tail (capacity : Nat) (raw tail : List (BitVec 8)) :
    prefixData ByteAuth.concrete capacity raw.length (raw++tail)=prefixData ByteAuth.concrete capacity raw.length raw := by
  unfold prefixData
  apply List.map_congr_left
  intro i hi
  by_cases bound : i<raw.length
  · simp [bound,OpenResult.get,List.getElem?_append]
  · simp [bound]

/-- Semantic carrier only; the length parameter is not a host/circuit input. -/
def ofContents (capacity : Nat) (raw : List (BitVec 8)) : Buffer (BitVec 8) :=
  ⟨255,publicLength ByteAuth.concrete raw.length,raw++List.replicate (capacity-raw.length) 0⟩

theorem resize_contents (capacity sourceCapacity : Nat) (hc : capacity<65536)
    (raw : List (BitVec 8)) (fit : raw.length≤capacity) :
    resize ByteAuth.concrete capacity (ofContents sourceCapacity raw)=ofContents capacity raw := by
  unfold ofContents
  rw [resize_public capacity raw.length hc fit,prefix_append_tail,prefix_contents capacity raw fit]

theorem fromPublic_contents (capacity : Nat) (hc : capacity<65536) (raw : List (BitVec 8))
    (fit : raw.length≤capacity) : fromPublic ByteAuth.concrete capacity raw=ofContents capacity raw := by
  unfold fromPublic
  rw [if_pos fit]
  have h:=make_decoded capacity hc (BitVec.ofNat 8 (raw.length/256)) (BitVec.ofNat 8 raw.length)
    (raw++List.replicate (capacity-raw.length) 0) (by simp;omega)
  rw [public_length_value raw.length (by omega),if_pos fit,prefix_append_tail,prefix_contents capacity raw fit]at h
  exact h

theorem append_contents (capacity leftCapacity rightCapacity : Nat) (hc : capacity<65536)
    (left right : List (BitVec 8)) (fit : left.length+right.length≤capacity) :
    append ByteAuth.concrete capacity (ofContents leftCapacity left) (ofContents rightCapacity right)=
      ofContents capacity (left++right) := by
  have hl : left.length≤capacity := by omega
  have hr : right.length≤capacity := by omega
  have resized : append ByteAuth.concrete capacity (ofContents leftCapacity left) (ofContents rightCapacity right)=
      append ByteAuth.concrete capacity (ofContents capacity left) (ofContents capacity right) := by
    unfold append
    rw [resize_contents capacity leftCapacity hc left hl,resize_contents capacity rightCapacity hc right hr,
      resize_contents capacity capacity hc left hl,resize_contents capacity capacity hc right hr]
  rw [resized]
  have leftEq : ofContents capacity left=
      ⟨255,publicLength ByteAuth.concrete left.length,prefixData ByteAuth.concrete capacity left.length left⟩ := by
    unfold ofContents
    rw [prefix_contents capacity left hl]
  have rightEq : ofContents capacity right=
      ⟨255,publicLength ByteAuth.concrete right.length,prefixData ByteAuth.concrete capacity right.length right⟩ := by
    unfold ofContents
    rw [prefix_contents capacity right hr]
  rw [leftEq,rightEq]
  have result:=append_decoded capacity hc
    (BitVec.ofNat 8 (left.length/256)) (BitVec.ofNat 8 left.length)
    (BitVec.ofNat 8 (right.length/256)) (BitVec.ofNat 8 right.length) left right
    (by rw [public_length_value left.length (by omega)];exact hl)
    (by rw [public_length_value right.length (by omega)];exact hr)
  rw [public_length_value left.length (by omega),public_length_value right.length (by omega),if_pos fit]at result
  change append ByteAuth.concrete capacity
      ⟨255,publicLength ByteAuth.concrete left.length,prefixData ByteAuth.concrete capacity left.length left⟩
      ⟨255,publicLength ByteAuth.concrete right.length,prefixData ByteAuth.concrete capacity right.length right⟩=
    ⟨255,(addLoop ByteAuth.concrete (publicLength ByteAuth.concrete left.length)
      (publicLength ByteAuth.concrete right.length) (List.range 16) 0).1,
      joinedData ByteAuth.concrete capacity left.length right.length left right⟩ at result
  rw [add_public_length left.length right.length (by omega),
    joinedData_as_append ByteAuth.concrete capacity left.length right.length left right (by omega) (by omega) fit]at result
  simpa only [ofContents,List.length_append,List.take_length,show ByteAuth.concrete.const 0=(0 : BitVec 8) from rfl] using result

end TlsMpc.Signal.PrivateBuffer
