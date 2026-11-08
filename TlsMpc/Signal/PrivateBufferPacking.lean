import TlsMpc.Signal.PrivateBufferSemantics

namespace TlsMpc.Signal.PrivateBuffer
open Semantics

theorem shifted_length (a : ByteAuth.Ops B) (n : Nat) (data : List B) :
    (shifted a n data).length=data.length := by simp [shifted]

theorem index_bytes (a : ByteAuth.Ops B) (data : List B) :
    (List.range data.length).map (OpenResult.get a data) = data := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,OpenResult.get,List.getElem?_eq_getElem hj,Option.getD_some]

theorem get_shifted (a : ByteAuth.Ops B) (amount : Nat) (data : List B) (i : Nat) (hi : i<data.length) :
    OpenResult.get a (shifted a amount data) i =
      if i<amount then a.const 0 else OpenResult.get a data (i-amount) := by
  simp [shifted,OpenResult.get,hi]

theorem shifted_shifted (a : ByteAuth.Ops B) (left right : Nat) (data : List B) :
    shifted a left (shifted a right data) = shifted a (left+right) data := by
  apply List.ext_getElem
  · simp only [shifted_length]
  · intro i hi hj
    have bound : i<data.length := by simpa only [shifted_length] using hj
    have hg (bytes : List B) (h : i<bytes.length) : OpenResult.get a bytes i=bytes[i] := by
      simp only [OpenResult.get,List.getElem?_eq_getElem h,Option.getD_some]
    rw [←hg _ hi,←hg _ hj]
    rw [get_shifted a left _ i (by simpa only [shifted_length] using bound),get_shifted a (left+right) data i bound]
    split
    · rw [if_pos (by omega)]
    · rw [get_shifted a right data (i-left) (by omega)]
      split
      · rw [if_pos (by omega)]
      · rw [if_neg (by omega)]
        congr 1
        omega

theorem choose_mask (b : Bool) (yes no : BitVec 8) :
    choose ByteAuth.concrete (mask b) yes no = if b then yes else no := by
  cases b
  · simp [choose,ByteAuth.concrete,mask]
  · change no ^^^ (BitVec.allOnes 8 &&& (yes ^^^ no)) = yes
    simp only [BitVec.allOnes_and]
    rw [BitVec.xor_comm yes no,←BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]

theorem choose_lists (b : Bool) (yes no : List (BitVec 8)) (same : yes.length=no.length) :
    (List.range no.length).map (fun i => choose ByteAuth.concrete (mask b)
      (OpenResult.get ByteAuth.concrete yes i) (OpenResult.get ByteAuth.concrete no i)) = if b then yes else no := by
  cases b
  · simp only [choose_mask,Bool.false_eq_true,if_false]
    exact index_bytes ByteAuth.concrete no
  · simp only [choose_mask,if_true]
    rw [←same]
    exact index_bytes ByteAuth.concrete yes

def shiftAmount (bits : List Bool) : List Nat → Nat
  | [] => 0
  | bit::rest => (if bits[bit]?.getD false then 2^bit else 0)+shiftAmount bits rest

theorem shiftLoop_masks (bits : List Bool) (is : List Nat) (data : List (BitVec 8)) :
    shiftLoop ByteAuth.concrete (bits.map mask) is data = shifted ByteAuth.concrete (shiftAmount bits is) data := by
  induction is generalizing data with
  | nil => simp [shiftLoop,shiftAmount,shifted,index_bytes]
  | cons bit rest ih =>
    simp only [shiftLoop,get_mask]
    rw [choose_lists _ _ _ (shifted_length ByteAuth.concrete _ data)]
    cases h : bits[bit]?.getD false
    · simp only [h,Bool.false_eq_true,if_false,shiftAmount,Nat.zero_add,ih]
    · simp only [h,if_true,shiftAmount,ih,shifted_shifted,Nat.add_comm]

theorem shiftAmount_append (bits : List Bool) (left right : List Nat) :
    shiftAmount bits (left++right) = shiftAmount bits left+shiftAmount bits right := by
  induction left with
  | nil => simp [shiftAmount]
  | cons bit left ih => simp [shiftAmount,ih,Nat.add_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem shiftAmount_byte (x : BitVec 8) : shiftAmount (byteBits x) (List.range 8)=x.toNat := by
  have all : ∀ x : BitVec 8, shiftAmount (byteBits x) (List.range 8)=x.toNat := by decide +kernel
  exact all x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem shiftAmount_highByte (x : BitVec 8) :
    shiftAmount (byteBits 0++byteBits x) (List.range' 8 8)=256*x.toNat := by
  have all : ∀ x : BitVec 8, shiftAmount (byteBits 0++byteBits x) (List.range' 8 8)=256*x.toNat := by decide +kernel
  exact all x

set_option maxRecDepth 100000 in
theorem shiftAmount_decoded (hi lo : BitVec 8) :
    shiftAmount (byteBits lo++byteBits hi) (List.range 16)=(hi++lo).toNat := by
  rw [show List.range 16=List.range 8++List.range' 8 8 from by decide,shiftAmount_append]
  have low : shiftAmount (byteBits lo++byteBits hi) (List.range 8)=lo.toNat := by
    change shiftAmount (byteBits lo) (List.range 8)=lo.toNat
    exact shiftAmount_byte lo
  have high : shiftAmount (byteBits lo++byteBits hi) (List.range' 8 8)=256*hi.toNat := by
    change shiftAmount (byteBits 0++byteBits hi) (List.range' 8 8)=256*hi.toNat
    exact shiftAmount_highByte hi
  rw [low,high]
  have value := bytePair_value hi lo
  rw [value_append,byteBits_value,byteBits_value] at value
  simpa only [byteBits,List.length_map,List.length_range] using value

theorem shiftLoop_decoded (hi lo : BitVec 8) (data : List (BitVec 8)) :
    shiftLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo]) (List.range 16) data =
      shifted ByteAuth.concrete (hi++lo).toNat data := by
  rw [decodeLength_masks,shiftLoop_masks,shiftAmount_decoded]

end TlsMpc.Signal.PrivateBuffer
