import TlsMpc.Signal.PrivateBuffer
namespace TlsMpc.Signal.PrivateBuffer

def maskedByte (a : ByteAuth.Ops B) (x : B) : B :=
  (List.range 8).foldl (fun acc bit => a.xor acc (a.and (a.maskBit x bit) (a.const (2^bit)))) (a.const 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskedByte_value (x : BitVec 8) : maskedByte ByteAuth.concrete x = x := by
  have all : ∀ x : BitVec 8, maskedByte ByteAuth.concrete x = x := by decide +kernel
  exact all x

set_option maxRecDepth 100000 in
theorem length_roundtrip (hi lo : BitVec 8) :
    encodeLength ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo]) = [hi,lo] := by
  change [maskedByte ByteAuth.concrete hi,maskedByte ByteAuth.concrete lo]=[hi,lo]
  rw [maskedByte_value,maskedByte_value]

namespace Semantics

def mask (b : Bool) : BitVec 8 := if b then 255 else 0

def digit (x y carry : Bool) : Bool × Bool :=
  (x ^^ y ^^ carry,(x && y) ^^ ((x ^^ y) && carry))

theorem digit_masks (x y carry : Bool) :
    (mask x ^^^ mask y ^^^ mask carry,
      (mask x &&& mask y) ^^^ ((mask x ^^^ mask y) &&& mask carry)) =
    (mask (digit x y carry).1,mask (digit x y carry).2) := by
  cases x <;> cases y <;> cases carry <;> decide

theorem digit_value (x y carry : Bool) :
    (digit x y carry).1.toNat + 2*(digit x y carry).2.toNat = x.toNat+y.toNat+carry.toNat := by
  cases x <;> cases y <;> cases carry <;> decide

def value : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*value bs

def add : List (Bool × Bool) → Bool → List Bool × Bool
  | [],carry => ([],carry)
  | (x,y)::rest,carry =>
    let d := digit x y carry
    let next := add rest d.2
    (d.1::next.1,next.2)

theorem add_value (pairs : List (Bool × Bool)) (carry : Bool) :
    value (add pairs carry).1 + 2^pairs.length*(add pairs carry).2.toNat =
      value (pairs.map Prod.fst)+value (pairs.map Prod.snd)+carry.toNat := by
  induction pairs generalizing carry with
  | nil => simp [add,value]
  | cons pair rest ih =>
    rcases pair with ⟨x,y⟩
    have h := ih (digit x y carry).2
    have d := digit_value x y carry
    simp only [add,List.length_cons,List.map_cons,value]
    calc
      _ = (digit x y carry).1.toNat + 2*(value (add rest (digit x y carry).2).1 +
          2^rest.length*(add rest (digit x y carry).2).2.toNat) := by
        simp [Nat.pow_succ,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc]
      _ = _ := by rw [h];omega

theorem get_mask (raw : List Bool) (index : Nat) :
    OpenResult.get ByteAuth.concrete (raw.map mask) index = mask (raw[index]?.getD false) := by
  simp only [OpenResult.get,List.getElem?_map]
  cases h : raw[index]? <;> rfl

theorem addLoop_masks (left right : List Bool) (is : List Nat) (carry : Bool) :
    addLoop ByteAuth.concrete (left.map mask) (right.map mask) is (mask carry) =
      ((add (is.map (fun i => (left[i]?.getD false,right[i]?.getD false))) carry).1.map mask,
        mask (add (is.map (fun i => (left[i]?.getD false,right[i]?.getD false))) carry).2) := by
  induction is generalizing carry with
  | nil => rfl
  | cons i is ih =>
    simp only [addLoop,get_mask,List.map_cons,add]
    have d := digit_masks (left[i]?.getD false) (right[i]?.getD false) carry
    have sum := congrArg Prod.fst d
    have next := congrArg Prod.snd d
    simp only at sum next
    simp only [ByteAuth.concrete] at ih ⊢
    rw [next,ih,sum]


def unmask (x : BitVec 8) : Bool := x == 255

theorem unmask_mask (b : Bool) : unmask (mask b)=b := by cases b <;> decide

theorem addLoop_integer (left right : List Bool) (is : List Nat) (carry : Bool) :
    let result := addLoop ByteAuth.concrete (left.map mask) (right.map mask) is (mask carry)
    value (result.1.map unmask) + 2^is.length*(unmask result.2).toNat =
      value (is.map (fun i => left[i]?.getD false))+
      value (is.map (fun i => right[i]?.getD false))+carry.toNat := by
  rw [addLoop_masks]
  simpa only [List.map_map,Function.comp_def,unmask_mask,List.map_id',List.length_map] using
    add_value (is.map (fun i => (left[i]?.getD false,right[i]?.getD false))) carry


def subtractDigit (x y borrow : Bool) : Bool × Bool :=
  (x ^^ y ^^ borrow,(!x && y) ^^ (!(x ^^ y) && borrow))

theorem subtractDigit_value (x y borrow : Bool) :
    x.toNat+2*(subtractDigit x y borrow).2.toNat =
      y.toNat+borrow.toNat+(subtractDigit x y borrow).1.toNat := by
  cases x <;> cases y <;> cases borrow <;> decide

theorem subtractDigit_mask (x y borrow : Bool) :
    ((~~~mask x) &&& mask y) ^^^ ((~~~(mask x ^^^ mask y)) &&& mask borrow) =
      mask (subtractDigit x y borrow).2 := by
  cases x <;> cases y <;> cases borrow <;> decide

def subtract : List (Bool × Bool) → Bool → List Bool × Bool
  | [],borrow => ([],borrow)
  | (x,y)::rest,borrow =>
    let d := subtractDigit x y borrow
    let next := subtract rest d.2
    (d.1::next.1,next.2)

theorem subtract_value (pairs : List (Bool × Bool)) (borrow : Bool) :
    value (pairs.map Prod.fst) + 2^pairs.length*(subtract pairs borrow).2.toNat =
      value (pairs.map Prod.snd)+borrow.toNat+value (subtract pairs borrow).1 := by
  induction pairs generalizing borrow with
  | nil => simp [subtract,value]
  | cons pair rest ih =>
    rcases pair with ⟨x,y⟩
    have h := ih (subtractDigit x y borrow).2
    have d := subtractDigit_value x y borrow
    simp only [subtract,List.length_cons,List.map_cons,value]
    calc
      _ = x.toNat+2*(value (rest.map Prod.fst)+2^rest.length*(subtract rest (subtractDigit x y borrow).2).2.toNat) := by
        simp [Nat.pow_succ,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc]
      _ = _ := by rw [h];omega

theorem subtract_length (pairs : List (Bool × Bool)) (borrow : Bool) :
    (subtract pairs borrow).1.length=pairs.length := by
  induction pairs generalizing borrow with
  | nil => rfl
  | cons pair rest ih => simp only [subtract,List.length_cons,ih]

theorem value_lt_pow (bits : List Bool) : value bits < 2^bits.length := by
  induction bits with
  | nil => decide
  | cons b bits ih => cases b <;> simp only [value,List.length_cons,Nat.pow_succ,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem subtract_borrow (pairs : List (Bool × Bool)) :
    (subtract pairs false).2 = decide (value (pairs.map Prod.fst)<value (pairs.map Prod.snd)) := by
  have h := subtract_value pairs false
  have bound := value_lt_pow (subtract pairs false).1
  rw [subtract_length] at bound
  cases hb : (subtract pairs false).2
  · simp only [hb,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    have hn : ¬value (pairs.map Prod.fst)<value (pairs.map Prod.snd) := by omega
    simp only [hn,decide_false]
  · simp only [hb,Bool.toNat_true,Nat.mul_one,Bool.toNat_false,Nat.add_zero] at h
    have hl : value (pairs.map Prod.fst)<value (pairs.map Prod.snd) := by omega
    simp only [hl,decide_true]

theorem borrowLoop_masks (left right : List Bool) (is : List Nat) (borrow : Bool) :
    borrowLoop ByteAuth.concrete (left.map mask) (right.map mask) is (mask borrow) =
      mask (subtract (is.map (fun i => (left[i]?.getD false,right[i]?.getD false))) borrow).2 := by
  induction is generalizing borrow with
  | nil => rfl
  | cons i is ih =>
    simp only [borrowLoop,get_mask,List.map_cons,subtract]
    simp only [ByteAuth.concrete] at ih ⊢
    rw [subtractDigit_mask,ih]

theorem less_integer (left right : List Bool) :
    less ByteAuth.concrete (left.map mask) (right.map mask) =
      if value ((List.range 16).map (fun i => left[i]?.getD false)) <
        value ((List.range 16).map (fun i => right[i]?.getD false)) then 255 else 0 := by
  change borrowLoop ByteAuth.concrete (left.map mask) (right.map mask) (List.range 16) (mask false) = _
  rw [borrowLoop_masks,subtract_borrow]
  simp only [List.map_map,Function.comp_def,mask]
  split <;> simp_all


def byteBits (x : BitVec 8) : List Bool := (List.range 8).map x.getLsbD

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskBit_value (x : BitVec 8) (index : Fin 8) :
    ByteAuth.concrete.maskBit x index.val = mask (x.getLsbD index.val) := by
  have all : ∀ (x : BitVec 8) (index : Fin 8),
      ByteAuth.concrete.maskBit x index.val = mask (x.getLsbD index.val) := by decide +kernel
  exact all x index

theorem maskBit_value_nat (x : BitVec 8) (index : Nat) (hi : index<8) :
    ByteAuth.concrete.maskBit x index = mask (x.getLsbD index) := maskBit_value x ⟨index,hi⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem byteBits_value (x : BitVec 8) : value (byteBits x)=x.toNat := by
  have all : ∀ x : BitVec 8, value (byteBits x)=x.toNat := by decide +kernel
  exact all x

theorem value_append (left right : List Bool) :
    value (left++right) = value left+2^left.length*value right := by
  induction left with
  | nil => simp [value]
  | cons b left ih => simp [value,ih,Nat.pow_succ,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc,Nat.mul_comm,Nat.mul_left_comm]

theorem decodeLength_masks (hi lo : BitVec 8) :
    decodeLength ByteAuth.concrete [hi,lo] = (byteBits lo++byteBits hi).map mask := by
  simp [decodeLength,byteBits,List.range_succ,OpenResult.get,maskBit_value_nat]

theorem decodeLength_value (hi lo : BitVec 8) :
    value ((decodeLength ByteAuth.concrete [hi,lo]).map unmask) = (hi++lo).toNat := by
  rw [decodeLength_masks]
  simp only [List.map_map,Function.comp_def,unmask_mask,List.map_id',value_append]
  rw [byteBits_value,byteBits_value]
  simp only [byteBits,List.length_map,List.length_range,BitVec.toNat_append]
  rw [←Nat.shiftLeft_add_eq_or_of_lt (i:=8) lo.isLt hi.toNat]
  simp [Nat.shiftLeft_eq,Nat.add_comm,Nat.mul_comm]



theorem index_bits (bits : List Bool) :
    (List.range bits.length).map (fun i => bits[i]?.getD false) = bits := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    simp only [List.getElem?_eq_getElem hj,Option.getD_some]

theorem bytePair_value (hi lo : BitVec 8) :
    value (byteBits lo++byteBits hi)=(hi++lo).toNat := by
  have h := decodeLength_value hi lo
  simpa only [decodeLength_masks,List.map_map,Function.comp_def,unmask_mask,List.map_id'] using h

theorem less_decoded_integer (hi lo hi' lo' : BitVec 8) :
    less ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo]) (decodeLength ByteAuth.concrete [hi',lo']) =
      if (hi++lo).toNat < (hi'++lo').toNat then 255 else 0 := by
  rw [decodeLength_masks,decodeLength_masks,less_integer]
  have hlen : (byteBits lo++byteBits hi).length=16 := by simp [byteBits]
  have hlen' : (byteBits lo'++byteBits hi').length=16 := by simp [byteBits]
  have hl := index_bits (byteBits lo++byteBits hi)
  have hr := index_bits (byteBits lo'++byteBits hi')
  rw [hlen] at hl
  rw [hlen'] at hr
  rw [hl,hr,bytePair_value,bytePair_value]

theorem add_decoded_integer (hi lo hi' lo' : BitVec 8) :
    let result := addLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])
      (decodeLength ByteAuth.concrete [hi',lo']) (List.range 16) 0
    value (result.1.map unmask)+65536*(unmask result.2).toNat = (hi++lo).toNat+(hi'++lo').toNat := by
  rw [decodeLength_masks,decodeLength_masks]
  change value ((addLoop ByteAuth.concrete _ _ (List.range 16) (mask false)).1.map unmask)+
    65536*(unmask (addLoop ByteAuth.concrete _ _ (List.range 16) (mask false)).2).toNat = _
  have h := addLoop_integer (byteBits lo++byteBits hi) (byteBits lo'++byteBits hi') (List.range 16) false
  have hl := index_bits (byteBits lo++byteBits hi)
  have hr := index_bits (byteBits lo'++byteBits hi')
  have hlen : (byteBits lo++byteBits hi).length=16 := by simp [byteBits]
  have hlen' : (byteBits lo'++byteBits hi').length=16 := by simp [byteBits]
  rw [hlen] at hl
  rw [hlen'] at hr
  simpa only [List.length_range,hl,hr,bytePair_value,Bool.toNat_false,Nat.add_zero] using h


end Semantics
end TlsMpc.Signal.PrivateBuffer
