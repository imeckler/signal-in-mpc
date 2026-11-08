import TlsMpc.Signal.PrivateBufferPacking

namespace TlsMpc.Signal.PrivateBuffer
open Semantics

theorem canonical_bit (b : Bool) :
    ByteAuth.concrete.xor (ByteAuth.eqMask ByteAuth.concrete (mask b) 0)
      (ByteAuth.eqMask ByteAuth.concrete (mask b) 255)=255 := by cases b <;> decide

theorem canonical_masks (bits : List Bool) : canonicalBits ByteAuth.concrete (bits.map mask)=255 := by
  have step (acc : BitVec 8) (b : Bool) :
      ByteAuth.concrete.and acc (ByteAuth.concrete.xor (ByteAuth.eqMask ByteAuth.concrete (mask b) 0)
        (ByteAuth.eqMask ByteAuth.concrete (mask b) 255))=acc := by
    rw [canonical_bit]
    exact BitVec.and_allOnes
  have fold (bits : List Bool) (acc : BitVec 8) :
      bits.foldl (fun acc b => ByteAuth.concrete.and acc
        (ByteAuth.concrete.xor (ByteAuth.eqMask ByteAuth.concrete (mask b) 0)
          (ByteAuth.eqMask ByteAuth.concrete (mask b) 255))) acc = acc := by
    induction bits generalizing acc with
    | nil => rfl
    | cons b bits ih => rw [List.foldl_cons,ih,step]
  unfold canonicalBits
  rw [List.foldl_map]
  change bits.foldl (fun acc b => ByteAuth.concrete.and acc
    (ByteAuth.concrete.xor (ByteAuth.eqMask ByteAuth.concrete (mask b) 0)
      (ByteAuth.eqMask ByteAuth.concrete (mask b) 255))) 255=255
  exact fold bits 255

theorem canonical_decoded (hi lo : BitVec 8) : canonicalBits ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])=255 := by
  rw [decodeLength_masks,canonical_masks]

theorem public_less_decoded (n : Nat) (hn : n<65536) (hi lo : BitVec 8) :
    less ByteAuth.concrete (publicLength ByteAuth.concrete n) (decodeLength ByteAuth.concrete [hi,lo]) =
      if n<(hi++lo).toNat then 255 else 0 := by
  unfold publicLength
  rw [less_decoded_integer]
  change (if ((BitVec.ofNat 8 (n/256))++BitVec.ofNat 8 n).toNat<(hi++lo).toNat then 255 else 0)=_
  rw [public_length_value n hn]

theorem mask_and (b : Bool) (x : BitVec 8) : (mask b &&& x) = if b then x else 0 := by
  cases b
  · simp [mask]
  · change BitVec.allOnes 8 &&& x=x
    exact BitVec.allOnes_and

theorem prefix_byte (capacity : Nat) (hc : capacity<65536) (hi lo : BitVec 8) (raw : List (BitVec 8))
    (i : Nat) (bound : i<capacity) :
    ByteAuth.concrete.and (less ByteAuth.concrete (publicLength ByteAuth.concrete i)
      (decodeLength ByteAuth.concrete [hi,lo])) (OpenResult.get ByteAuth.concrete raw i) =
      if i<(hi++lo).toNat then OpenResult.get ByteAuth.concrete raw i else 0 := by
  rw [public_less_decoded i (by omega)]
  split
  · exact BitVec.allOnes_and
  · simp [ByteAuth.concrete]

def prefixData (a : ByteAuth.Ops B) (capacity count : Nat) (raw : List B) : List B :=
  (List.range capacity).map (fun i => if i<count then OpenResult.get a raw i else a.const 0)

theorem prefixData_length (a : ByteAuth.Ops B) (capacity count : Nat) (raw : List B) :
    (prefixData a capacity count raw).length=capacity := by simp [prefixData]

theorem decoded_length (hi lo : BitVec 8) : (decodeLength ByteAuth.concrete [hi,lo]).length=16 := by
  simp [decodeLength]

theorem public_zero_bits : publicLength ByteAuth.concrete 0=List.replicate 16 0 := by decide

theorem finish_reject (capacity : Nat) (bits raw : List (BitVec 8)) (hb : bits.length=16) (hr : raw.length=capacity) :
    finish ByteAuth.concrete 0 bits raw=zero ByteAuth.concrete capacity := by
  simp only [finish,ByteAuth.release_reject,hb,hr,zero,public_zero_bits]
  rfl

theorem finish_accept (bits raw : List (BitVec 8)) :
    finish ByteAuth.concrete 255 bits raw=⟨255,bits,raw⟩ := by
  simp only [finish,ByteAuth.release_accept]

theorem make_decoded (capacity : Nat) (hc : capacity<65536) (hi lo : BitVec 8) (raw : List (BitVec 8))
    (hr : raw.length=capacity) :
    make ByteAuth.concrete capacity (decodeLength ByteAuth.concrete [hi,lo]) raw =
      if (hi++lo).toNat≤capacity then
        ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩
      else zero ByteAuth.concrete capacity := by
  unfold make
  rw [if_pos ⟨hc,decoded_length hi lo,hr⟩,canonical_decoded,public_less_decoded capacity hc]
  have data : (List.range capacity).map (fun i => ByteAuth.concrete.and
      (less ByteAuth.concrete (publicLength ByteAuth.concrete i) (decodeLength ByteAuth.concrete [hi,lo]))
      (OpenResult.get ByteAuth.concrete raw i)) = prefixData ByteAuth.concrete capacity (hi++lo).toNat raw := by
    apply List.map_congr_left
    intro i bound
    exact prefix_byte capacity hc hi lo raw i (List.mem_range.mp bound)
  rw [data]
  by_cases hn : (hi++lo).toNat≤capacity
  · rw [if_pos hn,if_neg (by omega)]
    change finish ByteAuth.concrete 255 _ _=_
    exact finish_accept _ _
  · rw [if_neg hn,if_pos (by omega)]
    change finish ByteAuth.concrete 0 _ _=_
    exact finish_reject capacity _ _ (decoded_length hi lo) (prefixData_length _ _ _ _)

theorem zero_bits_length (capacity : Nat) : (zero ByteAuth.concrete capacity).lengthBits.length=16 := by
  simp [zero,publicLength,decodeLength]

theorem zero_data_length (capacity : Nat) : (zero ByteAuth.concrete capacity).data.length=capacity := by simp [zero]

theorem fromWire_decoded (capacity : Nat) (hc : capacity<65536) (status hi lo : BitVec 8) (raw : List (BitVec 8))
    (hr : raw.length=capacity) :
    fromWire ByteAuth.concrete capacity (status::hi::lo::raw) =
      if status=255 ∧ (hi++lo).toNat≤capacity then
        ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩
      else zero ByteAuth.concrete capacity := by
  have hlen : (status::hi::lo::raw).length=capacity+3 := by simp [hr,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have take : raw.take capacity=raw := by rw [←hr,List.take_length]
  unfold fromWire
  rw [if_pos hlen]
  simp only [List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,take,OpenResult.get,List.getElem?_cons_zero,Option.getD_some]
  change finish ByteAuth.concrete
    (ByteAuth.concrete.and (make ByteAuth.concrete capacity (decodeLength ByteAuth.concrete [hi,lo]) raw).valid
      (ByteAuth.eqMask ByteAuth.concrete status 255))
    (make ByteAuth.concrete capacity (decodeLength ByteAuth.concrete [hi,lo]) raw).lengthBits
    (make ByteAuth.concrete capacity (decodeLength ByteAuth.concrete [hi,lo]) raw).data = _
  rw [make_decoded capacity hc hi lo raw hr,ByteAuth.eqMask_value]
  by_cases hs : status=255
  · rw [if_pos hs]
    by_cases hn : (hi++lo).toNat≤capacity
    · rw [if_pos hn,if_pos ⟨hs,hn⟩]
      change finish ByteAuth.concrete (ByteAuth.concrete.and 255 255) _ _=_
      rw [show ByteAuth.concrete.and 255 255=255 from by decide]
      exact finish_accept _ _
    · rw [if_neg hn,if_neg (by exact fun h => hn h.2)]
      change finish ByteAuth.concrete (ByteAuth.concrete.and 0 255) _ _=_
      rw [show ByteAuth.concrete.and 0 255=0 from by decide]
      exact finish_reject capacity _ _ (zero_bits_length capacity) (zero_data_length capacity)
  · have hnothing : ¬(status=255 ∧ (hi++lo).toNat≤capacity) := fun h => hs h.1
    rw [if_neg hs,if_neg hnothing]
    by_cases hn : (hi++lo).toNat≤capacity
    · rw [if_pos hn]
      change finish ByteAuth.concrete (ByteAuth.concrete.and 255 0) _ _=_
      rw [show ByteAuth.concrete.and 255 0=0 from by decide]
      exact finish_reject capacity _ _ (decoded_length hi lo) (prefixData_length _ _ _ _)
    · rw [if_neg hn]
      change finish ByteAuth.concrete (ByteAuth.concrete.and 0 0) _ _=_
      rw [show ByteAuth.concrete.and 0 0=0 from by decide]
      exact finish_reject capacity _ _ (zero_bits_length capacity) (zero_data_length capacity)

theorem get_prefixData (a : ByteAuth.Ops B) (capacity count : Nat) (raw : List B) (i : Nat) (hi : i<capacity) :
    OpenResult.get a (prefixData a capacity count raw) i =
      if i<count then OpenResult.get a raw i else a.const 0 := by
  simp [prefixData,OpenResult.get,hi]

theorem prefixData_idempotent (a : ByteAuth.Ops B) (capacity count : Nat) (raw : List B) :
    prefixData a capacity count (prefixData a capacity count raw) = prefixData a capacity count raw := by
  change (List.range capacity).map (fun i => if i<count then OpenResult.get a (prefixData a capacity count raw) i else a.const 0) = _
  apply List.map_congr_left
  intro i bound
  rw [get_prefixData a capacity count raw i (List.mem_range.mp bound)]
  split <;> rfl

theorem make_bits_length (a : ByteAuth.Ops B) (capacity : Nat) (bits raw : List B) :
    (make a capacity bits raw).lengthBits.length=16 := by
  unfold make
  split
  · rename_i good
    simp only [finish,ByteAuth.release,List.length_map,good.2.1]
  · simp [zero,publicLength,decodeLength]

theorem make_data_length (a : ByteAuth.Ops B) (capacity : Nat) (bits raw : List B) :
    (make a capacity bits raw).data.length=capacity := by
  unfold make
  split <;> simp [finish,zero,ByteAuth.release]

theorem and_zero_literal (x : BitVec 8) : x &&& (0 : BitVec 8)=0 := by exact BitVec.and_zero
theorem zero_and_literal (x : BitVec 8) : (0 : BitVec 8) &&& x=0 := by exact BitVec.zero_and

theorem resize_reject (capacity : Nat) (input : Buffer (BitVec 8)) (hs : input.valid≠255) :
    resize ByteAuth.concrete capacity input = zero ByteAuth.concrete capacity := by
  unfold resize
  rw [ByteAuth.eqMask_value]
  have hstatus : input.valid≠ByteAuth.concrete.const 255 := hs
  rw [if_neg hstatus]
  change finish ByteAuth.concrete (_ &&& (0 : BitVec 8)) _ _=_
  rw [and_zero_literal]
  exact finish_reject capacity _ _ (make_bits_length _ _ _ _) (make_data_length _ _ _ _)

theorem resize_decoded (capacity : Nat) (hc : capacity<65536) (hi lo : BitVec 8) (raw : List (BitVec 8))
    (hn : (hi++lo).toNat≤capacity) :
    resize ByteAuth.concrete capacity
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ =
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ := by
  unfold resize
  have mapped : (List.range capacity).map (OpenResult.get ByteAuth.concrete (prefixData ByteAuth.concrete capacity (hi++lo).toNat raw)) =
      prefixData ByteAuth.concrete capacity (hi++lo).toNat raw := by
    have h := index_bytes ByteAuth.concrete (prefixData ByteAuth.concrete capacity (hi++lo).toNat raw)
    simpa only [prefixData_length] using h
  rw [mapped,make_decoded capacity hc hi lo _ (prefixData_length _ _ _ _),if_pos hn,prefixData_idempotent]
  change finish ByteAuth.concrete (ByteAuth.concrete.and 255 (ByteAuth.eqMask ByteAuth.concrete 255 255)) _ _=_
  rw [show ByteAuth.concrete.and 255 (ByteAuth.eqMask ByteAuth.concrete 255 255)=255 from by decide]
  exact finish_accept _ _

theorem addLoop_length (a : ByteAuth.Ops B) (left right : List B) (is : List Nat) (carry : B) :
    (addLoop a left right is carry).1.length=is.length := by
  induction is generalizing carry with
  | nil => rfl
  | cons i is ih => simp only [addLoop,List.length_cons,ih]

theorem append_reject_left (capacity : Nat) (left right : Buffer (BitVec 8)) (hs : left.valid≠255) :
    append ByteAuth.concrete capacity left right = zero ByteAuth.concrete capacity := by
  unfold append
  rw [resize_reject capacity left hs]
  change finish ByteAuth.concrete ((0 : BitVec 8) &&& _) _ _=_
  rw [zero_and_literal]
  apply finish_reject
  · simpa only [List.length_range] using addLoop_length ByteAuth.concrete _ _ (List.range 16) (ByteAuth.concrete.const 0)
  · simp only [List.length_map,List.length_range]

theorem append_reject_right (capacity : Nat) (left right : Buffer (BitVec 8)) (hs : right.valid≠255) :
    append ByteAuth.concrete capacity left right = zero ByteAuth.concrete capacity := by
  unfold append
  rw [resize_reject capacity right hs]
  change finish ByteAuth.concrete (_ &&& ((0 : BitVec 8) &&& _)) _ _=_
  rw [zero_and_literal,and_zero_literal]
  apply finish_reject
  · simpa only [List.length_range] using addLoop_length ByteAuth.concrete _ _ (List.range 16) (ByteAuth.concrete.const 0)
  · simp only [List.length_map,List.length_range]

theorem append_zero_left (capacity : Nat) (right : Buffer (BitVec 8)) :
    append ByteAuth.concrete capacity (zero ByteAuth.concrete capacity) right=zero ByteAuth.concrete capacity :=
  append_reject_left capacity _ right (by change (0 : BitVec 8)≠255;decide)

theorem append_zero_right (capacity : Nat) (left : Buffer (BitVec 8)) :
    append ByteAuth.concrete capacity left (zero ByteAuth.concrete capacity)=zero ByteAuth.concrete capacity :=
  append_reject_right capacity left _ (by change (0 : BitVec 8)≠255;decide)

theorem add_length (pairs : List (Bool × Bool)) (carry : Bool) : (Semantics.add pairs carry).1.length=pairs.length := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair rest ih => simp only [Semantics.add,List.length_cons,ih]

theorem less_public_masks (capacity : Nat) (hc : capacity<65536) (bits : List Bool) (hb : bits.length=16) :
    less ByteAuth.concrete (publicLength ByteAuth.concrete capacity) (bits.map mask) =
      if capacity<value bits then 255 else 0 := by
  unfold publicLength
  rw [decodeLength_masks,less_integer]
  have left := index_bits (byteBits (ByteAuth.concrete.const capacity)++byteBits (ByteAuth.concrete.const (capacity/256)))
  have hlen : (byteBits (ByteAuth.concrete.const capacity)++byteBits (ByteAuth.concrete.const (capacity/256))).length=16 := by simp [byteBits]
  rw [hlen] at left
  have right := index_bits bits
  rw [hb] at right
  rw [left,right,bytePair_value]
  change (if ((BitVec.ofNat 8 (capacity/256))++BitVec.ofNat 8 capacity).toNat<value bits then 255 else 0)=_
  rw [public_length_value capacity hc]

theorem and_full_literal (x : BitVec 8) : (255 : BitVec 8) &&& x=x := by exact BitVec.allOnes_and

theorem add_guard_value (capacity : Nat) (hc : capacity<65536) (left right : List Bool)
    (hl : left.length=16) (hr : right.length=16) :
    let result := addLoop ByteAuth.concrete (left.map mask) (right.map mask) (List.range 16) (mask false)
    ByteAuth.concrete.and (ByteAuth.concrete.not result.2)
      (ByteAuth.concrete.not (less ByteAuth.concrete (publicLength ByteAuth.concrete capacity) result.1)) =
      if value left+value right≤capacity then 255 else 0 := by
  let pairs := (List.range 16).map (fun i => (left[i]?.getD false,right[i]?.getD false))
  let result := Semantics.add pairs false
  have hlen : result.1.length=16 := by simp only [result,add_length,pairs,List.length_map,List.length_range]
  have sum := add_value pairs false
  have li := index_bits left
  have ri := index_bits right
  rw [hl] at li
  rw [hr] at ri
  simp only [pairs,List.map_map,Function.comp_def,li,ri,Bool.toNat_false,Nat.add_zero,List.length_map,List.length_range] at sum
  change value result.1+2^16*result.2.toNat=value left+value right at sum
  have bound := value_lt_pow result.1
  rw [hlen] at bound
  dsimp only
  rw [addLoop_masks,less_public_masks capacity hc _ hlen]
  change ByteAuth.concrete.and (ByteAuth.concrete.not (mask result.2))
    (ByteAuth.concrete.not (if capacity<value result.1 then 255 else 0)) = _
  cases carry : result.2
  · simp only [carry,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at sum
    by_cases good : value left+value right≤capacity
    · rw [if_pos good,if_neg (by omega)]
      change ByteAuth.concrete.and (ByteAuth.concrete.not 0) (ByteAuth.concrete.not 0)=255
      decide
    · rw [if_neg good,if_pos (by omega)]
      change ByteAuth.concrete.and (ByteAuth.concrete.not 0) (ByteAuth.concrete.not 255)=0
      decide
  · simp only [carry,Bool.toNat_true,Nat.mul_one] at sum
    have bad : ¬value left+value right≤capacity := by omega
    rw [if_neg bad]
    change (0 : BitVec 8) &&& _=0
    exact zero_and_literal _

theorem append_decoded_status (capacity : Nat) (hc : capacity<65536)
    (hi lo hi' lo' : BitVec 8) (raw raw' : List (BitVec 8))
    (hl : (hi++lo).toNat≤capacity) (hr : (hi'++lo').toNat≤capacity) :
    (append ByteAuth.concrete capacity
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩
      ⟨255,decodeLength ByteAuth.concrete [hi',lo'],prefixData ByteAuth.concrete capacity (hi'++lo').toNat raw'⟩).valid =
      if (hi++lo).toNat+(hi'++lo').toNat≤capacity then 255 else 0 := by
  have guard := add_guard_value capacity hc (byteBits lo++byteBits hi) (byteBits lo'++byteBits hi')
    (by simp [byteBits]) (by simp [byteBits])
  dsimp only at guard
  rw [←decodeLength_masks hi lo,←decodeLength_masks hi' lo',bytePair_value,bytePair_value] at guard
  unfold append
  rw [resize_decoded capacity hc hi lo raw hl,resize_decoded capacity hc hi' lo' raw' hr]
  change (255 : BitVec 8) &&& ((255 : BitVec 8) &&& _)=_
  rw [and_full_literal,and_full_literal]
  exact guard

def joinedData (a : ByteAuth.Ops B) (capacity leftCount rightCount : Nat) (left right : List B) : List B :=
  (List.range capacity).map (fun i => if i<leftCount then OpenResult.get a left i else
    if i<leftCount+rightCount then OpenResult.get a right (i-leftCount) else a.const 0)

theorem joinedData_length (a : ByteAuth.Ops B) (capacity leftCount rightCount : Nat) (left right : List B) :
    (joinedData a capacity leftCount rightCount left right).length=capacity := by simp [joinedData]

theorem prefix_shift_xor (capacity leftCount rightCount : Nat) (left right : List (BitVec 8)) :
    (List.range capacity).map (fun i => ByteAuth.concrete.xor
      (OpenResult.get ByteAuth.concrete (prefixData ByteAuth.concrete capacity leftCount left) i)
      (OpenResult.get ByteAuth.concrete (shifted ByteAuth.concrete leftCount
        (prefixData ByteAuth.concrete capacity rightCount right)) i)) =
      joinedData ByteAuth.concrete capacity leftCount rightCount left right := by
  apply List.map_congr_left
  intro i member
  have bound := List.mem_range.mp member
  rw [get_prefixData ByteAuth.concrete capacity leftCount left i bound,
    get_shifted ByteAuth.concrete leftCount _ i (by simpa only [prefixData_length] using bound)]
  by_cases hi : i<leftCount
  · rw [if_pos hi,if_pos hi,if_pos hi]
    exact BitVec.xor_zero
  · rw [if_neg hi,if_neg hi,get_prefixData ByteAuth.concrete capacity rightCount right (i-leftCount) (by omega)]
    rw [if_neg hi]
    by_cases within : i<leftCount+rightCount
    · rw [if_pos within,if_pos (by omega)]
      exact BitVec.zero_xor
    · rw [if_neg within,if_neg (by omega)]
      decide

theorem append_decoded (capacity : Nat) (hc : capacity<65536)
    (hi lo hi' lo' : BitVec 8) (raw raw' : List (BitVec 8))
    (hl : (hi++lo).toNat≤capacity) (hr : (hi'++lo').toNat≤capacity) :
    append ByteAuth.concrete capacity
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩
      ⟨255,decodeLength ByteAuth.concrete [hi',lo'],prefixData ByteAuth.concrete capacity (hi'++lo').toNat raw'⟩ =
      if (hi++lo).toNat+(hi'++lo').toNat≤capacity then
        ⟨255,(addLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])
          (decodeLength ByteAuth.concrete [hi',lo']) (List.range 16) (ByteAuth.concrete.const 0)).1,
          joinedData ByteAuth.concrete capacity (hi++lo).toNat (hi'++lo').toNat raw raw'⟩
      else zero ByteAuth.concrete capacity := by
  have accepted := append_decoded_status capacity hc hi lo hi' lo' raw raw' hl hr
  unfold append at accepted ⊢
  rw [resize_decoded capacity hc hi lo raw hl,resize_decoded capacity hc hi' lo' raw' hr] at accepted ⊢
  dsimp only [finish] at accepted
  dsimp only
  rw [accepted,shiftLoop_decoded,prefix_shift_xor]
  by_cases fits : (hi++lo).toNat+(hi'++lo').toNat≤capacity
  · rw [if_pos fits,if_pos fits]
    exact finish_accept _ _
  · rw [if_neg fits,if_neg fits]
    apply finish_reject
    · simpa only [List.length_range] using addLoop_length ByteAuth.concrete _ _ (List.range 16) (ByteAuth.concrete.const 0)
    · exact joinedData_length _ _ _ _ _ _

theorem add_decoded_value_of_fits (capacity : Nat) (hc : capacity<65536) (hi lo hi' lo' : BitVec 8)
    (fits : (hi++lo).toNat+(hi'++lo').toNat≤capacity) :
    value ((addLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])
      (decodeLength ByteAuth.concrete [hi',lo']) (List.range 16) (ByteAuth.concrete.const 0)).1.map unmask) =
      (hi++lo).toNat+(hi'++lo').toNat := by
  have sum := add_decoded_integer hi lo hi' lo'
  change value ((addLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])
      (decodeLength ByteAuth.concrete [hi',lo']) (List.range 16) (ByteAuth.concrete.const 0)).1.map unmask)+
      65536*(unmask (addLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])
      (decodeLength ByteAuth.concrete [hi',lo']) (List.range 16) (ByteAuth.concrete.const 0)).2).toNat = _ at sum
  cases carry : unmask (addLoop ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo])
      (decodeLength ByteAuth.concrete [hi',lo']) (List.range 16) (ByteAuth.concrete.const 0)).2
  · simpa only [carry,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using sum
  · simp only [carry,Bool.toNat_true,Nat.mul_one] at sum
    omega

theorem get_joinedData (a : ByteAuth.Ops B) (capacity leftCount rightCount : Nat) (left right : List B)
    (i : Nat) (hi : i<capacity) :
    OpenResult.get a (joinedData a capacity leftCount rightCount left right) i =
      if i<leftCount then OpenResult.get a left i else
      if i<leftCount+rightCount then OpenResult.get a right (i-leftCount) else a.const 0 := by
  simp [joinedData,OpenResult.get,hi]

theorem joinedData_as_append (a : ByteAuth.Ops B) (capacity leftCount rightCount : Nat) (left right : List B)
    (hl : leftCount≤left.length) (hr : rightCount≤right.length) (fits : leftCount+rightCount≤capacity) :
    joinedData a capacity leftCount rightCount left right =
      left.take leftCount ++ right.take rightCount ++ List.replicate (capacity-(leftCount+rightCount)) (a.const 0) := by
  have llen : (left.take leftCount).length=leftCount := by simp [Nat.min_eq_left hl]
  have rlen : (right.take rightCount).length=rightCount := by simp [Nat.min_eq_left hr]
  apply List.ext_getElem
  · simp only [joinedData_length,List.length_append,llen,rlen,List.length_replicate]
    omega
  · intro i hi hj
    have bound : i<capacity := by simpa only [joinedData_length] using hi
    have hg (bytes : List B) (h : i<bytes.length) : OpenResult.get a bytes i=bytes[i] := by
      simp only [OpenResult.get,List.getElem?_eq_getElem h,Option.getD_some]
    rw [←hg _ hi,←hg _ hj,get_joinedData a capacity leftCount rightCount left right i bound]
    simp only [OpenResult.get,List.getElem?_append,List.length_append,llen,rlen,List.getElem?_take,List.getElem?_replicate]
    by_cases first : i<leftCount
    · have within : i<leftCount+rightCount := by omega
      simp only [if_pos first,if_pos within]
    · rw [if_neg first,if_neg first]
      by_cases second : i<leftCount+rightCount
      · have inside : i-leftCount<rightCount := by omega
        simp only [if_pos second,if_pos inside]
      · have outside : ¬i-leftCount<rightCount := by omega
        have padding : i-(leftCount+rightCount)<capacity-(leftCount+rightCount) := by omega
        simp only [if_neg second,if_neg outside,if_pos padding,Option.getD_some]

end TlsMpc.Signal.PrivateBuffer
