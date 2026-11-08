import TlsMpc.Signal.PrivateBufferWireSemantics
import TlsMpc.Signal.PrivateHash

namespace TlsMpc.Signal.PrivateHash
open PrivateBuffer PrivateBuffer.Semantics

theorem value_injective (left right : List Bool) (hlen : left.length=right.length) (heq : value left=value right) : left=right := by
  induction left generalizing right with
  | nil =>
    have empty : right=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    exact empty.symm
  | cons x xs ih =>
    cases right with
    | nil => simp at hlen
    | cons y ys =>
      have lengths : xs.length=ys.length := by simp only [List.length_cons] at hlen;omega
      have bits : x=y := by
        cases x <;> cases y <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at heq ⊢ <;> omega
      subst y
      have values : value xs=value ys := by simp only [value] at heq;omega
      rw [ih ys lengths values]

theorem decode_encode_masks (bits : List Bool) (hb : bits.length=16) :
    decodeLength ByteAuth.concrete (encodeLength ByteAuth.concrete (bits.map mask))=bits.map mask := by
  let high := encodeByte ByteAuth.concrete (bits.map mask) 0
  let low := encodeByte ByteAuth.concrete (bits.map mask) 1
  change decodeLength ByteAuth.concrete [high,low]=_
  rw [decodeLength_masks]
  apply congrArg (List.map mask)
  apply value_injective
  · simp [byteBits,hb]
  · rw [bytePair_value]
    exact encodeLength_masks_value bits hb

theorem decoded_equal_iff_value (hi lo hi' lo' : BitVec 8) :
    decodeLength ByteAuth.concrete [hi,lo]=decodeLength ByteAuth.concrete [hi',lo'] ↔
      (hi++lo).toNat=(hi'++lo').toNat := by
  constructor
  · intro h
    have numeric := congrArg (fun bits => value (bits.map unmask)) h
    simpa only [decodeLength_value] using numeric
  · intro numeric
    rw [byte_append_value,byte_append_value] at numeric
    have a : hi.toNat<256 := hi.isLt
    have b : lo.toNat<256 := lo.isLt
    have c : hi'.toNat<256 := hi'.isLt
    have d : lo'.toNat<256 := lo'.isLt
    have hhigh : hi=hi' := BitVec.eq_of_toNat_eq (by omega)
    have hlow : lo=lo' := BitVec.eq_of_toNat_eq (by omega)
    rw [hhigh,hlow]

theorem decoded_less_public (hi lo : BitVec 8) (n : Nat) (hn : n<65536) :
    less ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo]) (publicLength ByteAuth.concrete n) =
      if (hi++lo).toNat<n then 255 else 0 := by
  unfold publicLength
  rw [less_decoded_integer]
  change (if (hi++lo).toNat<((BitVec.ofNat 8 (n/256))++BitVec.ofNat 8 n).toNat then 255 else 0)=_
  rw [public_length_value n hn]

theorem decoded_equal_public (hi lo : BitVec 8) (n : Nat) (hn : n<65536) :
    ByteAuth.equalMask ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo]) (publicLength ByteAuth.concrete n) =
      if (hi++lo).toNat=n then 255 else 0 := by
  rw [ByteAuth.equalMask_value]
  unfold publicLength
  simp only [decoded_equal_iff_value]
  change (if (hi++lo).toNat=((BitVec.ofNat 8 (n/256))++BitVec.ofNat 8 n).toNat then 255 else 0)=_
  rw [public_length_value n hn]

theorem finalMask_decoded (hi lo : BitVec 8) (index : Nat) (hu : 64*index+56<65536) :
    finalMask ByteAuth.concrete (decodeLength ByteAuth.concrete [hi,lo]) index =
      if index=((hi++lo).toNat+8)/64 then 255 else 0 := by
  unfold finalMask
  rw [decoded_less_public hi lo (64*index+56) hu]
  by_cases zero : index=0
  · subst index
    rw [if_pos rfl]
    by_cases within : (hi++lo).toNat<56
    · have final : 0=((hi++lo).toNat+8)/64 := by omega
      rw [if_pos (by simpa using within),if_pos final]
      change ByteAuth.concrete.and 255 255=255
      decide
    · have final : ¬0=((hi++lo).toNat+8)/64 := by omega
      rw [if_neg (by simpa using within),if_neg final]
      change ByteAuth.concrete.and 0 255=0
      decide
  · rw [if_neg zero,decoded_less_public hi lo (64*index-8) (by omega)]
    by_cases upper : (hi++lo).toNat<64*index+56
    · rw [if_pos upper]
      by_cases lower : (hi++lo).toNat<64*index-8
      · have final : ¬index=((hi++lo).toNat+8)/64 := by omega
        rw [if_pos lower,if_neg final]
        change ByteAuth.concrete.and 255 (ByteAuth.concrete.not 255)=0
        decide
      · have final : index=((hi++lo).toNat+8)/64 := by omega
        rw [if_neg lower,if_pos final]
        change ByteAuth.concrete.and 255 (ByteAuth.concrete.not 0)=255
        decide
    · rw [if_neg upper]
      have final : ¬index=((hi++lo).toNat+8)/64 := by omega
      rw [if_neg final]
      by_cases lower : (hi++lo).toNat<64*index-8
      · rw [if_pos lower]
        change ByteAuth.concrete.and 0 (ByteAuth.concrete.not 255)=0
        decide
      · rw [if_neg lower]
        change ByteAuth.concrete.and 0 (ByteAuth.concrete.not 0)=0
        decide

theorem lengthBytes_decoded (prior : Nat) (hp : prior≤64) (hi lo : BitVec 8) :
    lengthBytes Sha256.concrete ByteAuth.concrete prior (decodeLength ByteAuth.concrete [hi,lo]) =
      List.replicate 4 0 ++ (List.range 4).map (fun i =>
        BitVec.ofNat 8 (((prior+(hi++lo).toNat)*8)/2^(8*(3-i)))) := by
  let n : BitVec 32 := Sha256.concrete.add (Sha256.concrete.pack 0 0 hi lo) (Sha256.concrete.wordConst prior)
  let twice := n+n
  let four := twice+twice
  let eight := four+four
  have inputBound : (hi++lo).toNat<65536 := (hi++lo).isLt
  have nVal : n.toNat=prior+(hi++lo).toNat := by
    change ((((0 : BitVec 16)++(hi++lo))+BitVec.ofNat 32 prior).toNat)=_
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    have packed : ((0 : BitVec 16)++(hi++lo)).toNat=(hi++lo).toNat := by
      rw [BitVec.toNat_append (0 : BitVec 16) (hi++lo)]
      simp
    rw [packed,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
    omega
  have twiceVal : twice.toNat=2*(prior+(hi++lo).toNat) := by
    change (n+n).toNat=_
    rw [BitVec.toNat_add,nVal,Nat.mod_eq_of_lt (by omega)]
    omega
  have fourVal : four.toNat=4*(prior+(hi++lo).toNat) := by
    change (twice+twice).toNat=_
    rw [BitVec.toNat_add,twiceVal,Nat.mod_eq_of_lt (by omega)]
    omega
  have eightVal : eight.toNat=(prior+(hi++lo).toNat)*8 := by
    change (four+four).toNat=_
    rw [BitVec.toNat_add,fourVal,Nat.mod_eq_of_lt (by omega)]
    omega
  unfold lengthBytes
  rw [length_roundtrip]
  change List.replicate 4 0 ++ (List.range 4).map (fun i => eight.extractLsb' (8*(3-i)) 8)=_
  congr 1
  apply List.map_congr_left
  intro i member
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,eightVal,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]

theorem get_prefix_all (capacity count : Nat) (raw : List (BitVec 8)) (hc : count≤capacity) (i : Nat) :
    OpenResult.get ByteAuth.concrete (prefixData ByteAuth.concrete capacity count raw) i =
      if i<count then OpenResult.get ByteAuth.concrete raw i else 0 := by
  by_cases within : i<capacity
  · exact get_prefixData _ _ _ _ _ within
  · have outside : (prefixData ByteAuth.concrete capacity count raw).length≤i := by
      rw [prefixData_length]
      omega
    have notData : ¬i<count := by omega
    rw [if_neg notData]
    simp only [OpenResult.get,List.getElem?_eq_none outside,Option.getD_none]
    rfl

theorem flag_and (p : Prop) [Decidable p] (x : BitVec 8) :
    ByteAuth.concrete.and (if p then 255 else 0) x = if p then x else 0 := by
  by_cases h : p
  · rw [if_pos h,if_pos h]
    exact BitVec.allOnes_and
  · rw [if_neg h,if_neg h]
    exact BitVec.zero_and

theorem xor_zero_literal (x : BitVec 8) : x ^^^ (0 : BitVec 8)=x := by exact BitVec.xor_zero
theorem zero_xor_literal (x : BitVec 8) : (0 : BitVec 8) ^^^ x=x := by exact BitVec.zero_xor

theorem xor_disjoint (p q r : Prop) [Decidable p] [Decidable q] [Decidable r]
    (pq : ¬(p∧q)) (pr : ¬(p∧r)) (qr : ¬(q∧r)) (x y z : BitVec 8) :
    (if p then x else 0) ^^^ ((if q then y else 0) ^^^ (if r then z else 0)) =
      if p then x else if q then y else if r then z else 0 := by
  by_cases hp : p
  · have hq : ¬q := fun h => pq ⟨hp,h⟩
    have hr : ¬r := fun h => pr ⟨hp,h⟩
    simp only [if_pos hp,if_neg hq,if_neg hr,xor_zero_literal]
  · rw [if_neg hp,if_neg hp,zero_xor_literal]
    by_cases hq : q
    · have hr : ¬r := fun h => qr ⟨hq,h⟩
      simp only [if_pos hq,if_neg hr,xor_zero_literal]
    · simp only [if_neg hq,zero_xor_literal]

def bitLengthSuffix (prior count : Nat) : List (BitVec 8) :=
  List.replicate 4 0 ++ (List.range 4).map (fun i => BitVec.ofNat 8 (((prior+count)*8)/2^(8*(3-i))))

def paddingByte (prior count blockIndex offset : Nat) (raw : List (BitVec 8)) : BitVec 8 :=
  let i := 64*blockIndex+offset
  if i<count then OpenResult.get ByteAuth.concrete raw i else if i=count then 128 else
    if 56≤offset ∧ blockIndex=(count+8)/64 then OpenResult.get ByteAuth.concrete (bitLengthSuffix prior count) (offset-56) else 0

theorem paddedBlock_decoded (prior capacity index : Nat) (hp : prior≤64) (blockBound : 64*(index+1)≤65536)
    (hi lo : BitVec 8) (raw : List (BitVec 8)) (hcount : (hi++lo).toNat≤capacity) :
    paddedBlock Sha256.concrete ByteAuth.concrete prior index
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ =
      (List.range 64).map (paddingByte prior (hi++lo).toNat index · raw) := by
  unfold paddedBlock
  dsimp only
  rw [finalMask_decoded hi lo index (by omega),lengthBytes_decoded prior hp hi lo]
  apply List.map_congr_left
  intro offset member
  have offsetBound : offset<64 := List.mem_range.mp member
  rw [decoded_equal_public hi lo (index*64+offset) (by omega),get_prefix_all capacity _ raw hcount (index*64+offset),flag_and]
  change (if index*64+offset<(hi++lo).toNat then _ else (0 : BitVec 8)) ^^^
    ((if (hi++lo).toNat=index*64+offset then 128 else 0) ^^^
      (if 56≤offset then ByteAuth.concrete.and (if index=((hi++lo).toNat+8)/64 then 255 else 0)
        (OpenResult.get ByteAuth.concrete (bitLengthSuffix prior (hi++lo).toNat) (offset-56)) else 0)) = _
  have suffix : (if 56≤offset then ByteAuth.concrete.and (if index=((hi++lo).toNat+8)/64 then 255 else 0)
      (OpenResult.get ByteAuth.concrete (bitLengthSuffix prior (hi++lo).toNat) (offset-56)) else 0) =
      if 56≤offset ∧ index=((hi++lo).toNat+8)/64 then
        OpenResult.get ByteAuth.concrete (bitLengthSuffix prior (hi++lo).toNat) (offset-56) else 0 := by
    by_cases last : 56≤offset
    · rw [if_pos last,flag_and]
      simp only [last,true_and]
    · rw [if_neg last]
      simp only [last,false_and,if_false]
  rw [suffix,xor_disjoint]
  · unfold paddingByte
    simp only [Nat.mul_comm,eq_comm]
  · omega
  · intro both
    obtain ⟨data,last,final⟩ := both
    omega
  · intro both
    obtain ⟨marker,last,final⟩ := both
    omega

theorem public_length_suffix (length : Nat) (bound : length*8<2^32) :
    (List.range 8).map (fun i => Sha256.concrete.byteConst (length*8/2^(8*(7-i)))) = bitLengthSuffix 0 length := by
  have h56 : length*8/2^56=0 := Nat.div_eq_of_lt (by omega)
  have h48 : length*8/2^48=0 := Nat.div_eq_of_lt (by omega)
  have h40 : length*8/2^40=0 := Nat.div_eq_of_lt (by omega)
  have h32 : length*8/2^32=0 := Nat.div_eq_of_lt bound
  simp [bitLengthSuffix,List.range_succ,h56,h48,h40,h32,Sha256.concrete]

def paddingEnd (count : Nat) : Nat := 64*((count+8)/64+1)

theorem padding_end_arithmetic (prior count : Nat) (hp : prior%64=0) :
    count+9+((64-(prior+count+9)%64)%64)=paddingEnd count := by
  have rem : (prior+count+9)%64=(count+9)%64 := by
    rw [Nat.add_assoc,Nat.add_mod,hp]
    simp
  rw [rem]
  unfold paddingEnd
  omega

def paddedPublic (prior count : Nat) (raw : List (BitVec 8)) : List (BitVec 8) :=
  raw.take count ++ [128] ++ List.replicate (paddingEnd count-count-9) 0 ++ bitLengthSuffix prior count

theorem paddedPublic_eq_sha (prior count : Nat) (hp : prior%64=0) (bound : (prior+count)*8<2^32)
    (raw : List (BitVec 8)) :
    paddedPublic prior count raw=raw.take count++Sha256.padding Sha256.concrete (prior+count) := by
  have length := public_length_suffix (prior+count) bound
  simp only [bitLengthSuffix,Nat.zero_add] at length
  change (List.range 8).map (fun i => Sha256.concrete.byteConst ((prior+count)*8/2^(8*(7-i)))) =
    bitLengthSuffix prior count at length
  unfold paddedPublic Sha256.padding
  rw [length]
  have zeros : paddingEnd count-count-9=(64-(prior+count+9)%64)%64 := by
    have h := padding_end_arithmetic prior count hp
    omega
  rw [zeros]
  simp only [List.append_assoc]
  rfl

theorem suffix_length (prior count : Nat) : (bitLengthSuffix prior count).length=8 := by simp [bitLengthSuffix]

theorem paddingEnd_bound (count : Nat) : count+9≤paddingEnd count := by unfold paddingEnd;omega

theorem paddingEnd_tail (count : Nat) : paddingEnd count-8=64*((count+8)/64)+56 := by unfold paddingEnd;omega

theorem paddedPublic_length (prior count : Nat) (raw : List (BitVec 8)) (hraw : count≤raw.length) :
    (paddedPublic prior count raw).length=paddingEnd count := by
  have bound := paddingEnd_bound count
  simp only [paddedPublic,List.length_append,List.length_take,Nat.min_eq_left hraw,List.length_cons,List.length_nil,List.length_replicate,suffix_length]
  omega

theorem get_paddedPublic (prior count pos : Nat) (raw : List (BitVec 8)) (hraw : count≤raw.length) :
    OpenResult.get ByteAuth.concrete (paddedPublic prior count raw) pos =
      if pos<count then OpenResult.get ByteAuth.concrete raw pos else if pos=count then 128 else
        if paddingEnd count-8≤pos ∧ pos<paddingEnd count then
          OpenResult.get ByteAuth.concrete (bitLengthSuffix prior count) (pos-(paddingEnd count-8)) else 0 := by
  have bound := paddingEnd_bound count
  have firstLength : (raw.take count).length=count := by simp [Nat.min_eq_left hraw]
  have headerLength : count+1+(paddingEnd count-count-9)=paddingEnd count-8 := by omega
  unfold paddedPublic
  simp only [OpenResult.get,List.getElem?_append,List.length_append,firstLength,List.length_cons,List.length_nil,List.length_replicate,headerLength]
  by_cases data : pos<count
  · have head : pos<paddingEnd count-8 := by omega
    have before : pos<count+1 := by omega
    simp only [if_pos data,if_pos head,if_pos before,List.getElem?_take_of_lt data]
  · simp only [if_neg data]
    by_cases marker : pos=count
    · subst pos
      have head : count<paddingEnd count-8 := by omega
      simp only [if_pos head,if_pos (Nat.lt_succ_self count),if_neg (Nat.lt_irrefl count),Nat.sub_self,List.getElem?_cons_zero,Option.getD_some,if_pos rfl,if_true]
    · rw [if_neg marker]
      have notBefore : ¬pos<count+1 := by omega
      by_cases head : pos<paddingEnd count-8
      · have inside : pos-(count+1)<paddingEnd count-count-9 := by omega
        have notTail : ¬(paddingEnd count-8≤pos ∧ pos<paddingEnd count) := by omega
        simp only [if_pos head,if_neg notBefore,if_neg data,List.getElem?_replicate_of_lt inside,Option.getD_some,if_neg notTail]
      · rw [if_neg head]
        by_cases within : pos<paddingEnd count
        · have tail : paddingEnd count-8≤pos ∧ pos<paddingEnd count := by omega
          rw [if_pos tail]
        · have outside : (bitLengthSuffix prior count).length≤pos-(paddingEnd count-8) := by rw [suffix_length];omega
          have notTail : ¬(paddingEnd count-8≤pos ∧ pos<paddingEnd count) := by omega
          simp only [List.getElem?_eq_none outside,Option.getD_none,if_neg notTail]
          rfl

theorem paddingByte_eq_get (prior count index offset : Nat) (raw : List (BitVec 8))
    (hraw : count≤raw.length) (hoffset : offset<64) :
    paddingByte prior count index offset raw =
      OpenResult.get ByteAuth.concrete (paddedPublic prior count raw) (64*index+offset) := by
  rw [get_paddedPublic prior count (64*index+offset) raw hraw]
  unfold paddingByte
  by_cases data : 64*index+offset<count
  · simp only [if_pos data]
  · simp only [if_neg data]
    by_cases marker : 64*index+offset=count
    · simp only [if_pos marker]
    · simp only [if_neg marker]
      have tail : (56≤offset ∧ index=(count+8)/64) ↔
          (paddingEnd count-8≤64*index+offset ∧ 64*index+offset<paddingEnd count) := by
        unfold paddingEnd
        omega
      by_cases last : 56≤offset ∧ index=(count+8)/64
      · rw [if_pos last,if_pos (tail.mp last)]
        have indexEq := last.2
        subst index
        congr 1
        unfold paddingEnd
        omega
      · rw [if_neg last,if_neg (fun h => last (tail.mpr h))]

theorem paddedBlock_reference (prior capacity index : Nat) (hp : prior≤64) (blockBound : 64*(index+1)≤65536)
    (hi lo : BitVec 8) (raw : List (BitVec 8)) (hcount : (hi++lo).toNat≤capacity) (hraw : (hi++lo).toNat≤raw.length) :
    paddedBlock Sha256.concrete ByteAuth.concrete prior index
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ =
      (List.range 64).map (fun offset => OpenResult.get ByteAuth.concrete
        (paddedPublic prior (hi++lo).toNat raw) (64*index+offset)) := by
  rw [paddedBlock_decoded prior capacity index hp blockBound hi lo raw hcount]
  apply List.map_congr_left
  intro offset member
  exact paddingByte_eq_get prior _ index offset raw hraw (List.mem_range.mp member)

theorem chunk_eq_gets (data : List (BitVec 8)) (index : Nat) (bound : 64*index+64≤data.length) :
    (data.drop (64*index)).take 64=(List.range 64).map (fun offset => OpenResult.get ByteAuth.concrete data (64*index+offset)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_map,List.length_range]
    omega
  · intro offset hi hj
    have ho : offset<64 := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_take,List.getElem_drop,List.getElem_map,List.getElem_range]
    have element : 64*index+offset<data.length := by omega
    simp only [OpenResult.get,List.getElem?_eq_getElem element,Option.getD_some]

theorem paddedBlock_eq_public_chunk (prior capacity index : Nat) (hp : prior≤64) (blockBound : 64*(index+1)≤65536)
    (hi lo : BitVec 8) (raw : List (BitVec 8)) (hcount : (hi++lo).toNat≤capacity) (hraw : (hi++lo).toNat≤raw.length)
    (beforeFinal : index≤((hi++lo).toNat+8)/64) :
    paddedBlock Sha256.concrete ByteAuth.concrete prior index
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ =
      ((paddedPublic prior (hi++lo).toNat raw).drop (64*index)).take 64 := by
  rw [paddedBlock_reference prior capacity index hp blockBound hi lo raw hcount hraw]
  symm
  apply chunk_eq_gets
  rw [paddedPublic_length prior _ raw hraw]
  unfold paddingEnd
  omega

theorem blocks_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (prior : Nat) (input : Buffer B)
    (count index : Nat) (state : Sha256.State W) : (blocks s a prior input count index state).length=32 := by
  induction count generalizing index state with
  | zero => simp [blocks]
  | succ count ih => simp only [blocks,List.length_zipWith,ByteAuth.release,List.length_map,Sha256.digest_length,ih,Nat.min_self]

theorem xor_zero_list (data : List (BitVec 8)) :
    (List.replicate data.length 0).zipWith ByteAuth.concrete.xor data=data := by
  induction data with
  | nil => rfl
  | cons b data ih =>
    simp only [List.length_cons,List.replicate_succ,List.zipWith_cons_cons,ih]
    congr 1
    exact BitVec.zero_xor

theorem xor_list_zero (data : List (BitVec 8)) :
    data.zipWith ByteAuth.concrete.xor (List.replicate data.length 0)=data := by
  induction data with
  | nil => rfl
  | cons b data ih =>
    simp only [List.length_cons,List.replicate_succ,List.zipWith_cons_cons,ih]
    congr 1
    exact BitVec.xor_zero

theorem blocks_after_final (prior capacity : Nat) (hi lo : BitVec 8) (raw : List (BitVec 8))
    (count index : Nat) (state : Sha256.State (BitVec 32)) (afterFinal : ((hi++lo).toNat+8)/64<index)
    (rangeBound : 64*(index+count)≤65536) :
    blocks Sha256.concrete ByteAuth.concrete prior
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩
      count index state=List.replicate 32 0 := by
  induction count generalizing index state with
  | zero => rfl
  | succ count ih =>
    rw [blocks,finalMask_decoded hi lo index (by omega),if_neg (by omega),ByteAuth.release_reject,Sha256.digest_length]
    rw [ih (index+1) _ (by omega) (by omega)]
    simpa only [List.length_replicate] using xor_zero_list (List.replicate 32 (0 : BitVec 8))

theorem packWords_head (s : Sha256.Ops B W) (data : List B) (bound : 64≤data.length) :
    (Sha256.packWords s data).take 16=Sha256.packWords s (data.take 64) ∧
      (Sha256.packWords s data).drop 16=Sha256.packWords s (data.drop 64) := by
  have size : (data.take 64).length=64 := by simp only [List.length_take];omega
  have eq := HmacPrepared.packWords_append s (data.take 64) (data.drop 64) (by simpa only [size] using (show 64%4=0 from by decide))
  rw [List.take_append_drop] at eq
  have words : (Sha256.packWords s (data.take 64)).length=16 := by rw [Sha256.packed_length,size]
  rw [eq,List.take_left' words,List.drop_left' words]
  exact ⟨rfl,rfl⟩

theorem blocks_through_final (prior capacity : Nat) (hp : prior≤64) (hi lo : BitVec 8) (raw : List (BitVec 8))
    (hcount : (hi++lo).toNat≤capacity) (hraw : (hi++lo).toNat≤raw.length)
    (count index : Nat) (state : Sha256.State (BitVec 32))
    (beforeFinal : index≤((hi++lo).toNat+8)/64) (containsFinal : ((hi++lo).toNat+8)/64<index+count)
    (rangeBound : 64*(index+count)≤65536) :
    blocks Sha256.concrete ByteAuth.concrete prior
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ count index state =
      Sha256.digest Sha256.concrete (Sha256.processBlocks Sha256.concrete (((hi++lo).toNat+8)/64-index+1)
        (Sha256.packWords Sha256.concrete ((paddedPublic prior (hi++lo).toNat raw).drop (64*index))) state) := by
  induction count generalizing index state with
  | zero => omega
  | succ count ih =>
    have blockBound : 64*(index+1)≤65536 := by omega
    have block := paddedBlock_eq_public_chunk prior capacity index hp blockBound hi lo raw hcount hraw beforeFinal
    have remain : 64≤((paddedPublic prior (hi++lo).toNat raw).drop (64*index)).length := by
      rw [List.length_drop,paddedPublic_length prior _ raw hraw]
      unfold paddingEnd
      omega
    have packed := packWords_head Sha256.concrete ((paddedPublic prior (hi++lo).toNat raw).drop (64*index)) remain
    rw [blocks,block,finalMask_decoded hi lo index (by omega)]
    by_cases hit : index=((hi++lo).toNat+8)/64
    · rw [if_pos hit,ByteAuth.release_accept,
        blocks_after_final prior capacity hi lo raw count (index+1) _ (by omega) (by omega)]
      have cancel := xor_list_zero (Sha256.digest Sha256.concrete (Sha256.compress Sha256.concrete state
        (Sha256.packWords Sha256.concrete (((paddedPublic prior (hi++lo).toNat raw).drop (64*index)).take 64))))
      simp only [Sha256.digest_length] at cancel
      rw [cancel]
      have one : ((hi++lo).toNat+8)/64-index+1=1 := by omega
      rw [one,Sha256.processBlocks]
      simp only [Sha256.processBlocks]
      rw [packed.1]
    · rw [if_neg hit,ByteAuth.release_reject,Sha256.digest_length]
      have cancel := xor_zero_list (blocks Sha256.concrete ByteAuth.concrete prior
        ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩
        count (index+1) (Sha256.compress Sha256.concrete state
          (Sha256.packWords Sha256.concrete (((paddedPublic prior (hi++lo).toNat raw).drop (64*index)).take 64))))
      simp only [blocks_length] at cancel
      rw [cancel,ih (index+1) _ (by omega) (by omega) (by omega)]
      have steps : ((hi++lo).toNat+8)/64-index+1=(((hi++lo).toNat+8)/64-(index+1)+1)+1 := by omega
      conv => rhs; rw [steps,Sha256.processBlocks]
      rw [packed.1,packed.2]
      simp only [List.drop_drop,Nat.mul_add,Nat.mul_one]

def hashAfterSpec (prior : Nat) (state : Sha256.State (BitVec 32)) (message : List (BitVec 8)) : List (BitVec 8) :=
  let words := Sha256.packWords Sha256.concrete (message++Sha256.padding Sha256.concrete (prior+message.length))
  Sha256.digest Sha256.concrete (Sha256.processBlocks Sha256.concrete (words.length/16) words state)

theorem hashAfter_decoded (prior capacity : Nat) (hp : prior≤64) (hpmod : prior%64=0) (hcap : capacity≤16384)
    (hi lo : BitVec 8) (raw : List (BitVec 8)) (hcount : (hi++lo).toNat≤capacity) (hraw : (hi++lo).toNat≤raw.length)
    (state : Sha256.State (BitVec 32)) :
    hashAfter Sha256.concrete ByteAuth.concrete prior state capacity
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ =
      ⟨255,publicLength ByteAuth.concrete 32,hashAfterSpec prior state (raw.take (hi++lo).toNat)⟩ := by
  have hc : capacity<65536 := by omega
  have blockCount : ((hi++lo).toNat+8)/64<(capacity+9+63)/64 := by omega
  have blockRange : 64*(0+(capacity+9+63)/64)≤65536 := by omega
  have blocksCorrect := blocks_through_final prior capacity hp hi lo raw hcount hraw ((capacity+9+63)/64) 0 state
    (by omega) (by omega) blockRange
  simp only [Nat.sub_zero,Nat.mul_zero,List.drop_zero] at blocksCorrect
  have padded := paddedPublic_eq_sha prior (hi++lo).toNat hpmod (by omega) raw
  have rawLength : (raw.take (hi++lo).toNat).length=(hi++lo).toNat := by simp [Nat.min_eq_left hraw]
  have size : (Sha256.packWords Sha256.concrete (raw.take (hi++lo).toNat++
      Sha256.padding Sha256.concrete (prior+(hi++lo).toNat))).length/16=((hi++lo).toNat+8)/64+1 := by
    rw [←padded,Sha256.packed_length,paddedPublic_length prior _ raw hraw]
    unfold paddingEnd
    omega
  unfold hashAfter
  rw [resize_decoded capacity hc hi lo raw hcount,if_pos hcap,blocksCorrect,padded]
  unfold hashAfterSpec
  dsimp only
  rw [rawLength,size]
  exact finish_accept _ _

theorem hashAfterSpec_zero (message : List (BitVec 8)) :
    hashAfterSpec 0 (Sha256.initial Sha256.concrete) message=Sha256.hash Sha256.concrete message := by
  simp only [hashAfterSpec,Sha256.hash,Nat.zero_add]

theorem hashAfterSpec_sixtyfour (state : Sha256.State (BitVec 32)) (message : List (BitVec 8)) :
    hashAfterSpec 64 state message=HmacPrepared.hashAfterBlock Sha256.concrete state message := by
  rfl

theorem hash_decoded (capacity : Nat) (hcap : capacity≤16384) (hi lo : BitVec 8) (raw : List (BitVec 8))
    (hcount : (hi++lo).toNat≤capacity) (hraw : (hi++lo).toNat≤raw.length) :
    hash Sha256.concrete ByteAuth.concrete capacity
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ =
      ⟨255,publicLength ByteAuth.concrete 32,Sha256.hash Sha256.concrete (raw.take (hi++lo).toNat)⟩ := by
  unfold hash
  rw [hashAfter_decoded 0 capacity (by decide) (by decide) hcap hi lo raw hcount hraw,hashAfterSpec_zero]

theorem hmac_decoded (capacity : Nat) (hcap : capacity≤16384) (key : List (BitVec 8)) (hi lo : BitVec 8) (raw : List (BitVec 8))
    (hcount : (hi++lo).toNat≤capacity) (hraw : (hi++lo).toNat≤raw.length) :
    hmac Sha256.concrete ByteAuth.concrete key capacity
      ⟨255,decodeLength ByteAuth.concrete [hi,lo],prefixData ByteAuth.concrete capacity (hi++lo).toNat raw⟩ =
      ⟨255,publicLength ByteAuth.concrete 32,Sha256.hmac Sha256.concrete key (raw.take (hi++lo).toNat)⟩ := by
  unfold hmac
  dsimp only
  rw [hashAfter_decoded 64 capacity (by decide) (by decide) hcap hi lo raw hcount hraw,hashAfterSpec_sixtyfour]
  dsimp only
  rw [HmacPrepared.hash_block_prefix Sha256.concrete (HmacPrepared.padBlock Sha256.concrete key 0x5c) _
    (HmacPrepared.padBlock_length Sha256.concrete key 0x5c)]
  change finish ByteAuth.concrete 255 (publicLength ByteAuth.concrete 32)
    (HmacPrepared.run Sha256.concrete (HmacPrepared.prepare Sha256.concrete key) (raw.take (hi++lo).toNat))=_
  rw [HmacPrepared.run_prepare]
  exact finish_accept _ _

theorem hashAfter_reject (prior capacity : Nat) (state : Sha256.State (BitVec 32)) (input : Buffer (BitVec 8))
    (hs : input.valid≠255) :
    hashAfter Sha256.concrete ByteAuth.concrete prior state capacity input=zero ByteAuth.concrete 32 := by
  unfold hashAfter
  rw [resize_reject capacity input hs]
  by_cases supported : capacity≤16384
  · rw [if_pos supported]
    change finish ByteAuth.concrete 0 (publicLength ByteAuth.concrete 32) _=_
    apply finish_reject
    · simp [publicLength,decodeLength]
    · exact blocks_length _ _ _ _ _ _ _
  · rw [if_neg supported]

theorem hash_reject (capacity : Nat) (input : Buffer (BitVec 8)) (hs : input.valid≠255) :
    hash Sha256.concrete ByteAuth.concrete capacity input=zero ByteAuth.concrete 32 := by
  exact hashAfter_reject 0 capacity _ input hs

theorem hmac_reject (capacity : Nat) (key : List (BitVec 8)) (input : Buffer (BitVec 8)) (hs : input.valid≠255) :
    hmac Sha256.concrete ByteAuth.concrete key capacity input=zero ByteAuth.concrete 32 := by
  unfold hmac
  dsimp only
  rw [hashAfter_reject 64 capacity _ input hs]
  change finish ByteAuth.concrete 0 (publicLength ByteAuth.concrete 32) _=_
  apply finish_reject
  · simp [publicLength,decodeLength]
  · exact Sha256.hash_length _ _

theorem hash_wire_decoded (capacity : Nat) (hcap : capacity≤16384) (status hi lo : BitVec 8) (raw : List (BitVec 8))
    (hr : raw.length=capacity) :
    output ByteAuth.concrete (hash Sha256.concrete ByteAuth.concrete capacity
      (fromWire ByteAuth.concrete capacity (status::hi::lo::raw))) =
      if status=255 ∧ (hi++lo).toNat≤capacity then
        255::([0,32]++Sha256.hash Sha256.concrete (raw.take (hi++lo).toNat)) else List.replicate 35 0 := by
  rw [fromWire_decoded capacity (by omega) status hi lo raw hr]
  by_cases valid : status=255 ∧ (hi++lo).toNat≤capacity
  · rw [if_pos valid,if_pos valid,hash_decoded capacity hcap hi lo raw valid.2 (by omega)]
    unfold output
    have encoded : encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete 32)=[0,32] := by decide
    rw [encoded]
  · rw [if_neg valid,if_neg valid,hash_reject capacity _ (by change (0 : BitVec 8)≠255;decide),output_zero]

theorem hmac_wire_decoded (capacity : Nat) (hcap : capacity≤16384) (key : List (BitVec 8)) (status hi lo : BitVec 8) (raw : List (BitVec 8))
    (hr : raw.length=capacity) :
    output ByteAuth.concrete (hmac Sha256.concrete ByteAuth.concrete key capacity
      (fromWire ByteAuth.concrete capacity (status::hi::lo::raw))) =
      if status=255 ∧ (hi++lo).toNat≤capacity then
        255::([0,32]++Sha256.hmac Sha256.concrete key (raw.take (hi++lo).toNat)) else List.replicate 35 0 := by
  rw [fromWire_decoded capacity (by omega) status hi lo raw hr]
  by_cases valid : status=255 ∧ (hi++lo).toNat≤capacity
  · rw [if_pos valid,if_pos valid,hmac_decoded capacity hcap key hi lo raw valid.2 (by omega)]
    unfold output
    have encoded : encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete 32)=[0,32] := by decide
    rw [encoded]
  · rw [if_neg valid,if_neg valid,hmac_reject capacity key _ (by change (0 : BitVec 8)≠255;decide),output_zero]

theorem hash_wrong_dimensions (capacity : Nat) (raw : List (BitVec 8)) (bad : raw.length≠capacity+3) :
    output ByteAuth.concrete (hash Sha256.concrete ByteAuth.concrete capacity
      (fromWire ByteAuth.concrete capacity raw))=List.replicate 35 0 := by
  unfold fromWire
  rw [if_neg bad,hash_reject capacity _ (by change (0 : BitVec 8)≠255;decide),output_zero]

theorem hmac_wrong_dimensions (capacity : Nat) (key raw : List (BitVec 8)) (bad : raw.length≠capacity+3) :
    output ByteAuth.concrete (hmac Sha256.concrete ByteAuth.concrete key capacity
      (fromWire ByteAuth.concrete capacity raw))=List.replicate 35 0 := by
  unfold fromWire
  rw [if_neg bad,hmac_reject capacity key _ (by change (0 : BitVec 8)≠255;decide),output_zero]

theorem hashAfter_unsupported (prior capacity : Nat) (state : Sha256.State (BitVec 32)) (input : Buffer (BitVec 8))
    (bad : ¬capacity≤16384) : hashAfter Sha256.concrete ByteAuth.concrete prior state capacity input=zero ByteAuth.concrete 32 := by
  unfold hashAfter
  rw [if_neg bad]

theorem hmac_unsupported (capacity : Nat) (key : List (BitVec 8)) (input : Buffer (BitVec 8)) (bad : ¬capacity≤16384) :
    hmac Sha256.concrete ByteAuth.concrete key capacity input=zero ByteAuth.concrete 32 := by
  unfold hmac
  dsimp only
  rw [hashAfter_unsupported 64 capacity _ input bad]
  change finish ByteAuth.concrete 0 (publicLength ByteAuth.concrete 32) _=_
  apply finish_reject
  · simp [publicLength,decodeLength]
  · exact Sha256.hash_length _ _

end TlsMpc.Signal.PrivateHash
