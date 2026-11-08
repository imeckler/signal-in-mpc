import FieldReferenceWork.Replayed.SliceReference
import TlsMpc.Signal.ProtoParseProofs

namespace LibSignalReference.Candidate.ProstFieldSlice
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open TlsMpc.Signal.VarintDecode
set_option maxHeartbeats 200000

theorem payload_zero_of_small (b : BitVec 8) (h : b.toNat < 128) :
    Spqr.payload b 0 = b.setWidth 64 := by
  simp only [Spqr.payload, Nat.mul_zero, BitVec.shiftLeft_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and]
  change (b.setWidth 64).toNat &&& (2^7-1) = (b.setWidth 64).toNat
  apply Nat.and_two_pow_sub_one_of_lt_two_pow
  simp only [BitVec.toNat_setWidth]
  exact lt_of_le_of_lt (Nat.mod_le _ _) h

theorem terminates_of_small (b : BitVec 8) (h : b.toNat < 128) : Spqr.terminates b = true := by
  have hm : b &&& 127 = b := by
    apply BitVec.eq_of_toNat_eq
    change b.toNat &&& (2^7-1) = b.toNat
    exact Nat.and_two_pow_sub_one_of_lt_two_pow h
  have hz : b &&& 128 = 0 := calc
    b &&& 128 = (b &&& 127) &&& 128 := congrArg (fun x : BitVec 8 => x &&& 128) hm.symm
    _ = b &&& (127 &&& 128) := BitVec.and_assoc _ _ _
    _ = 0 := by change b &&& 0 = 0; exact BitVec.and_zero
  exact beq_iff_eq.mpr hz

theorem run_done (wire : List (BitVec 8)) (fuel index : Nat) (value : BitVec 64) :
    Spqr.run wire fuel index value true = ⟨value,index,true⟩ := by
  cases fuel <;> simp [Spqr.run]

theorem decode_first (wire : List (BitVec 8)) (hn : 0 < wire.length)
    (hb : wire[0].toNat < 128) : Spqr.decode wire = ⟨wire[0].setWidth 64,1,true⟩ := by
  have hf : min 10 wire.length = (min 10 wire.length-1)+1 := by omega
  rw [Spqr.decode,hf,Spqr.run]
  simp only [Bool.false_eq_true, if_false, List.getElem?_eq_getElem hn, Option.getD_some,
    terminates_of_small _ hb, payload_zero_of_small _ hb, run_done]
  exact congrArg (fun value => (⟨value,1,true⟩ : Spqr.State)) BitVec.zero_or

theorem pack_valueBytes (value : BitVec 64) :
    Word64.concrete.pack (Spqr.valueBytes value) = value := by
  change (((value.extractLsb' 56 8 ++ value.extractLsb' 48 8) ++
      (value.extractLsb' 40 8 ++ value.extractLsb' 32 8)) ++
      ((value.extractLsb' 24 8 ++ value.extractLsb' 16 8) ++
      (value.extractLsb' 8 8 ++ value.extractLsb' 0 8))) = value
  repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bor_full (x : BitVec 8) : Word64.bor ByteAuth.concrete 255 x = 255 := by
  change (255 ^^^ x) ^^^ (255 &&& x) = 255
  have hx : (255 : BitVec 8) &&& x = x := BitVec.allOnes_and
  rw [hx,BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero]

/-- Exact strict Prost circuit fields for a terminating first byte. -/
theorem prefix_one (wire : List (BitVec 8)) (hn : 0 < wire.length) (hb : wire[0].toNat < 128) :
    ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete wire 0 =
      ⟨255,1,wire[0].setWidth 64⟩ := by
  unfold ProtoParse.decodePrefix
  simp only [List.drop_zero,Spqr.decodeCore_spec,decode_first wire hn hb,Spqr.encodeResult,
    if_true]
  have he : ByteAuth.eqMask ByteAuth.concrete (BitVec.ofNat 8 1) (ByteAuth.concrete.const 10) = 0 := by decide
  simp only [OpenResult.get,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    he]
  have hn0 : ByteAuth.concrete.not 0 = 255 := by decide
  rw [hn0,bor_full]
  change (⟨255,1,Word64.concrete.pack (Spqr.valueBytes (wire[0].setWidth 64))⟩ : ProtoParse.Decoded (BitVec 8) (BitVec 64)) = _
  rw [pack_valueBytes]

theorem payload_number (b : U8) (i : Nat) :
    Spqr.payload b.bv i = BitVec.ofNat 64 ((b.val % 128)*2^(7*i)) := by
  apply BitVec.eq_of_toNat_eq
  have hb : b.val < 2^64 := by have h := b.hmax; scalar_tac
  simp only [Spqr.payload,BitVec.toNat_shiftLeft,BitVec.toNat_and,BitVec.toNat_setWidth,
    BitVec.toNat_ofNat,UScalar.bv_toNat,Nat.shiftLeft_eq,Nat.mod_eq_of_lt hb]
  change ((b.val &&& (2^7-1))*2^(7*i))%2^64 = ((b.val%128)*2^(7*i))%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem or_number_shift (acc payload shift : Nat) (ha : acc < 2^shift)
    (ht : acc+payload*2^shift < 2^64) :
    (BitVec.ofNat 64 acc ||| BitVec.ofNat 64 (payload*2^shift)) =
      BitVec.ofNat 64 (acc+payload*2^shift) := by
  apply BitVec.eq_of_toNat_eq
  have hac : acc < 2^64 := by omega
  have hp : payload*2^shift < 2^64 := by omega
  simp only [BitVec.toNat_or,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hac,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt ht]
  calc
    acc ||| payload*2^shift = (payload <<< shift) ||| acc := by rw [Nat.shiftLeft_eq,Nat.or_comm]
    _ = (payload <<< shift)+acc := (Nat.shiftLeft_add_eq_or_of_lt ha payload).symm
    _ = acc+payload*2^shift := by rw [Nat.shiftLeft_eq,Nat.add_comm]

theorem terminates_of_large (b : U8) (h : 128 ≤ b.val) : Spqr.terminates b.bv = false := by
  have hbit : b.bv.getLsbD 7 = true := by
    change b.val.testBit 7 = true
    apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
    · exact h
    · have hb := b.hmax; scalar_tac
  have hn : b.bv &&& 128 ≠ 0 := by
    intro he
    have hb := congrArg (fun x : BitVec 8 => x.getLsbD 7) he
    simp only [BitVec.getLsbD_and,hbit] at hb
    contradiction
  exact Bool.eq_false_iff.mpr (fun he => hn (beq_iff_eq.mp he))

theorem contents_get (bytes : Slice U8) (i : Nat) :
    (contents bytes)[i]?.getD 0 = (byte bytes i).bv := by
  simp only [contents,byte,List.getElem?_map]
  cases bytes.val[i]? <;> rfl

theorem spqr_2 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : (byte bytes 1).val < 128)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+(byte bytes 1).val*128))),2,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have lastBound : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = (byte bytes 1).val := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = true :=
    terminates_of_small (byte bytes 1).bv (by change (byte bytes 1).val < 128; omega)
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+(byte bytes 1).val*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) ((byte bytes 1).val) 7 (by omega) (by omega)
  have lengthBound : 2 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 2 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-2)+2 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,run_done]

theorem spqr_3 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : (byte bytes 2).val < 128)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+(byte bytes 2).val*16384))),3,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have lastBound : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = (byte bytes 2).val := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = true :=
    terminates_of_small (byte bytes 2).bv (by change (byte bytes 2).val < 128; omega)
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+(byte bytes 2).val*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) ((byte bytes 2).val) 14 (by omega) (by omega)
  have lengthBound : 3 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 3 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-3)+3 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,run_done]

theorem spqr_4 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : (byte bytes 3).val < 128)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+(byte bytes 3).val*2097152))),4,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have lastBound : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = ((byte bytes 2).val-128) := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = false :=
    terminates_of_large (byte bytes 2) h2
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) (((byte bytes 2).val-128)) 14 (by omega) (by omega)
  have m3 : (byte bytes 3).val%128 = (byte bytes 3).val := by omega
  have t3 : Spqr.terminates (byte bytes 3).bv = true :=
    terminates_of_small (byte bytes 3).bv (by change (byte bytes 3).val < 128; omega)
  have a3 : ((BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) ||| Spqr.payload (byte bytes 3).bv 3) = (BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+(byte bytes 3).val*2097152))) := by
    rw [payload_number,m3]
    exact or_number_shift ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)) ((byte bytes 3).val) 21 (by omega) (by omega)
  have lengthBound : 4 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 4 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-4)+4 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,t3,a3,run_done]

theorem spqr_5 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : (byte bytes 4).val < 128)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+(byte bytes 4).val*268435456))),5,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have lastBound : 4 < bytes.length := prefix_access bytes hp 4 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = ((byte bytes 2).val-128) := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = false :=
    terminates_of_large (byte bytes 2) h2
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) (((byte bytes 2).val-128)) 14 (by omega) (by omega)
  have m3 : (byte bytes 3).val%128 = ((byte bytes 3).val-128) := by omega
  have t3 : Spqr.terminates (byte bytes 3).bv = false :=
    terminates_of_large (byte bytes 3) h3
  have a3 : ((BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) ||| Spqr.payload (byte bytes 3).bv 3) = (BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) := by
    rw [payload_number,m3]
    exact or_number_shift ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)) (((byte bytes 3).val-128)) 21 (by omega) (by omega)
  have m4 : (byte bytes 4).val%128 = (byte bytes 4).val := by omega
  have t4 : Spqr.terminates (byte bytes 4).bv = true :=
    terminates_of_small (byte bytes 4).bv (by change (byte bytes 4).val < 128; omega)
  have a4 : ((BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) ||| Spqr.payload (byte bytes 4).bv 4) = (BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+(byte bytes 4).val*268435456))) := by
    rw [payload_number,m4]
    exact or_number_shift (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)) ((byte bytes 4).val) 28 (by omega) (by omega)
  have lengthBound : 5 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 5 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-5)+5 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,t3,a3,t4,a4,run_done]

theorem spqr_6 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : (byte bytes 5).val < 128)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+(byte bytes 5).val*34359738368))),6,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have lastBound : 5 < bytes.length := prefix_access bytes hp 5 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjcases with he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = ((byte bytes 2).val-128) := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = false :=
    terminates_of_large (byte bytes 2) h2
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) (((byte bytes 2).val-128)) 14 (by omega) (by omega)
  have m3 : (byte bytes 3).val%128 = ((byte bytes 3).val-128) := by omega
  have t3 : Spqr.terminates (byte bytes 3).bv = false :=
    terminates_of_large (byte bytes 3) h3
  have a3 : ((BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) ||| Spqr.payload (byte bytes 3).bv 3) = (BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) := by
    rw [payload_number,m3]
    exact or_number_shift ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)) (((byte bytes 3).val-128)) 21 (by omega) (by omega)
  have m4 : (byte bytes 4).val%128 = ((byte bytes 4).val-128) := by omega
  have t4 : Spqr.terminates (byte bytes 4).bv = false :=
    terminates_of_large (byte bytes 4) h4
  have a4 : ((BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) ||| Spqr.payload (byte bytes 4).bv 4) = (BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) := by
    rw [payload_number,m4]
    exact or_number_shift (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)) (((byte bytes 4).val-128)) 28 (by omega) (by omega)
  have m5 : (byte bytes 5).val%128 = (byte bytes 5).val := by omega
  have t5 : Spqr.terminates (byte bytes 5).bv = true :=
    terminates_of_small (byte bytes 5).bv (by change (byte bytes 5).val < 128; omega)
  have a5 : ((BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) ||| Spqr.payload (byte bytes 5).bv 5) = (BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+(byte bytes 5).val*34359738368))) := by
    rw [payload_number,m5]
    exact or_number_shift ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)) ((byte bytes 5).val) 35 (by omega) (by omega)
  have lengthBound : 6 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 6 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-6)+6 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,t3,a3,t4,a4,t5,a5,run_done]

theorem spqr_7 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : (byte bytes 6).val < 128)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+(byte bytes 6).val*4398046511104))),7,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have lastBound : 6 < bytes.length := prefix_access bytes hp 6 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hjcases with he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = ((byte bytes 2).val-128) := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = false :=
    terminates_of_large (byte bytes 2) h2
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) (((byte bytes 2).val-128)) 14 (by omega) (by omega)
  have m3 : (byte bytes 3).val%128 = ((byte bytes 3).val-128) := by omega
  have t3 : Spqr.terminates (byte bytes 3).bv = false :=
    terminates_of_large (byte bytes 3) h3
  have a3 : ((BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) ||| Spqr.payload (byte bytes 3).bv 3) = (BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) := by
    rw [payload_number,m3]
    exact or_number_shift ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)) (((byte bytes 3).val-128)) 21 (by omega) (by omega)
  have m4 : (byte bytes 4).val%128 = ((byte bytes 4).val-128) := by omega
  have t4 : Spqr.terminates (byte bytes 4).bv = false :=
    terminates_of_large (byte bytes 4) h4
  have a4 : ((BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) ||| Spqr.payload (byte bytes 4).bv 4) = (BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) := by
    rw [payload_number,m4]
    exact or_number_shift (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)) (((byte bytes 4).val-128)) 28 (by omega) (by omega)
  have m5 : (byte bytes 5).val%128 = ((byte bytes 5).val-128) := by omega
  have t5 : Spqr.terminates (byte bytes 5).bv = false :=
    terminates_of_large (byte bytes 5) h5
  have a5 : ((BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) ||| Spqr.payload (byte bytes 5).bv 5) = (BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) := by
    rw [payload_number,m5]
    exact or_number_shift ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)) (((byte bytes 5).val-128)) 35 (by omega) (by omega)
  have m6 : (byte bytes 6).val%128 = (byte bytes 6).val := by omega
  have t6 : Spqr.terminates (byte bytes 6).bv = true :=
    terminates_of_small (byte bytes 6).bv (by change (byte bytes 6).val < 128; omega)
  have a6 : ((BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) ||| Spqr.payload (byte bytes 6).bv 6) = (BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+(byte bytes 6).val*4398046511104))) := by
    rw [payload_number,m6]
    exact or_number_shift (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)) ((byte bytes 6).val) 42 (by omega) (by omega)
  have lengthBound : 7 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 7 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-7)+7 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,t3,a3,t4,a4,t5,a5,t6,a6,run_done]

theorem spqr_8 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : (byte bytes 7).val < 128)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+(byte bytes 7).val*562949953421312))),8,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have b7 := byte_lt bytes 7
  have lastBound : 7 < bytes.length := prefix_access bytes hp 7 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases hjcases with he | he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5
    · simpa only [he] using h6)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = ((byte bytes 2).val-128) := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = false :=
    terminates_of_large (byte bytes 2) h2
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) (((byte bytes 2).val-128)) 14 (by omega) (by omega)
  have m3 : (byte bytes 3).val%128 = ((byte bytes 3).val-128) := by omega
  have t3 : Spqr.terminates (byte bytes 3).bv = false :=
    terminates_of_large (byte bytes 3) h3
  have a3 : ((BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) ||| Spqr.payload (byte bytes 3).bv 3) = (BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) := by
    rw [payload_number,m3]
    exact or_number_shift ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)) (((byte bytes 3).val-128)) 21 (by omega) (by omega)
  have m4 : (byte bytes 4).val%128 = ((byte bytes 4).val-128) := by omega
  have t4 : Spqr.terminates (byte bytes 4).bv = false :=
    terminates_of_large (byte bytes 4) h4
  have a4 : ((BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) ||| Spqr.payload (byte bytes 4).bv 4) = (BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) := by
    rw [payload_number,m4]
    exact or_number_shift (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)) (((byte bytes 4).val-128)) 28 (by omega) (by omega)
  have m5 : (byte bytes 5).val%128 = ((byte bytes 5).val-128) := by omega
  have t5 : Spqr.terminates (byte bytes 5).bv = false :=
    terminates_of_large (byte bytes 5) h5
  have a5 : ((BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) ||| Spqr.payload (byte bytes 5).bv 5) = (BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) := by
    rw [payload_number,m5]
    exact or_number_shift ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)) (((byte bytes 5).val-128)) 35 (by omega) (by omega)
  have m6 : (byte bytes 6).val%128 = ((byte bytes 6).val-128) := by omega
  have t6 : Spqr.terminates (byte bytes 6).bv = false :=
    terminates_of_large (byte bytes 6) h6
  have a6 : ((BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) ||| Spqr.payload (byte bytes 6).bv 6) = (BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104))) := by
    rw [payload_number,m6]
    exact or_number_shift (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)) (((byte bytes 6).val-128)) 42 (by omega) (by omega)
  have m7 : (byte bytes 7).val%128 = (byte bytes 7).val := by omega
  have t7 : Spqr.terminates (byte bytes 7).bv = true :=
    terminates_of_small (byte bytes 7).bv (by change (byte bytes 7).val < 128; omega)
  have a7 : ((BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104))) ||| Spqr.payload (byte bytes 7).bv 7) = (BitVec.ofNat 64 (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+(byte bytes 7).val*562949953421312))) := by
    rw [payload_number,m7]
    exact or_number_shift ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)) ((byte bytes 7).val) 49 (by omega) (by omega)
  have lengthBound : 8 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 8 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-8)+8 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,t3,a3,t4,a4,t5,a5,t6,a6,t7,a7,run_done]

theorem spqr_9 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : 128 ≤ (byte bytes 7).val)
    (h8 : (byte bytes 8).val < 128)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 ((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+(byte bytes 8).val*72057594037927936))),9,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have b7 := byte_lt bytes 7
  have b8 := byte_lt bytes 8
  have lastBound : 8 < bytes.length := prefix_access bytes hp 8 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hjcases with he | he | he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5
    · simpa only [he] using h6
    · simpa only [he] using h7)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = ((byte bytes 2).val-128) := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = false :=
    terminates_of_large (byte bytes 2) h2
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) (((byte bytes 2).val-128)) 14 (by omega) (by omega)
  have m3 : (byte bytes 3).val%128 = ((byte bytes 3).val-128) := by omega
  have t3 : Spqr.terminates (byte bytes 3).bv = false :=
    terminates_of_large (byte bytes 3) h3
  have a3 : ((BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) ||| Spqr.payload (byte bytes 3).bv 3) = (BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) := by
    rw [payload_number,m3]
    exact or_number_shift ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)) (((byte bytes 3).val-128)) 21 (by omega) (by omega)
  have m4 : (byte bytes 4).val%128 = ((byte bytes 4).val-128) := by omega
  have t4 : Spqr.terminates (byte bytes 4).bv = false :=
    terminates_of_large (byte bytes 4) h4
  have a4 : ((BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) ||| Spqr.payload (byte bytes 4).bv 4) = (BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) := by
    rw [payload_number,m4]
    exact or_number_shift (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)) (((byte bytes 4).val-128)) 28 (by omega) (by omega)
  have m5 : (byte bytes 5).val%128 = ((byte bytes 5).val-128) := by omega
  have t5 : Spqr.terminates (byte bytes 5).bv = false :=
    terminates_of_large (byte bytes 5) h5
  have a5 : ((BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) ||| Spqr.payload (byte bytes 5).bv 5) = (BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) := by
    rw [payload_number,m5]
    exact or_number_shift ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)) (((byte bytes 5).val-128)) 35 (by omega) (by omega)
  have m6 : (byte bytes 6).val%128 = ((byte bytes 6).val-128) := by omega
  have t6 : Spqr.terminates (byte bytes 6).bv = false :=
    terminates_of_large (byte bytes 6) h6
  have a6 : ((BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) ||| Spqr.payload (byte bytes 6).bv 6) = (BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104))) := by
    rw [payload_number,m6]
    exact or_number_shift (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)) (((byte bytes 6).val-128)) 42 (by omega) (by omega)
  have m7 : (byte bytes 7).val%128 = ((byte bytes 7).val-128) := by omega
  have t7 : Spqr.terminates (byte bytes 7).bv = false :=
    terminates_of_large (byte bytes 7) h7
  have a7 : ((BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104))) ||| Spqr.payload (byte bytes 7).bv 7) = (BitVec.ofNat 64 (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312))) := by
    rw [payload_number,m7]
    exact or_number_shift ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)) (((byte bytes 7).val-128)) 49 (by omega) (by omega)
  have m8 : (byte bytes 8).val%128 = (byte bytes 8).val := by omega
  have t8 : Spqr.terminates (byte bytes 8).bv = true :=
    terminates_of_small (byte bytes 8).bv (by change (byte bytes 8).val < 128; omega)
  have a8 : ((BitVec.ofNat 64 (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312))) ||| Spqr.payload (byte bytes 8).bv 8) = (BitVec.ofNat 64 ((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+(byte bytes 8).val*72057594037927936))) := by
    rw [payload_number,m8]
    exact or_number_shift (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)) ((byte bytes 8).val) 56 (by omega) (by omega)
  have lengthBound : 9 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 9 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-9)+9 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,t3,a3,t4,a4,t5,a5,t6,a6,t7,a7,t8,a8,run_done]

theorem spqr_10 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : 128 ≤ (byte bytes 7).val)
    (h8 : 128 ≤ (byte bytes 8).val)
    (h9 : (byte bytes 9).val < 2)
    : Spqr.decode (contents bytes) = ⟨(BitVec.ofNat 64 (((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+((byte bytes 8).val-128)*72057594037927936)+(byte bytes 9).val*9223372036854775808))),10,true⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have b7 := byte_lt bytes 7
  have b8 := byte_lt bytes 8
  have b9 := byte_lt bytes 9
  have lastBound : 9 < bytes.length := prefix_access bytes hp 9 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
    rcases hjcases with he | he | he | he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5
    · simpa only [he] using h6
    · simpa only [he] using h7
    · simpa only [he] using h8)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = ((byte bytes 2).val-128) := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = false :=
    terminates_of_large (byte bytes 2) h2
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) (((byte bytes 2).val-128)) 14 (by omega) (by omega)
  have m3 : (byte bytes 3).val%128 = ((byte bytes 3).val-128) := by omega
  have t3 : Spqr.terminates (byte bytes 3).bv = false :=
    terminates_of_large (byte bytes 3) h3
  have a3 : ((BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) ||| Spqr.payload (byte bytes 3).bv 3) = (BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) := by
    rw [payload_number,m3]
    exact or_number_shift ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)) (((byte bytes 3).val-128)) 21 (by omega) (by omega)
  have m4 : (byte bytes 4).val%128 = ((byte bytes 4).val-128) := by omega
  have t4 : Spqr.terminates (byte bytes 4).bv = false :=
    terminates_of_large (byte bytes 4) h4
  have a4 : ((BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) ||| Spqr.payload (byte bytes 4).bv 4) = (BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) := by
    rw [payload_number,m4]
    exact or_number_shift (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)) (((byte bytes 4).val-128)) 28 (by omega) (by omega)
  have m5 : (byte bytes 5).val%128 = ((byte bytes 5).val-128) := by omega
  have t5 : Spqr.terminates (byte bytes 5).bv = false :=
    terminates_of_large (byte bytes 5) h5
  have a5 : ((BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) ||| Spqr.payload (byte bytes 5).bv 5) = (BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) := by
    rw [payload_number,m5]
    exact or_number_shift ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)) (((byte bytes 5).val-128)) 35 (by omega) (by omega)
  have m6 : (byte bytes 6).val%128 = ((byte bytes 6).val-128) := by omega
  have t6 : Spqr.terminates (byte bytes 6).bv = false :=
    terminates_of_large (byte bytes 6) h6
  have a6 : ((BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) ||| Spqr.payload (byte bytes 6).bv 6) = (BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104))) := by
    rw [payload_number,m6]
    exact or_number_shift (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)) (((byte bytes 6).val-128)) 42 (by omega) (by omega)
  have m7 : (byte bytes 7).val%128 = ((byte bytes 7).val-128) := by omega
  have t7 : Spqr.terminates (byte bytes 7).bv = false :=
    terminates_of_large (byte bytes 7) h7
  have a7 : ((BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104))) ||| Spqr.payload (byte bytes 7).bv 7) = (BitVec.ofNat 64 (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312))) := by
    rw [payload_number,m7]
    exact or_number_shift ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)) (((byte bytes 7).val-128)) 49 (by omega) (by omega)
  have m8 : (byte bytes 8).val%128 = ((byte bytes 8).val-128) := by omega
  have t8 : Spqr.terminates (byte bytes 8).bv = false :=
    terminates_of_large (byte bytes 8) h8
  have a8 : ((BitVec.ofNat 64 (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312))) ||| Spqr.payload (byte bytes 8).bv 8) = (BitVec.ofNat 64 ((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+((byte bytes 8).val-128)*72057594037927936))) := by
    rw [payload_number,m8]
    exact or_number_shift (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)) (((byte bytes 8).val-128)) 56 (by omega) (by omega)
  have m9 : (byte bytes 9).val%128 = (byte bytes 9).val := by omega
  have t9 : Spqr.terminates (byte bytes 9).bv = true :=
    terminates_of_small (byte bytes 9).bv (by change (byte bytes 9).val < 128; omega)
  have a9 : ((BitVec.ofNat 64 ((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+((byte bytes 8).val-128)*72057594037927936))) ||| Spqr.payload (byte bytes 9).bv 9) = (BitVec.ofNat 64 (((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+((byte bytes 8).val-128)*72057594037927936)+(byte bytes 9).val*9223372036854775808))) := by
    rw [payload_number,m9]
    exact or_number_shift ((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+((byte bytes 8).val-128)*72057594037927936)) ((byte bytes 9).val) 63 (by omega) (by omega)
  have lengthBound : 10 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 10 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = (min 10 (contents bytes).length-10)+10 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,t3,a3,t4,a4,t5,a5,t6,a6,t7,a7,t8,a8,t9,a9,run_done]

theorem spqr_invalid (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : 128 ≤ (byte bytes 7).val)
    (h8 : 128 ≤ (byte bytes 8).val)
    (_h9 : 2 ≤ (byte bytes 9).val)
    : Spqr.decode (contents bytes) = ⟨((BitVec.ofNat 64 ((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+((byte bytes 8).val-128)*72057594037927936))) ||| Spqr.payload (byte bytes 9).bv 9),10,Spqr.terminates (byte bytes 9).bv⟩ := by
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have b7 := byte_lt bytes 7
  have b8 := byte_lt bytes 8
  have b9 := byte_lt bytes 9
  have lastBound : 9 < bytes.length := prefix_access bytes hp 9 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
    rcases hjcases with he | he | he | he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5
    · simpa only [he] using h6
    · simpa only [he] using h7
    · simpa only [he] using h8)
  have m0 : (byte bytes 0).val%128 = ((byte bytes 0).val-128) := by omega
  have t0 : Spqr.terminates (byte bytes 0).bv = false :=
    terminates_of_large (byte bytes 0) h0
  have a0 : (0 ||| Spqr.payload (byte bytes 0).bv 0) = (BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) := by
    rw [payload_number,m0]
    exact or_number_shift (0) (((byte bytes 0).val-128)) 0 (by omega) (by omega)
  have m1 : (byte bytes 1).val%128 = ((byte bytes 1).val-128) := by omega
  have t1 : Spqr.terminates (byte bytes 1).bv = false :=
    terminates_of_large (byte bytes 1) h1
  have a1 : ((BitVec.ofNat 64 ((0+((byte bytes 0).val-128)*1))) ||| Spqr.payload (byte bytes 1).bv 1) = (BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) := by
    rw [payload_number,m1]
    exact or_number_shift ((0+((byte bytes 0).val-128)*1)) (((byte bytes 1).val-128)) 7 (by omega) (by omega)
  have m2 : (byte bytes 2).val%128 = ((byte bytes 2).val-128) := by omega
  have t2 : Spqr.terminates (byte bytes 2).bv = false :=
    terminates_of_large (byte bytes 2) h2
  have a2 : ((BitVec.ofNat 64 (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128))) ||| Spqr.payload (byte bytes 2).bv 2) = (BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) := by
    rw [payload_number,m2]
    exact or_number_shift (((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)) (((byte bytes 2).val-128)) 14 (by omega) (by omega)
  have m3 : (byte bytes 3).val%128 = ((byte bytes 3).val-128) := by omega
  have t3 : Spqr.terminates (byte bytes 3).bv = false :=
    terminates_of_large (byte bytes 3) h3
  have a3 : ((BitVec.ofNat 64 ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384))) ||| Spqr.payload (byte bytes 3).bv 3) = (BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) := by
    rw [payload_number,m3]
    exact or_number_shift ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)) (((byte bytes 3).val-128)) 21 (by omega) (by omega)
  have m4 : (byte bytes 4).val%128 = ((byte bytes 4).val-128) := by omega
  have t4 : Spqr.terminates (byte bytes 4).bv = false :=
    terminates_of_large (byte bytes 4) h4
  have a4 : ((BitVec.ofNat 64 (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152))) ||| Spqr.payload (byte bytes 4).bv 4) = (BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) := by
    rw [payload_number,m4]
    exact or_number_shift (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)) (((byte bytes 4).val-128)) 28 (by omega) (by omega)
  have m5 : (byte bytes 5).val%128 = ((byte bytes 5).val-128) := by omega
  have t5 : Spqr.terminates (byte bytes 5).bv = false :=
    terminates_of_large (byte bytes 5) h5
  have a5 : ((BitVec.ofNat 64 ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456))) ||| Spqr.payload (byte bytes 5).bv 5) = (BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) := by
    rw [payload_number,m5]
    exact or_number_shift ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)) (((byte bytes 5).val-128)) 35 (by omega) (by omega)
  have m6 : (byte bytes 6).val%128 = ((byte bytes 6).val-128) := by omega
  have t6 : Spqr.terminates (byte bytes 6).bv = false :=
    terminates_of_large (byte bytes 6) h6
  have a6 : ((BitVec.ofNat 64 (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368))) ||| Spqr.payload (byte bytes 6).bv 6) = (BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104))) := by
    rw [payload_number,m6]
    exact or_number_shift (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)) (((byte bytes 6).val-128)) 42 (by omega) (by omega)
  have m7 : (byte bytes 7).val%128 = ((byte bytes 7).val-128) := by omega
  have t7 : Spqr.terminates (byte bytes 7).bv = false :=
    terminates_of_large (byte bytes 7) h7
  have a7 : ((BitVec.ofNat 64 ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104))) ||| Spqr.payload (byte bytes 7).bv 7) = (BitVec.ofNat 64 (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312))) := by
    rw [payload_number,m7]
    exact or_number_shift ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)) (((byte bytes 7).val-128)) 49 (by omega) (by omega)
  have m8 : (byte bytes 8).val%128 = ((byte bytes 8).val-128) := by omega
  have t8 : Spqr.terminates (byte bytes 8).bv = false :=
    terminates_of_large (byte bytes 8) h8
  have a8 : ((BitVec.ofNat 64 (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312))) ||| Spqr.payload (byte bytes 8).bv 8) = (BitVec.ofNat 64 ((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+((byte bytes 8).val-128)*72057594037927936))) := by
    rw [payload_number,m8]
    exact or_number_shift (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)) (((byte bytes 8).val-128)) 56 (by omega) (by omega)
  have lengthBound : 10 ≤ (contents bytes).length := by
    simp only [contents,List.length_map]
    change 10 ≤ bytes.length
    omega
  have hf : min 10 (contents bytes).length = 10 := by omega
  rw [Spqr.decode,hf]
  simp only [Spqr.run,Bool.false_eq_true,if_false,contents_get,Nat.reduceAdd,t0,a0,t1,a1,t2,a2,t3,a3,t4,a4,t5,a5,t6,a6,t7,a7,t8,a8]


theorem pack_count (n : Nat) (hn : n < 256) :
    Word64.concrete.pack (List.replicate 7 (ByteAuth.concrete.const 0) ++ [BitVec.ofNat 8 n]) =
      BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change ((((0#8 ++ 0#8) ++ (0#8 ++ 0#8)) ++ ((0#8 ++ 0#8) ++ (0#8 ++ BitVec.ofNat 8 n))) : BitVec 64).toNat = _
  simp only [BitVec.toNat_append,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  have hn64 : n < 18446744073709551616 := by omega
  simp [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hn64]

theorem mask254_small (b : BitVec 8) (h : b.toNat < 2) : b &&& 254 = 0 := by
  have hc : b.toNat = 0 ∨ b.toNat = 1 := by omega
  rcases hc with h0 | h1
  · have he : b = 0 := BitVec.eq_of_toNat_eq h0
    rw [he]; rfl
  · have he : b = 1 := BitVec.eq_of_toNat_eq h1
    rw [he]; rfl

theorem mask254_large (b : BitVec 8) (h : 2 ≤ b.toNat) : b &&& 254 ≠ 0 := by
  intro hz
  have he : (b &&& 1) ||| (b &&& 254) = b := by
    rw [← BitVec.and_or_distrib_left]
    change b &&& 255 = b
    exact BitVec.and_allOnes
  rw [hz] at he
  have he' : b &&& 1 = b := by simpa using he
  have hv := congrArg BitVec.toNat he'
  change b.toNat &&& (2^1-1) = b.toNat at hv
  rw [Nat.and_two_pow_sub_one_eq_mod] at hv
  omega

/-- Converts the independently proved SPQR state into the strict Prost prefix
fields. The extra tenth-byte condition is exactly the uint64 overflow check. -/
theorem prefix_accepted (wire : List (BitVec 8)) (n : Nat) (value : BitVec 64)
    (hs : Spqr.decode wire = ⟨value,n,true⟩) (hn : n ≤ 10)
    (hf : n = 10 → (wire[9]?.getD 0).toNat < 2) :
    ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete wire 0 =
      ⟨255,BitVec.ofNat 64 n,value⟩ := by
  have hn8 : n < 256 := by omega
  have hfit : Word64.bor ByteAuth.concrete
      (ByteAuth.concrete.not (ByteAuth.eqMask ByteAuth.concrete (BitVec.ofNat 8 n) (ByteAuth.concrete.const 10)))
      (ByteAuth.zeroMask ByteAuth.concrete (ByteAuth.concrete.and
        (wire[9]?.getD (ByteAuth.concrete.const 0)) (ByteAuth.concrete.const 254))) = 255 := by
    by_cases he : n = 10
    · subst n
      have hz := mask254_small (wire[9]?.getD 0) (hf rfl)
      have heq : ByteAuth.eqMask ByteAuth.concrete (BitVec.ofNat 8 10) (ByteAuth.concrete.const 10) = 255 := by decide
      rw [heq]
      change Word64.bor ByteAuth.concrete 0 (ByteAuth.zeroMask ByteAuth.concrete ((wire[9]?.getD 0) &&& 254)) = 255
      rw [hz]
      rfl
    · have hne : BitVec.ofNat 8 n ≠ ByteAuth.concrete.const 10 := by
        intro hx
        have hv := congrArg BitVec.toNat hx
        change n%256 = 10 at hv
        rw [Nat.mod_eq_of_lt hn8] at hv
        exact he hv
      have heq : ByteAuth.eqMask ByteAuth.concrete (BitVec.ofNat 8 n) (ByteAuth.concrete.const 10) = 0 := by
        rw [ByteAuth.eqMask_value,if_neg hne]
      rw [heq]
      exact bor_full _
  unfold ProtoParse.decodePrefix
  simp only [List.drop_zero,Spqr.decodeCore_spec,hs,Spqr.encodeResult,if_true,
    OpenResult.get,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,hfit]
  have hand : ByteAuth.concrete.and 255 255 = 255 := by decide
  simp only [hand,List.drop_succ_cons,List.drop_zero,pack_count n hn8,pack_valueBytes]
  change (⟨255,0+BitVec.ofNat 64 n,value⟩ : ProtoParse.Decoded (BitVec 8) (BitVec 64)) = _
  exact congrArg (fun stop => (⟨255,stop,value⟩ : ProtoParse.Decoded (BitVec 8) (BitVec 64))) (BitVec.zero_add _)

theorem prefix_rejected_tenth (wire : List (BitVec 8)) (value : BitVec 64)
    (hs : Spqr.decode wire = ⟨value,10,Spqr.terminates (wire[9]?.getD 0)⟩)
    (hb : 2 ≤ (wire[9]?.getD 0).toNat) :
    (ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete wire 0).ok = 0 := by
  unfold ProtoParse.decodePrefix
  simp only [List.drop_zero,Spqr.decodeCore_spec,hs]
  cases ht : Spqr.terminates (wire[9]?.getD 0) with
  | false =>
      simp only [Spqr.encodeResult,Bool.false_eq_true,if_false]
      exact BitVec.zero_and
  | true =>
      simp only [Spqr.encodeResult,if_true,OpenResult.get,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some]
      have heq : ByteAuth.eqMask ByteAuth.concrete (BitVec.ofNat 8 10) (ByteAuth.concrete.const 10) = 255 := by decide
      rw [heq]
      change ByteAuth.concrete.and 255 (Word64.bor ByteAuth.concrete 0
        (ByteAuth.zeroMask ByteAuth.concrete ((wire[9]?.getD 0) &&& 254))) = 0
      rw [ByteAuth.zeroMask_value,if_neg (mask254_large _ hb)]
      rfl

/-- Success preserves all decoded fields; rejection preserves the exact Rust
error and proves the circuit status is zero. Error-only cursor/value fields are
not constrained because ProtoParse gates their use on the status byte. -/
def Matches (wire : List (BitVec 8))
    (result : core.result.Result (U64 × Usize) ProstFieldCandidate.error.DecodeError) : Prop :=
  match result with
  | .Ok (value,count) =>
      ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete wire 0 =
        ⟨255,BitVec.ofNat 64 count.val,value.bv⟩
  | .Err error => error = invalidError ∧
      (ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete wire 0).ok = 0

theorem case_1 (bytes : Slice U8) (hp : Preconditions bytes) (h0 : (byte bytes 0).val < 128) :
    ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 (byte bytes 0).val,1#usize),decode_1 bytes hp h0,?_⟩
  have hn : 0 < (contents bytes).length := by simpa only [contents,List.length_map] using hp.1
  have hg : (contents bytes)[0] = (byte bytes 0).bv := by
    simpa only [List.getElem?_eq_getElem hn,Option.getD_some] using contents_get bytes 0
  have hs := decode_first (contents bytes) hn (by rw [hg]; exact h0)
  rw [hg] at hs
  have hv : (byte bytes 0).bv.setWidth 64 = (number .U64 (byte bytes 0).val).bv := by
    apply BitVec.eq_of_toNat_eq
    change ((byte bytes 0).bv.setWidth 64).toNat = (BitVec.ofNat 64 (byte bytes 0).val).toNat
    rw [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    rfl
  rw [hv] at hs
  exact prefix_accepted (contents bytes) 1 (number .U64 (byte bytes 0).val).bv hs (by decide) (by omega)

theorem case_2 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : (byte bytes 1).val < 128)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 ((byte bytes 0).val-128+(byte bytes 1).val*128),2#usize),decode_two bytes hp h0 h1,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have hs := spqr_2 bytes hp h0 h1
  have he : (((0+((byte bytes 0).val-128)*1)+(byte bytes 1).val*128)) = ((byte bytes 0).val-128+(byte bytes 1).val*128) := by omega
  rw [he] at hs
  have hc : (2#usize).val = 2 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 2 (number .U64 ((byte bytes 0).val-128+(byte bytes 1).val*128)).bv hs (by decide)
  omega

theorem case_3 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : (byte bytes 2).val < 128)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))),3#usize),decode_3 bytes hp h0 h1 h2,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have hs := spqr_3 bytes hp h0 h1 h2
  have he : ((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+(byte bytes 2).val*16384)) = ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) := by omega
  rw [he] at hs
  have hc : (3#usize).val = 3 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 3 (number .U64 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))).bv hs (by decide)
  omega

theorem case_4 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : (byte bytes 3).val < 128)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))),4#usize),decode_4 bytes hp h0 h1 h2 h3,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have hs := spqr_4 bytes hp h0 h1 h2 h3
  have he : (((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+(byte bytes 3).val*2097152)) = ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) := by omega
  rw [he] at hs
  have hc : (4#usize).val = 4 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 4 (number .U64 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))).bv hs (by decide)
  omega

theorem case_5 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : (byte bytes 4).val < 128)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((byte bytes 4).val*268435456))),5#usize),decode_5 bytes hp h0 h1 h2 h3 h4,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have hs := spqr_5 bytes hp h0 h1 h2 h3 h4
  have he : ((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+(byte bytes 4).val*268435456)) = ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((byte bytes 4).val*268435456))) := by omega
  rw [he] at hs
  have hc : (5#usize).val = 5 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 5 (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((byte bytes 4).val*268435456)))).bv hs (by decide)
  omega

theorem case_6 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : (byte bytes 5).val < 128)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456))),6#usize),decode_6 bytes hp h0 h1 h2 h3 h4 h5,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have hs := spqr_6 bytes hp h0 h1 h2 h3 h4 h5
  have he : (((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+(byte bytes 5).val*34359738368)) = ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456))) := by omega
  rw [he] at hs
  have hc : (6#usize).val = 6 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 6 (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456)))).bv hs (by decide)
  omega

theorem case_7 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : (byte bytes 6).val < 128)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456))),7#usize),decode_7 bytes hp h0 h1 h2 h3 h4 h5 h6,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have hs := spqr_7 bytes hp h0 h1 h2 h3 h4 h5 h6
  have he : ((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+(byte bytes 6).val*4398046511104)) = ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456))) := by omega
  rw [he] at hs
  have hc : (7#usize).val = 7 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 7 (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456)))).bv hs (by decide)
  omega

theorem case_8 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : (byte bytes 7).val < 128)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456))),8#usize),decode_8 bytes hp h0 h1 h2 h3 h4 h5 h6 h7,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have b7 := byte_lt bytes 7
  have hs := spqr_8 bytes hp h0 h1 h2 h3 h4 h5 h6 h7
  have he : (((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+(byte bytes 7).val*562949953421312)) = ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456))) := by omega
  rw [he] at hs
  have hc : (8#usize).val = 8 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 8 (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456)))).bv hs (by decide)
  omega

theorem case_9 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : 128 ≤ (byte bytes 7).val)
    (h8 : (byte bytes 8).val < 128)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((byte bytes 8).val*72057594037927936))),9#usize),decode_9 bytes hp h0 h1 h2 h3 h4 h5 h6 h7 h8,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have b7 := byte_lt bytes 7
  have b8 := byte_lt bytes 8
  have hs := spqr_9 bytes hp h0 h1 h2 h3 h4 h5 h6 h7 h8
  have he : ((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+(byte bytes 8).val*72057594037927936)) = (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((byte bytes 8).val*72057594037927936))) := by omega
  rw [he] at hs
  have hc : (9#usize).val = 9 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 9 (number .U64 (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((byte bytes 8).val*72057594037927936)))).bv hs (by decide)
  omega

theorem case_10 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : 128 ≤ (byte bytes 7).val)
    (h8 : 128 ≤ (byte bytes 8).val)
    (h9 : (byte bytes 9).val < 2)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Ok (number .U64 (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936))),10#usize),decode_10 bytes hp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9,?_⟩
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have b2 := byte_lt bytes 2
  have b3 := byte_lt bytes 3
  have b4 := byte_lt bytes 4
  have b5 := byte_lt bytes 5
  have b6 := byte_lt bytes 6
  have b7 := byte_lt bytes 7
  have b8 := byte_lt bytes 8
  have b9 := byte_lt bytes 9
  have hs := spqr_10 bytes hp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have he : (((((((((((0+((byte bytes 0).val-128)*1)+((byte bytes 1).val-128)*128)+((byte bytes 2).val-128)*16384)+((byte bytes 3).val-128)*2097152)+((byte bytes 4).val-128)*268435456)+((byte bytes 5).val-128)*34359738368)+((byte bytes 6).val-128)*4398046511104)+((byte bytes 7).val-128)*562949953421312)+((byte bytes 8).val-128)*72057594037927936)+(byte bytes 9).val*9223372036854775808)) = (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936))) := by omega
  rw [he] at hs
  have hc : (10#usize).val = 10 := by scalar_tac
  simp only [Matches]
  rw [hc]
  apply prefix_accepted (contents bytes) 10 (number .U64 (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936)))).bv hs (by decide)
  intro _
  rw [contents_get]
  exact h9

theorem case_invalid (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : 128 ≤ (byte bytes 7).val)
    (h8 : 128 ≤ (byte bytes 8).val)
    (h9 : 2 ≤ (byte bytes 9).val)
    : ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  refine ⟨.Err invalidError,decode_invalid bytes hp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9,rfl,?_⟩
  apply prefix_rejected_tenth (contents bytes) _
  · simpa only [contents_get] using spqr_invalid bytes hp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  · rw [contents_get]; exact h9

/-- Full unchanged pinned Prost slice decoder under its actual assertions,
including exact successful values/counts and strict uint64 overflow errors. -/
theorem decode_reference (bytes : Slice U8) (hp : Preconditions bytes) :
    ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result := by
  by_cases h0 : (byte bytes 0).val < 128
  · exact case_1 bytes hp h0
  · have c0 : 128 ≤ (byte bytes 0).val := by omega
    by_cases h1 : (byte bytes 1).val < 128
    · exact case_2 bytes hp c0 h1
    · have c1 : 128 ≤ (byte bytes 1).val := by omega
      by_cases h2 : (byte bytes 2).val < 128
      · exact case_3 bytes hp c0 c1 h2
      · have c2 : 128 ≤ (byte bytes 2).val := by omega
        by_cases h3 : (byte bytes 3).val < 128
        · exact case_4 bytes hp c0 c1 c2 h3
        · have c3 : 128 ≤ (byte bytes 3).val := by omega
          by_cases h4 : (byte bytes 4).val < 128
          · exact case_5 bytes hp c0 c1 c2 c3 h4
          · have c4 : 128 ≤ (byte bytes 4).val := by omega
            by_cases h5 : (byte bytes 5).val < 128
            · exact case_6 bytes hp c0 c1 c2 c3 c4 h5
            · have c5 : 128 ≤ (byte bytes 5).val := by omega
              by_cases h6 : (byte bytes 6).val < 128
              · exact case_7 bytes hp c0 c1 c2 c3 c4 c5 h6
              · have c6 : 128 ≤ (byte bytes 6).val := by omega
                by_cases h7 : (byte bytes 7).val < 128
                · exact case_8 bytes hp c0 c1 c2 c3 c4 c5 c6 h7
                · have c7 : 128 ≤ (byte bytes 7).val := by omega
                  by_cases h8 : (byte bytes 8).val < 128
                  · exact case_9 bytes hp c0 c1 c2 c3 c4 c5 c6 c7 h8
                  · have c8 : 128 ≤ (byte bytes 8).val := by omega
                    by_cases h9 : (byte bytes 9).val < 2
                    · exact case_10 bytes hp c0 c1 c2 c3 c4 c5 c6 c7 c8 h9
                    · have c9 : 2 ≤ (byte bytes 9).val := by omega
                      exact case_invalid bytes hp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9

/-- A normalized shared-byte view: status, consumedBE8, valueBE8. Error
outputs are zero. This transport wraps the existing strict prefix circuit. -/
def decodedBytes (o : Word64.Ops B W) (a : ByteAuth.Ops B) (r : ProtoParse.Decoded B W) : List B :=
  r.ok :: ByteAuth.release a r.ok (Word64.bytes o r.stop ++ Word64.bytes o r.value)

def prefixBytes (d : Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B) (wire : List B) : List B :=
  decodedBytes o a (ProtoParse.decodePrefix d o a wire 0)

def resultBytes (result : core.result.Result (U64 × Usize) ProstFieldCandidate.error.DecodeError) : List (BitVec 8) :=
  match result with
  | .Ok (value,count) => 255 :: (Word64.bytes Word64.concrete (BitVec.ofNat 64 count.val) ++ Word64.bytes Word64.concrete value.bv)
  | .Err _ => List.replicate 17 0

theorem decodedBytes_map {o : Word64.Ops B W} {o' : Word64.Ops B' W'}
    {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
    (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f) (r : ProtoParse.Decoded B W) :
    (decodedBytes o a r).map f = decodedBytes o' a' (r.map f fw) := by
  simp only [decodedBytes,ProtoParse.Decoded.map,List.map_cons,ByteAuth.release_map ha,
    List.map_append,Word64.bytes_map ho]

theorem prefixBytes_map {d : Spqr.Ops B W} {d' : Spqr.Ops B' W'}
    {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
    {f : B → B'} {fw : W → W'} (hd : Spqr.Hom d d' f fw) (ho : Word64.Hom o o' f fw)
    (ha : ByteAuth.Hom a a' f) (wire : List B) :
    (prefixBytes d o a wire).map f = prefixBytes d' o' a' (wire.map f) := by
  unfold prefixBytes
  rw [decodedBytes_map ho ha,ProtoParse.decodePrefix_map hd ho ha]

theorem matches_bytes (wire : List (BitVec 8))
    (result : core.result.Result (U64 × Usize) ProstFieldCandidate.error.DecodeError)
    (h : Matches wire result) :
    prefixBytes Spqr.concrete Word64.concrete ByteAuth.concrete wire = resultBytes result := by
  cases result with
  | Ok pair =>
      rcases pair with ⟨value,count⟩
      unfold prefixBytes
      rw [show ProtoParse.decodePrefix Spqr.concrete Word64.concrete ByteAuth.concrete wire 0 =
        ⟨255,BitVec.ofNat 64 count.val,value.bv⟩ from h]
      exact congrArg (List.cons 255) (ByteAuth.release_accept _)
  | Err error =>
      have hz := h.2
      simp only [prefixBytes,decodedBytes,hz,ByteAuth.release_reject,List.length_append,Word64.bytes_length,resultBytes]
      rfl

theorem decode_bytes_reference (bytes : Slice U8) (hp : Preconditions bytes) :
    ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result ∧
      prefixBytes Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) = resultBytes result := by
  obtain ⟨result,hd,hm⟩ := decode_reference bytes hp
  exact ⟨result,hd,hm,matches_bytes _ _ hm⟩

open _root_.Std.Tactic.BVDecide
/-- Every bit of the compiled strict-prefix transport agrees with unchanged
actual Prost, under the actual slice preconditions and the explicit candidate
valid-index model extension. No handwritten decoder replaces the Rust reference. -/
theorem decode_refines_artifact (bytes : Slice U8) (hp : Preconditions bytes)
    (secret : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (hinput : secret.map (BVExpr.eval assign) = contents bytes) :
    ∃ result, ProstFieldCandidate.encoding.varint.decode_varint_slice bytes = .ok result ∧
      Matches (contents bytes) result ∧
      ∀ (index : Nat) (hi : index < 8*(prefixBytes Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (prefixBytes Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (prefixBytes Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (resultBytes result)).getLsbD index := by
  obtain ⟨result,hd,hm,hb⟩ := decode_bytes_reference bytes hp
  refine ⟨result,hd,hm,?_⟩
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,prefixBytes_map (Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign),hinput,hb]

#print axioms decode_refines_artifact
#print axioms decode_bytes_reference
#print axioms decode_reference
#print axioms spqr_invalid
#print axioms prefix_rejected_tenth
#print axioms pack_count
#print axioms mask254_large
#print axioms prefix_accepted
#print axioms spqr_2
#print axioms spqr_3
#print axioms spqr_4
#print axioms spqr_5
#print axioms spqr_6
#print axioms spqr_7
#print axioms spqr_8
#print axioms spqr_9
#print axioms spqr_10
#print axioms payload_number
#print axioms or_number_shift
#print axioms terminates_of_large
#print axioms payload_zero_of_small
#print axioms terminates_of_small
#print axioms decode_first
#print axioms pack_valueBytes
#print axioms prefix_one
end LibSignalReference.Candidate.ProstFieldSlice
