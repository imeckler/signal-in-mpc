import ProtoParseWork.KeyReferenceWork.Generated.key_step.Funs

namespace LibSignalReference.Candidate.ProstKeySlice
open Aeneas Aeneas.Std
set_option maxHeartbeats 100000

/-- Actual debug assertions of the slice fast path. This formulation exposes
its last-byte promise without making any out-of-bounds read. -/
def Preconditions (bytes : Slice U8) : Prop :=
  0 < bytes.length ∧ (10 < bytes.length ∨
    ∀ (i : Nat) (hi : i < bytes.val.length), i+1 = bytes.length → bytes.val[i].val < 128)

theorem preconditions_iff (bytes : Slice U8) (hn : 0 < bytes.length) :
    Preconditions bytes ↔ (10 < bytes.length ∨
      (bytes.val[bytes.length-1]'(by change bytes.length-1 < bytes.length; omega)).val < 128) := by
  constructor
  · intro hp
    rcases hp.2 with hl | hlast
    · exact Or.inl hl
    · exact Or.inr (hlast (bytes.length-1) (by change bytes.length-1 < bytes.length; omega) (by omega))
  · intro hp
    refine ⟨hn,?_⟩
    rcases hp with hl | hlast
    · exact Or.inl hl
    · right
      intro i hi he
      have heq : i = bytes.length-1 := by omega
      subst i
      exact hlast

/-- Each unrolled unsafe access is bounded: if all preceding bytes continued,
the last-byte promise prevents the slice from ending before this access. -/
theorem access_bound (bytes : Slice U8) (hp : Preconditions bytes) (i : Nat) (hi : i < 10)
    (continued : ∀ (j : Nat) (hj : j < bytes.val.length), j < i → 128 ≤ bytes.val[j].val) :
    i < bytes.length := by
  rcases hp with ⟨hne, hlong | hlast⟩
  · omega
  · by_contra h
    have hindex : bytes.length-1 < bytes.val.length := by change bytes.length-1 < bytes.length; omega
    have ht := hlast (bytes.length-1) hindex (by omega)
    have hc := continued (bytes.length-1) hindex (by omega)
    omega

theorem get_unchecked_at (bytes : Slice U8) (i : Usize) (hi : i.val < bytes.length) :
    core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes i =
      .ok bytes.val[i.val] := by
  obtain ⟨x,hx,he⟩ := WP.spec_imp_exists (core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec (s := bytes) (i := i) hi)
  simpa only [he, Slice.getElem_Usize_eq] using hx

def initialChecks (bytes : Slice U8) : Result Unit := do
  if bytes.len > 10#usize then .ok () else do
    let lastIndex ← bytes.len - 1#usize
    let last ← bytes.index_usize lastIndex
    massert (last < 128#u8)

theorem initialChecks_ok (bytes : Slice U8) (hp : Preconditions bytes) :
    initialChecks bytes = .ok () := by
  unfold initialChecks
  by_cases hl : bytes.len > 10#usize
  · simp only [if_pos hl]
  · rw [if_neg hl]
    obtain ⟨lastIndex, hs, hv⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := bytes.len) (y := 1#usize) (by have hn := hp.1; scalar_tac))
    have hi : lastIndex.val < bytes.val.length := by have hn := hp.1; scalar_tac
    obtain ⟨last,hg,he⟩ := WP.spec_imp_exists (Slice.index_usize_spec bytes lastIndex hi)
    have ht : last < 128#u8 := by
      rcases hp.2 with hlong | hlast
      · have hsmall : bytes.length ≤ 10 := by exact Nat.le_of_not_gt hl
        omega
      · change last.val < 128
        rw [he]
        exact hlast lastIndex.val hi (by scalar_tac)
    simp only [hs, bind_tc_ok, hg, ht, massert_True]

def contents (bytes : Slice U8) : List (BitVec 8) := bytes.val.map UScalar.bv

/-- Exact unchanged Rust fast-path result when the first byte terminates. -/
theorem decode_one (bytes : Slice U8) (hp : Preconditions bytes)
    (hb : bytes.val[0]'hp.1 < 128#u8) :
    ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok (core.convert.num.FromU64U32.from
        (core.convert.num.FromU32U8.from (bytes.val[0]'hp.1)), 1#usize)) := by
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by have h := hp.1; omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice, he]
  simp only [bind_tc_ok, Bool.false_eq_true, not_false_eq_true, massert_True]
  rw [hc]
  simp only [bind_tc_ok]
  rw [get_unchecked_at bytes 0#usize hp.1]
  simp only [bind_tc_ok, lift]
  exact if_pos hb

/-- Numeric representatives used only in proofs of the unchanged scalar steps. -/
def number (ty : UScalarTy) (n : Nat) : UScalar ty := ⟨BitVec.ofNat ty.numBits n⟩

theorem number_val (ty : UScalarTy) (n : Nat) (h : n < 2^ty.numBits) :
    (number ty n).val = n := Nat.mod_eq_of_lt h

theorem add_number (ty : UScalarTy) (x y : Nat) (h : x+y < 2^ty.numBits) :
    (number ty x + number ty y : Result (UScalar ty)) = .ok (number ty (x+y)) := by
  have hx := number_val ty x (by omega : x < 2^ty.numBits)
  have hy := number_val ty y (by omega : y < 2^ty.numBits)
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := number ty x) (y := number ty y) (by
      rw [UScalar.max]
      rw [hx,hy]; omega))
  have he : z = number ty (x+y) := by
    apply UScalar.eq_of_val_eq
    rw [number_val ty (x+y) h]
    simpa only [hx,hy] using hv
  simpa only [he] using hz

theorem sub_number (ty : UScalarTy) (x y : Nat) (h : x < 2^ty.numBits) (hy : y ≤ x) :
    (number ty x - number ty y : Result (UScalar ty)) = .ok (number ty (x-y)) := by
  have hx := number_val ty x h
  have hyv := number_val ty y (by omega : y < 2^ty.numBits)
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := number ty x) (y := number ty y) (by
      rw [hx,hyv]; exact hy))
  have he : z = number ty (x-y) := by
    apply UScalar.eq_of_val_eq
    rw [number_val ty (x-y) (by omega)]
    simpa only [hx,hyv] using hv.1
  simpa only [he] using hz

theorem shift_number (ty : UScalarTy) (x : Nat) (shift : I32)
    (h0 : 0 ≤ shift.val) (hs : shift.val < ty.numBits)
    (hx : x < 2^ty.numBits) (h : x*2^shift.toNat < 2^ty.numBits) :
    (number ty x <<< shift : Result (UScalar ty)) = .ok (number ty (x*2^shift.toNat)) := by
  obtain ⟨z,hz,hv,hbv⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_IScalar_spec (number ty x) shift (2^ty.numBits) h0 hs (by rw [UScalar.size]))
  have he : z = number ty (x*2^shift.toNat) := by
    apply UScalar.eq_of_val_eq
    rw [number_val ty _ h]
    simpa only [number_val ty x hx,Nat.shiftLeft_eq,Nat.mod_eq_of_lt h] using hv
  simpa only [he] using hz

theorem cast8_number (b : U8) :
    core.convert.num.FromU32U8.from b = number .U32 b.val := by
  apply UScalar.eq_of_val_eq
  rw [core.convert.num.FromU32U8.from_val_eq,number_val]
  have h := b.hmax; scalar_tac

theorem cast32_number (x : Nat) (h : x < 2^32) :
    core.convert.num.FromU64U32.from (number .U32 x) = number .U64 x := by
  apply UScalar.eq_of_val_eq
  rw [core.convert.num.FromU64U32.from_val_eq,number_val .U32 x h,number_val .U64 x (by change x < 2^64; omega)]

def byte (bytes : Slice U8) (i : Nat) : U8 := bytes.val[i]?.getD 0#u8

theorem byte_at (bytes : Slice U8) (i : Nat) (h : i < bytes.length) :
    byte bytes i = bytes.val[i] := by
  simp only [byte,List.getElem?_eq_getElem h,Option.getD_some]

theorem byte_lt (bytes : Slice U8) (i : Nat) : (byte bytes i).val < 256 := by
  have h := (byte bytes i).hmax
  scalar_tac

theorem prefix_access (bytes : Slice U8) (hp : Preconditions bytes) (i : Nat) (hi : i < 10)
    (continued : ∀ j, j < i → 128 ≤ (byte bytes j).val) : i < bytes.length := by
  apply access_bound bytes hp i hi
  intro j hj hji
  simpa only [byte_at bytes j hj] using continued j hji

theorem get_unchecked_byte (bytes : Slice U8) (i : Usize) (hi : i.val < bytes.length) :
    core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes i =
      .ok (byte bytes i.val) := by
  rw [get_unchecked_at bytes i hi,byte_at bytes i.val hi]

theorem decode_two (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val) (h1 : (byte bytes 1).val < 128) :
    ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok (number .U64 ((byte bytes 0).val-128+(byte bytes 1).val*128),2#usize)) := by
  have l0 : 0 < bytes.length := hp.1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have he : j = 0 := by omega
    simpa only [he] using h0)
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have c1 : byte bytes 1 < 128#u8 := h1
  have b0 := byte_lt bytes 0
  have b1 := byte_lt bytes 1
  have hs : (number .U32 (byte bytes 0).val - 128#u32 : Result U32) =
      .ok (number .U32 ((byte bytes 0).val-128)) :=
    sub_number .U32 _ 128 (by change (byte bytes 0).val < 4294967296; omega) h0
  have hl : (number .U32 (byte bytes 1).val <<< 7#i32 : Result U32) =
      .ok (number .U32 ((byte bytes 1).val*128)) :=
    shift_number .U32 _ 7#i32 (by decide) (by decide) (by change (byte bytes 1).val < 4294967296; omega)
      (by change (byte bytes 1).val*128 < 4294967296; omega)
  have ha := add_number .U32 ((byte bytes 0).val-128) ((byte bytes 1).val*128)
    (by change (byte bytes 0).val-128+(byte bytes 1).val*128 < 4294967296; omega)
  have hv := cast32_number ((byte bytes 0).val-128+(byte bytes 1).val*128) (by omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,g0,g1,lift,if_neg c0,if_pos c1,cast8_number,hs,hl,ha,hv]

/-- Exact unchanged fast-path arithmetic for the 3-byte success branch. -/
theorem decode_3 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : (byte bytes 2).val < 128)
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok ((number .U64 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))), 3#usize)) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : byte bytes 2 < 128#u8 := h2
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have cast2 : core.convert.num.FromU64U32.from (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) = (number .U64 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    cast32_number ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) (by omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,if_neg c0,if_neg c1,if_pos c2,sub0,shift1,add1,constant1,sub1,shift2,add2,cast2]

/-- Exact unchanged fast-path arithmetic for the 4-byte success branch. -/
theorem decode_4 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : (byte bytes 3).val < 128)
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok ((number .U64 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))), 4#usize)) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : ¬byte bytes 2 < 128#u8 := by change ¬(byte bytes 2).val < 128; omega
  have b3 := byte_lt bytes 3
  have l3 : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have g3 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 3#usize = .ok (byte bytes 3) :=
    get_unchecked_byte bytes 3#usize l3
  have c3 : byte bytes 3 < 128#u8 := h3
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have constant2 : (128#u32 <<< 14#i32 : Result U32) = .ok (number .U32 (2097152)) :=
    by rfl
  have sub2 : ((number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) 2097152 (by change (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)) < 4294967296; omega) (by omega)
  have shift3 : ((number .U32 ((byte bytes 3).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 3).val*2097152))) :=
    shift_number .U32 ((byte bytes 3).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 3).val < 4294967296; omega) (by change (byte bytes 3).val*2097152 < 4294967296; omega)
  have add3 : ((number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) + (number .U32 (((byte bytes 3).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)) (((byte bytes 3).val*2097152)) (by change ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152) < 4294967296; omega)
  have cast3 : core.convert.num.FromU64U32.from (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) = (number .U64 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    cast32_number ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) (by omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,g3,if_neg c0,if_neg c1,if_neg c2,if_pos c3,sub0,shift1,add1,constant1,sub1,shift2,add2,constant2,sub2,shift3,add3,cast3]

/-- Exact unchanged fast-path arithmetic for the 5-byte success branch. -/
theorem decode_5 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : (byte bytes 4).val < 128)
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok ((number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((byte bytes 4).val*268435456)))), 5#usize)) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : ¬byte bytes 2 < 128#u8 := by change ¬(byte bytes 2).val < 128; omega
  have b3 := byte_lt bytes 3
  have l3 : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have g3 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 3#usize = .ok (byte bytes 3) :=
    get_unchecked_byte bytes 3#usize l3
  have c3 : ¬byte bytes 3 < 128#u8 := by change ¬(byte bytes 3).val < 128; omega
  have b4 := byte_lt bytes 4
  have l4 : 4 < bytes.length := prefix_access bytes hp 4 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3)
  have g4 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 4#usize = .ok (byte bytes 4) :=
    get_unchecked_byte bytes 4#usize l4
  have c4 : byte bytes 4 < 128#u8 := h4
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have constant2 : (128#u32 <<< 14#i32 : Result U32) = .ok (number .U32 (2097152)) :=
    by rfl
  have sub2 : ((number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) 2097152 (by change (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)) < 4294967296; omega) (by omega)
  have shift3 : ((number .U32 ((byte bytes 3).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 3).val*2097152))) :=
    shift_number .U32 ((byte bytes 3).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 3).val < 4294967296; omega) (by change (byte bytes 3).val*2097152 < 4294967296; omega)
  have add3 : ((number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) + (number .U32 (((byte bytes 3).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)) (((byte bytes 3).val*2097152)) (by change ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152) < 4294967296; omega)
  have constant3 : (128#u32 <<< 21#i32 : Result U32) = .ok (number .U32 (268435456)) :=
    by rfl
  have sub3 : ((number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) 268435456 (by change (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock0 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (by omega)
  have cast4 : core.convert.num.FromU64U32.from (number .U32 ((byte bytes 4).val)) = (number .U64 ((byte bytes 4).val)) :=
    cast32_number ((byte bytes 4).val) (by omega)
  have wideShift4 : ((number .U64 ((byte bytes 4).val)) <<< 28#i32 : Result U64) = .ok (number .U64 (((byte bytes 4).val*268435456))) :=
    shift_number .U64 ((byte bytes 4).val) 28#i32 (by decide) (by decide)
      (by change (byte bytes 4).val < 18446744073709551616; omega) (by change (byte bytes 4).val*268435456 < 18446744073709551616; omega)
  have wideAdd4 : ((number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) + (number .U64 (((byte bytes 4).val*268435456))) : Result U64) = .ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((byte bytes 4).val*268435456)))) :=
    add_number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (((byte bytes 4).val*268435456)) (by change ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((byte bytes 4).val*268435456) < 18446744073709551616; omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,g3,g4,if_neg c0,if_neg c1,if_neg c2,if_neg c3,if_pos c4,sub0,shift1,add1,constant1,sub1,shift2,add2,constant2,sub2,shift3,add3,constant3,sub3,castBlock0,cast4,wideShift4,wideAdd4]

/-- Exact unchanged fast-path arithmetic for the 6-byte success branch. -/
theorem decode_6 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : (byte bytes 5).val < 128)
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok ((number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456)))), 6#usize)) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : ¬byte bytes 2 < 128#u8 := by change ¬(byte bytes 2).val < 128; omega
  have b3 := byte_lt bytes 3
  have l3 : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have g3 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 3#usize = .ok (byte bytes 3) :=
    get_unchecked_byte bytes 3#usize l3
  have c3 : ¬byte bytes 3 < 128#u8 := by change ¬(byte bytes 3).val < 128; omega
  have b4 := byte_lt bytes 4
  have l4 : 4 < bytes.length := prefix_access bytes hp 4 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3)
  have g4 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 4#usize = .ok (byte bytes 4) :=
    get_unchecked_byte bytes 4#usize l4
  have c4 : ¬byte bytes 4 < 128#u8 := by change ¬(byte bytes 4).val < 128; omega
  have b5 := byte_lt bytes 5
  have l5 : 5 < bytes.length := prefix_access bytes hp 5 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjcases with he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4)
  have g5 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 5#usize = .ok (byte bytes 5) :=
    get_unchecked_byte bytes 5#usize l5
  have c5 : byte bytes 5 < 128#u8 := h5
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have constant2 : (128#u32 <<< 14#i32 : Result U32) = .ok (number .U32 (2097152)) :=
    by rfl
  have sub2 : ((number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) 2097152 (by change (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)) < 4294967296; omega) (by omega)
  have shift3 : ((number .U32 ((byte bytes 3).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 3).val*2097152))) :=
    shift_number .U32 ((byte bytes 3).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 3).val < 4294967296; omega) (by change (byte bytes 3).val*2097152 < 4294967296; omega)
  have add3 : ((number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) + (number .U32 (((byte bytes 3).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)) (((byte bytes 3).val*2097152)) (by change ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152) < 4294967296; omega)
  have constant3 : (128#u32 <<< 21#i32 : Result U32) = .ok (number .U32 (268435456)) :=
    by rfl
  have sub3 : ((number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) 268435456 (by change (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock0 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (by omega)
  have sub4 : ((number .U32 ((byte bytes 4).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 4).val-128))) :=
    sub_number .U32 ((byte bytes 4).val) 128 (by change (byte bytes 4).val < 4294967296; omega) (by omega)
  have shift5 : ((number .U32 ((byte bytes 5).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 5).val*128))) :=
    shift_number .U32 ((byte bytes 5).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 5).val < 4294967296; omega) (by change (byte bytes 5).val*128 < 4294967296; omega)
  have add5 : ((number .U32 (((byte bytes 4).val-128))) + (number .U32 (((byte bytes 5).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) :=
    add_number .U32 (((byte bytes 4).val-128)) (((byte bytes 5).val*128)) (by change ((byte bytes 4).val-128)+((byte bytes 5).val*128) < 4294967296; omega)
  have cast5 : core.convert.num.FromU64U32.from (number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) = (number .U64 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) :=
    cast32_number ((((byte bytes 4).val-128)+((byte bytes 5).val*128))) (by omega)
  have wideShift5 : ((number .U64 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) <<< 28#i32 : Result U64) = .ok (number .U64 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456))) :=
    shift_number .U64 ((((byte bytes 4).val-128)+((byte bytes 5).val*128))) 28#i32 (by decide) (by decide)
      (by change (((byte bytes 4).val-128)+((byte bytes 5).val*128)) < 18446744073709551616; omega) (by change (((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456 < 18446744073709551616; omega)
  have wideAdd5 : ((number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) + (number .U64 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456))) : Result U64) = .ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456)))) :=
    add_number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456)) (by change ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((byte bytes 4).val-128)+((byte bytes 5).val*128))*268435456) < 18446744073709551616; omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,g3,g4,g5,if_neg c0,if_neg c1,if_neg c2,if_neg c3,if_neg c4,if_pos c5,sub0,shift1,add1,constant1,sub1,shift2,add2,constant2,sub2,shift3,add3,constant3,sub3,castBlock0,sub4,shift5,add5,cast5,wideShift5,wideAdd5]

/-- Exact unchanged fast-path arithmetic for the 7-byte success branch. -/
theorem decode_7 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : (byte bytes 6).val < 128)
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok ((number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456)))), 7#usize)) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : ¬byte bytes 2 < 128#u8 := by change ¬(byte bytes 2).val < 128; omega
  have b3 := byte_lt bytes 3
  have l3 : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have g3 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 3#usize = .ok (byte bytes 3) :=
    get_unchecked_byte bytes 3#usize l3
  have c3 : ¬byte bytes 3 < 128#u8 := by change ¬(byte bytes 3).val < 128; omega
  have b4 := byte_lt bytes 4
  have l4 : 4 < bytes.length := prefix_access bytes hp 4 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3)
  have g4 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 4#usize = .ok (byte bytes 4) :=
    get_unchecked_byte bytes 4#usize l4
  have c4 : ¬byte bytes 4 < 128#u8 := by change ¬(byte bytes 4).val < 128; omega
  have b5 := byte_lt bytes 5
  have l5 : 5 < bytes.length := prefix_access bytes hp 5 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjcases with he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4)
  have g5 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 5#usize = .ok (byte bytes 5) :=
    get_unchecked_byte bytes 5#usize l5
  have c5 : ¬byte bytes 5 < 128#u8 := by change ¬(byte bytes 5).val < 128; omega
  have b6 := byte_lt bytes 6
  have l6 : 6 < bytes.length := prefix_access bytes hp 6 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hjcases with he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5)
  have g6 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 6#usize = .ok (byte bytes 6) :=
    get_unchecked_byte bytes 6#usize l6
  have c6 : byte bytes 6 < 128#u8 := h6
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have constant2 : (128#u32 <<< 14#i32 : Result U32) = .ok (number .U32 (2097152)) :=
    by rfl
  have sub2 : ((number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) 2097152 (by change (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)) < 4294967296; omega) (by omega)
  have shift3 : ((number .U32 ((byte bytes 3).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 3).val*2097152))) :=
    shift_number .U32 ((byte bytes 3).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 3).val < 4294967296; omega) (by change (byte bytes 3).val*2097152 < 4294967296; omega)
  have add3 : ((number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) + (number .U32 (((byte bytes 3).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)) (((byte bytes 3).val*2097152)) (by change ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152) < 4294967296; omega)
  have constant3 : (128#u32 <<< 21#i32 : Result U32) = .ok (number .U32 (268435456)) :=
    by rfl
  have sub3 : ((number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) 268435456 (by change (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock0 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (by omega)
  have sub4 : ((number .U32 ((byte bytes 4).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 4).val-128))) :=
    sub_number .U32 ((byte bytes 4).val) 128 (by change (byte bytes 4).val < 4294967296; omega) (by omega)
  have shift5 : ((number .U32 ((byte bytes 5).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 5).val*128))) :=
    shift_number .U32 ((byte bytes 5).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 5).val < 4294967296; omega) (by change (byte bytes 5).val*128 < 4294967296; omega)
  have add5 : ((number .U32 (((byte bytes 4).val-128))) + (number .U32 (((byte bytes 5).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) :=
    add_number .U32 (((byte bytes 4).val-128)) (((byte bytes 5).val*128)) (by change ((byte bytes 4).val-128)+((byte bytes 5).val*128) < 4294967296; omega)
  have sub5 : ((number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128))) 16384 (by change (((byte bytes 4).val-128)+((byte bytes 5).val*128)) < 4294967296; omega) (by omega)
  have shift6 : ((number .U32 ((byte bytes 6).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 6).val*16384))) :=
    shift_number .U32 ((byte bytes 6).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 6).val < 4294967296; omega) (by change (byte bytes 6).val*16384 < 4294967296; omega)
  have add6 : ((number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) + (number .U32 (((byte bytes 6).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) :=
    add_number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)) (((byte bytes 6).val*16384)) (by change ((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384) < 4294967296; omega)
  have cast6 : core.convert.num.FromU64U32.from (number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) = (number .U64 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) :=
    cast32_number ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))) (by omega)
  have wideShift6 : ((number .U64 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) <<< 28#i32 : Result U64) = .ok (number .U64 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456))) :=
    shift_number .U64 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))) 28#i32 (by decide) (by decide)
      (by change (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)) < 18446744073709551616; omega) (by change (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456 < 18446744073709551616; omega)
  have wideAdd6 : ((number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) + (number .U64 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456))) : Result U64) = .ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456)))) :=
    add_number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456)) (by change ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))*268435456) < 18446744073709551616; omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,g3,g4,g5,g6,if_neg c0,if_neg c1,if_neg c2,if_neg c3,if_neg c4,if_neg c5,if_pos c6,sub0,shift1,add1,constant1,sub1,shift2,add2,constant2,sub2,shift3,add3,constant3,sub3,castBlock0,sub4,shift5,add5,sub5,shift6,add6,cast6,wideShift6,wideAdd6]

/-- Exact unchanged fast-path arithmetic for the 8-byte success branch. -/
theorem decode_8 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : (byte bytes 7).val < 128)
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok ((number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456)))), 8#usize)) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : ¬byte bytes 2 < 128#u8 := by change ¬(byte bytes 2).val < 128; omega
  have b3 := byte_lt bytes 3
  have l3 : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have g3 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 3#usize = .ok (byte bytes 3) :=
    get_unchecked_byte bytes 3#usize l3
  have c3 : ¬byte bytes 3 < 128#u8 := by change ¬(byte bytes 3).val < 128; omega
  have b4 := byte_lt bytes 4
  have l4 : 4 < bytes.length := prefix_access bytes hp 4 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3)
  have g4 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 4#usize = .ok (byte bytes 4) :=
    get_unchecked_byte bytes 4#usize l4
  have c4 : ¬byte bytes 4 < 128#u8 := by change ¬(byte bytes 4).val < 128; omega
  have b5 := byte_lt bytes 5
  have l5 : 5 < bytes.length := prefix_access bytes hp 5 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjcases with he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4)
  have g5 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 5#usize = .ok (byte bytes 5) :=
    get_unchecked_byte bytes 5#usize l5
  have c5 : ¬byte bytes 5 < 128#u8 := by change ¬(byte bytes 5).val < 128; omega
  have b6 := byte_lt bytes 6
  have l6 : 6 < bytes.length := prefix_access bytes hp 6 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hjcases with he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5)
  have g6 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 6#usize = .ok (byte bytes 6) :=
    get_unchecked_byte bytes 6#usize l6
  have c6 : ¬byte bytes 6 < 128#u8 := by change ¬(byte bytes 6).val < 128; omega
  have b7 := byte_lt bytes 7
  have l7 : 7 < bytes.length := prefix_access bytes hp 7 (by decide) (by
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
  have g7 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 7#usize = .ok (byte bytes 7) :=
    get_unchecked_byte bytes 7#usize l7
  have c7 : byte bytes 7 < 128#u8 := h7
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have constant2 : (128#u32 <<< 14#i32 : Result U32) = .ok (number .U32 (2097152)) :=
    by rfl
  have sub2 : ((number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) 2097152 (by change (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)) < 4294967296; omega) (by omega)
  have shift3 : ((number .U32 ((byte bytes 3).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 3).val*2097152))) :=
    shift_number .U32 ((byte bytes 3).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 3).val < 4294967296; omega) (by change (byte bytes 3).val*2097152 < 4294967296; omega)
  have add3 : ((number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) + (number .U32 (((byte bytes 3).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)) (((byte bytes 3).val*2097152)) (by change ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152) < 4294967296; omega)
  have constant3 : (128#u32 <<< 21#i32 : Result U32) = .ok (number .U32 (268435456)) :=
    by rfl
  have sub3 : ((number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) 268435456 (by change (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock0 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (by omega)
  have sub4 : ((number .U32 ((byte bytes 4).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 4).val-128))) :=
    sub_number .U32 ((byte bytes 4).val) 128 (by change (byte bytes 4).val < 4294967296; omega) (by omega)
  have shift5 : ((number .U32 ((byte bytes 5).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 5).val*128))) :=
    shift_number .U32 ((byte bytes 5).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 5).val < 4294967296; omega) (by change (byte bytes 5).val*128 < 4294967296; omega)
  have add5 : ((number .U32 (((byte bytes 4).val-128))) + (number .U32 (((byte bytes 5).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) :=
    add_number .U32 (((byte bytes 4).val-128)) (((byte bytes 5).val*128)) (by change ((byte bytes 4).val-128)+((byte bytes 5).val*128) < 4294967296; omega)
  have sub5 : ((number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128))) 16384 (by change (((byte bytes 4).val-128)+((byte bytes 5).val*128)) < 4294967296; omega) (by omega)
  have shift6 : ((number .U32 ((byte bytes 6).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 6).val*16384))) :=
    shift_number .U32 ((byte bytes 6).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 6).val < 4294967296; omega) (by change (byte bytes 6).val*16384 < 4294967296; omega)
  have add6 : ((number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) + (number .U32 (((byte bytes 6).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) :=
    add_number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)) (((byte bytes 6).val*16384)) (by change ((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384) < 4294967296; omega)
  have sub6 : ((number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))) 2097152 (by change (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)) < 4294967296; omega) (by omega)
  have shift7 : ((number .U32 ((byte bytes 7).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 7).val*2097152))) :=
    shift_number .U32 ((byte bytes 7).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 7).val < 4294967296; omega) (by change (byte bytes 7).val*2097152 < 4294967296; omega)
  have add7 : ((number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152))) + (number .U32 (((byte bytes 7).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)) (((byte bytes 7).val*2097152)) (by change ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152) < 4294967296; omega)
  have cast7 : core.convert.num.FromU64U32.from (number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) = (number .U64 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) :=
    cast32_number ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))) (by omega)
  have wideShift7 : ((number .U64 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) <<< 28#i32 : Result U64) = .ok (number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456))) :=
    shift_number .U64 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))) 28#i32 (by decide) (by decide)
      (by change (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)) < 18446744073709551616; omega) (by change (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456 < 18446744073709551616; omega)
  have wideAdd7 : ((number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) + (number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456))) : Result U64) = .ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456)))) :=
    add_number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456)) (by change ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))*268435456) < 18446744073709551616; omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,g3,g4,g5,g6,g7,if_neg c0,if_neg c1,if_neg c2,if_neg c3,if_neg c4,if_neg c5,if_neg c6,if_pos c7,sub0,shift1,add1,constant1,sub1,shift2,add2,constant2,sub2,shift3,add3,constant3,sub3,castBlock0,sub4,shift5,add5,sub5,shift6,add6,sub6,shift7,add7,cast7,wideShift7,wideAdd7]

/-- Exact unchanged fast-path arithmetic for the 9-byte success branch. -/
theorem decode_9 (bytes : Slice U8) (hp : Preconditions bytes)
    (h0 : 128 ≤ (byte bytes 0).val)
    (h1 : 128 ≤ (byte bytes 1).val)
    (h2 : 128 ≤ (byte bytes 2).val)
    (h3 : 128 ≤ (byte bytes 3).val)
    (h4 : 128 ≤ (byte bytes 4).val)
    (h5 : 128 ≤ (byte bytes 5).val)
    (h6 : 128 ≤ (byte bytes 6).val)
    (h7 : 128 ≤ (byte bytes 7).val)
    (h8 : (byte bytes 8).val < 128)
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok ((number .U64 (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((byte bytes 8).val*72057594037927936)))), 9#usize)) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : ¬byte bytes 2 < 128#u8 := by change ¬(byte bytes 2).val < 128; omega
  have b3 := byte_lt bytes 3
  have l3 : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have g3 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 3#usize = .ok (byte bytes 3) :=
    get_unchecked_byte bytes 3#usize l3
  have c3 : ¬byte bytes 3 < 128#u8 := by change ¬(byte bytes 3).val < 128; omega
  have b4 := byte_lt bytes 4
  have l4 : 4 < bytes.length := prefix_access bytes hp 4 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3)
  have g4 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 4#usize = .ok (byte bytes 4) :=
    get_unchecked_byte bytes 4#usize l4
  have c4 : ¬byte bytes 4 < 128#u8 := by change ¬(byte bytes 4).val < 128; omega
  have b5 := byte_lt bytes 5
  have l5 : 5 < bytes.length := prefix_access bytes hp 5 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjcases with he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4)
  have g5 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 5#usize = .ok (byte bytes 5) :=
    get_unchecked_byte bytes 5#usize l5
  have c5 : ¬byte bytes 5 < 128#u8 := by change ¬(byte bytes 5).val < 128; omega
  have b6 := byte_lt bytes 6
  have l6 : 6 < bytes.length := prefix_access bytes hp 6 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hjcases with he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5)
  have g6 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 6#usize = .ok (byte bytes 6) :=
    get_unchecked_byte bytes 6#usize l6
  have c6 : ¬byte bytes 6 < 128#u8 := by change ¬(byte bytes 6).val < 128; omega
  have b7 := byte_lt bytes 7
  have l7 : 7 < bytes.length := prefix_access bytes hp 7 (by decide) (by
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
  have g7 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 7#usize = .ok (byte bytes 7) :=
    get_unchecked_byte bytes 7#usize l7
  have c7 : ¬byte bytes 7 < 128#u8 := by change ¬(byte bytes 7).val < 128; omega
  have b8 := byte_lt bytes 8
  have l8 : 8 < bytes.length := prefix_access bytes hp 8 (by decide) (by
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
  have g8 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 8#usize = .ok (byte bytes 8) :=
    get_unchecked_byte bytes 8#usize l8
  have c8 : byte bytes 8 < 128#u8 := h8
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have constant2 : (128#u32 <<< 14#i32 : Result U32) = .ok (number .U32 (2097152)) :=
    by rfl
  have sub2 : ((number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) 2097152 (by change (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)) < 4294967296; omega) (by omega)
  have shift3 : ((number .U32 ((byte bytes 3).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 3).val*2097152))) :=
    shift_number .U32 ((byte bytes 3).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 3).val < 4294967296; omega) (by change (byte bytes 3).val*2097152 < 4294967296; omega)
  have add3 : ((number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) + (number .U32 (((byte bytes 3).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)) (((byte bytes 3).val*2097152)) (by change ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152) < 4294967296; omega)
  have constant3 : (128#u32 <<< 21#i32 : Result U32) = .ok (number .U32 (268435456)) :=
    by rfl
  have sub3 : ((number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) 268435456 (by change (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock0 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (by omega)
  have sub4 : ((number .U32 ((byte bytes 4).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 4).val-128))) :=
    sub_number .U32 ((byte bytes 4).val) 128 (by change (byte bytes 4).val < 4294967296; omega) (by omega)
  have shift5 : ((number .U32 ((byte bytes 5).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 5).val*128))) :=
    shift_number .U32 ((byte bytes 5).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 5).val < 4294967296; omega) (by change (byte bytes 5).val*128 < 4294967296; omega)
  have add5 : ((number .U32 (((byte bytes 4).val-128))) + (number .U32 (((byte bytes 5).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) :=
    add_number .U32 (((byte bytes 4).val-128)) (((byte bytes 5).val*128)) (by change ((byte bytes 4).val-128)+((byte bytes 5).val*128) < 4294967296; omega)
  have sub5 : ((number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128))) 16384 (by change (((byte bytes 4).val-128)+((byte bytes 5).val*128)) < 4294967296; omega) (by omega)
  have shift6 : ((number .U32 ((byte bytes 6).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 6).val*16384))) :=
    shift_number .U32 ((byte bytes 6).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 6).val < 4294967296; omega) (by change (byte bytes 6).val*16384 < 4294967296; omega)
  have add6 : ((number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) + (number .U32 (((byte bytes 6).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) :=
    add_number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)) (((byte bytes 6).val*16384)) (by change ((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384) < 4294967296; omega)
  have sub6 : ((number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))) 2097152 (by change (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)) < 4294967296; omega) (by omega)
  have shift7 : ((number .U32 ((byte bytes 7).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 7).val*2097152))) :=
    shift_number .U32 ((byte bytes 7).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 7).val < 4294967296; omega) (by change (byte bytes 7).val*2097152 < 4294967296; omega)
  have add7 : ((number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152))) + (number .U32 (((byte bytes 7).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)) (((byte bytes 7).val*2097152)) (by change ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152) < 4294967296; omega)
  have sub7 : ((number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))) 268435456 (by change (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock1 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)) (by omega)
  have wideShiftBlock1 : ((number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) <<< 28#i32 : Result U64) = .ok (number .U64 ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))) :=
    shift_number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)) 28#i32 (by decide) (by decide)
      (by change ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456) < 18446744073709551616; omega) (by change ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456 < 18446744073709551616; omega)
  have wideAddBlock1 : ((number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) + (number .U64 ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))) : Result U64) = .ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456)))) :=
    add_number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456)) (by change ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456) < 18446744073709551616; omega)
  have cast8 : core.convert.num.FromU64U32.from (number .U32 ((byte bytes 8).val)) = (number .U64 ((byte bytes 8).val)) :=
    cast32_number ((byte bytes 8).val) (by omega)
  have wideShift8 : ((number .U64 ((byte bytes 8).val)) <<< 56#i32 : Result U64) = .ok (number .U64 (((byte bytes 8).val*72057594037927936))) :=
    shift_number .U64 ((byte bytes 8).val) 56#i32 (by decide) (by decide)
      (by change (byte bytes 8).val < 18446744073709551616; omega) (by change (byte bytes 8).val*72057594037927936 < 18446744073709551616; omega)
  have wideAdd8 : ((number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456)))) + (number .U64 (((byte bytes 8).val*72057594037927936))) : Result U64) = .ok (number .U64 (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((byte bytes 8).val*72057594037927936)))) :=
    add_number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))) (((byte bytes 8).val*72057594037927936)) (by change (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((byte bytes 8).val*72057594037927936) < 18446744073709551616; omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,g3,g4,g5,g6,g7,g8,if_neg c0,if_neg c1,if_neg c2,if_neg c3,if_neg c4,if_neg c5,if_neg c6,if_neg c7,if_pos c8,sub0,shift1,add1,constant1,sub1,shift2,add2,constant2,sub2,shift3,add3,constant3,sub3,castBlock0,sub4,shift5,add5,sub5,shift6,add6,sub6,shift7,add7,sub7,castBlock1,wideShiftBlock1,wideAddBlock1,cast8,wideShift8,wideAdd8]

/-- Exact unchanged fast-path arithmetic for the 10-byte success branch. -/
theorem decode_10 (bytes : Slice U8) (hp : Preconditions bytes)
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
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok ((number .U64 (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936)))), 10#usize)) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : ¬byte bytes 2 < 128#u8 := by change ¬(byte bytes 2).val < 128; omega
  have b3 := byte_lt bytes 3
  have l3 : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have g3 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 3#usize = .ok (byte bytes 3) :=
    get_unchecked_byte bytes 3#usize l3
  have c3 : ¬byte bytes 3 < 128#u8 := by change ¬(byte bytes 3).val < 128; omega
  have b4 := byte_lt bytes 4
  have l4 : 4 < bytes.length := prefix_access bytes hp 4 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3)
  have g4 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 4#usize = .ok (byte bytes 4) :=
    get_unchecked_byte bytes 4#usize l4
  have c4 : ¬byte bytes 4 < 128#u8 := by change ¬(byte bytes 4).val < 128; omega
  have b5 := byte_lt bytes 5
  have l5 : 5 < bytes.length := prefix_access bytes hp 5 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjcases with he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4)
  have g5 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 5#usize = .ok (byte bytes 5) :=
    get_unchecked_byte bytes 5#usize l5
  have c5 : ¬byte bytes 5 < 128#u8 := by change ¬(byte bytes 5).val < 128; omega
  have b6 := byte_lt bytes 6
  have l6 : 6 < bytes.length := prefix_access bytes hp 6 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hjcases with he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5)
  have g6 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 6#usize = .ok (byte bytes 6) :=
    get_unchecked_byte bytes 6#usize l6
  have c6 : ¬byte bytes 6 < 128#u8 := by change ¬(byte bytes 6).val < 128; omega
  have b7 := byte_lt bytes 7
  have l7 : 7 < bytes.length := prefix_access bytes hp 7 (by decide) (by
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
  have g7 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 7#usize = .ok (byte bytes 7) :=
    get_unchecked_byte bytes 7#usize l7
  have c7 : ¬byte bytes 7 < 128#u8 := by change ¬(byte bytes 7).val < 128; omega
  have b8 := byte_lt bytes 8
  have l8 : 8 < bytes.length := prefix_access bytes hp 8 (by decide) (by
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
  have g8 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 8#usize = .ok (byte bytes 8) :=
    get_unchecked_byte bytes 8#usize l8
  have c8 : ¬byte bytes 8 < 128#u8 := by change ¬(byte bytes 8).val < 128; omega
  have b9 := byte_lt bytes 9
  have l9 : 9 < bytes.length := prefix_access bytes hp 9 (by decide) (by
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
  have g9 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 9#usize = .ok (byte bytes 9) :=
    get_unchecked_byte bytes 9#usize l9
  have c9 : byte bytes 9 < 2#u8 := h9
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have constant2 : (128#u32 <<< 14#i32 : Result U32) = .ok (number .U32 (2097152)) :=
    by rfl
  have sub2 : ((number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) 2097152 (by change (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)) < 4294967296; omega) (by omega)
  have shift3 : ((number .U32 ((byte bytes 3).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 3).val*2097152))) :=
    shift_number .U32 ((byte bytes 3).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 3).val < 4294967296; omega) (by change (byte bytes 3).val*2097152 < 4294967296; omega)
  have add3 : ((number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) + (number .U32 (((byte bytes 3).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)) (((byte bytes 3).val*2097152)) (by change ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152) < 4294967296; omega)
  have constant3 : (128#u32 <<< 21#i32 : Result U32) = .ok (number .U32 (268435456)) :=
    by rfl
  have sub3 : ((number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) 268435456 (by change (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock0 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (by omega)
  have sub4 : ((number .U32 ((byte bytes 4).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 4).val-128))) :=
    sub_number .U32 ((byte bytes 4).val) 128 (by change (byte bytes 4).val < 4294967296; omega) (by omega)
  have shift5 : ((number .U32 ((byte bytes 5).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 5).val*128))) :=
    shift_number .U32 ((byte bytes 5).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 5).val < 4294967296; omega) (by change (byte bytes 5).val*128 < 4294967296; omega)
  have add5 : ((number .U32 (((byte bytes 4).val-128))) + (number .U32 (((byte bytes 5).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) :=
    add_number .U32 (((byte bytes 4).val-128)) (((byte bytes 5).val*128)) (by change ((byte bytes 4).val-128)+((byte bytes 5).val*128) < 4294967296; omega)
  have sub5 : ((number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128))) 16384 (by change (((byte bytes 4).val-128)+((byte bytes 5).val*128)) < 4294967296; omega) (by omega)
  have shift6 : ((number .U32 ((byte bytes 6).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 6).val*16384))) :=
    shift_number .U32 ((byte bytes 6).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 6).val < 4294967296; omega) (by change (byte bytes 6).val*16384 < 4294967296; omega)
  have add6 : ((number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) + (number .U32 (((byte bytes 6).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) :=
    add_number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)) (((byte bytes 6).val*16384)) (by change ((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384) < 4294967296; omega)
  have sub6 : ((number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))) 2097152 (by change (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)) < 4294967296; omega) (by omega)
  have shift7 : ((number .U32 ((byte bytes 7).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 7).val*2097152))) :=
    shift_number .U32 ((byte bytes 7).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 7).val < 4294967296; omega) (by change (byte bytes 7).val*2097152 < 4294967296; omega)
  have add7 : ((number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152))) + (number .U32 (((byte bytes 7).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)) (((byte bytes 7).val*2097152)) (by change ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152) < 4294967296; omega)
  have sub7 : ((number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))) 268435456 (by change (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock1 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)) (by omega)
  have wideShiftBlock1 : ((number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) <<< 28#i32 : Result U64) = .ok (number .U64 ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))) :=
    shift_number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)) 28#i32 (by decide) (by decide)
      (by change ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456) < 18446744073709551616; omega) (by change ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456 < 18446744073709551616; omega)
  have wideAddBlock1 : ((number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) + (number .U64 ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))) : Result U64) = .ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456)))) :=
    add_number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456)) (by change ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456) < 18446744073709551616; omega)
  have sub8 : ((number .U32 ((byte bytes 8).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 8).val-128))) :=
    sub_number .U32 ((byte bytes 8).val) 128 (by change (byte bytes 8).val < 4294967296; omega) (by omega)
  have shift9 : ((number .U32 ((byte bytes 9).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 9).val*128))) :=
    shift_number .U32 ((byte bytes 9).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 9).val < 4294967296; omega) (by change (byte bytes 9).val*128 < 4294967296; omega)
  have add9 : ((number .U32 (((byte bytes 8).val-128))) + (number .U32 (((byte bytes 9).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 8).val-128)+((byte bytes 9).val*128)))) :=
    add_number .U32 (((byte bytes 8).val-128)) (((byte bytes 9).val*128)) (by change ((byte bytes 8).val-128)+((byte bytes 9).val*128) < 4294967296; omega)
  have cast9 : core.convert.num.FromU64U32.from (number .U32 ((((byte bytes 8).val-128)+((byte bytes 9).val*128)))) = (number .U64 ((((byte bytes 8).val-128)+((byte bytes 9).val*128)))) :=
    cast32_number ((((byte bytes 8).val-128)+((byte bytes 9).val*128))) (by omega)
  have wideShift9 : ((number .U64 ((((byte bytes 8).val-128)+((byte bytes 9).val*128)))) <<< 56#i32 : Result U64) = .ok (number .U64 (((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936))) :=
    shift_number .U64 ((((byte bytes 8).val-128)+((byte bytes 9).val*128))) 56#i32 (by decide) (by decide)
      (by change (((byte bytes 8).val-128)+((byte bytes 9).val*128)) < 18446744073709551616; omega) (by change (((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936 < 18446744073709551616; omega)
  have wideAdd9 : ((number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456)))) + (number .U64 (((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936))) : Result U64) = .ok (number .U64 (((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936)))) :=
    add_number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))) (((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936)) (by change (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))+((((byte bytes 8).val-128)+((byte bytes 9).val*128))*72057594037927936) < 18446744073709551616; omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,if_neg c0,if_neg c1,if_neg c2,if_neg c3,if_neg c4,if_neg c5,if_neg c6,if_neg c7,if_neg c8,if_pos c9,sub0,shift1,add1,constant1,sub1,shift2,add2,constant2,sub2,shift3,add3,constant3,sub3,castBlock0,sub4,shift5,add5,sub5,shift6,add6,sub6,shift7,add7,sub7,castBlock1,wideShiftBlock1,wideAddBlock1,sub8,shift9,add9,cast9,wideShift9,wideAdd9]

def invalidError : ProstKeyCandidate.error.DecodeError :=
  ⟨⟨.InvalidVarint, alloc.vec.Vec.new (Str × Str)⟩⟩

/-- Exact unchanged fast-path arithmetic for the tenth-byte overflow error branch. -/
theorem decode_invalid (bytes : Slice U8) (hp : Preconditions bytes)
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
    : ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Err invalidError) := by
  have b0 := byte_lt bytes 0
  have l0 : 0 < bytes.length := hp.1
  have g0 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 0#usize = .ok (byte bytes 0) :=
    get_unchecked_byte bytes 0#usize l0
  have c0 : ¬byte bytes 0 < 128#u8 := by change ¬(byte bytes 0).val < 128; omega
  have b1 := byte_lt bytes 1
  have l1 : 1 < bytes.length := prefix_access bytes hp 1 (by decide) (by
    intro j hj
    have hjcases : j = 0 := by omega
    simpa only [hjcases] using h0)
  have g1 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 1#usize = .ok (byte bytes 1) :=
    get_unchecked_byte bytes 1#usize l1
  have c1 : ¬byte bytes 1 < 128#u8 := by change ¬(byte bytes 1).val < 128; omega
  have b2 := byte_lt bytes 2
  have l2 : 2 < bytes.length := prefix_access bytes hp 2 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with he | he
    · simpa only [he] using h0
    · simpa only [he] using h1)
  have g2 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 2#usize = .ok (byte bytes 2) :=
    get_unchecked_byte bytes 2#usize l2
  have c2 : ¬byte bytes 2 < 128#u8 := by change ¬(byte bytes 2).val < 128; omega
  have b3 := byte_lt bytes 3
  have l3 : 3 < bytes.length := prefix_access bytes hp 3 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2)
  have g3 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 3#usize = .ok (byte bytes 3) :=
    get_unchecked_byte bytes 3#usize l3
  have c3 : ¬byte bytes 3 < 128#u8 := by change ¬(byte bytes 3).val < 128; omega
  have b4 := byte_lt bytes 4
  have l4 : 4 < bytes.length := prefix_access bytes hp 4 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3)
  have g4 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 4#usize = .ok (byte bytes 4) :=
    get_unchecked_byte bytes 4#usize l4
  have c4 : ¬byte bytes 4 < 128#u8 := by change ¬(byte bytes 4).val < 128; omega
  have b5 := byte_lt bytes 5
  have l5 : 5 < bytes.length := prefix_access bytes hp 5 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjcases with he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4)
  have g5 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 5#usize = .ok (byte bytes 5) :=
    get_unchecked_byte bytes 5#usize l5
  have c5 : ¬byte bytes 5 < 128#u8 := by change ¬(byte bytes 5).val < 128; omega
  have b6 := byte_lt bytes 6
  have l6 : 6 < bytes.length := prefix_access bytes hp 6 (by decide) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hjcases with he | he | he | he | he | he
    · simpa only [he] using h0
    · simpa only [he] using h1
    · simpa only [he] using h2
    · simpa only [he] using h3
    · simpa only [he] using h4
    · simpa only [he] using h5)
  have g6 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 6#usize = .ok (byte bytes 6) :=
    get_unchecked_byte bytes 6#usize l6
  have c6 : ¬byte bytes 6 < 128#u8 := by change ¬(byte bytes 6).val < 128; omega
  have b7 := byte_lt bytes 7
  have l7 : 7 < bytes.length := prefix_access bytes hp 7 (by decide) (by
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
  have g7 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 7#usize = .ok (byte bytes 7) :=
    get_unchecked_byte bytes 7#usize l7
  have c7 : ¬byte bytes 7 < 128#u8 := by change ¬(byte bytes 7).val < 128; omega
  have b8 := byte_lt bytes 8
  have l8 : 8 < bytes.length := prefix_access bytes hp 8 (by decide) (by
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
  have g8 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 8#usize = .ok (byte bytes 8) :=
    get_unchecked_byte bytes 8#usize l8
  have c8 : ¬byte bytes 8 < 128#u8 := by change ¬(byte bytes 8).val < 128; omega
  have b9 := byte_lt bytes 9
  have l9 : 9 < bytes.length := prefix_access bytes hp 9 (by decide) (by
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
  have g9 : core.slice.Slice.get_unchecked (core.slice.index.SliceIndexUsizeSlice U8) bytes 9#usize = .ok (byte bytes 9) :=
    get_unchecked_byte bytes 9#usize l9
  have c9 : ¬byte bytes 9 < 2#u8 := by change ¬(byte bytes 9).val < 2; omega
  have sub0 : ((number .U32 ((byte bytes 0).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 0).val-128))) :=
    sub_number .U32 ((byte bytes 0).val) 128 (by change (byte bytes 0).val < 4294967296; omega) (by omega)
  have shift1 : ((number .U32 ((byte bytes 1).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 1).val*128))) :=
    shift_number .U32 ((byte bytes 1).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 1).val < 4294967296; omega) (by change (byte bytes 1).val*128 < 4294967296; omega)
  have add1 : ((number .U32 (((byte bytes 0).val-128))) + (number .U32 (((byte bytes 1).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) :=
    add_number .U32 (((byte bytes 0).val-128)) (((byte bytes 1).val*128)) (by change ((byte bytes 0).val-128)+((byte bytes 1).val*128) < 4294967296; omega)
  have constant1 : (128#u32 <<< 7#i32 : Result U32) = .ok (number .U32 (16384)) :=
    by rfl
  have sub1 : ((number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 0).val-128)+((byte bytes 1).val*128))) 16384 (by change (((byte bytes 0).val-128)+((byte bytes 1).val*128)) < 4294967296; omega) (by omega)
  have shift2 : ((number .U32 ((byte bytes 2).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 2).val*16384))) :=
    shift_number .U32 ((byte bytes 2).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 2).val < 4294967296; omega) (by change (byte bytes 2).val*16384 < 4294967296; omega)
  have add2 : ((number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384))) + (number .U32 (((byte bytes 2).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) :=
    add_number .U32 (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)) (((byte bytes 2).val*16384)) (by change ((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384) < 4294967296; omega)
  have constant2 : (128#u32 <<< 14#i32 : Result U32) = .ok (number .U32 (2097152)) :=
    by rfl
  have sub2 : ((number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))) 2097152 (by change (((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384)) < 4294967296; omega) (by omega)
  have shift3 : ((number .U32 ((byte bytes 3).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 3).val*2097152))) :=
    shift_number .U32 ((byte bytes 3).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 3).val < 4294967296; omega) (by change (byte bytes 3).val*2097152 < 4294967296; omega)
  have add3 : ((number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152))) + (number .U32 (((byte bytes 3).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)) (((byte bytes 3).val*2097152)) (by change ((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152) < 4294967296; omega)
  have constant3 : (128#u32 <<< 21#i32 : Result U32) = .ok (number .U32 (268435456)) :=
    by rfl
  have sub3 : ((number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))) 268435456 (by change (((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock0 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) (by omega)
  have sub4 : ((number .U32 ((byte bytes 4).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 4).val-128))) :=
    sub_number .U32 ((byte bytes 4).val) 128 (by change (byte bytes 4).val < 4294967296; omega) (by omega)
  have shift5 : ((number .U32 ((byte bytes 5).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 5).val*128))) :=
    shift_number .U32 ((byte bytes 5).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 5).val < 4294967296; omega) (by change (byte bytes 5).val*128 < 4294967296; omega)
  have add5 : ((number .U32 (((byte bytes 4).val-128))) + (number .U32 (((byte bytes 5).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) :=
    add_number .U32 (((byte bytes 4).val-128)) (((byte bytes 5).val*128)) (by change ((byte bytes 4).val-128)+((byte bytes 5).val*128) < 4294967296; omega)
  have sub5 : ((number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128)))) - (number .U32 (16384)) : Result U32) = .ok (number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) :=
    sub_number .U32 ((((byte bytes 4).val-128)+((byte bytes 5).val*128))) 16384 (by change (((byte bytes 4).val-128)+((byte bytes 5).val*128)) < 4294967296; omega) (by omega)
  have shift6 : ((number .U32 ((byte bytes 6).val)) <<< 14#i32 : Result U32) = .ok (number .U32 (((byte bytes 6).val*16384))) :=
    shift_number .U32 ((byte bytes 6).val) 14#i32 (by decide) (by decide)
      (by change (byte bytes 6).val < 4294967296; omega) (by change (byte bytes 6).val*16384 < 4294967296; omega)
  have add6 : ((number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384))) + (number .U32 (((byte bytes 6).val*16384))) : Result U32) = .ok (number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) :=
    add_number .U32 (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)) (((byte bytes 6).val*16384)) (by change ((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384) < 4294967296; omega)
  have sub6 : ((number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)))) - (number .U32 (2097152)) : Result U32) = .ok (number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152))) :=
    sub_number .U32 ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))) 2097152 (by change (((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384)) < 4294967296; omega) (by omega)
  have shift7 : ((number .U32 ((byte bytes 7).val)) <<< 21#i32 : Result U32) = .ok (number .U32 (((byte bytes 7).val*2097152))) :=
    shift_number .U32 ((byte bytes 7).val) 21#i32 (by decide) (by decide)
      (by change (byte bytes 7).val < 4294967296; omega) (by change (byte bytes 7).val*2097152 < 4294967296; omega)
  have add7 : ((number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152))) + (number .U32 (((byte bytes 7).val*2097152))) : Result U32) = .ok (number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) :=
    add_number .U32 (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)) (((byte bytes 7).val*2097152)) (by change ((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152) < 4294967296; omega)
  have sub7 : ((number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)))) - (number .U32 (268435456)) : Result U32) = .ok (number .U32 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) :=
    sub_number .U32 ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))) 268435456 (by change (((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152)) < 4294967296; omega) (by omega)
  have castBlock1 : core.convert.num.FromU64U32.from (number .U32 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) = (number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) :=
    cast32_number (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)) (by omega)
  have wideShiftBlock1 : ((number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456))) <<< 28#i32 : Result U64) = .ok (number .U64 ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))) :=
    shift_number .U64 (((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)) 28#i32 (by decide) (by decide)
      (by change ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456) < 18446744073709551616; omega) (by change ((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456 < 18446744073709551616; omega)
  have wideAddBlock1 : ((number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456))) + (number .U64 ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456))) : Result U64) = .ok (number .U64 ((((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456)))) :=
    add_number .U64 (((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)) ((((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456)) (by change ((((((((byte bytes 0).val-128)+((byte bytes 1).val*128))-16384)+((byte bytes 2).val*16384))-2097152)+((byte bytes 3).val*2097152))-268435456)+(((((((((byte bytes 4).val-128)+((byte bytes 5).val*128))-16384)+((byte bytes 6).val*16384))-2097152)+((byte bytes 7).val*2097152))-268435456)*268435456) < 18446744073709551616; omega)
  have sub8 : ((number .U32 ((byte bytes 8).val)) - 128#u32 : Result U32) = .ok (number .U32 (((byte bytes 8).val-128))) :=
    sub_number .U32 ((byte bytes 8).val) 128 (by change (byte bytes 8).val < 4294967296; omega) (by omega)
  have shift9 : ((number .U32 ((byte bytes 9).val)) <<< 7#i32 : Result U32) = .ok (number .U32 (((byte bytes 9).val*128))) :=
    shift_number .U32 ((byte bytes 9).val) 7#i32 (by decide) (by decide)
      (by change (byte bytes 9).val < 4294967296; omega) (by change (byte bytes 9).val*128 < 4294967296; omega)
  have add9 : ((number .U32 (((byte bytes 8).val-128))) + (number .U32 (((byte bytes 9).val*128))) : Result U32) = .ok (number .U32 ((((byte bytes 8).val-128)+((byte bytes 9).val*128)))) :=
    add_number .U32 (((byte bytes 8).val-128)) (((byte bytes 9).val*128)) (by change ((byte bytes 8).val-128)+((byte bytes 9).val*128) < 4294967296; omega)
  have he : core.slice.Slice.is_empty bytes = .ok false := by
    have hn : bytes.length ≠ 0 := by omega
    simp [core.slice.Slice.is_empty, hn]
  have hc := initialChecks_ok bytes hp
  unfold initialChecks at hc
  rw [ProstKeyCandidate.encoding.varint.decode_varint_slice,he]
  simp only [bind_tc_ok,Bool.false_eq_true,not_false_eq_true,massert_True]
  rw [hc]
  simp only [bind_tc_ok,lift,cast8_number,g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,if_neg c0,if_neg c1,if_neg c2,if_neg c3,if_neg c4,if_neg c5,if_neg c6,if_neg c7,if_neg c8,if_neg c9,sub0,shift1,add1,constant1,sub1,shift2,add2,constant2,sub2,shift3,add3,constant3,sub3,castBlock0,sub4,shift5,add5,sub5,shift6,add6,sub6,shift7,add7,sub7,castBlock1,wideShiftBlock1,wideAddBlock1,sub8,shift9,add9]
  rfl

theorem decode_1 (bytes : Slice U8) (hp : Preconditions bytes) (h0 : (byte bytes 0).val < 128) :
    ProstKeyCandidate.encoding.varint.decode_varint_slice bytes =
      .ok (.Ok (number .U64 (byte bytes 0).val,1#usize)) := by
  have hb : bytes.val[0]'hp.1 < 128#u8 := by
    rw [← byte_at bytes 0 hp.1]
    exact h0
  rw [decode_one bytes hp hb]
  rw [← byte_at bytes 0 hp.1,cast8_number,cast32_number _ (by omega)]

#print axioms preconditions_iff
#print axioms decode_1
#print axioms decode_invalid
#print axioms decode_3
#print axioms decode_4
#print axioms decode_5
#print axioms decode_6
#print axioms decode_7
#print axioms decode_8
#print axioms decode_9
#print axioms preconditions_iff
#print axioms decode_10
#print axioms access_bound
#print axioms get_unchecked_at
#print axioms initialChecks_ok
#print axioms decode_one
#print axioms add_number
#print axioms sub_number
#print axioms shift_number
#print axioms cast8_number
#print axioms decode_two
#print axioms cast32_number
end LibSignalReference.Candidate.ProstKeySlice
