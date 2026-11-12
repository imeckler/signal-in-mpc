import TlsMpc.MlKemFastProofs

/-!
# KEM kernels: the bit-list encodings against the specification's shift-and-mask encodings

`TlsMpc/Signal/MlKemFast.lean` regroups bit lists (`decode12`, `encode`, `cbd`,
`messagePoly`); the specification (`MlKemEncoding.decode` / `encode`,
`MlKemArithmetic.cbd`, `MlKemEncoding.decompress 1`, `MlKemPke.noise`) shifts and
masks 32-bit words. On values (the `concrete` instances) they agree:

* `decode12_refines`: `decode12 count bytes`, zero-extended, is
  `MlKemEncoding.decode 12 count bytes`, for every byte string and count.
* `encode_refines`: `encode width poly` is `MlKemEncoding.encode width count` of the
  zero-extended polynomial, for `0 < width ≤ 12`, `count = poly.length`, `8 ∣ width·count`
  (any coefficient values: only the low `width` bits are packed on both sides).
* `cbd_refines`, `cbd_canon`: the centered binomial sample, zero-extended, is
  `MlKemArithmetic.cbd 2 256`, and every coefficient is below q.
* `noise_refines`: the kernels' `noise` is `MlKemPke.noise … 2` (which also goes
  through the specification's 16-bit serialisation and back).
* `messagePoly_refines`: for a 32-byte message, `messagePoly` is
  `decompress 1 ∘ decode 1 256`.
* `decode12_encode`, `polyAt_flatMap_encode`: the 384-byte serialisation between
  kernels round-trips (any 12-bit coefficients).

Everything here is about the existing definitions; nothing is redefined.
-/
namespace TlsMpc.KernelSpecs.KemEncoding
open TlsMpc.Signal

local notation "FO" => MlKemFast.concrete
local notation "SH" => Sha256.concrete
local notation "BA" => ByteAuth.concrete
local notation "AR" => MlKemArithmetic.concrete
local notation "EN" => MlKemEncoding.concrete

/-! ### Bits of a byte string -/

/-- Bit `n` (little-endian) of a byte string; 0 past the end. -/
def bitAt (bytes : List (BitVec 8)) (n : Nat) : Bool := (bytes[n / 8]?.getD 0#8).getLsbD (n % 8)

theorem bitAt_eq (bytes : List (BitVec 8)) (q r : Nat) (hr : r < 8) :
    bitAt bytes (8 * q + r) = (bytes[q]?.getD 0#8).getLsbD r := by
  have h1 : (8 * q + r) / 8 = q := by omega
  have h2 : (8 * q + r) % 8 = r := by omega
  simp only [bitAt, h1, h2]

theorem bitAt_cons_lt (b : BitVec 8) (bs : List (BitVec 8)) (m : Nat) (hm : m < 8) :
    bitAt (b :: bs) m = b.getLsbD m := by
  have h1 : m / 8 = 0 := by omega
  have h2 : m % 8 = m := by omega
  simp only [bitAt, h1, h2, List.getElem?_cons_zero, Option.getD_some]

theorem bitAt_cons_add (b : BitVec 8) (bs : List (BitVec 8)) (m : Nat) :
    bitAt (b :: bs) (m + 8) = bitAt bs m := by
  have h1 : (m + 8) / 8 = m / 8 + 1 := by omega
  have h2 : (m + 8) % 8 = m % 8 := by omega
  simp only [bitAt, h1, h2, List.getElem?_cons_succ]

theorem bitAt_nil (m : Nat) : bitAt [] m = false := by
  simp [bitAt]

theorem extract_one {n : Nat} (x : BitVec n) (i : Nat) : x.extractLsb' i 1 = BitVec.ofBool (x.getLsbD i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have : j = 0 := by omega
  subst this
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool]

theorem byteBits_eq (b : BitVec 8) : MlKemFast.concrete.byteBits b = (List.range 8).map (fun i => b.extractLsb' i 1) := rfl

theorem bitsOf_getElem? (bytes : List (BitVec 8)) : ∀ m : Nat,
    (MlKemFast.bitsOf FO bytes)[m]? =
      if m < 8 * bytes.length then some (BitVec.ofBool (bitAt bytes m)) else none := by
  induction bytes with
  | nil => intro m; simp [MlKemFast.bitsOf]
  | cons b bs ih =>
      intro m
      have split : MlKemFast.bitsOf FO (b :: bs) = MlKemFast.concrete.byteBits b ++ MlKemFast.bitsOf FO bs := by
        simp only [MlKemFast.bitsOf, List.flatMap_cons]
      have len : (MlKemFast.concrete.byteBits b).length = 8 := by simp [byteBits_eq]
      rw [split]
      by_cases hm : m < 8
      · rw [List.getElem?_append_left (by rw [len]; exact hm), byteBits_eq, List.getElem?_map,
          List.getElem?_range hm, bitAt_cons_lt b bs m hm, if_pos (by simp; omega)]
        simp only [Option.map_some, extract_one]
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
        rw [List.getElem?_append_right (by rw [len]; omega), len, Nat.add_sub_cancel, ih k, bitAt_cons_add]
        simp only [List.length_cons]
        by_cases hk : k < 8 * bs.length
        · rw [if_pos hk, if_pos (by omega)]
        · rw [if_neg hk, if_neg (by omega)]

theorem bitsOf_getD (bytes : List (BitVec 8)) (m : Nat) :
    (MlKemFast.bitsOf FO bytes).getD m 0#1 = BitVec.ofBool (bitAt bytes m) := by
  rw [List.getD_eq_getElem?_getD, bitsOf_getElem?]
  split
  · rfl
  · rename_i h
    have hb : bitAt bytes m = false := by
      have hq : bytes[m / 8]? = none := List.getElem?_eq_none (by omega)
      simp [bitAt, hq]
    rw [hb]
    rfl

theorem bitsOf_length (bytes : List (BitVec 8)) : (MlKemFast.bitsOf FO bytes).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
      simp only [MlKemFast.bitsOf, List.flatMap_cons, List.length_append] at ih ⊢
      rw [ih, show (MlKemFast.concrete.byteBits b).length = 8 by simp [byteBits_eq], List.length_cons]
      omega

theorem bitsOf_eq (bytes : List (BitVec 8)) :
    MlKemFast.bitsOf FO bytes = (List.range (8 * bytes.length)).map (fun m => BitVec.ofBool (bitAt bytes m)) := by
  apply List.ext_getElem?
  intro m
  rw [bitsOf_getElem?, List.getElem?_map]
  by_cases hm : m < 8 * bytes.length
  · rw [if_pos hm, List.getElem?_range hm]; rfl
  · rw [if_neg hm, List.getElem?_eq_none (by simp; omega)]; rfl

/-! ### Packing bits into a word -/

theorem packValue_getLsbD : ∀ (n : Nat) (bit : Nat → BitVec 1) (j : Nat),
    (MlKemFast.packValue n bit).getLsbD j = (decide (j < n) && (bit j).getLsbD 0)
  | 0, bit, j => by simp [MlKemFast.packValue]
  | n + 1, bit, j => by
      simp only [MlKemFast.packValue, BitVec.getLsbD_cast, BitVec.getLsbD_append, packValue_getLsbD n]
      by_cases h : j < n
      · simp [h, show j < n + 1 by omega]
      · by_cases h' : j = n
        · subst h'; simp
        · have hz : (bit n).getLsbD (j - n) = false := BitVec.getLsbD_of_ge _ _ (by omega)
          simp [h, hz, show ¬ j < n + 1 by omega]

theorem ofBits_getLsbD (l : List (BitVec 1)) (j : Nat) :
    (MlKemFast.concrete.ofBits l).getLsbD j = (decide (j < 12) && (l.getD j 0#1).getLsbD 0) := by
  have h : MlKemFast.concrete.ofBits l = MlKemFast.packValue 12 (fun i => l.getD i 0#1) := rfl
  rw [h, packValue_getLsbD]

theorem bitsByte_getLsbD (l : List (BitVec 1)) (j : Nat) :
    (MlKemFast.concrete.bitsByte l).getLsbD j = (decide (j < 8) && (l.getD j 0#1).getLsbD 0) := by
  have h : MlKemFast.concrete.bitsByte l = MlKemFast.packValue 8 (fun i => l.getD i 0#1) := rfl
  rw [h, packValue_getLsbD]

theorem ofBool_getLsbD_zero (b : Bool) : (BitVec.ofBool b).getLsbD 0 = b := by
  cases b <;> rfl

theorem chunk_getD {α : Type} (l : List α) (size i j : Nat) (d : α) (hj : j < size) :
    (MlKemFast.chunk l size i).getD j d = l.getD (size * i + j) d := by
  simp only [MlKemFast.chunk, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, List.getElem?_drop]

theorem flatMap_getElem? {α β : Type} (f : α → List β) (w : Nat) (hw : 0 < w) (hf : ∀ x, (f x).length = w) :
    ∀ (l : List α) (n : Nat), (l.flatMap f)[n]? = l[n / w]?.bind (fun x => (f x)[n % w]?) := by
  intro l
  induction l with
  | nil => intro n; simp
  | cons a l ih =>
      intro n
      rw [List.flatMap_cons]
      by_cases hn : n < w
      · rw [List.getElem?_append_left (by rw [hf]; exact hn), Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn]
        simp
      · have hn' : w ≤ n := by omega
        rw [List.getElem?_append_right (by rw [hf]; exact hn'), hf, ih, Nat.div_eq_sub_div (a := n) hw hn',
          Nat.mod_eq_sub_mod (a := n) hn']
        simp

/-! ### `decode12` -/

theorem decode12_coeff_getLsbD (bytes : List (BitVec 8)) (i j : Nat) :
    (MlKemFast.concrete.ofBits (MlKemFast.chunk (MlKemFast.bitsOf FO bytes) 12 i)).getLsbD j =
      (decide (j < 12) && bitAt bytes (12 * i + j)) := by
  rw [ofBits_getLsbD]
  by_cases hj : j < 12
  · rw [chunk_getD _ _ _ _ _ hj, bitsOf_getD, ofBool_getLsbD_zero]
  · simp [hj]

theorem bit_eq (input : List (BitVec 8)) (index : Nat) :
    MlKemArithmetic.bit SH BA input index = if bitAt input index then 1#32 else 0#32 := by
  apply BitVec.eq_of_toNat_eq
  have hb : MlKemArithmetic.bitNat input index = if bitAt input index then 1 else 0 := rfl
  rw [MlKemArithmetic.bit_value, hb]
  cases bitAt input index <;> rfl

theorem rot_one : ∀ k : Fin 12, (1#32).rotateRight (32 - k.val) = BitVec.twoPow 32 k.val := by decide +kernel
theorem rot_zero : ∀ k : Fin 12, (0#32).rotateRight (32 - k.val) = 0#32 := by decide +kernel

theorem decodeLoop_getLsbD (input : List (BitVec 8)) (base : Nat) : ∀ (n : Nat), n ≤ 12 → ∀ j : Nat,
    ((List.range n).foldl (fun acc bit =>
        Sha256.concrete.xor acc (Sha256.concrete.rotr (MlKemArithmetic.bit SH BA input (base + bit)) (32 - bit))) (Sha256.concrete.wordConst 0)).getLsbD j =
      (decide (j < n) && bitAt input (base + j))
  | 0, _, j => by simp [Sha256.concrete]
  | n + 1, hn, j => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ih := decodeLoop_getLsbD input base n (by omega) j
      have hx : ∀ x y : BitVec 32, Sha256.concrete.xor x y = x ^^^ y := fun _ _ => rfl
      have hr : ∀ (x : BitVec 32) (k : Nat), Sha256.concrete.rotr x k = x.rotateRight k := fun _ _ => rfl
      rw [hx, BitVec.getLsbD_xor, ih, hr, bit_eq]
      cases hb : bitAt input (base + n)
      · rw [if_neg (by simp), rot_zero ⟨n, by omega⟩, BitVec.getLsbD_zero]
        rcases Nat.lt_trichotomy j n with h | h | h
        · simp [h, show j < n + 1 by omega]
        · subst h; simp [hb]
        · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega]
      · rw [if_pos rfl, rot_one ⟨n, by omega⟩, BitVec.getLsbD_twoPow]
        rcases Nat.lt_trichotomy j n with h | h | h
        · simp [h, show j < n + 1 by omega, show n ≠ j by omega]
        · subst h; simp [hb, show j < 32 by omega]
        · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega, show n ≠ j by omega]

theorem decodeCoeff_getLsbD (width : Nat) (hw : width ≤ 12) (input : List (BitVec 8)) (index j : Nat) :
    (MlKemEncoding.decodeCoeff SH BA width input index).getLsbD j =
      (decide (j < width) && bitAt input (width * index + j)) :=
  decodeLoop_getLsbD input (width * index) width hw j

theorem wide_getLsbD (x : BitVec 12) (j : Nat) : (MlKemFast.wide x).getLsbD j = x.getLsbD j := by
  simp only [MlKemFast.wide, BitVec.getLsbD_setWidth]
  by_cases h : j < 32
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge x j (by omega)]

theorem decodeCoeff_eq (input : List (BitVec 8)) (index : Nat) :
    MlKemEncoding.decodeCoeff SH BA 12 input index =
      MlKemFast.wide (MlKemFast.concrete.ofBits (MlKemFast.chunk (MlKemFast.bitsOf FO input) 12 index)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  rw [decodeCoeff_getLsbD 12 (by decide), wide_getLsbD, decode12_coeff_getLsbD]

/-- `decode12`, zero-extended, is the specification's `ByteDecode_12`. -/
theorem decode12_refines (count : Nat) (bytes : List (BitVec 8)) :
    (MlKemFast.decode12 FO count bytes).map MlKemFast.wide = MlKemEncoding.decode SH BA 12 count bytes := by
  simp only [MlKemFast.decode12, MlKemEncoding.decode, List.map_map]
  apply List.map_congr_left
  intro i _
  exact (decodeCoeff_eq bytes i).symm

theorem decode12_length (count : Nat) (bytes : List (BitVec 8)) :
    (MlKemFast.decode12 FO count bytes).length = count := by
  simp [MlKemFast.decode12]

/-! ### `encode` -/

theorem get_getLsbD_wide (poly : List (BitVec 12)) (k r : Nat) :
    (MlKemNtt.get SH (poly.map MlKemFast.wide) k).getLsbD r = (MlKemFast.get FO poly k).getLsbD r := by
  rw [← MlKemFast.wide_get, wide_getLsbD]

/-- Bit `t` of byte `j` of the specification's encoding. -/
theorem encodeLoop_getLsbD (width : Nat) (poly : List (BitVec 32)) (byteIndex : Nat) : ∀ n, n ≤ 8 → ∀ t,
    ((List.range n).foldl (fun acc bit =>
        ByteAuth.concrete.xor acc (ByteAuth.concrete.and (ByteAuth.concrete.maskBit (Sha256.concrete.unpack (Sha256.concrete.shr (MlKemNtt.get SH poly ((8 * byteIndex + bit) / width))
          ((8 * byteIndex + bit) % width)) 3) 0) (ByteAuth.concrete.const (2 ^ bit)))) (ByteAuth.concrete.const 0)).getLsbD t =
      (decide (t < n) && (MlKemNtt.get SH poly ((8 * byteIndex + t) / width)).getLsbD ((8 * byteIndex + t) % width))
  | 0, _, t => by simp [ByteAuth.concrete]
  | n + 1, hn, t => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ih := encodeLoop_getLsbD width poly byteIndex n (by omega) t
      have hx : ∀ x y : BitVec 8, ByteAuth.concrete.xor x y = x ^^^ y := fun _ _ => rfl
      rw [hx, BitVec.getLsbD_xor, ih]
      have term : (ByteAuth.concrete.and (ByteAuth.concrete.maskBit (Sha256.concrete.unpack (Sha256.concrete.shr (MlKemNtt.get SH poly ((8 * byteIndex + n) / width))
          ((8 * byteIndex + n) % width)) 3) 0) (ByteAuth.concrete.const (2 ^ n))).getLsbD t =
          (decide (t = n) && (MlKemNtt.get SH poly ((8 * byteIndex + n) / width)).getLsbD ((8 * byteIndex + n) % width)) := by
        simp only [ByteAuth.concrete, Sha256.concrete, BitVec.getLsbD_and, BitVec.getLsbD_replicate,
          BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, Nat.testBit_two_pow,
          Nat.mod_one, Nat.add_zero]
        by_cases h : t = n
        · subst h; simp [show t < 8 by omega]
        · simp [h, show n ≠ t by omega]
      rw [term]
      rcases Nat.lt_trichotomy t n with h | h | h
      · simp [h, show t < n + 1 by omega, show t ≠ n by omega]
      · subst h; simp
      · simp [show ¬ t < n by omega, show ¬ t < n + 1 by omega, show t ≠ n by omega]

theorem encodeByte_getLsbD (width : Nat) (poly : List (BitVec 32)) (byteIndex t : Nat) :
    (MlKemEncoding.encodeByte SH BA width poly byteIndex).getLsbD t =
      (decide (t < 8) && (MlKemNtt.get SH poly ((8 * byteIndex + t) / width)).getLsbD ((8 * byteIndex + t) % width)) :=
  encodeLoop_getLsbD width poly byteIndex 8 (Nat.le_refl 8) t

/-- Bit `t` of byte `j` of the kernels' encoding. -/
theorem kernelByte_getLsbD (width : Nat) (hw : 0 < width) (hw' : width ≤ 12) (poly : List (BitVec 12))
    (j t : Nat) (ht : t < 8) (hj : 8 * j + t < width * poly.length) :
    (MlKemFast.concrete.bitsByte (MlKemFast.chunk (poly.flatMap (fun x => (MlKemFast.concrete.bits x).take width)) 8 j)).getLsbD t =
      (MlKemFast.get FO poly ((8 * j + t) / width)).getLsbD ((8 * j + t) % width) := by
  rw [bitsByte_getLsbD, chunk_getD _ _ _ _ _ ht, decide_eq_true ht, Bool.true_and]
  have lens : ∀ x : BitVec 12, ((MlKemFast.concrete.bits x).take width).length = width := by
    intro x
    simp [MlKemFast.concrete]
    omega
  have hk : (8 * j + t) / width < poly.length := by
    rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm poly.length width]
    exact hj
  have hr : (8 * j + t) % width < width := Nat.mod_lt _ hw
  obtain ⟨x, hx⟩ : ∃ x, poly[(8 * j + t) / width]? = some x :=
    ⟨poly[(8 * j + t) / width], List.getElem?_eq_getElem hk⟩
  rw [List.getD_eq_getElem?_getD, flatMap_getElem? _ width hw lens, hx]
  have hbit : ((MlKemFast.concrete.bits x).take width)[(8 * j + t) % width]? = some (x.extractLsb' ((8 * j + t) % width) 1) := by
    rw [List.getElem?_take, if_pos hr]
    simp only [MlKemFast.concrete, List.getElem?_map, List.getElem?_range (show (8 * j + t) % width < 12 by omega),
      Option.map_some]
  simp only [Option.bind_some, hbit, Option.getD_some, MlKemFast.get, hx]
  rw [extract_one, ofBool_getLsbD_zero]

/-- `encode` is the specification's `ByteEncode_width` of the zero-extended polynomial. -/
theorem encode_refines (width count : Nat) (poly : List (BitVec 12)) (hlen : poly.length = count)
    (hw : 0 < width) (hw' : width ≤ 12) (hdiv : width * count % 8 = 0) :
    MlKemFast.encode FO width poly = MlKemEncoding.encode SH BA width count (poly.map MlKemFast.wide) := by
  simp only [MlKemFast.encode, MlKemEncoding.encode, hlen]
  have hr : width * count / 8 = (width * count + 7) / 8 := by omega
  rw [hr]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hj' : 8 * j + t < width * poly.length := by rw [hlen]; omega
  rw [kernelByte_getLsbD width hw hw' poly j t ht hj', encodeByte_getLsbD, decide_eq_true ht, Bool.true_and,
    get_getLsbD_wide]

theorem encode_length (width : Nat) (poly : List (BitVec 12)) :
    (MlKemFast.encode FO width poly).length = width * poly.length / 8 := by
  simp [MlKemFast.encode]

/-! ### The 384-byte round trip between kernels -/

theorem bitAt_encode (width : Nat) (hw : 0 < width) (hw' : width ≤ 12) (poly : List (BitVec 12)) (n : Nat)
    (hn : n < 8 * (width * poly.length / 8)) :
    bitAt (MlKemFast.encode FO width poly) n = (MlKemFast.get FO poly (n / width)).getLsbD (n % width) := by
  have hq : n / 8 < width * poly.length / 8 := by omega
  have e : n = 8 * (n / 8) + n % 8 := by omega
  rw [e, bitAt_eq _ _ _ (Nat.mod_lt _ (by decide))]
  simp only [MlKemFast.encode, List.getElem?_map, List.getElem?_range hq, Option.map_some, Option.getD_some]
  rw [kernelByte_getLsbD width hw hw' poly _ _ (Nat.mod_lt _ (by decide)) (by omega)]

/-- Decoding the 12-bit encoding gives the polynomial back (any 12-bit coefficients). -/
theorem decode12_encode (count : Nat) (p : List (BitVec 12)) (hlen : p.length = count) (hdiv : 12 * count % 8 = 0) :
    MlKemFast.decode12 FO count (MlKemFast.encode FO 12 p) = p := by
  apply List.ext_getElem?
  intro i
  simp only [MlKemFast.decode12, List.getElem?_map]
  by_cases hi : i < count
  · rw [List.getElem?_range hi, Option.map_some]
    have hp : p[i]? = some p[i] := List.getElem?_eq_getElem (by omega)
    rw [hp]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [decode12_coeff_getLsbD, decide_eq_true hj, Bool.true_and,
      bitAt_encode 12 (by decide) (by decide) p _ (by rw [hlen]; omega)]
    have h1 : (12 * i + j) / 12 = i := by omega
    have h2 : (12 * i + j) % 12 = j := by omega
    rw [h1, h2]
    simp only [MlKemFast.get, hp, Option.getD_some]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rfl

theorem flatMap_range_length {α : Type} (f : Nat → List α) (L : Nat) (hf : ∀ i, (f i).length = L) :
    ∀ n, ((List.range n).flatMap f).length = L * n
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_range_length f L hf n]
      simp [hf, Nat.mul_succ]

theorem flatMap_range_chunk {α : Type} (f : Nat → List α) (L : Nat) (hf : ∀ i, (f i).length = L) :
    ∀ n j, j < n → (((List.range n).flatMap f).drop (L * j)).take L = f j
  | 0, j, h => absurd h (Nat.not_lt_zero j)
  | n + 1, j, h => by
      rw [List.range_succ, List.flatMap_append]
      have hlen := flatMap_range_length f L hf n
      by_cases hj : j < n
      · have le1 : L * j ≤ ((List.range n).flatMap f).length := by
          rw [hlen]; exact Nat.mul_le_mul_left L (by omega)
        rw [List.drop_append_of_le_length le1]
        have le2 : L ≤ (((List.range n).flatMap f).drop (L * j)).length := by
          rw [List.length_drop, hlen]
          have := Nat.mul_le_mul_left L (show j + 1 ≤ n by omega)
          rw [Nat.mul_succ] at this
          omega
        rw [List.take_append_of_le_length le2]
        exact flatMap_range_chunk f L hf n j hj
      · have hj' : j = n := by omega
        subst hj'
        rw [List.drop_left' hlen]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact List.take_of_length_le (Nat.le_of_eq (hf j))

/-- The kernels' `polyAt` on a concatenation of four 12-bit encodings is the j-th polynomial. -/
theorem polyAt_flatMap_encode (P : Nat → List (BitVec 12)) (hP : ∀ i, (P i).length = 256) (j : Nat) (hj : j < 4) :
    MlKemFast.polyAt FO ((List.range 4).flatMap (fun i => MlKemFast.encode FO 12 (P i))) j = P j := by
  have lens : ∀ i, (MlKemFast.encode FO 12 (P i)).length = 384 := by
    intro i; rw [encode_length, hP]
  simp only [MlKemFast.polyAt]
  rw [flatMap_range_chunk _ 384 lens 4 j hj]
  exact decode12_encode 256 (P j) (hP j) (by decide)

/-! ### `cbd`, `noise` -/

theorem sumNat_two (input : List (BitVec 8)) (s : Nat) :
    MlKemArithmetic.sumNat input s 2 = (bitAt input s).toNat + (bitAt input (s + 1)).toNat := by
  have hb : ∀ k, MlKemArithmetic.bitNat input k = (bitAt input k).toNat := by
    intro k
    show (if bitAt input k then 1 else 0) = (bitAt input k).toNat
    cases bitAt input k <;> rfl
  simp only [MlKemArithmetic.sumNat, hb, Nat.add_zero, Nat.zero_add]

theorem cbd_coeff_eq (bytes : List (BitVec 8)) (i : Nat) :
    (MlKemFast.concrete.subMod
      (MlKemFast.concrete.ofBits [MlKemFast.concrete.xor ((MlKemFast.bitsOf FO bytes).getD (4 * i + 0) MlKemFast.concrete.zero) ((MlKemFast.bitsOf FO bytes).getD (4 * i + 1) MlKemFast.concrete.zero),
        MlKemFast.concrete.and ((MlKemFast.bitsOf FO bytes).getD (4 * i + 0) MlKemFast.concrete.zero) ((MlKemFast.bitsOf FO bytes).getD (4 * i + 1) MlKemFast.concrete.zero)])
      (MlKemFast.concrete.ofBits [MlKemFast.concrete.xor ((MlKemFast.bitsOf FO bytes).getD (4 * i + 2) MlKemFast.concrete.zero) ((MlKemFast.bitsOf FO bytes).getD (4 * i + 3) MlKemFast.concrete.zero),
        MlKemFast.concrete.and ((MlKemFast.bitsOf FO bytes).getD (4 * i + 2) MlKemFast.concrete.zero) ((MlKemFast.bitsOf FO bytes).getD (4 * i + 3) MlKemFast.concrete.zero)])).toNat =
      (3329 + ((bitAt bytes (4 * i)).toNat + (bitAt bytes (4 * i + 1)).toNat) -
        ((bitAt bytes (4 * i + 2)).toNat + (bitAt bytes (4 * i + 3)).toNat)) % 3329 := by
  have z : MlKemFast.concrete.zero = 0#1 := rfl
  rw [z, bitsOf_getD, bitsOf_getD, bitsOf_getD, bitsOf_getD]
  have := MlKemFast.cbd_coefficient (BitVec.ofBool (bitAt bytes (4 * i + 0))) (BitVec.ofBool (bitAt bytes (4 * i + 1)))
    (BitVec.ofBool (bitAt bytes (4 * i + 2))) (BitVec.ofBool (bitAt bytes (4 * i + 3)))
  simp only [BitVec.toNat_ofBool, Nat.add_zero] at this
  exact this

theorem cbd_refines (bytes : List (BitVec 8)) :
    (MlKemFast.cbd FO bytes).map MlKemFast.wide = MlKemArithmetic.cbd AR SH BA 2 256 bytes := by
  simp only [MlKemFast.cbd, MlKemArithmetic.cbd, List.map_map]
  apply List.map_congr_left
  intro i _
  apply BitVec.eq_of_toNat_eq
  simp only [Function.comp_apply]
  rw [MlKemFast.wide_toNat, cbd_coeff_eq]
  have b1 := MlKemArithmetic.sumNat_bound bytes (2 * 2 * i) 2
  have b2 := MlKemArithmetic.sumNat_bound bytes (2 * 2 * i + 2) 2
  rw [MlKemArithmetic.subMod_value _ _ (by rw [MlKemArithmetic.bitSum_value _ _ _ (by decide)]; omega)
      (by rw [MlKemArithmetic.bitSum_value _ _ _ (by decide)]; omega),
    MlKemArithmetic.bitSum_value _ _ _ (by decide), MlKemArithmetic.bitSum_value _ _ _ (by decide),
    sumNat_two, sumNat_two]

theorem cbd_canon (bytes : List (BitVec 8)) : MlKemFast.Canon (MlKemFast.cbd FO bytes) := by
  intro x hx
  simp only [MlKemFast.cbd, List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  rw [cbd_coeff_eq]
  exact Nat.mod_lt _ (by decide)

theorem cbd_length (bytes : List (BitVec 8)) : (MlKemFast.cbd FO bytes).length = 256 := by
  simp [MlKemFast.cbd]

theorem pack16 (x : BitVec 32) (hx : x.toNat < 65536) :
    Sha256.concrete.pack (Sha256.concrete.byteConst 0) (Sha256.concrete.byteConst 0) (Sha256.concrete.unpack x 2) (Sha256.concrete.unpack x 3) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Sha256.concrete, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat]
  by_cases h8 : j < 8
  · simp [h8, show j < 16 by omega]
  · by_cases h16 : j < 16
    · simp [h8, h16, show j - 8 < 8 by omega, show 8 + (j - 8) = j by omega]
    · have hz : x.getLsbD j = false := by
        simp only [BitVec.getLsbD]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (by
          have : 2 ^ 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          simpa using this))
      simp [h16, hz]

/-- The specification's 16-bit serialisation and its `decodePoly` round-trip on 256 coefficients below 2^16. -/
theorem decodePoly_encode (p : List (BitVec 32)) (hlen : p.length = 256) (hp : ∀ x ∈ p, x.toNat < 65536) :
    MlKemNtt.decodePoly SH BA (p.flatMap (MlKemArithmetic.encode SH)) = p := by
  have lens : ∀ x : BitVec 32, (MlKemArithmetic.encode SH x).length = 2 := fun _ => rfl
  apply List.ext_getElem?
  intro i
  simp only [MlKemNtt.decodePoly, List.getElem?_map]
  by_cases hi : i < 256
  · rw [List.getElem?_range hi, Option.map_some]
    have hpi : p[i]? = some p[i] := List.getElem?_eq_getElem (by omega)
    have g0 : OpenResult.get BA (p.flatMap (MlKemArithmetic.encode SH)) (2 * i) = Sha256.concrete.unpack p[i] 3 := by
      simp only [OpenResult.get]
      rw [flatMap_getElem? _ 2 (by decide) lens, show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega, hpi]
      rfl
    have g1 : OpenResult.get BA (p.flatMap (MlKemArithmetic.encode SH)) (2 * i + 1) = Sha256.concrete.unpack p[i] 2 := by
      simp only [OpenResult.get]
      rw [flatMap_getElem? _ 2 (by decide) lens, show (2 * i + 1) / 2 = i by omega,
        show (2 * i + 1) % 2 = 1 by omega, hpi]
      rfl
    rw [g0, g1, pack16 _ (hp _ (List.getElem_mem _)), hpi]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rfl

theorem specCbd_bound (bytes : List (BitVec 8)) : ∀ x ∈ MlKemArithmetic.cbd AR SH BA 2 256 bytes, x.toNat < 3329 := by
  intro x hx
  simp only [MlKemArithmetic.cbd, List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact MlKemArithmetic.reduce_bound _

/-- The kernels' noise polynomial, zero-extended, is the specification's `MlKemPke.noise … 2`. -/
theorem noise_refines (coins : List (BitVec 8)) (nonce : Nat) :
    (MlKemFast.noise FO BA Keccak.concrete coins nonce).map MlKemFast.wide =
      MlKemPke.noise AR SH BA Keccak.concrete 2 coins nonce := by
  simp only [MlKemFast.noise, MlKemPke.noise, MlKemArithmetic.noise, MlKemArithmetic.cbdBytes]
  rw [show (64 * 2 : Nat) = 128 from rfl, cbd_refines]
  rw [decodePoly_encode _ (by simp [MlKemArithmetic.cbd])
    (fun x hx => Nat.lt_trans (specCbd_bound _ x hx) (by decide))]

theorem noise_canon (coins : List (BitVec 8)) (nonce : Nat) :
    MlKemFast.Canon (MlKemFast.noise FO BA Keccak.concrete coins nonce) := cbd_canon _

theorem noise_length (coins : List (BitVec 8)) (nonce : Nat) :
    (MlKemFast.noise FO BA Keccak.concrete coins nonce).length = 256 := cbd_length _

/-! ### `messagePoly` -/

theorem message_coeff : ∀ b : Bool,
    MlKemFast.concrete.ofBits ((List.range 12).map (fun i => if (1665).testBit i then BitVec.ofBool b else MlKemFast.concrete.zero)) =
      if b then 1665#12 else 0#12 := by decide +kernel

theorem decodeCoeff_one (input : List (BitVec 8)) (m : Nat) :
    MlKemEncoding.decodeCoeff SH BA 1 input m = if bitAt input m then 1#32 else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  rw [decodeCoeff_getLsbD 1 (by decide)]
  by_cases hj : j = 0
  · subst hj
    simp only [Nat.one_mul, Nat.add_zero]
    cases bitAt input m <;> decide
  · have h1 : ¬ j < 1 := by omega
    cases h : bitAt input m <;> simp [h1, hj]

/-- `Decompress_1 ∘ ByteDecode_1` of a 32-byte message. -/
theorem messagePoly_refines (message : List (BitVec 8)) (hm : message.length = 32) :
    (MlKemFast.messagePoly FO message).map MlKemFast.wide =
      (MlKemEncoding.decode SH BA 1 256 message).map (MlKemEncoding.decompress AR SH 1) := by
  simp only [MlKemFast.messagePoly, MlKemEncoding.decode, bitsOf_eq, hm, List.map_map]
  apply List.map_congr_left
  intro m _
  simp only [Function.comp_apply, decodeCoeff_one]
  rw [message_coeff]
  cases bitAt message m <;> decide

theorem messagePoly_canon (message : List (BitVec 8)) : MlKemFast.Canon (MlKemFast.messagePoly FO message) := by
  intro x hx
  simp only [MlKemFast.messagePoly, bitsOf_eq, List.mem_map] at hx
  obtain ⟨b, ⟨m, _, rfl⟩, rfl⟩ := hx
  rw [message_coeff]
  cases bitAt message m <;> decide

theorem messagePoly_length (message : List (BitVec 8)) :
    (MlKemFast.messagePoly FO message).length = 8 * message.length := by
  simp [MlKemFast.messagePoly, bitsOf_length]

#print axioms decode12_refines
#print axioms encode_refines
#print axioms cbd_refines
#print axioms noise_refines
#print axioms messagePoly_refines
#print axioms decode12_encode
#print axioms polyAt_flatMap_encode

end TlsMpc.KernelSpecs.KemEncoding
