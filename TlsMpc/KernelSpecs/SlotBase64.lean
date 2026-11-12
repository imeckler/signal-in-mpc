import TlsMpc.KernelSpecs.RequestCtr

/-!
# The base64 slot encoder against RFC 4648 (section 4, with padding)

New file; it changes no definition and no emitter imports it.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `base64_eq`: `RelayEncoding.base64` on concrete bytes is `refBase64`, the RFC 4648 encoding written
  independently here (each 24-bit group as four 6-bit indices into the standard alphabet
  `A–Z a–z 0–9 + /`, a final group of one or two bytes padded with `=`), for every input length.
* `base64_decode`: `refBase64Decode (refBase64 raw) = raw` for every `raw` (so the encoding is
  injective), and `base64_slot_decode` for the circuit's encoder.
-/
namespace TlsMpc.KernelSpecs.SlotBase64
open TlsMpc TlsMpc.Signal

abbrev Byte := BitVec 8

/-! ### The reference (RFC 4648) -/

/-- The character of a 6-bit value: `A–Z` 0–25, `a–z` 26–51, `0–9` 52–61, `+` 62, `/` 63. -/
def b64char (n : Nat) : Byte :=
  BitVec.ofNat 8 (if n < 26 then 65 + n else if n < 52 then 71 + n else if n < 62 then n - 4 else if n = 62 then 43 else 47)

/-- RFC 4648 base64 with `=` padding. -/
def refBase64 : List Byte → List Byte
  | x :: y :: z :: rest =>
      let n := x.toNat * 65536 + y.toNat * 256 + z.toNat
      [b64char (n / 262144 % 64), b64char (n / 4096 % 64), b64char (n / 64 % 64), b64char (n % 64)] ++ refBase64 rest
  | [x, y] =>
      let n := x.toNat * 65536 + y.toNat * 256
      [b64char (n / 262144 % 64), b64char (n / 4096 % 64), b64char (n / 64 % 64), 61]
  | [x] =>
      let n := x.toNat * 65536
      [b64char (n / 262144 % 64), b64char (n / 4096 % 64), 61, 61]
  | [] => []

/-- The 6-bit value of a base64 character (`=` is not one; it is handled by the decoder). -/
def b64value (c : Byte) : Nat :=
  let v := c.toNat
  if 65 ≤ v ∧ v ≤ 90 then v - 65 else if 97 ≤ v ∧ v ≤ 122 then v - 71 else if 48 ≤ v ∧ v ≤ 57 then v + 4
  else if v = 43 then 62 else 63

/-- RFC 4648 decoding of padded base64, four characters at a time. -/
def refBase64Decode : List Byte → List Byte
  | c0 :: c1 :: c2 :: c3 :: rest =>
      let n := b64value c0 * 262144 + b64value c1 * 4096 + (if c2 = 61 then 0 else b64value c2 * 64) +
        (if c3 = 61 then 0 else b64value c3)
      [BitVec.ofNat 8 (n / 65536)] ++ (if c2 = 61 then [] else [BitVec.ofNat 8 (n / 256 % 256)]) ++
        (if c3 = 61 then [] else [BitVec.ofNat 8 (n % 256)]) ++ refBase64Decode rest
  | _ => []

/-! ### The circuit's pieces on concrete bytes -/

/-- `RelayEncoding.table` with the alphabet given as character codes and the equality masks as
values. -/
def tableOf (codes : List Nat) (x : Byte) : Byte :=
  codes.zipIdx.foldl (fun acc p => acc ^^^ ((if x = BitVec.ofNat 8 p.2 then 255 else 0) &&& BitVec.ofNat 8 p.1)) 0

theorem table_eq (s : String) (x : Byte) :
    RelayEncoding.table ByteAuth.concrete s x = tableOf (s.toUTF8.data.toList.map UInt8.toNat) x := by
  simp only [RelayEncoding.table, tableOf, List.zipIdx_map, List.foldl_map, ByteAuth.eqMask_value]
  rfl

def alphabetCodes : List Nat :=
  [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90,
   97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
   120, 121, 122, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 43, 47]

theorem alphabet_codes :
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toUTF8.data.toList.map UInt8.toNat =
      alphabetCodes := by decide

set_option maxRecDepth 100000 in
theorem tableOf_char (v : Nat) (h : v < 64) : tableOf alphabetCodes (BitVec.ofNat 8 v) = b64char v := by
  have all : ∀ v : Fin 64, tableOf alphabetCodes (BitVec.ofNat 8 v) = b64char v := by decide +kernel
  exact all ⟨v, h⟩

theorem encode_eq (v : Nat) (h : v < 64) :
    RelayEncoding.table ByteAuth.concrete "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
      (BitVec.ofNat 8 v) = b64char v := by
  rw [table_eq, alphabet_codes, tableOf_char v h]

local notation "slice" => RelayEncoding.slice ByteAuth.concrete

theorem slice_x0 (x : Byte) : slice x 2 6 0 = BitVec.ofNat 8 (x.toNat / 4) := by
  have all : ∀ x : Byte, slice x 2 6 0 = BitVec.ofNat 8 (x.toNat / 4) := by decide
  exact all x
theorem slice_x1 (x : Byte) : slice x 0 2 4 = BitVec.ofNat 8 (x.toNat % 4 * 16) := by
  have all : ∀ x : Byte, slice x 0 2 4 = BitVec.ofNat 8 (x.toNat % 4 * 16) := by decide
  exact all x
theorem slice_y1 (y : Byte) : slice y 4 4 0 = BitVec.ofNat 8 (y.toNat / 16) := by
  have all : ∀ y : Byte, slice y 4 4 0 = BitVec.ofNat 8 (y.toNat / 16) := by decide
  exact all y
theorem slice_y2 (y : Byte) : slice y 0 4 2 = BitVec.ofNat 8 (y.toNat % 16 * 4) := by
  have all : ∀ y : Byte, slice y 0 4 2 = BitVec.ofNat 8 (y.toNat % 16 * 4) := by decide
  exact all y
theorem slice_z2 (z : Byte) : slice z 6 2 0 = BitVec.ofNat 8 (z.toNat / 64) := by
  have all : ∀ z : Byte, slice z 6 2 0 = BitVec.ofNat 8 (z.toNat / 64) := by decide
  exact all z
theorem slice_z3 (z : Byte) : slice z 0 6 0 = BitVec.ofNat 8 (z.toNat % 64) := by
  have all : ∀ z : Byte, slice z 0 6 0 = BitVec.ofNat 8 (z.toNat % 64) := by decide
  exact all z

theorem xor16 (a b : Nat) (ha : a < 4) (hb : b < 16) :
    BitVec.ofNat 8 (a * 16) ^^^ BitVec.ofNat 8 b = BitVec.ofNat 8 (a * 16 + b) := by
  have all : ∀ a : Fin 4, ∀ b : Fin 16,
      BitVec.ofNat 8 (a.val * 16) ^^^ BitVec.ofNat 8 b.val = BitVec.ofNat 8 (a.val * 16 + b.val) := by decide
  exact all ⟨a, ha⟩ ⟨b, hb⟩

theorem xor4 (a b : Nat) (ha : a < 16) (hb : b < 4) :
    BitVec.ofNat 8 (a * 4) ^^^ BitVec.ofNat 8 b = BitVec.ofNat 8 (a * 4 + b) := by
  have all : ∀ a : Fin 16, ∀ b : Fin 4,
      BitVec.ofNat 8 (a.val * 4) ^^^ BitVec.ofNat 8 b.val = BitVec.ofNat 8 (a.val * 4 + b.val) := by decide
  exact all ⟨a, ha⟩ ⟨b, hb⟩

local notation "encode" =>
  RelayEncoding.table ByteAuth.concrete "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

theorem char0 (x : Byte) : encode (slice x 2 6 0) = b64char (x.toNat / 4) := by
  have := x.isLt
  rw [slice_x0, encode_eq _ (by omega)]

theorem char1 (x y : Byte) :
    encode (ByteAuth.concrete.xor (slice x 0 2 4) (slice y 4 4 0)) = b64char (x.toNat % 4 * 16 + y.toNat / 16) := by
  have := y.isLt
  show encode (slice x 0 2 4 ^^^ slice y 4 4 0) = _
  rw [slice_x1, slice_y1, xor16 _ _ (by omega) (by omega), encode_eq _ (by omega)]

theorem char2 (y z : Byte) :
    encode (ByteAuth.concrete.xor (slice y 0 4 2) (slice z 6 2 0)) = b64char (y.toNat % 16 * 4 + z.toNat / 64) := by
  have := z.isLt
  show encode (slice y 0 4 2 ^^^ slice z 6 2 0) = _
  rw [slice_y2, slice_z2, xor4 _ _ (by omega) (by omega), encode_eq _ (by omega)]

theorem char3 (z : Byte) : encode (slice z 0 6 0) = b64char (z.toNat % 64) := by
  rw [slice_z3, encode_eq _ (Nat.mod_lt _ (by decide))]

theorem get_cons3 {B : Type} (a : ByteAuth.Ops B) (x y z : B) (rest : List B) (j : Nat) :
    OpenResult.get a (x :: y :: z :: rest) (j + 3) = OpenResult.get a rest j := by
  simp [OpenResult.get]

/-- The circuit's base64: the first three bytes give four characters, then the rest. -/
theorem base64_cons3 {B : Type} (a : ByteAuth.Ops B) (x y z : B) (rest : List B) :
    RelayEncoding.base64 a (x :: y :: z :: rest) =
      [RelayEncoding.table a "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
          (RelayEncoding.slice a x 2 6 0),
        RelayEncoding.table a "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
          (a.xor (RelayEncoding.slice a x 0 2 4) (RelayEncoding.slice a y 4 4 0)),
        RelayEncoding.table a "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
          (a.xor (RelayEncoding.slice a y 0 4 2) (RelayEncoding.slice a z 6 2 0)),
        RelayEncoding.table a "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
          (RelayEncoding.slice a z 0 6 0)] ++ RelayEncoding.base64 a rest := by
  unfold RelayEncoding.base64
  simp only [List.length_cons]
  rw [show (rest.length + 1 + 1 + 1 + 2) / 3 = (rest.length + 2) / 3 + 1 by omega, List.range_succ_eq_map,
    List.flatMap_cons, List.flatMap_map]
  congr 1
  congr 1
  funext i
  rw [show 3 * (i + 1) = 3 * i + 3 by omega, show 3 * i + 3 + 1 = (3 * i + 1) + 3 by omega,
    show 3 * i + 3 + 2 = (3 * i + 2) + 3 by omega, get_cons3, get_cons3, get_cons3]
  simp only [show rest.length + 1 + 1 + 1 = rest.length + 3 by omega, Nat.add_lt_add_iff_right]

theorem const61 : ByteAuth.concrete.const 61 = (61 : Byte) := rfl
theorem const0 : ByteAuth.concrete.const 0 = (0 : Byte) := rfl

/-- **The circuit's base64 encoder is RFC 4648 base64** (with padding), for every input. -/
theorem base64_eq : ∀ raw : List Byte, RelayEncoding.base64 ByteAuth.concrete raw = refBase64 raw
  | [] => by simp [RelayEncoding.base64, refBase64]
  | [x] => by
      have := x.isLt
      simp only [RelayEncoding.base64, refBase64, List.length_cons, List.length_nil]
      simp [OpenResult.get, const0, char0, char1, const61]
      constructor <;> congr 1 <;> omega
  | [x, y] => by
      have := x.isLt; have := y.isLt
      simp only [RelayEncoding.base64, refBase64, List.length_cons, List.length_nil]
      simp [OpenResult.get, const0, char0, char1, char2, const61]
      refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> omega
  | x :: y :: z :: rest => by
      have := x.isLt; have := y.isLt; have := z.isLt
      rw [base64_cons3, base64_eq rest, char0, char1, char2, char3]
      simp only [refBase64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega

/-! ### Decoding back -/

set_option maxRecDepth 100000 in
theorem b64value_char (v : Nat) (h : v < 64) : b64value (b64char v) = v := by
  have all : ∀ v : Fin 64, b64value (b64char v) = v := by decide +kernel
  exact all ⟨v, h⟩

set_option maxRecDepth 100000 in
theorem b64char_ne (v : Nat) (h : v < 64) : b64char v ≠ 61 := by
  have all : ∀ v : Fin 64, b64char v ≠ 61 := by decide +kernel
  exact all ⟨v, h⟩

theorem ofNat_eq (b : Byte) (m : Nat) (h : m = b.toNat) : BitVec.ofNat 8 m = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, h]
  exact Nat.mod_eq_of_lt b.isLt

/-- **Round trip:** decoding RFC 4648 base64 gives the bytes back, for every input. -/
theorem base64_decode : ∀ raw : List Byte, refBase64Decode (refBase64 raw) = raw
  | [] => rfl
  | [x] => by
      have := x.isLt
      have c0 : x.toNat * 65536 / 262144 % 64 < 64 := Nat.mod_lt _ (by decide)
      have c1 : x.toNat * 65536 / 4096 % 64 < 64 := Nat.mod_lt _ (by decide)
      simp only [refBase64, refBase64Decode, b64value_char _ c0, b64value_char _ c1, ↓reduceIte,
        List.append_nil, List.cons.injEq, and_true, List.cons_append, List.nil_append]
      apply ofNat_eq
      omega
  | [x, y] => by
      have := x.isLt; have := y.isLt
      have c0 : (x.toNat * 65536 + y.toNat * 256) / 262144 % 64 < 64 := Nat.mod_lt _ (by decide)
      have c1 : (x.toNat * 65536 + y.toNat * 256) / 4096 % 64 < 64 := Nat.mod_lt _ (by decide)
      have c2 : (x.toNat * 65536 + y.toNat * 256) / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
      simp only [refBase64, refBase64Decode, b64value_char _ c0, b64value_char _ c1, b64value_char _ c2,
        if_neg (b64char_ne _ c2), ↓reduceIte, List.append_nil, List.cons_append, List.nil_append, List.cons.injEq,
        and_true]
      refine ⟨?_, ?_⟩ <;> (apply ofNat_eq; omega)
  | x :: y :: z :: rest => by
      have := x.isLt; have := y.isLt; have := z.isLt
      have c0 : (x.toNat * 65536 + y.toNat * 256 + z.toNat) / 262144 % 64 < 64 := Nat.mod_lt _ (by decide)
      have c1 : (x.toNat * 65536 + y.toNat * 256 + z.toNat) / 4096 % 64 < 64 := Nat.mod_lt _ (by decide)
      have c2 : (x.toNat * 65536 + y.toNat * 256 + z.toNat) / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
      have c3 : (x.toNat * 65536 + y.toNat * 256 + z.toNat) % 64 < 64 := Nat.mod_lt _ (by decide)
      simp only [refBase64, List.cons_append, List.nil_append, refBase64Decode, b64value_char _ c0,
        b64value_char _ c1, b64value_char _ c2, b64value_char _ c3, if_neg (b64char_ne _ c2),
        if_neg (b64char_ne _ c3), base64_decode rest, List.cons.injEq]
      refine ⟨?_, ?_, ?_, trivial⟩ <;> (apply ofNat_eq; omega)

/-- The circuit's base64 slot decodes back to the bytes it encodes. -/
theorem base64_slot_decode (raw : List Byte) :
    refBase64Decode (RelayEncoding.base64 ByteAuth.concrete raw) = raw := by
  rw [base64_eq, base64_decode]

#print axioms base64_eq
#print axioms base64_decode
#print axioms base64_slot_decode

end TlsMpc.KernelSpecs.SlotBase64
