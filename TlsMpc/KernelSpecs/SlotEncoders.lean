import TlsMpc.KernelSpecs.RequestCtr

/-!
# The request-slot encoders against independent references (RFC 4122 text form, RFC 4648 base64)

New file; it changes no definition and no emitter imports it. The base64 encoder is in
`SlotBase64.lean`, the padded decimal in `SlotDecimal.lean`.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`; the two nibble tables by
`decide +kernel`, about 50 s and 6 GB):

* `uuid_eq`: `RelayEncoding.uuid` on 16 concrete bytes is `refUuid`, the RFC 4122 string form
  written independently here (8-4-4-4-12 lower-case hexadecimal digits, high nibble first).
* `uuid_parse`: `refUuidParse (refUuid raw) = raw` (drop the hyphens, read hex pairs), so the form
  is injective; `uuid_slot_parse` for the circuit's encoder.
-/
namespace TlsMpc.KernelSpecs.SlotEncoders
open TlsMpc TlsMpc.Signal

abbrev Byte := BitVec 8

/-! ### UUID text form (RFC 4122, section 3: 8-4-4-4-12 hexadecimal digits, lower case) -/

/-- The lower-case hexadecimal digit of `n < 16`: `0`–`9` are 48–57, `a`–`f` are 97–102. -/
def hexDigit (n : Nat) : Byte := BitVec.ofNat 8 (if n < 10 then 48 + n else 87 + n)

def hexByte (b : Byte) : List Byte := [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- RFC 4122 string form of 16 bytes: the bytes 0–3, 4–5, 6–7, 8–9, 10–15 in hexadecimal (two
digits per byte, high nibble first), separated by `-` (45). -/
def refUuid (raw : List Byte) : List Byte :=
  let group := fun (i j : Nat) => ((raw.drop i).take (j - i)).flatMap hexByte
  group 0 4 ++ [45] ++ group 4 6 ++ [45] ++ group 6 8 ++ [45] ++ group 8 10 ++ [45] ++ group 10 16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem uuid_high (x : Byte) :
    RelayEncoding.table ByteAuth.concrete "0123456789abcdef" (RelayEncoding.slice ByteAuth.concrete x 4 4 0) =
      hexDigit (x.toNat / 16) := by
  have all : ∀ x : Byte, RelayEncoding.table ByteAuth.concrete "0123456789abcdef"
      (RelayEncoding.slice ByteAuth.concrete x 4 4 0) = hexDigit (x.toNat / 16) := by decide +kernel
  exact all x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem uuid_low (x : Byte) :
    RelayEncoding.table ByteAuth.concrete "0123456789abcdef" (RelayEncoding.slice ByteAuth.concrete x 0 4 0) =
      hexDigit (x.toNat % 16) := by
  have all : ∀ x : Byte, RelayEncoding.table ByteAuth.concrete "0123456789abcdef"
      (RelayEncoding.slice ByteAuth.concrete x 0 4 0) = hexDigit (x.toNat % 16) := by decide +kernel
  exact all x

/-- **The circuit's UUID encoder is the RFC 4122 string form** (on 16 bytes). -/
theorem uuid_eq (raw : List Byte) (h : raw.length = 16) : RelayEncoding.uuid ByteAuth.concrete raw = refUuid raw := by
  match raw, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], _ =>
      simp [RelayEncoding.uuid, refUuid, List.range_succ, List.flatMap_append, OpenResult.get, uuid_high, uuid_low,
        hexByte]
      rfl

/-! Parsing the string form back. -/

def hexValue (c : Byte) : Nat := if c.toNat < 58 then c.toNat - 48 else c.toNat - 87

/-- Two hexadecimal digits at a time, high nibble first. -/
def unhex : List Byte → List Byte
  | c1 :: c2 :: rest => BitVec.ofNat 8 (16 * hexValue c1 + hexValue c2) :: unhex rest
  | _ => []

/-- RFC 4122 string form to bytes: drop the hyphens, read the hexadecimal digits in pairs. -/
def refUuidParse (text : List Byte) : List Byte := unhex (text.filter (· != 45))

theorem hexValue_digit (n : Nat) (h : n < 16) : hexValue (hexDigit n) = n := by
  have all : ∀ n : Fin 16, hexValue (hexDigit n) = n := by decide
  exact all ⟨n, h⟩

theorem hexDigit_ne (n : Nat) (h : n < 16) : (hexDigit n != 45) = true := by
  have all : ∀ n : Fin 16, (hexDigit n != 45) = true := by decide
  exact all ⟨n, h⟩

theorem unhex_hex : ∀ raw : List Byte, unhex (raw.flatMap hexByte) = raw
  | [] => rfl
  | b :: rest => by
      have hb := b.isLt
      have hd : b.toNat / 16 < 16 := by omega
      have hm : b.toNat % 16 < 16 := by omega
      simp only [List.flatMap_cons, hexByte, List.cons_append, List.nil_append, unhex, unhex_hex rest,
        hexValue_digit _ hd, hexValue_digit _ hm, List.cons.injEq, and_true]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega

theorem filter_hex (raw : List Byte) : (raw.flatMap hexByte).filter (· != 45) = raw.flatMap hexByte := by
  induction raw with
  | nil => rfl
  | cons b rest ih =>
      have hb := b.isLt
      have hd : b.toNat / 16 < 16 := by omega
      have hm : b.toNat % 16 < 16 := by omega
      simp only [List.flatMap_cons, List.filter_append, ih, hexByte, List.filter_cons, hexDigit_ne _ hd,
        hexDigit_ne _ hm, if_true, List.filter_nil]

/-- **Round trip:** parsing the RFC 4122 string form of 16 bytes gives the bytes back (so the form
is injective: different UUIDs give different slot texts). -/
theorem uuid_parse (raw : List Byte) (h : raw.length = 16) : refUuidParse (refUuid raw) = raw := by
  match raw, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], _ =>
      have whole := unhex_hex [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]
      have filt := filter_hex [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]
      rw [← filt] at whole
      have dash : ((45 : Byte) != 45) = false := by decide
      simp only [refUuidParse, refUuid, List.filter_append, List.filter_cons, dash, List.filter_nil] at whole ⊢
      simpa [List.flatMap_cons, List.filter_append] using whole

/-- The circuit's UUID slot parses back to the contact's 16 UUID bytes. -/
theorem uuid_slot_parse (raw : List Byte) (h : raw.length = 16) :
    refUuidParse (RelayEncoding.uuid ByteAuth.concrete raw) = raw := by
  rw [uuid_eq raw h, uuid_parse raw h]

#print axioms uuid_eq
#print axioms uuid_parse
#print axioms uuid_slot_parse

end TlsMpc.KernelSpecs.SlotEncoders
