import TlsMpc.KernelSpecs.SlotBase64

/-!
# The WebSocket upgrade's nonce and `Sec-WebSocket-Accept` value (RFC 6455 section 4.2.2)

Advance work for REORGANIZATION_PLAN.md stage S9 (`Upgrade.public`, op 45). New file: it changes
no definition, and no emitter imports it.

What the worker computes today (`handshake_backend/EmpHybridWork/service_kernels.h`,
`upgrade_public`, and the same lines in the authenticated `upgrade`), all in the clear on public
values:

```
key      = EVP_EncodeBlock(nonce, 16)                        -- 24 characters
material = key ++ "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"     -- 60 bytes
accept   = EVP_EncodeBlock(SHA1(material), 20)                -- 28 characters
reply    = nonce ++ accept                                    -- 44 bytes
```

with the request refused unless the nonce is 16 bytes (and, session state not modelled here,
unless no upgrade was started and the session is not closed). `upgradePublic` is that function;
`acceptFast` is the computation it uses (SHA-1 on the fixed-length material as two precomputed
blocks, no generic padding).

Written here, independently of any circuit:

* `Sha1.digest` / `sha1`: SHA-1 as FIPS 180-4 specifies it (section 5.1.1 padding, 5.2.1 parsing,
  6.1.2 computation, 4.1.1 functions, 4.2.1 constants, 5.3.1 initial value), for byte messages
  (a message of `l` bytes is the bit string of `8 l` bits, so padding appends the byte `0x80`, then
  zero bytes up to 56 mod 64, then the 64-bit big-endian bit length).
* base64: `SlotBase64.refBase64`, the RFC 4648 section 4 reference (with `=` padding), imported.
  OpenSSL's `EVP_EncodeBlock` is that encoding.
* `acceptOf key = base64 (SHA1 (key ++ GUID))`: RFC 6455 section 4.2.2, item 5, point 4; and
  `keyOf nonce = base64 nonce` (section 4.1, client requirement 7: a 16-byte random nonce,
  base64-encoded).

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `accept_spec`: for every 16-byte nonce, `upgradePublic nonce = .ok (nonce ++ acceptOf (keyOf nonce))`,
  and `acceptFast_spec`: `acceptFast nonce = acceptOf (keyOf nonce)` (the two-block computation is the
  FIPS definition on this input length);
* `upgradePublic_length`, `upgradePublic_refuses`, `sha1_length`, `refBase64_length`;
* test vectors, by kernel evaluation (`decide +kernel`): FIPS 180-4 / RFC 3174 `sha1_abc`, `sha1_empty`,
  `sha1_448` (the 448-bit two-block message), and RFC 6455's example: `rfc6455_key`
  (the nonce "the sample nonce" is the key "dGhlIHNhbXBsZSBub25jZQ=="), `rfc6455_accept`
  (its accept value "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="), `rfc6455_upgradePublic` (op 45's reply on it).
-/
namespace TlsMpc.Local.WebSocketAccept
open TlsMpc.KernelSpecs.SlotBase64 (refBase64)

abbrev Byte := BitVec 8

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List Byte := s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-! ### SHA-1 (FIPS 180-4), on 32-bit words held as natural numbers below `2^32` -/

namespace Sha1

def modulus : Nat := 4294967296

/-- Addition modulo `2^32` (FIPS 180-4 section 3.2, item 1). -/
def add (x y : Nat) : Nat := (x + y) % modulus
/-- `ROTL^n` (section 3.2, item 5): `(x << n) ∨ (x >> (32 - n))`, on 32 bits. -/
def rotl (n x : Nat) : Nat := ((x <<< n) ||| (x >>> (32 - n))) % modulus
/-- The complement of a 32-bit word. -/
def compl (x : Nat) : Nat := x ^^^ (modulus - 1)

/-- Section 4.1.1. -/
def ch (x y z : Nat) : Nat := (x &&& y) ^^^ (compl x &&& z)
def parity (x y z : Nat) : Nat := x ^^^ y ^^^ z
def maj (x y z : Nat) : Nat := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def f (t x y z : Nat) : Nat :=
  if t < 20 then ch x y z else if t < 40 then parity x y z else if t < 60 then maj x y z else parity x y z

/-- Section 4.2.1. -/
def K (t : Nat) : Nat :=
  if t < 20 then 0x5a827999 else if t < 40 then 0x6ed9eba1 else if t < 60 then 0x8f1bbcdc else 0xca62c1d6

/-- `v` as `n` big-endian bytes. -/
def be (n v : Nat) : List Nat := (List.range n).map (fun i => v / 256 ^ (n - 1 - i) % 256)

/-- Section 5.1.1, for a message of whole bytes: `0x80`, then `k` zero bytes with
`l + 1 + k ≡ 56 (mod 64)`, then the message length in bits as a 64-bit big-endian number. -/
def pad (m : List Nat) : List Nat :=
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ be 8 (8 * m.length)

/-- Section 5.2.1: big-endian 32-bit words. -/
def words : List Nat → List Nat
  | a :: b :: c :: d :: rest => (a * 16777216 + b * 65536 + c * 256 + d) :: words rest
  | _ => []

/-- Section 5.2.1: 512-bit (64-byte) blocks. -/
def blocks : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | fuel + 1, m => if m.isEmpty then [] else m.take 64 :: blocks fuel (m.drop 64)

/-- Section 6.1.2, step 1: the message schedule, `W_t = ROTL^1(W_{t-3} ⊕ W_{t-8} ⊕ W_{t-14} ⊕ W_{t-16})`
for `16 ≤ t ≤ 79` (here `t + 16`). -/
def schedule (m : List Nat) : List Nat :=
  (List.range 64).foldl (fun w t =>
    w ++ [rotl 1 (w.getD (t + 13) 0 ^^^ w.getD (t + 8) 0 ^^^ w.getD (t + 2) 0 ^^^ w.getD t 0)]) m

/-- The working variables `a, b, c, d, e` (also the hash value `H0 … H4`). -/
structure H where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat

/-- Section 6.1.2, step 3: one of the 80 rounds. -/
def round (s : H) (t w : Nat) : H :=
  ⟨add (add (add (add (rotl 5 s.a) (f t s.b s.c s.d)) s.e) (K t)) w, s.a, rotl 30 s.b, s.c, s.d⟩

/-- Section 6.1.2, steps 1–4: one 512-bit block. -/
def compress (h : H) (block : List Nat) : H :=
  let w := schedule (words block)
  let s := (List.range 80).foldl (fun s t => round s t (w.getD t 0)) h
  ⟨add h.a s.a, add h.b s.b, add h.c s.c, add h.d s.d, add h.e s.e⟩

/-- Section 5.3.1. -/
def init : H := ⟨0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0⟩

/-- The 160-bit message digest `H0 ‖ H1 ‖ H2 ‖ H3 ‖ H4`, big-endian. -/
def out (h : H) : List Nat := be 4 h.a ++ be 4 h.b ++ be 4 h.c ++ be 4 h.d ++ be 4 h.e

/-- SHA-1 of a byte message (bytes as numbers below 256). -/
def digest (m : List Nat) : List Nat :=
  let p := pad m
  out ((blocks p.length p).foldl compress init)

end Sha1

/-- SHA-1 on bytes. -/
def sha1 (m : List Byte) : List Byte := (Sha1.digest (m.map BitVec.toNat)).map (BitVec.ofNat 8)

/-! ### RFC 6455 -/

/-- RFC 6455 section 1.3 / 4.2.2: the GUID `258EAFA5-E914-47DA-95CA-C5AB0DC85B11`. -/
def guid : List Byte := ascii "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

/-- RFC 6455 section 4.1, client requirement 7: `Sec-WebSocket-Key` is the 16-byte nonce,
base64-encoded. -/
def keyOf (nonce : List Byte) : List Byte := refBase64 nonce

/-- RFC 6455 section 4.2.2, item 5, point 4: `Sec-WebSocket-Accept` is the base64 encoding of the
SHA-1 of the key (as sent, not decoded) concatenated with the GUID. -/
def acceptOf (key : List Byte) : List Byte := refBase64 (sha1 (key ++ guid))

/-! ### The computation op 45 performs -/

/-- The padding of the 60-byte material: `0x80`, 59 zero bytes, the bit length 480. -/
def materialTail : List Nat := [0x80] ++ List.replicate 59 0 ++ Sha1.be 8 480

/-- The accept value as the worker computes it: key, material, SHA-1 of the material's two
blocks (the padding is fixed, the material being 60 bytes), base64. -/
def acceptFast (nonce : List Byte) : List Byte :=
  let material := (refBase64 nonce ++ guid).map BitVec.toNat
  let padded := material ++ materialTail
  refBase64 ((Sha1.out (Sha1.compress (Sha1.compress Sha1.init (padded.take 64)) (padded.drop 64))).map
    (BitVec.ofNat 8))

/-- Op 45 (`Upgrade.public`): the reply `nonce ‖ accept` to a 16-byte public nonce; any other
length is refused. (The worker also refuses a second upgrade or a closed session: session state,
not modelled here.) -/
def upgradePublic (nonce : List Byte) : Except String (List Byte) :=
  if nonce.length = 16 then .ok (nonce ++ acceptFast nonce) else .error "upgrade unavailable"

/-! ### Lengths -/

theorem refBase64_length (l : List Byte) : (refBase64 l).length = 4 * ((l.length + 2) / 3) := by
  fun_induction refBase64 l <;> simp_all <;> omega

theorem be_length (n v : Nat) : (Sha1.be n v).length = n := by simp [Sha1.be]

theorem sha1_length (m : List Byte) : (sha1 m).length = 20 := by
  simp [sha1, Sha1.digest, Sha1.out, be_length]

theorem guid_length : guid.length = 36 := by decide +kernel

theorem keyOf_length (nonce : List Byte) (h : nonce.length = 16) : (keyOf nonce).length = 24 := by
  rw [keyOf, refBase64_length, h]

theorem acceptOf_length (key : List Byte) : (acceptOf key).length = 28 := by
  rw [acceptOf, refBase64_length, sha1_length]

/-! ### The fixed-length computation is the definition -/

theorem materialTail_length : materialTail.length = 68 := by decide +kernel

theorem blocks_two (p : List Nat) (h : p.length = 128) :
    Sha1.blocks p.length p = [p.take 64, p.drop 64] := by
  rw [h]
  have h1 : (p.drop 64).length = 64 := by simp [h]
  have h2 : ((p.drop 64).drop 64) = [] := by simp [h]
  have e1 : p.isEmpty = false := by cases p <;> simp_all
  have e2 : (p.drop 64).isEmpty = false := by
    cases hp : p.drop 64 <;> simp_all
  have e3 : ((p.drop 64).take 64) = p.drop 64 := by simp [List.take_of_length_le, h1]
  show Sha1.blocks (127 + 1) p = _
  rw [Sha1.blocks, e1]
  show _ :: Sha1.blocks (126 + 1) (p.drop 64) = _
  rw [Sha1.blocks, e2, h2, e3]
  rfl

theorem pad_sixty (m : List Nat) (h : m.length = 60) : Sha1.pad m = m ++ materialTail := by
  simp [Sha1.pad, materialTail, h]

theorem acceptFast_spec (nonce : List Byte) (h : nonce.length = 16) :
    acceptFast nonce = acceptOf (keyOf nonce) := by
  have hm : ((refBase64 nonce ++ guid).map BitVec.toNat).length = 60 := by
    simp [refBase64_length, h, guid_length]
  have hp : (((refBase64 nonce ++ guid).map BitVec.toNat) ++ materialTail).length = 128 := by
    simp only [List.length_append, hm, materialTail_length]
  simp only [acceptFast, acceptOf, sha1, keyOf, Sha1.digest]
  rw [pad_sixty _ hm, blocks_two _ hp]
  rfl

/-- **`accept_spec`.** Op 45 on a 16-byte nonce replies the nonce followed by RFC 6455's
`Sec-WebSocket-Accept` for the key `base64(nonce)`. -/
theorem accept_spec (nonce : List Byte) (h : nonce.length = 16) :
    upgradePublic nonce = .ok (nonce ++ acceptOf (keyOf nonce)) := by
  rw [upgradePublic, if_pos h, acceptFast_spec nonce h]

theorem upgradePublic_length (nonce reply : List Byte) (h : upgradePublic nonce = .ok reply) :
    nonce.length = 16 ∧ reply.length = 44 := by
  unfold upgradePublic at h
  split at h
  · next hn =>
    cases h
    refine ⟨hn, ?_⟩
    rw [List.length_append, hn, acceptFast_spec nonce hn, acceptOf_length]
  · cases h

theorem upgradePublic_refuses (nonce : List Byte) (h : nonce.length ≠ 16) :
    upgradePublic nonce = .error "upgrade unavailable" := by
  rw [upgradePublic, if_neg h]

/-! ### Test vectors (kernel evaluation) -/

/-- FIPS 180-4 example / RFC 3174 test 1: SHA-1("abc"). -/
theorem sha1_abc : Sha1.digest [0x61, 0x62, 0x63] =
    [0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a, 0xba, 0x3e,
     0x25, 0x71, 0x78, 0x50, 0xc2, 0x6c, 0x9c, 0xd0, 0xd8, 0x9d] := by
  decide +kernel

/-- SHA-1 of the empty message. -/
theorem sha1_empty : Sha1.digest [] =
    [0xda, 0x39, 0xa3, 0xee, 0x5e, 0x6b, 0x4b, 0x0d, 0x32, 0x55,
     0xbf, 0xef, 0x95, 0x60, 0x18, 0x90, 0xaf, 0xd8, 0x07, 0x09] := by
  decide +kernel

/-- FIPS 180-4 example / RFC 3174 test 2: the 448-bit message
"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" (two blocks after padding). -/
theorem sha1_448 : sha1 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
    ([0x84, 0x98, 0x3e, 0x44, 0x1c, 0x3b, 0xd2, 0x6e, 0xba, 0xae,
      0x4a, 0xa1, 0xf9, 0x51, 0x29, 0xe5, 0xe5, 0x46, 0x70, 0xf1] : List Nat).map (BitVec.ofNat 8) := by
  decide +kernel

/-- RFC 6455 section 4.1: the example key is the base64 of the nonce "the sample nonce". -/
theorem rfc6455_key : keyOf (ascii "the sample nonce") = ascii "dGhlIHNhbXBsZSBub25jZQ==" := by
  decide +kernel

/-- RFC 6455 sections 1.3 and 4.2.2: the example's accept value. -/
theorem rfc6455_accept : acceptOf (ascii "dGhlIHNhbXBsZSBub25jZQ==") = ascii "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=" := by
  decide +kernel

/-- Op 45's reply to the RFC's nonce, computed (not through `accept_spec`). -/
theorem rfc6455_upgradePublic :
    upgradePublic (ascii "the sample nonce") =
      .ok (ascii "the sample nonce" ++ ascii "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=") := by
  have hlen : (ascii "the sample nonce").length = 16 := by decide +kernel
  have hacc : acceptFast (ascii "the sample nonce") = ascii "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=" := by
    decide +kernel
  rw [upgradePublic, if_pos hlen, hacc]

end TlsMpc.Local.WebSocketAccept
