import TlsMpc.KernelSpecs.ReceiveAccept

/-!
# `receive-text`: what is released when it accepts (T13, proof track P6)

New file; it changes no definition and no emitter imports it.

`receive-text` (`ReceiveFirst.text`, proved equal to the kernel by `ReceiveProofs.text_spec`) opens
its status, the body length, the body and three layout flags. This file proves exactly which bytes
of the decrypted content those are.

PROVED (standard axioms only), for `capacity < 65536` (the kernel's `find` allows at most 16378):
* `text_eq`, `text_status`: the status is 255 exactly when `Accepted` (content byte 0 is `0A`, the
  body's tag is `0A`, the body's length prefix has at most two bytes, the body fits `capacity`),
  and 0 otherwise;
* `text_rejects`: otherwise every output byte is zero (the `_rejects` lemma that was missing);
* `text_accepted`: when accepted, the opened text is exactly the `bodyLength` bytes at `bodyStart`;
* `text_of_reference`, `text_reference` (converse): a content that a protobuf reading
  (`referenceBody`) parses, with both length prefixes of at most two bytes and a body that fits, is
  accepted and the opened text is exactly the reference body.

COUNTEREXAMPLE (`overlongBody_accepted`, `overlongBody_reference`): the accept direction does NOT
hold against the reference in general. The kernel never compares the body's extent with the
DataMessage's length `len₁` (and judges `len₁`'s width from one continuation bit), so a content
whose body runs past its DataMessage is accepted and bytes outside the DataMessage are opened.
Only the authenticated sender can produce such a plaintext.
-/
namespace TlsMpc.KernelSpecs.ReceiveAcceptText
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open Signal.ReceiveFirst
open ReceiveAccept

/-! ### Byte-level facts -/

theorem top_mk : ∀ x : BitVec 8, top ByteAuth.concrete x = mk (128 ≤ x.toNat) := by decide

theorem chooseByte_mk (P : Prop) [Decidable P] (y n : BitVec 8) :
    Unpad.chooseByte ByteAuth.concrete (mk P) y n = if P then y else n := by
  unfold mk; split
  · exact Unpad.chooseByte_accept y n
  · exact Unpad.chooseByte_reject y n

theorem length0 : ∀ h : BitVec 8,
    (List.range 7).foldl (fun acc k => ByteAuth.concrete.xor acc
      (ByteAuth.concrete.and (ByteAuth.concrete.maskBit h (k + 1)) (ByteAuth.concrete.const (2 ^ k))))
      (ByteAuth.concrete.const 0) = BitVec.ofNat 8 (h.toNat / 2) := by decide

theorem bit0_mask : ∀ h : BitVec 8,
    ByteAuth.concrete.and (ByteAuth.concrete.maskBit h 0) (ByteAuth.concrete.const 128) =
      BitVec.ofNat 8 (128 * (h.toNat % 2)) := by decide

theorem low_join : ∀ (l : BitVec 8) (b : Fin 2),
    ByteAuth.concrete.xor (ByteAuth.concrete.and l (ByteAuth.concrete.const 127)) (BitVec.ofNat 8 (128 * b.val)) =
      BitVec.ofNat 8 (l.toNat % 128 + 128 * b.val) := by decide

/-- The two length bytes `text` computes from the varint bytes `lo`, `hi`. -/
theorem lengthBytes_eq (lo hi : BitVec 8) :
    [(List.range 7).foldl (fun acc k => ByteAuth.concrete.xor acc
        (ByteAuth.concrete.and (ByteAuth.concrete.maskBit hi (k + 1)) (ByteAuth.concrete.const (2 ^ k))))
        (ByteAuth.concrete.const 0),
      ByteAuth.concrete.xor (ByteAuth.concrete.and lo (ByteAuth.concrete.const 127))
        (ByteAuth.concrete.and (ByteAuth.concrete.maskBit hi 0) (ByteAuth.concrete.const 128))] =
      [BitVec.ofNat 8 (hi.toNat / 2), BitVec.ofNat 8 (lo.toNat % 128 + 128 * (hi.toNat % 2))] := by
  rw [length0, bit0_mask, low_join lo ⟨hi.toNat % 2, Nat.mod_lt _ (by decide)⟩]

theorem val_two_ofNat (a b : Nat) (ha : a < 256) (hb : b < 256) :
    val (bitsOf [BitVec.ofNat 8 a, BitVec.ofNat 8 b]) = a * 256 + b := by
  rw [val_bitsOf_two, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem atMost_number (lo hi : BitVec 8) (n : Nat) (hn : n < 65536) :
    atMost ByteAuth.concrete [BitVec.ofNat 8 (hi.toNat / 2), BitVec.ofNat 8 (lo.toNat % 128 + 128 * (hi.toNat % 2))]
        (lit ByteAuth.concrete [n / 256 % 256, n % 256]) =
      mk (lo.toNat % 128 + 128 * hi.toNat ≤ n) := by
  have hl := lo.isLt
  have hh := hi.isLt
  simp only [Nat.reducePow] at hl hh
  rw [atMost_value _ _ (by simp [lit])]
  apply mk_congr
  simp only [lit, List.map_cons, List.map_nil, concrete_const]
  rw [val_two_ofNat _ _ (by omega) (by omega), val_two_ofNat _ _ (by omega) (by omega)]
  omega

/-! ### The parse `text` performs

The content is `0A len₁ (0A len₂ body …) …`: field 1 of `Content` (the DataMessage) whose first
field is the body. -/

section
variable (c : List (BitVec 8))

/-- Byte `i` of the content (the plaintext after its 8-byte length prefix). -/
def g (i : Nat) : BitVec 8 := OpenResult.get ByteAuth.concrete c i

/-- The DataMessage's length prefix `len₁` is taken to have two bytes: byte 1 has its continuation
bit set. (Its second byte is not checked.) -/
def Wide : Prop := 128 ≤ (g c 1).toNat

instance : Decidable (Wide c) := inferInstanceAs (Decidable (_ ≤ _))

/-- The byte that must be the body's tag `0A`. -/
def tagByte : BitVec 8 := if Wide c then g c 3 else g c 2

/-- First byte of the body's length prefix `len₂`. -/
def lowByte : BitVec 8 := if Wide c then g c 4 else g c 3

/-- `len₂` has two bytes. -/
def Long : Prop := 128 ≤ (lowByte c).toNat

instance : Decidable (Long c) := inferInstanceAs (Decidable (_ ≤ _))

/-- Second byte of `len₂` (0 if it has one byte). -/
def highByte : BitVec 8 := if Long c then (if Wide c then g c 5 else g c 4) else 0

/-- The body's length: the value of `len₂`. -/
def bodyLength : Nat := (lowByte c).toNat % 128 + 128 * (highByte c).toNat

/-- Where the body starts: 4, plus one for each two-byte prefix. -/
def bodyStart : Nat := 4 + (if Wide c then 1 else 0) + (if Long c then 1 else 0)

/-- What `receive-text` checks: `0A` at 0 and as the body's tag, `len₂` of at most two bytes, and a
body length of at most `capacity`. -/
def Accepted (capacity : Nat) : Prop :=
  g c 0 = ByteAuth.concrete.const 10 ∧ tagByte c = ByteAuth.concrete.const 10 ∧ ¬ 128 ≤ (highByte c).toNat ∧
    bodyLength c ≤ capacity

instance (capacity : Nat) : Decidable (Accepted c capacity) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end

theorem not_255 : ByteAuth.concrete.not 255 = 0 := by decide
theorem not_0 : ByteAuth.concrete.not 0 = 255 := by decide
theorem xor_255_0 : ByteAuth.concrete.xor 255 0 = 255 := by decide
theorem xor_0_255 : ByteAuth.concrete.xor 0 255 = 255 := by decide
theorem xor_255_255 : ByteAuth.concrete.xor 255 255 = 0 := by decide
theorem xor_0_0 : ByteAuth.concrete.xor 0 0 = 0 := by decide
theorem and_255 (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := ones_and' x
theorem and_0 (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := zero_and' x
theorem and_x_255 (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
theorem and_x_0 (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
theorem mk_true' (P : Prop) [Decidable P] (h : P) : mk P = 255 := if_pos h
theorem mk_false' (P : Prop) [Decidable P] (h : ¬P) : mk P = 0 := if_neg h

theorem eqMask_mk (x y : BitVec 8) : ByteAuth.eqMask ByteAuth.concrete x y = mk (x = y) := ByteAuth.eqMask_value x y

theorem all_mk4 (P Q R S : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S] :
    all ByteAuth.concrete [mk P, mk Q, mk R, mk S] = mk (P ∧ Q ∧ R ∧ S) := by
  unfold mk all
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hr : R <;> by_cases hs : S <;> simp [hp, hq, hr, hs] <;> decide

theorem all_mk_mk (P Q : Prop) [Decidable P] [Decidable Q] (v : BitVec 8) :
    all ByteAuth.concrete [mk P, mk Q, v] = if P ∧ Q then v else 0 := by
  unfold mk all
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, zero_and', ones_and', BitVec.and_zero, concrete_const,
    ofNat255_and]

set_option linter.unusedSimpArgs false in
theorem pick_select (W L : Prop) [Decidable W] [Decidable L] (a b d : BitVec 8) :
    pick ByteAuth.concrete [(ByteAuth.concrete.and (ByteAuth.concrete.not (mk W)) (ByteAuth.concrete.not (mk L)), a),
      (ByteAuth.concrete.xor (mk W) (mk L), b), (ByteAuth.concrete.and (mk W) (mk L), d)] =
      if W then (if L then d else b) else (if L then b else a) := by
  unfold mk pick
  by_cases hw : W <;> by_cases hl : L <;>
    simp [hw, hl, not_255, not_0, xor_255_0, xor_0_255, xor_255_255, xor_0_0, and_255, and_0, concrete_const,
      zero_xor', xor_zero']

set_option linter.unusedSimpArgs false in
/-- **`receive-text`, exactly**, for `capacity < 65536`: with `c` the content (the plaintext after
its 8-byte length), the status is `mk (Accepted c capacity)`; the length is the body length
(released under the status); text byte `i` is content byte `bodyStart + i` when accepted and
`i < bodyLength`, else 0; the layout flags say which of the two prefixes have two bytes (released
under the status). -/
theorem text_eq (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8)) :
    text ByteAuth.concrete capacity plain =
      [[mk (Accepted (plain.drop 8) capacity)],
        ByteAuth.release ByteAuth.concrete (mk (Accepted (plain.drop 8) capacity))
          [BitVec.ofNat 8 ((highByte (plain.drop 8)).toNat / 2),
            BitVec.ofNat 8 ((lowByte (plain.drop 8)).toNat % 128 + 128 * ((highByte (plain.drop 8)).toNat % 2))],
        (List.range capacity).map (fun i =>
          if Accepted (plain.drop 8) capacity ∧ ¬ bodyLength (plain.drop 8) ≤ i then
            g (plain.drop 8) (bodyStart (plain.drop 8) + i) else 0),
        ByteAuth.release ByteAuth.concrete (mk (Accepted (plain.drop 8) capacity))
          [mk (¬Wide (plain.drop 8) ∧ ¬Long (plain.drop 8)), mk (¬(Wide (plain.drop 8) ↔ Long (plain.drop 8))),
            mk (Wide (plain.drop 8) ∧ Long (plain.drop 8))]] := by
  unfold text
  generalize plain.drop 8 = c
  have hwide : top ByteAuth.concrete (OpenResult.get ByteAuth.concrete c 1) = mk (Wide c) := top_mk _
  have hlow : Unpad.chooseByte ByteAuth.concrete (mk (Wide c)) (OpenResult.get ByteAuth.concrete c 4)
      (OpenResult.get ByteAuth.concrete c 3) = lowByte c := by rw [chooseByte_mk]; rfl
  have htag : Unpad.chooseByte ByteAuth.concrete (mk (Wide c)) (OpenResult.get ByteAuth.concrete c 3)
      (OpenResult.get ByteAuth.concrete c 2) = tagByte c := by rw [chooseByte_mk]; rfl
  have hlong : top ByteAuth.concrete (lowByte c) = mk (Long c) := top_mk _
  have hhigh : ByteAuth.concrete.and (mk (Long c)) (Unpad.chooseByte ByteAuth.concrete (mk (Wide c))
      (OpenResult.get ByteAuth.concrete c 5) (OpenResult.get ByteAuth.concrete c 4)) = highByte c := by
    rw [chooseByte_mk]
    unfold highByte mk
    by_cases hl : Long c <;> simp [hl, and_255, and_0]; rfl
  have hhighTop : top ByteAuth.concrete (highByte c) = mk (128 ≤ (highByte c).toNat) := top_mk _
  have hok : all ByteAuth.concrete [ByteAuth.eqMask ByteAuth.concrete (OpenResult.get ByteAuth.concrete c 0)
        (ByteAuth.concrete.const 10), ByteAuth.eqMask ByteAuth.concrete (tagByte c) (ByteAuth.concrete.const 10),
        ByteAuth.concrete.not (mk (128 ≤ (highByte c).toNat)),
        atMost ByteAuth.concrete [BitVec.ofNat 8 ((highByte c).toNat / 2),
          BitVec.ofNat 8 ((lowByte c).toNat % 128 + 128 * ((highByte c).toNat % 2))]
          (lit ByteAuth.concrete [capacity / 256 % 256, capacity % 256])] = mk (Accepted c capacity) := by
    rw [eqMask_mk, eqMask_mk, mk_not, atMost_number _ _ _ hcap, all_mk4]
    rfl
  simp only [hwide, hlow, htag, hlong, hhigh, hhighTop, lengthBytes_eq, hok]
  congr 1
  congr 1
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < 65536 := by simp at hi; omega
    rw [atMost_number _ _ _ hi', mk_not, pick_select, all_mk_mk]
    unfold bodyStart bodyLength
    by_cases hw : Wide c <;> by_cases hl : Long c <;> simp [hw, hl, g, Nat.add_comm]
  · simp only [mk_not, mk_and, mk_xor]

/-- **`receive-text`'s status is 255 exactly when the content passes `Accepted`** (and 0 otherwise). -/
theorem text_status (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8)) :
    (text ByteAuth.concrete capacity plain).getD 0 [] = [mk (Accepted (plain.drop 8) capacity)] := by
  rw [text_eq capacity hcap plain]; rfl

/-- **A refused `receive-text` releases nothing** (the missing `_rejects` lemma): when the content
fails `Accepted`, every output byte is zero. -/
theorem text_rejects (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8))
    (h : ¬Accepted (plain.drop 8) capacity) :
    ∀ field ∈ text ByteAuth.concrete capacity plain, ∀ b ∈ field, b = 0 := by
  rw [text_eq capacity hcap plain, mk_false' _ h, ByteAuth.release_reject, ByteAuth.release_reject]
  intro field hf b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · simpa using hb
  · exact List.eq_of_mem_replicate hb
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
    simp [h]
  · exact List.eq_of_mem_replicate hb

/-- **What an accepted `receive-text` opens**: status 255; the body length as two big-endian bytes;
exactly the `bodyLength` content bytes starting at `bodyStart` (4, 5 or 6), then zeros up to
`capacity`; and the flags of `bodyStart = 4, 5, 6`. -/
theorem text_accepted (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8))
    (h : Accepted (plain.drop 8) capacity) :
    text ByteAuth.concrete capacity plain =
      [[255], [BitVec.ofNat 8 (bodyLength (plain.drop 8) / 256), BitVec.ofNat 8 (bodyLength (plain.drop 8) % 256)],
        (List.range capacity).map (fun i =>
          if i < bodyLength (plain.drop 8) then g (plain.drop 8) (bodyStart (plain.drop 8) + i) else 0),
        [mk (bodyStart (plain.drop 8) = 4), mk (bodyStart (plain.drop 8) = 5), mk (bodyStart (plain.drop 8) = 6)]] := by
  rw [text_eq capacity hcap plain, mk_true' _ h, release_255, release_255]
  generalize plain.drop 8 = c at h ⊢
  have hh : (highByte c).toNat < 128 := by have := h.2.2.1; omega
  have hl := (lowByte c).isLt
  simp only [Nat.reducePow] at hl
  have e1 : (highByte c).toNat / 2 = bodyLength c / 256 := by unfold bodyLength; omega
  have e2 : (lowByte c).toNat % 128 + 128 * ((highByte c).toNat % 2) = bodyLength c % 256 := by
    unfold bodyLength; omega
  have f1 : mk (¬Wide c ∧ ¬Long c) = mk (bodyStart c = 4) :=
    mk_congr (by unfold bodyStart; by_cases hw : Wide c <;> by_cases hl : Long c <;> simp [hw, hl])
  have f2 : mk (¬(Wide c ↔ Long c)) = mk (bodyStart c = 5) :=
    mk_congr (by unfold bodyStart; by_cases hw : Wide c <;> by_cases hl : Long c <;> simp [hw, hl])
  have f3 : mk (Wide c ∧ Long c) = mk (bodyStart c = 6) :=
    mk_congr (by unfold bodyStart; by_cases hw : Wide c <;> by_cases hl : Long c <;> simp [hw, hl])
  rw [e1, e2, f1, f2, f3]
  simp only [h, true_and, Nat.not_le]

/-! ### Against a reference parse of the content

The reference reads the content as protobuf: field 1 (tag `0A`) of `Content` is the DataMessage,
whose field 1 (tag `0A`) is the body; each length prefix is a varint (at most 10 bytes); the
DataMessage must lie inside the content and the body inside the DataMessage (a protobuf decoder
rejects a length that runs past its enclosing message). Like the kernel, it takes the first
occurrence of each field and assumes the DataMessage is the content's first field and the body the
DataMessage's first field (what Signal clients emit). -/

/-- A varint at `pos` (value, width), reading at most `fuel` bytes. -/
def varintAt (c : List (BitVec 8)) (pos : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
      if (g c pos).toNat < 128 then some ((g c pos).toNat, 1)
      else (varintAt c (pos + 1) fuel).map (fun r => ((g c pos).toNat % 128 + 128 * r.1, r.2 + 1))

/-- The reference body of a content, or `none` when the content does not parse. -/
def referenceBody (c : List (BitVec 8)) : Option (List (BitVec 8)) :=
  if g c 0 = ByteAuth.concrete.const 10 then
    match varintAt c 1 10 with
    | some (len₁, w₁) =>
        if 1 + w₁ + len₁ ≤ c.length ∧ 1 ≤ len₁ ∧ g c (1 + w₁) = ByteAuth.concrete.const 10 then
          match varintAt c (2 + w₁) 10 with
          | some (len₂, w₂) =>
              if 2 + w₁ + w₂ + len₂ ≤ 1 + w₁ + len₁ then some (Establish.part c (2 + w₁ + w₂) len₂) else none
          | none => none
        else none
    | none => none
  else none

/-- **Counterexample (accepted, but the reference rejects).** A content whose DataMessage is 3
bytes long (`0A 03 …`) but whose body claims 5 bytes (`0A 05 …`): a protobuf decoder rejects it,
since the body runs past the DataMessage. `receive-text` accepts it and opens 5 bytes, four of
which lie outside the DataMessage. The kernel never compares the body's extent with the
DataMessage's length `len₁` (nor reads `len₁`'s second byte). Only the sender can produce such a
plaintext (the session's MAC check passed), so what is opened is still the sender's own bytes. -/
def overlongBodyPlain : List (BitVec 8) :=
  List.replicate 8 0 ++ [0x0A, 0x03, 0x0A, 0x05, 0x61, 0x62, 0x63, 0x64, 0x65] ++ List.replicate 7 0

theorem overlongBody_accepted :
    text ByteAuth.concrete 10 overlongBodyPlain =
      [[255], [0, 5], [0x61, 0x62, 0x63, 0x64, 0x65, 0, 0, 0, 0, 0], [255, 0, 0]] := by
  decide

theorem overlongBody_reference : referenceBody (overlongBodyPlain.drop 8) = none := by
  decide

/-- **Converse: a content the reference parses, whose two length prefixes have at most two bytes
each and whose body fits `capacity`, is accepted, and the opened text is exactly the reference
body (zero-padded to `capacity`).** -/
theorem text_of_reference (capacity : Nat) (plain body : List (BitVec 8))
    (href : referenceBody (plain.drop 8) = some body)
    (hw₁ : (g (plain.drop 8) 1).toNat < 128 ∨ (g (plain.drop 8) 2).toNat < 128)
    (hw₂ : (lowByte (plain.drop 8)).toNat < 128 ∨ (highByte (plain.drop 8)).toNat < 128)
    (hfit : body.length ≤ capacity) :
    Accepted (plain.drop 8) capacity ∧ bodyLength (plain.drop 8) = body.length ∧
      (List.range capacity).map (fun i =>
          if i < bodyLength (plain.drop 8) then g (plain.drop 8) (bodyStart (plain.drop 8) + i) else 0) =
        (List.range capacity).map (fun i => body.getD i 0) := by
  generalize plain.drop 8 = c at href hw₁ hw₂ ⊢
  unfold referenceBody at href
  have h0 : g c 0 = ByteAuth.concrete.const 10 := by
    by_cases h : g c 0 = ByteAuth.concrete.const 10
    · exact h
    · simp [h] at href
  rw [if_pos h0] at href
  -- the first prefix
  have hv₁ : ∃ len₁ w₁, varintAt c 1 10 = some (len₁, w₁) ∧ (w₁ = 1 ↔ ¬Wide c) ∧ (w₁ = 1 ∨ w₁ = 2) := by
    by_cases hw : Wide c
    · have h2 : (g c 2).toNat < 128 := by unfold Wide at hw; omega
      refine ⟨(g c 1).toNat % 128 + 128 * (g c 2).toNat, 2, ?_, by simp [hw], Or.inr rfl⟩
      unfold Wide at hw
      simp [varintAt, h2, Nat.not_lt.mpr hw]
    · refine ⟨(g c 1).toNat, 1, ?_, by simp [hw], Or.inl rfl⟩
      unfold Wide at hw
      simp [varintAt, Nat.lt_of_not_le hw]
  obtain ⟨len₁, w₁, hv₁, hw₁iff, hw₁cases⟩ := hv₁
  rw [hv₁] at href
  simp only at href
  have hb₁ : 1 + w₁ + len₁ ≤ c.length ∧ 1 ≤ len₁ ∧ g c (1 + w₁) = ByteAuth.concrete.const 10 := by
    by_cases h : 1 + w₁ + len₁ ≤ c.length ∧ 1 ≤ len₁ ∧ g c (1 + w₁) = ByteAuth.concrete.const 10
    · exact h
    · rw [if_neg h] at href
      simp at href
  rw [if_pos hb₁] at href
  have htag : tagByte c = ByteAuth.concrete.const 10 := by
    have := hb₁.2.2
    unfold tagByte
    rcases hw₁cases with rfl | rfl
    · simp only [show ¬Wide c from hw₁iff.mp rfl, if_false]; exact this
    · have : Wide c := Classical.byContradiction fun h => absurd (hw₁iff.mpr h) (by decide)
      simp only [this, if_true]; assumption
  have hlow : lowByte c = g c (2 + w₁) := by
    unfold lowByte
    rcases hw₁cases with rfl | rfl
    · simp [show ¬Wide c from hw₁iff.mp rfl]
    · have : Wide c := Classical.byContradiction fun h => absurd (hw₁iff.mpr h) (by decide)
      simp [this]
  have hhighAt : (if Wide c then g c 5 else g c 4) = g c (3 + w₁) := by
    rcases hw₁cases with rfl | rfl
    · simp [show ¬Wide c from hw₁iff.mp rfl]
    · have : Wide c := Classical.byContradiction fun h => absurd (hw₁iff.mpr h) (by decide)
      simp [this]
  -- the second prefix
  have hv₂ : varintAt c (2 + w₁) 10 = some (bodyLength c, if Long c then 2 else 1) ∧
      ¬ 128 ≤ (highByte c).toNat := by
    by_cases hl : Long c
    · have hl' : 128 ≤ (g c (2 + w₁)).toNat := by unfold Long at hl; rw [hlow] at hl; exact hl
      have hhb : highByte c = g c (3 + w₁) := by unfold highByte; rw [if_pos hl, hhighAt]
      have h3 : (g c (3 + w₁)).toNat < 128 := by
        rcases hw₂ with h | h
        · rw [hlow] at h; omega
        · rw [hhb] at h; exact h
      rw [if_pos hl]
      unfold bodyLength
      rw [hhb, hlow]
      refine ⟨?_, by omega⟩
      simp [varintAt, show ¬ (g c (2 + w₁)).toNat < 128 by omega, show 2 + w₁ + 1 = 3 + w₁ by omega, h3]
    · have hl' : (g c (2 + w₁)).toNat < 128 := by unfold Long at hl; rw [hlow] at hl; omega
      have hhb : highByte c = 0 := by unfold highByte; rw [if_neg hl]
      rw [if_neg hl]
      unfold bodyLength
      rw [hhb, hlow]
      refine ⟨?_, by decide⟩
      simp [varintAt, hl']
      omega
  have hhigh := hv₂.2
  rw [hv₂.1] at href
  simp only at href
  have hb₂ : 2 + w₁ + (if Long c then 2 else 1) + bodyLength c ≤ 1 + w₁ + len₁ := by
    by_cases h : 2 + w₁ + (if Long c then 2 else 1) + bodyLength c ≤ 1 + w₁ + len₁
    · exact h
    · rw [if_neg h] at href
      simp at href
  rw [if_pos hb₂] at href
  simp only [Option.some.injEq] at href
  have hstart : bodyStart c = 2 + w₁ + (if Long c then 2 else 1) := by
    unfold bodyStart
    rcases hw₁cases with rfl | rfl
    · simp only [show ¬Wide c from hw₁iff.mp rfl, if_false]; split <;> omega
    · have : Wide c := Classical.byContradiction fun h => absurd (hw₁iff.mpr h) (by decide)
      simp only [this, if_true]; split <;> omega
  have hlen : body.length = bodyLength c := by
    rw [← href, Establish.part, List.length_take, List.length_drop]; omega
  refine ⟨⟨h0, htag, hhigh, by omega⟩, hlen.symm, ?_⟩
  apply List.map_congr_left
  intro i _
  rw [← href, hstart]
  by_cases hi : i < bodyLength c
  · rw [if_pos hi]
    simp only [g, OpenResult.get, Establish.part, List.getD_eq_getElem?_getD, List.getElem?_take, hi, if_true,
      List.getElem?_drop]
    rfl
  · rw [if_neg hi]
    simp [Establish.part, List.getD_eq_getElem?_getD, List.getElem?_take, hi]

/-- **The converse at the level of `receive-text`'s outputs**: for such a content, `receive-text`
opens status 255, the reference body's length, the reference body (zero-padded to `capacity`) and
the layout flags. -/
theorem text_reference (capacity : Nat) (hcap : capacity < 65536) (plain body : List (BitVec 8))
    (href : referenceBody (plain.drop 8) = some body)
    (hw₁ : (g (plain.drop 8) 1).toNat < 128 ∨ (g (plain.drop 8) 2).toNat < 128)
    (hw₂ : (lowByte (plain.drop 8)).toNat < 128 ∨ (highByte (plain.drop 8)).toNat < 128)
    (hfit : body.length ≤ capacity) :
    text ByteAuth.concrete capacity plain =
      [[255], [BitVec.ofNat 8 (body.length / 256), BitVec.ofNat 8 (body.length % 256)],
        (List.range capacity).map (fun i => body.getD i 0),
        [mk (bodyStart (plain.drop 8) = 4), mk (bodyStart (plain.drop 8) = 5), mk (bodyStart (plain.drop 8) = 6)]] := by
  obtain ⟨hacc, hlen, hbytes⟩ := text_of_reference capacity plain body href hw₁ hw₂ hfit
  rw [text_accepted capacity hcap plain hacc, hbytes, hlen]

end TlsMpc.KernelSpecs.ReceiveAcceptText
