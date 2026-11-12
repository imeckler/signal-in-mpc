import TlsMpc.KernelSpecs.ReceiveAccept

/-!
# `receive-text`: what is released when it accepts (T13, proof track P6)

No emitter imports this file. The kernel definition it is about (`ReceiveFirst.text`) changed in the
emitter batch (EMITTER_BATCH.md): it now also checks the DataMessage's length `len₁` (its second
byte, the body's extent inside it, and its own extent inside the content). The circuits change only
after the re-lowering.

`receive-text` (`ReceiveFirst.text`, proved equal to the kernel by `ReceiveProofs.text_spec`) opens
its status, the body length, the body and three layout flags. This file proves exactly which bytes
of the decrypted content those are, and that the kernel accepts exactly the contents a protobuf
reading accepts (for length prefixes of at most two bytes and a body that fits).

PROVED (standard axioms only), for `capacity < 65536` (the kernel's `find` allows at most 16378):
* `text_eq`, `text_status`: the status is 255 exactly when `Accepted` (content byte 0 is `0A`, the
  body's tag is `0A`, both length prefixes have at most two bytes, the body lies inside the
  DataMessage, the DataMessage inside the content, the body fits `capacity`), and 0 otherwise;
* `text_rejects`: otherwise every output byte is zero (the `_rejects` lemma that was missing);
* `text_accepted`: when accepted, the opened text is exactly the `bodyLength` bytes at `bodyStart`;
* `text_of_reference`, `text_reference` (converse): a content that a protobuf reading
  (`referenceBody`) parses, with both length prefixes of at most two bytes and a body that fits, is
  accepted and the opened text is exactly the reference body;
* `accepted_iff_reference`, `text_status_iff_reference`: accepted EXACTLY when the reference parses
  the content with both prefixes of at most two bytes (`Covered`) and the body fits `capacity`;
  `text_accepted_reference`: and then the opened text is the reference body.

The former COUNTEREXAMPLE is now a refusal theorem (`overlongBody_refused`, with
`overlongBody_reference`): a content whose 3-byte DataMessage claims a 5-byte body is refused and
nothing is opened.
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
    decodeLength ByteAuth.concrete lo hi =
      [BitVec.ofNat 8 (hi.toNat / 2), BitVec.ofNat 8 (lo.toNat % 128 + 128 * (hi.toNat % 2))] := by
  unfold decodeLength
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

/-! ### Adding a carry to big-endian bit masks (`incBits`) -/

/-- `incBits` on bits: the sum bits and the carry out. -/
def incB : List Bool → Bool → List Bool × Bool
  | [], carry => ([], carry)
  | b :: bs, carry => ((b ^^ (incB bs carry).2) :: (incB bs carry).1, b && (incB bs carry).2)

theorem mk_bool_xor (b r : Bool) :
    ByteAuth.concrete.xor (mk (b = true)) (mk (r = true)) = mk ((b ^^ r) = true) := by
  cases b <;> cases r <;> decide

theorem mk_bool_and (b r : Bool) :
    ByteAuth.concrete.and (mk (b = true)) (mk (r = true)) = mk ((b && r) = true) := by
  cases b <;> cases r <;> decide

theorem incBits_concrete (bs : List Bool) (carry : Bool) :
    incBits ByteAuth.concrete (bs.map fun b => mk (b = true)) (mk (carry = true)) =
      ((incB bs carry).1.map fun b => mk (b = true), mk ((incB bs carry).2 = true)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, incBits, ih, incB, mk_bool_xor, mk_bool_and]
      try rfl

theorem incB_val (bs : List Bool) (carry : Bool) :
    (incB bs carry).1.length = bs.length ∧
      val (incB bs carry).1 + (if (incB bs carry).2 then 2 ^ bs.length else 0) =
        val bs + (if carry then 1 else 0) := by
  induction bs with
  | nil => cases carry <;> simp [incB, val]
  | cons b bs ih =>
      obtain ⟨hl, hv⟩ := ih
      simp only [incB, List.length_cons, hl, val, Nat.pow_succ]
      generalize (incB bs carry).1 = s at hl hv ⊢
      generalize (incB bs carry).2 = r at hv ⊢
      refine ⟨by trivial, ?_⟩
      have := val_lt bs
      cases b <;> cases r <;> cases carry <;> (try simp at hv ⊢) <;> omega

theorem const255_mk : ByteAuth.concrete.const 255 = mk (true = true) := rfl
theorem const0_mk : ByteAuth.concrete.const 0 = mk False := rfl

/-- **`inside`, by value**: for two 2-byte numbers `x` (with the carry-in `L`) and `y`, the mask
`text` computes is that of `x + [L] + 1 < y`. -/
theorem inside_value (x y : List (BitVec 8)) (hx : x.length = 2) (hy : y.length = 2) (L : Prop) [Decidable L]
    (hsmall : val (bitsOf x) + 2 < 2 ^ 16) :
    (compareBits ByteAuth.concrete
        (incBits ByteAuth.concrete (incBits ByteAuth.concrete (maskBits ByteAuth.concrete x) (mk L)).1
          (ByteAuth.concrete.const 255)).1
        (maskBits ByteAuth.concrete y) (ByteAuth.concrete.const 0) (ByteAuth.concrete.const 255)).1 =
      mk (val (bitsOf x) + (if L then 1 else 0) + 1 < val (bitsOf y)) := by
  have hbx : (bitsOf x).length = 16 := by rw [bitsOf_length, hx]
  have hby : (bitsOf y).length = 16 := by rw [bitsOf_length, hy]
  have hL : mk L = mk (decide L = true) := mk_congr (by simp)
  rw [maskBits_eq, maskBits_eq, hL, incBits_concrete]
  simp only
  rw [const255_mk, incBits_concrete]
  simp only
  obtain ⟨l1, v1⟩ := incB_val (bitsOf x) (decide L)
  obtain ⟨l2, v2⟩ := incB_val (incB (bitsOf x) (decide L)).1 true
  generalize hs1 : incB (bitsOf x) (decide L) = s1 at l1 v1 l2 v2
  generalize hs2 : incB s1.1 true = s2 at l2 v2
  rw [hbx] at l1 v1
  rw [l1] at l2 v2
  have hl : s2.1.length = (bitsOf y).length := by rw [l2, hby]
  rw [const0_mk, compareBits_value _ _ hl]
  apply mk_congr
  have c1 : s1.2 = false := by
    cases h : s1.2
    · rfl
    · rw [h] at v1; simp only [if_true] at v1; by_cases hl' : L <;> simp [hl'] at v1 <;> omega
  have c2 : s2.2 = false := by
    cases h : s2.2
    · rfl
    · rw [h] at v2; rw [c1] at v1; simp only [if_true, if_false, Bool.false_eq_true] at v1 v2
      by_cases hl' : L <;> simp [hl'] at v1 <;> omega
  rw [c1] at v1
  rw [c2] at v2
  simp only [if_false, Bool.false_eq_true, Nat.add_zero, if_true] at v1 v2
  by_cases hl' : L <;> simp [hl'] at v1 ⊢ <;> omega

/-! ### The parse `text` performs

The content is `0A len₁ (0A len₂ body …) …`: field 1 of `Content` (the DataMessage) whose first
field is the body. -/

section
variable (c : List (BitVec 8))

/-- Byte `i` of the content (the plaintext after its 8-byte length prefix). -/
def g (i : Nat) : BitVec 8 := OpenResult.get ByteAuth.concrete c i

/-- The DataMessage's length prefix `len₁` has two bytes: byte 1 has its continuation bit set
(the kernel then requires byte 2 to have it clear). -/
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

/-- Second byte of `len₁` (0 if it has one byte). -/
def outerHigh : BitVec 8 := if Wide c then g c 2 else 0

/-- The DataMessage's length: the value of `len₁`. -/
def dataLength : Nat := (g c 1).toNat % 128 + 128 * (outerHigh c).toNat

/-- The body field (its tag, its prefix `len₂` and the body) lies inside the DataMessage:
`2 + w₁ + w₂ + len₂ ≤ 1 + w₁ + len₁`, i.e. `len₂ + w₂ + 1 ≤ len₁`. -/
def Inside : Prop := bodyLength c + (if Long c then 2 else 1) + 1 ≤ dataLength c

/-- The DataMessage lies inside the content, as the kernel checks it: `1 + w₁ + len₁ ≤ c.length`,
checked only when `c.length < 16386` (above that it always holds for a `len₁` of two bytes). -/
def Fits : Prop :=
  c.length < 16386 → (dataLength c ≤ c.length - 3 ∨ (¬Wide c ∧ dataLength c ≤ c.length - 2))

instance : Decidable (Inside c) := inferInstanceAs (Decidable (_ ≤ _))
instance : Decidable (Fits c) := inferInstanceAs (Decidable (_ → _))

/-- What `receive-text` checks: `0A` at 0 and as the body's tag, `len₂` of at most two bytes, a
body length of at most `capacity`, `len₁` of at most two bytes, the body inside the DataMessage and
the DataMessage inside the content. -/
def Accepted (capacity : Nat) : Prop :=
  g c 0 = ByteAuth.concrete.const 10 ∧ tagByte c = ByteAuth.concrete.const 10 ∧ ¬ 128 ≤ (highByte c).toNat ∧
    bodyLength c ≤ capacity ∧ ¬(Wide c ∧ 128 ≤ (g c 2).toNat) ∧ Inside c ∧ Fits c

instance (capacity : Nat) : Decidable (Accepted c capacity) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

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

theorem all_mk7 (P₁ P₂ P₃ P₄ P₅ P₆ P₇ : Prop) [Decidable P₁] [Decidable P₂] [Decidable P₃] [Decidable P₄]
    [Decidable P₅] [Decidable P₆] [Decidable P₇] :
    all ByteAuth.concrete [mk P₁, mk P₂, mk P₃, mk P₄, mk P₅, mk P₆, mk P₇] =
      mk (P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ P₇) := by
  unfold all
  rw [show ByteAuth.concrete.const 255 = mk True from rfl]
  simp only [List.foldl_cons, List.foldl_nil, mk_and]
  exact mk_congr (by simp only [true_and, and_assoc])

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
  have hsecond : top ByteAuth.concrete (OpenResult.get ByteAuth.concrete c 2) = mk (128 ≤ (g c 2).toNat) := top_mk _
  have houter : ByteAuth.concrete.and (mk (Wide c)) (OpenResult.get ByteAuth.concrete c 2) = outerHigh c := by
    unfold outerHigh mk
    by_cases hw : Wide c <;> simp [hw, and_255, and_0]; rfl
  have hhl := (highByte c).isLt
  have hll := (lowByte c).isLt
  have hol := (outerHigh c).isLt
  have g1l := (g c 1).isLt
  simp only [Nat.reducePow] at hhl hll hol g1l
  have hinside : (compareBits ByteAuth.concrete
      (incBits ByteAuth.concrete (incBits ByteAuth.concrete (maskBits ByteAuth.concrete
        [BitVec.ofNat 8 ((highByte c).toNat / 2),
          BitVec.ofNat 8 ((lowByte c).toNat % 128 + 128 * ((highByte c).toNat % 2))]) (mk (Long c))).1
        (ByteAuth.concrete.const 255)).1
      (maskBits ByteAuth.concrete [BitVec.ofNat 8 ((outerHigh c).toNat / 2),
          BitVec.ofNat 8 ((OpenResult.get ByteAuth.concrete c 1).toNat % 128 + 128 * ((outerHigh c).toNat % 2))])
      (ByteAuth.concrete.const 0) (ByteAuth.concrete.const 255)).1 = mk (Inside c) := by
    rw [inside_value _ _ rfl rfl _ (by rw [val_two_ofNat _ _ (by omega) (by omega)]; omega)]
    apply mk_congr
    have g1l' := (OpenResult.get ByteAuth.concrete c 1).isLt
    simp only [Nat.reducePow] at g1l'
    rw [val_two_ofNat _ _ (by omega) (by omega), val_two_ofNat _ _ (by omega) (by omega)]
    unfold Inside bodyLength dataLength
    simp only [g]
    by_cases hl : Long c <;> simp only [hl, if_true, if_false] <;> omega
  have hfits : whenever ByteAuth.concrete (decide (c.length < 16386))
      (either ByteAuth.concrete (atMost ByteAuth.concrete [BitVec.ofNat 8 ((outerHigh c).toNat / 2),
          BitVec.ofNat 8 ((OpenResult.get ByteAuth.concrete c 1).toNat % 128 + 128 * ((outerHigh c).toNat % 2))]
          (lit ByteAuth.concrete [(c.length - 3) / 256 % 256, (c.length - 3) % 256]))
        (ByteAuth.concrete.and (ByteAuth.concrete.not (mk (Wide c)))
          (atMost ByteAuth.concrete [BitVec.ofNat 8 ((outerHigh c).toNat / 2),
            BitVec.ofNat 8 ((OpenResult.get ByteAuth.concrete c 1).toNat % 128 + 128 * ((outerHigh c).toNat % 2))]
            (lit ByteAuth.concrete [(c.length - 2) / 256 % 256, (c.length - 2) % 256])))) = mk (Fits c) := by
    unfold Fits
    by_cases hL : c.length < 16386
    · simp only [hL, decide_true, whenever, if_true]
      rw [atMost_number _ _ _ (by omega), atMost_number _ _ _ (by omega), mk_not, mk_and, mk_either]
      apply mk_congr
      unfold dataLength g
      simp only [hL, true_implies]
    · simp only [hL, decide_false, whenever, Bool.false_eq_true, if_false]
      exact (mk_true' (False → _) (fun h => h.elim)).symm
  have hok : all ByteAuth.concrete [ByteAuth.eqMask ByteAuth.concrete (OpenResult.get ByteAuth.concrete c 0)
        (ByteAuth.concrete.const 10), ByteAuth.eqMask ByteAuth.concrete (tagByte c) (ByteAuth.concrete.const 10),
        ByteAuth.concrete.not (mk (128 ≤ (highByte c).toNat)),
        atMost ByteAuth.concrete [BitVec.ofNat 8 ((highByte c).toNat / 2),
          BitVec.ofNat 8 ((lowByte c).toNat % 128 + 128 * ((highByte c).toNat % 2))]
          (lit ByteAuth.concrete [capacity / 256 % 256, capacity % 256]),
        ByteAuth.concrete.not (ByteAuth.concrete.and (mk (Wide c)) (mk (128 ≤ (g c 2).toNat))),
        mk (Inside c), mk (Fits c)] = mk (Accepted c capacity) := by
    rw [eqMask_mk, eqMask_mk, mk_not, atMost_number _ _ _ hcap, mk_and, mk_not, all_mk7]
    rfl
  simp only [hwide, hlow, htag, hlong, hhigh, hhighTop, lengthBytes_eq, hsecond, houter, hinside, hfits, hok]
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

/-- **The former counterexample, now refused.** A content whose DataMessage is 3 bytes long
(`0A 03 …`) but whose body claims 5 bytes (`0A 05 …`): a protobuf decoder rejects it, since the body
runs past the DataMessage (`overlongBody_reference`). Before the emitter batch `receive-text`
accepted it and opened 5 bytes, four of them outside the DataMessage. It now checks
`len₂ + w₂ + 1 ≤ len₁`, so the status is 0 and nothing is opened. -/
def overlongBodyPlain : List (BitVec 8) :=
  List.replicate 8 0 ++ [0x0A, 0x03, 0x0A, 0x05, 0x61, 0x62, 0x63, 0x64, 0x65] ++ List.replicate 7 0

theorem overlongBody_refused :
    text ByteAuth.concrete 10 overlongBodyPlain =
      [[0], [0, 0], List.replicate 10 0, [0, 0, 0]] := by
  decide

theorem overlongBody_reference : referenceBody (overlongBodyPlain.drop 8) = none := by
  decide

/-! ### The kernel's checks are the reference's, for length prefixes of at most two bytes -/

section
variable (c : List (BitVec 8))

/-- Width of `len₁`. -/
def width₁ : Nat := if Wide c then 2 else 1

/-- Width of `len₂`. -/
def width₂ : Nat := if Long c then 2 else 1

/-- Both length prefixes have at most two bytes (the widths the kernel covers). -/
def Covered : Prop :=
  ((g c 1).toNat < 128 ∨ (g c 2).toNat < 128) ∧ ((lowByte c).toNat < 128 ∨ (highByte c).toNat < 128)

end

theorem covered_iff (c : List (BitVec 8)) :
    Covered c ↔ ¬(Wide c ∧ 128 ≤ (g c 2).toNat) ∧ ¬ 128 ≤ (highByte c).toNat := by
  unfold Covered Wide highByte Long
  by_cases hl : 128 ≤ (lowByte c).toNat
  · simp only [hl, if_true]; omega
  · simp only [hl, if_false]
    have : (0 : BitVec 8).toNat = 0 := rfl
    rw [this]; omega

theorem low_at (c : List (BitVec 8)) : lowByte c = g c (2 + width₁ c) := by
  unfold lowByte width₁; by_cases hw : Wide c <;> simp [hw]

theorem tag_at (c : List (BitVec 8)) : tagByte c = g c (1 + width₁ c) := by
  unfold tagByte width₁; by_cases hw : Wide c <;> simp [hw]

theorem start_at (c : List (BitVec 8)) : bodyStart c = 2 + width₁ c + width₂ c := by
  unfold bodyStart width₁ width₂; by_cases hw : Wide c <;> by_cases hl : Long c <;> simp [hw, hl] <;> omega

theorem outerHigh_lt (c : List (BitVec 8)) (h2 : ¬(Wide c ∧ 128 ≤ (g c 2).toNat)) : (outerHigh c).toNat < 128 := by
  unfold outerHigh
  by_cases hw : Wide c
  · simp only [hw, if_true]; exact Nat.lt_of_not_le (fun h => h2 ⟨hw, h⟩)
  · simp only [hw, if_false]; decide

/-- The reference reads `len₁` as the kernel does when its second byte has no continuation bit. -/
theorem varint₁ (c : List (BitVec 8)) (h2 : ¬(Wide c ∧ 128 ≤ (g c 2).toNat)) :
    varintAt c 1 10 = some (dataLength c, width₁ c) := by
  unfold dataLength outerHigh width₁
  by_cases hw : Wide c
  · have h2' : (g c 2).toNat < 128 := Nat.lt_of_not_le (fun h => h2 ⟨hw, h⟩)
    have hw' : ¬ (g c 1).toNat < 128 := by unfold Wide at hw; omega
    simp only [hw, if_true]
    simp [varintAt, h2', hw']
  · have hw' : (g c 1).toNat < 128 := by unfold Wide at hw; omega
    simp only [hw, if_false]
    simp [varintAt, hw']
    omega

/-- The reference reads `len₂` as the kernel does when its second byte has no continuation bit. -/
theorem varint₂ (c : List (BitVec 8)) (hh : ¬ 128 ≤ (highByte c).toNat) :
    varintAt c (2 + width₁ c) 10 = some (bodyLength c, width₂ c) := by
  have hlow := low_at c
  have hhighAt : (if Wide c then g c 5 else g c 4) = g c (3 + width₁ c) := by
    unfold width₁; by_cases hw : Wide c <;> simp [hw]
  unfold width₂ bodyLength
  by_cases hl : Long c
  · have hl' : 128 ≤ (g c (2 + width₁ c)).toNat := by unfold Long at hl; rw [hlow] at hl; exact hl
    have hhb : highByte c = g c (3 + width₁ c) := by unfold highByte; rw [if_pos hl, hhighAt]
    have h3 : (g c (3 + width₁ c)).toNat < 128 := by rw [← hhb]; omega
    rw [if_pos hl, hhb, hlow]
    simp [varintAt, show ¬ (g c (2 + width₁ c)).toNat < 128 by omega, show 2 + width₁ c + 1 = 3 + width₁ c by omega,
      h3]
  · have hl' : (g c (2 + width₁ c)).toNat < 128 := by unfold Long at hl; rw [hlow] at hl; omega
    have hhb : highByte c = 0 := by unfold highByte; rw [if_neg hl]
    rw [if_neg hl, hhb, hlow]
    simp [varintAt, hl']
    omega

/-- **The reference on a covered content**, as one condition. -/
theorem referenceBody_eq (c : List (BitVec 8)) (h2 : ¬(Wide c ∧ 128 ≤ (g c 2).toNat))
    (hh : ¬ 128 ≤ (highByte c).toNat) :
    referenceBody c =
      if g c 0 = ByteAuth.concrete.const 10 ∧ 1 + width₁ c + dataLength c ≤ c.length ∧ 1 ≤ dataLength c ∧
          tagByte c = ByteAuth.concrete.const 10 ∧
          2 + width₁ c + width₂ c + bodyLength c ≤ 1 + width₁ c + dataLength c
      then some (Establish.part c (bodyStart c) (bodyLength c)) else none := by
  unfold referenceBody
  rw [varint₁ c h2]
  simp only
  rw [← tag_at, varint₂ c hh, start_at]
  simp only
  by_cases h0 : g c 0 = ByteAuth.concrete.const 10
  · by_cases h1 : 1 + width₁ c + dataLength c ≤ c.length ∧ 1 ≤ dataLength c ∧ tagByte c = ByteAuth.concrete.const 10
    · by_cases h3 : 2 + width₁ c + width₂ c + bodyLength c ≤ 1 + width₁ c + dataLength c
      · rw [if_pos h0, if_pos h1, if_pos h3, if_pos ⟨h0, h1.1, h1.2.1, h1.2.2, h3⟩]
      · rw [if_pos h0, if_pos h1, if_neg h3, if_neg (fun h => h3 h.2.2.2.2)]
    · rw [if_pos h0, if_neg h1, if_neg (fun h => h1 ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩)]
  · rw [if_neg h0, if_neg (fun h => h0 h.1)]

theorem part_length_of (c : List (BitVec 8)) (s n : Nat) (h : s + n ≤ c.length) : (Establish.part c s n).length = n := by
  rw [Establish.part, List.length_take, List.length_drop]; omega

/-- **`receive-text` accepts exactly what the reference accepts** (for both length prefixes of at
most two bytes and a body that fits `capacity`). -/
theorem accepted_iff_reference (capacity : Nat) (c : List (BitVec 8)) :
    Accepted c capacity ↔ (∃ body, referenceBody c = some body ∧ body.length ≤ capacity) ∧ Covered c := by
  rw [covered_iff]
  have hol := (outerHigh c).isLt
  have g1l := (g c 1).isLt
  simp only [Nat.reducePow] at hol g1l
  have hw1 : width₁ c = if Wide c then 2 else 1 := rfl
  have hw2 : width₂ c = if Long c then 2 else 1 := rfl
  constructor
  · intro h
    obtain ⟨h0, htag, hh, hcap, h2, hin, hfit⟩ := h
    have hdl : dataLength c ≤ 16383 := by
      have := outerHigh_lt c h2; unfold dataLength; omega
    have hpos : 2 ≤ dataLength c := by unfold Inside at hin; split at hin <;> omega
    have hfit' : 1 + width₁ c + dataLength c ≤ c.length := by
      by_cases hL : c.length < 16386
      · rcases hfit hL with h | ⟨hw, h⟩
        · rw [hw1]; split <;> omega
        · rw [hw1, if_neg hw]; omega
      · rw [hw1]; split <;> omega
    have hin' : 2 + width₁ c + width₂ c + bodyLength c ≤ 1 + width₁ c + dataLength c := by
      unfold Inside at hin; rw [hw2]; omega
    refine ⟨⟨Establish.part c (bodyStart c) (bodyLength c), ?_, ?_⟩, h2, hh⟩
    · rw [referenceBody_eq c h2 hh, if_pos ⟨h0, hfit', by unfold Inside at hin; omega, htag, hin'⟩]
    · rw [part_length_of c _ _ (by rw [start_at]; omega)]; exact hcap
  · rintro ⟨⟨body, href, hcap⟩, h2, hh⟩
    rw [referenceBody_eq c h2 hh] at href
    by_cases hc : g c 0 = ByteAuth.concrete.const 10 ∧ 1 + width₁ c + dataLength c ≤ c.length ∧ 1 ≤ dataLength c ∧
        tagByte c = ByteAuth.concrete.const 10 ∧ 2 + width₁ c + width₂ c + bodyLength c ≤ 1 + width₁ c + dataLength c
    · rw [if_pos hc, Option.some.injEq] at href
      obtain ⟨h0, hfit, _, htag, hin⟩ := hc
      have hlen : body.length = bodyLength c := by
        rw [← href, part_length_of c _ _ (by rw [start_at]; omega)]
      refine ⟨h0, htag, hh, by omega, h2, ?_, ?_⟩
      · unfold Inside; rw [hw2] at hin; omega
      · intro _
        rw [hw1] at hfit
        by_cases hw : Wide c
        · left; rw [if_pos hw] at hfit; omega
        · right; rw [if_neg hw] at hfit; exact ⟨hw, by omega⟩
    · rw [if_neg hc] at href; cases href

/-- **`receive-text`'s status is 255 exactly when the reference parses the content** (both length
prefixes of at most two bytes, body of at most `capacity` bytes), and 0 otherwise. -/
theorem text_status_iff_reference (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8)) :
    (text ByteAuth.concrete capacity plain).getD 0 [] = [255] ↔
      (∃ body, referenceBody (plain.drop 8) = some body ∧ body.length ≤ capacity) ∧ Covered (plain.drop 8) := by
  rw [text_status capacity hcap plain, ← accepted_iff_reference, List.cons.injEq, mk_eq_255]
  simp

/-- The opened text, when accepted, is the reference body. -/
theorem opened_reference (capacity : Nat) (c body : List (BitVec 8)) (h : Accepted c capacity)
    (href : referenceBody c = some body) :
    bodyLength c = body.length ∧
      (List.range capacity).map (fun i => if i < bodyLength c then g c (bodyStart c + i) else 0) =
        (List.range capacity).map (fun i => body.getD i 0) := by
  have h2 := h.2.2.2.2.1
  have hh := h.2.2.1
  obtain ⟨⟨body', href', _⟩, _⟩ := (accepted_iff_reference capacity c).mp h
  rw [href] at href'
  cases href'
  rw [referenceBody_eq c h2 hh] at href
  split at href
  · rename_i hc
    rw [Option.some.injEq] at href
    have hstart := start_at c
    have hlen : body.length = bodyLength c := by
      rw [← href, part_length_of c _ _ (by rw [hstart]; omega)]
    refine ⟨hlen.symm, ?_⟩
    apply List.map_congr_left
    intro i _
    rw [← href]
    by_cases hi : i < bodyLength c
    · rw [if_pos hi]
      simp only [g, OpenResult.get, Establish.part, List.getD_eq_getElem?_getD, List.getElem?_take, hi, if_true,
        List.getElem?_drop]
      rfl
    · rw [if_neg hi]
      simp [Establish.part, List.getD_eq_getElem?_getD, List.getElem?_take, hi]
  · cases href

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
  have hacc : Accepted (plain.drop 8) capacity :=
    (accepted_iff_reference capacity _).mpr ⟨⟨body, href, hfit⟩, hw₁, hw₂⟩
  exact ⟨hacc, opened_reference capacity _ body hacc href⟩

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

/-- **Accept direction, at the level of `receive-text`'s outputs**: whenever `receive-text`'s
status is 255, the reference parses the content, its prefixes are covered, the body fits, and the
opened length and text are exactly the reference body's. -/
theorem text_accepted_reference (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8))
    (h : (text ByteAuth.concrete capacity plain).getD 0 [] = [255]) :
    ∃ body, referenceBody (plain.drop 8) = some body ∧ body.length ≤ capacity ∧ Covered (plain.drop 8) ∧
      text ByteAuth.concrete capacity plain =
        [[255], [BitVec.ofNat 8 (body.length / 256), BitVec.ofNat 8 (body.length % 256)],
          (List.range capacity).map (fun i => body.getD i 0),
          [mk (bodyStart (plain.drop 8) = 4), mk (bodyStart (plain.drop 8) = 5), mk (bodyStart (plain.drop 8) = 6)]] := by
  obtain ⟨⟨body, href, hfit⟩, hcov⟩ := (text_status_iff_reference capacity hcap plain).mp h
  exact ⟨body, href, hfit, hcov, text_reference capacity hcap plain body href hcov.1 hcov.2 hfit⟩

end TlsMpc.KernelSpecs.ReceiveAcceptText
