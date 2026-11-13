import TlsMpc.Node.Flows.ConvertBase
import TlsMpc.Node.Flows.RunLemmas
import TlsMpc.Node.Flows.MasksProofs

/-!
# Conversions between the engines (P-W2F, P-F2W, P-PAIR / P-B2F, P-BITS)

REORGANIZATION_PLAN.md 7.1, stage S10. Replaces `tls_kernels.h` `word_to_field` (82-90),
`bits_to_field` (58-72), `shared_scalar` / `swap_bit` (44-80) and `dyn_word_mask.h`
`field_to_word` (123-131) for the Lean flows. Each conversion consumes masks from the pool
(`Masks.generate`), uses them in exactly one `run` or `program`, and FREES them in both engines at
the end, so the shell's `check` (an operand must be live) refuses any second use: single use (P-CUT
(h)) is enforced by the engine's handle table as well as by the pool (`MaskPool.take*_fresh`).

THE SCRIPTS (handles: Boolean ids from `n0`, field ids from `f0`, fresh blocks):
  * `wordToField n0 f0 u m` (P-W2F): `into-field-open` on (u, w); open c = (u mod p + r) mod p;
    check canonical; re-compare c with the peer (`exchange`, plan default: kept as today); return
    `public(c) − f`.
  * `fieldToWord n0 f0 v m` (P-F2W): `field-mask-sub` on (v, f) (its output is declared public);
    open c = v − f; re-compare; `modadd` on (w, public c): the word of (r + c) mod p = v.
  * `bitsToField n0 f0 x ps` (P-PAIR / P-B2F): `xor-bit-open` on the interleaving of x and the pairs'
    Boolean bits ρ; open o = x ⊕ ρ; per bit `1 − ρ_field` when o = 1, else `ρ_field − 0`.
  * `sharedBits f0 n slot` (P-BITS): both parties input their local bits as field coins; open the
    `field-bit-check` of all 2n inputs (must be 0); return the `field-bit-xor` of the two parties'.

PROVED (ideal model, `WordLoaded` / `ProgsLoaded` for the circuits and programs named):
  * W2F: `w2f_disclosure` (T3: the adversary sees exactly c, twice: the opening and the
    re-comparison), `w2f_honest` (P-W2F (a): two honest parties end with the field value u mod p),
    `w2f_open_bijective` / `w2f_hides` (P-W2F (b): for a fixed u, r ↦ c is a bijection of [0, p);
    7.0 form: for any two words the transcripts correspond under r ↦ r + u − u′ mod p).
  * F2W: `f2w_disclosure`, `f2w_honest` (P-F2W (a): the word of v), `f2w_hides` (P-F2W (b):
    f ↦ v − f is a bijection of F).
  * B2F: `b2f_disclosure`, `b2f_value` (P-B2F (a): for a consistent pair the result is x's bit),
    `b2f_hides` (P-B2F (b): ρ ↦ x ⊕ ρ is a bijection, its own inverse).
  * BITS: `bits_checks_zero_iff` (P-BITS (a): the checks open to 0 iff every input of both parties
    is 0 or 1, with `FieldInverse`), `bits_xor` (P-BITS (b): honest inputs give the bits of the XOR;
    with `X25519SwapBits.swapBit_shares`, the swap bits of the XORed scalar), `bits_honest_checks`
    (P-BITS (c): an honest party's checks are the constant 0).
  * `*_reveals`: the kinds each declares; `*_once` (P-*(c)): the pool after a take holds no handle
    of the mask used, and the script frees it.
-/

namespace TlsMpc.Node.Flows.Convert

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire every_seq every_seqs every_openThen)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus ofNat)

abbrev W : Nat := 255

/-! ## Field arithmetic in `P` terms -/

theorem fval_lt (x : F) : x.val < P := by
  rw [P_modulus]
  exact x.isLt

theorem ofNat_val (n : Nat) : (ofNat n).val = n % P := by
  show (Fin.ofNat modulus n).val = n % P
  rw [Fin.val_ofNat, P_modulus]

theorem fsub_val (a b : F) : (a - b).val = ((P - b.val) + a.val) % P := by
  rw [Fin.val_sub, P_modulus]

/-- One copy of a circuit on exactly its input width. -/
theorem runCopies_one (c : Circuit) (v : Bits) (h : v.length = c.inWidth) : runCopies c 1 v = c.eval v := by
  simp [runCopies, List.take_of_length_le (Nat.le_of_eq h)]

theorem intoFieldEval_pair (a b : Bits) (ha : a.length = W) (hb : b.length = W) :
    intoFieldEval (a ++ b) = word (addModSpec (reduceSpec (natOf a)) (natOf b)) := by
  have hx : wordX (a ++ b) = natOf a := by simp [wordX, List.take_left' ha]
  have hy : wordY (a ++ b) = natOf b := by simp [wordY, List.drop_left' ha, List.take_of_length_le (Nat.le_of_eq hb)]
  simp only [intoFieldEval, hx, hy]

theorem modaddEval_pair' (a b : Bits) (ha : a.length = W) (hb : b.length = W) :
    modaddEval (a ++ b) = word (addModSpec (natOf a) (natOf b)) := by
  have hx : wordX (a ++ b) = natOf a := by simp [wordX, List.take_left' ha]
  have hy : wordY (a ++ b) = natOf b := by simp [wordY, List.drop_left' ha, List.take_of_length_le (Nat.le_of_eq hb)]
  simp only [modaddEval, hx, hy]

/-- The value word to field opens: `(u mod p + r) mod p`. -/
def w2fOpen (u r : Nat) : Nat := (u % P + r) % P

theorem intoField_value (ub wb : Bits) (hu : ub.length = W) (hw : wb.length = W) (hr : natOf wb < P) :
    intoFieldEval (ub ++ wb) = word (w2fOpen (natOf ub) (natOf wb)) := by
  rw [intoFieldEval_pair _ _ hu hw, reduceSpec_eq _ (by have := natOf_lt ub; rw [hu] at this; exact this),
    addModSpec_canonical _ _ (Nat.mod_lt _ (by decide)) hr]
  rfl

/-! ## Word to field (P-W2F) -/

/-- The instructions after the comparison. -/
def w2fTail (n0 f0 : Nat) (m : WordMask) (c : Nat) : List Instr :=
  [.fieldPublic ⟨f0⟩ (ofNat c), .fieldSub ⟨f0 + 1⟩ ⟨f0⟩ m.field,
   .freeBool ⟨n0⟩, .freeBool ⟨n0 + 1⟩, .freeBool m.bits, .freeField m.field, .freeField ⟨f0⟩]

/-- After the opening: check canonical, re-compare with the peer, unmask. -/
def w2fRest (n0 f0 : Nat) (m : WordMask) (c : Bits) : Script FieldH :=
  if c.length = W ∧ natOf c < P then
    sayThen 32 Label.maskedWord (le 32 (natOf c)) fun peer =>
      if peer = le 32 (natOf c) then seqs (w2fTail n0 f0 m (natOf c)) (.done ⟨f0 + 1⟩)
      else .abort "public masked value disagreement"
  else .abort "noncanonical masked word"

/-- **Word to field.** `u`: 255 private bits; `m`: a word mask from the pool. -/
def wordToField (n0 f0 : Nat) (u : BoolH) (m : WordMask) : Script FieldH :=
  seqs [.concat ⟨n0⟩ [u, m.bits], .run ⟨n0 + 1⟩ intoFieldOpenName 1 ⟨n0⟩] <|
  openThen ⟨n0 + 1⟩ Label.maskedWord (w2fRest n0 f0 m)

theorem w2fTail_local (n0 f0 : Nat) (m : WordMask) (c : Nat) : ∀ i ∈ w2fTail n0 f0 m c, isLocal i = true := by
  intro i hi
  simp only [w2fTail, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def w2fKinds : List TlsMpc.Node.RevealKind := [.maskedWord]

theorem w2f_reveals (n0 f0 : Nat) (u : BoolH) (m : WordMask) : Reveals w2fKinds (wordToField n0 f0 u m) := by
  unfold wordToField
  refine every_seqs (every_openThen (LabelIn.of_mem (k := .maskedWord) (by simp [w2fKinds]) rfl) fun c => ?_) _
    (fun i hi => ?_)
  · unfold w2fRest
    split
    · refine every_sayThen (LabelIn.of_mem (k := .maskedWord) (by simp [w2fKinds]) rfl) fun r => ?_
      split
      · exact every_seqs (Every.done _) _ (fun i hi => LabelIn.of_none (label_local i (w2fTail_local n0 f0 m _ i hi)))
      · exact Every.abort _
    · exact Every.abort _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact LabelIn.of_none rfl

section W2F

variable (E : Env) (me : Party) (adv : Adversary) (n0 f0 : Nat) (u : BoolH) (m : WordMask)

theorem w2f_block (hW : WordLoaded E) (I : Ideal) (ub wb : Bits) (hu : I.bools u.id = some ub)
    (hm : I.bools m.bits.id = some wb) (hlu : ub.length = W) (hlw : wb.length = W) :
    runLocal E [.concat ⟨n0⟩ [u, m.bits], .run ⟨n0 + 1⟩ intoFieldOpenName 1 ⟨n0⟩] I =
      some ((I.setBool ⟨n0⟩ (ub ++ wb)).setBool ⟨n0 + 1⟩ (intoFieldEval (ub ++ wb))) := by
  have hl : (ub ++ wb).length = intoFieldOpenC.inWidth := by simp [hlu, hlw, intoFieldOpenC, W]
  have hw : intoFieldOpenC.inWidth = 510 := rfl
  have he : intoFieldOpenC.eval = intoFieldEval := rfl
  simp [runLocal, localStep, idealStep, blankWire, InstrP.map, hu, hm, hW.intoFieldOpen, Ideal.setBool,
    hlu, hlw, hw, runCopies_one intoFieldOpenC _ hl, he, W]

/-- **T3 for word to field.** The adversary's view is a prefix of [c, c]: the opened
`(u mod p + r) mod p` (Boolean, `maskedWord`) and its 32-byte re-comparison (`maskedWord`). -/
theorem w2f_disclosure (hW : WordLoaded E) (σ : Store) (I : Ideal) (vD : List Release) (ub wb : Bits)
    (hu : I.bools u.id = some ub) (hm : I.bools m.bits.id = some wb) (hlu : ub.length = W) (hlw : wb.length = W) :
    (withAdv E me adv (wordToField n0 f0 u m) σ I vD).viewD <+:
      [⟨Label.maskedWord, .bits (intoFieldEval (ub ++ wb))⟩,
       ⟨Label.maskedWord, .bytes (le 32 (natOf (intoFieldEval (ub ++ wb))))⟩] := by
  unfold wordToField
  refine viewD_locals E me adv _ σ _ _ (by simp [isLocal]) I vD (fun I1 h1 => ?_)
  rw [w2f_block E n0 u m hW I ub wb hu hm hlu hlw, Option.some.injEq] at h1
  subst h1
  refine TlsMpc.Node.Flows.Contacts.viewD_openThen E me adv _ _ _ σ _ vD _ _ (by simp [Ideal.setBool]) ?_
  unfold w2fRest
  split
  · refine viewD_sayThen E me adv _ _ _ _ σ _ _ _ (by simp [length_le]) (fun r => ?_)
    split
    · exact TlsMpc.Node.Flows.Contacts.silent_prefix E me adv _
        (silent_locals (Silent.done _) _ (w2fTail_local n0 f0 m _)) _ _ _ _
    · exact TlsMpc.Node.Flows.Contacts.silent_prefix E me adv _ (Silent.abort _) _ _ _ _
  · exact TlsMpc.Node.Flows.Contacts.silent_prefix E me adv _ (Silent.abort _) _ _ _ _

/-- The unmasking identity in F: `ofNat c − f = ofNat u` for `c = (u mod p + f) mod p`. -/
theorem unmask_word (uval : Nat) (fv : F) :
    ofNat (w2fOpen uval fv.val) - fv = ofNat uval := by
  apply Fin.ext
  rw [fsub_val, ofNat_val, ofNat_val, w2fOpen, Nat.mod_mod]
  have h := TlsMpc.WordMask.into_field_roundtrip uval fv.val (fval_lt fv)
  rw [Nat.add_comm (P - fv.val)]
  exact h

/-- **P-W2F (a).** Two honest parties with a consistent mask (`val(w) = f`, canonical) end with
the field handle `f0 + 1` holding `u mod p` (as an element: `ofNat (val u)`). -/
theorem w2f_honest (hW : WordLoaded E) (σA σB : Store) (I : Ideal) (ub wb : Bits) (fv : F)
    (hu : I.bools u.id = some ub) (hm : I.bools m.bits.id = some wb) (hlu : ub.length = W) (hlw : wb.length = W)
    (hf : I.fields m.field.id = some fv) (hcons : natOf wb = fv.val)
    (hf0 : m.field.id ≠ f0) (hf1 : m.field.id ≠ f0 + 1) :
    (jointRun E (wordToField n0 f0 u m) (wordToField n0 f0 u m) σA σB I).result = some (⟨f0 + 1⟩, ⟨f0 + 1⟩) ∧
      (jointRun E (wordToField n0 f0 u m) (wordToField n0 f0 u m) σA σB I).ideal.fields (f0 + 1) =
        some (ofNat (natOf ub)) := by
  have hr : natOf wb < P := by rw [hcons]; exact fval_lt fv
  have hval := intoField_value ub wb hlu hlw hr
  have hc : (word (w2fOpen (natOf ub) (natOf wb))).length = W ∧ natOf (word (w2fOpen (natOf ub) (natOf wb))) < P := by
    refine ⟨length_word _, ?_⟩
    rw [natOf_word _ (by have := Nat.mod_lt (natOf ub % P + natOf wb) (by decide : 0 < P); have := P_lt_two_pow; unfold w2fOpen; omega)]
    exact Nat.mod_lt _ (by decide)
  have hc' : natOf (word (w2fOpen (natOf ub) (natOf wb))) = w2fOpen (natOf ub) (natOf wb) :=
    natOf_word _ (by have := Nat.mod_lt (natOf ub % P + natOf wb) (by decide : 0 < P); have := P_lt_two_pow; unfold w2fOpen; omega)
  unfold wordToField
  obtain ⟨r1, i1⟩ := jointRun_locals E _ _ σA σB _ (by simp [isLocal]) I _ (w2f_block E n0 u m hW I ub wb hu hm hlu hlw)
  rw [r1, i1]
  have hopen : ((I.setBool ⟨n0⟩ (ub ++ wb)).setBool ⟨n0 + 1⟩ (intoFieldEval (ub ++ wb))).bools (n0 + 1) =
      some (word (w2fOpen (natOf ub) (natOf wb))) := by simp [Ideal.setBool, hval]
  obtain ⟨r2, i2⟩ := TlsMpc.Node.Flows.Contacts.jointRun_openThen E ⟨n0 + 1⟩ Label.maskedWord (w2fRest n0 f0 m)
    (w2fRest n0 f0 m) σA σB _ _ hopen
  rw [r2, i2]
  unfold w2fRest
  rw [if_pos hc]
  obtain ⟨r3, i3⟩ := jointRun_sayThen E 32 Label.maskedWord
    (le 32 (natOf (word (w2fOpen (natOf ub) (natOf wb))))) (le 32 (natOf (word (w2fOpen (natOf ub) (natOf wb)))))
    _ _ σA σB ((I.setBool ⟨n0⟩ (ub ++ wb)).setBool ⟨n0 + 1⟩ (intoFieldEval (ub ++ wb)))
    (length_le _ _) (length_le _ _)
  rw [r3, i3, if_pos rfl, hc']
  -- the tail
  have htail : runLocal E (w2fTail n0 f0 m (w2fOpen (natOf ub) (natOf wb)))
      ((I.setBool ⟨n0⟩ (ub ++ wb)).setBool ⟨n0 + 1⟩ (intoFieldEval (ub ++ wb))) =
      some ((((((((I.setBool ⟨n0⟩ (ub ++ wb)).setBool ⟨n0 + 1⟩ (intoFieldEval (ub ++ wb))).setField ⟨f0⟩
        (ofNat (w2fOpen (natOf ub) (natOf wb)))).setField ⟨f0 + 1⟩ (ofNat (w2fOpen (natOf ub) (natOf wb)) - fv)).dropBool
        ⟨n0⟩).dropBool ⟨n0 + 1⟩).dropBool m.bits).dropField m.field |>.dropField ⟨f0⟩) := by
    simp [w2fTail, runLocal, localStep, idealStep, blankWire, InstrP.map, Ideal.setField, Ideal.setBool, hf, hf0]
  obtain ⟨r4, i4⟩ := jointRun_locals E (.done (⟨f0 + 1⟩ : FieldH)) (.done (⟨f0 + 1⟩ : FieldH)) σA σB _
    (w2fTail_local n0 f0 m _) _ _ htail
  rw [r4, i4]
  refine ⟨rfl, ?_⟩
  simp [jointRun, Ideal.dropField, Ideal.dropBool, Ideal.setField, Ne.symm hf1, hcons, unmask_word]

/-- **P-W2F (b).** For a fixed word u, r ↦ (u mod p + r) mod p is a bijection of [0, p): it maps
[0, p) into [0, p) and has the inverse c ↦ (c + p − u mod p) mod p. -/
theorem w2f_open_bijective (uval : Nat) :
    (∀ r < P, w2fOpen uval r < P) ∧ (∀ r < P, (w2fOpen uval r + (P - uval % P)) % P = r) ∧
      (∀ c < P, w2fOpen uval ((c + (P - uval % P)) % P) = c) := by
  have hu := Nat.mod_lt uval (by decide : 0 < P)
  refine ⟨fun r _ => Nat.mod_lt _ (by decide), fun r hr => ?_, fun c hc => ?_⟩
  · unfold w2fOpen
    generalize uval % P = a at hu ⊢
    rw [P_eq] at *
    omega
  · unfold w2fOpen
    generalize uval % P = a at hu ⊢
    rw [P_eq] at *
    omega

/-- **P-W2F (b), plan 7.0's form.** For any two words u, u′ and every mask r < p, the opened value
for (u, r) equals the opened value for (u′, σ r) with σ r = (r + u − u′) mod p, and σ is a
bijection of [0, p). So the adversary's view (c, and its re-comparison) is the same function of
the mask whichever word is converted. -/
theorem w2f_hides (u u' : Nat) :
    ∃ σ : Nat → Nat, (∀ r < P, σ r < P) ∧ (∃ τ : Nat → Nat, ∀ r < P, τ (σ r) = r) ∧
      ∀ r < P, w2fOpen u r = w2fOpen u' (σ r) := by
  refine ⟨fun r => (r + u % P + (P - u' % P)) % P, fun r _ => Nat.mod_lt _ (by decide),
    ⟨fun s => (s + u' % P + (P - u % P)) % P, fun r hr => ?_⟩, fun r hr => ?_⟩
  · dsimp only
    have h1 := Nat.mod_lt u (by decide : 0 < P)
    have h2 := Nat.mod_lt u' (by decide : 0 < P)
    generalize u % P = a at *
    generalize u' % P = b at *
    rw [P_eq] at *
    omega
  · unfold w2fOpen
    dsimp only
    have h1 := Nat.mod_lt u (by decide : 0 < P)
    have h2 := Nat.mod_lt u' (by decide : 0 < P)
    generalize u % P = a at *
    generalize u' % P = b at *
    rw [P_eq] at *
    omega

end W2F

/-! ## Field to word (P-F2W) -/

def f2wTail (n0 f0 : Nat) (m : WordMask) (c : F) : List Instr :=
  [.boolPublic ⟨n0⟩ (word c.val), .concat ⟨n0 + 1⟩ [m.bits, ⟨n0⟩], .run ⟨n0 + 2⟩ modaddName 1 ⟨n0 + 1⟩,
   .freeBool ⟨n0⟩, .freeBool ⟨n0 + 1⟩, .freeBool m.bits, .freeField m.field, .freeField ⟨f0⟩]

def f2wRest (n0 f0 : Nat) (m : WordMask) (cs : List F) : Script BoolH :=
  match cs with
  | [c] =>
    sayThen 32 Label.maskedFieldValue (le 32 c.val) fun peer =>
      if peer = le 32 c.val then seqs (f2wTail n0 f0 m c) (.done ⟨n0 + 2⟩)
      else .abort "public masked value disagreement"
  | _ => .abort "reply shape"

/-- **Field to word.** `v`: a field handle; `m`: a word mask from the pool. The result: 255 private
bits holding v's canonical value. -/
def fieldToWord (n0 f0 : Nat) (v : FieldH) (m : WordMask) : Script BoolH :=
  seq (.program maskSubName 1 [v, m.field] [] [⟨f0⟩] Label.maskedFieldValue) <|
  openFieldThen [⟨f0⟩] Label.maskedFieldValue (f2wRest n0 f0 m)

theorem f2wTail_local (n0 f0 : Nat) (m : WordMask) (c : F) : ∀ i ∈ f2wTail n0 f0 m c, isLocal i = true := by
  intro i hi
  simp only [f2wTail, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def f2wKinds : List TlsMpc.Node.RevealKind := [.maskedFieldValue]

theorem f2w_reveals (n0 f0 : Nat) (v : FieldH) (m : WordMask) : Reveals f2wKinds (fieldToWord n0 f0 v m) := by
  unfold fieldToWord
  refine every_seq (LabelIn.of_mem (k := .maskedFieldValue) (by simp [f2wKinds]) rfl)
    (every_openFieldThen (LabelIn.of_mem (k := .maskedFieldValue) (by simp [f2wKinds]) rfl) fun cs => ?_)
  unfold f2wRest
  split
  · refine every_sayThen (LabelIn.of_mem (k := .maskedFieldValue) (by simp [f2wKinds]) rfl) fun r => ?_
    split
    · exact every_seqs (Every.done _) _ (fun i hi => LabelIn.of_none (label_local i (f2wTail_local n0 f0 m _ i hi)))
    · exact Every.abort _
  · exact Every.abort _

section F2W

variable (E : Env) (me : Party) (adv : Adversary) (n0 f0 : Nat) (v : FieldH) (m : WordMask)

theorem maskSub_run (vv fv : F) : runProgram maskSub 1 [vv, fv] [] = some ([vv - fv], []) := by
  unfold runProgram
  rw [if_pos ⟨rfl, rfl⟩]
  rfl

/-- **T3 for field to word.** The adversary's view is a prefix of [the program's (empty) openings,
c = v − f, its 32-byte re-comparison], all labelled `maskedFieldValue`. -/
theorem f2w_disclosure (hP : ProgsLoaded E) (σ : Store) (I : Ideal) (vD : List Release) (vv fv : F)
    (hv : I.fields v.id = some vv) (hf : I.fields m.field.id = some fv) :
    (withAdv E me adv (fieldToWord n0 f0 v m) σ I vD).viewD <+:
      [⟨Label.maskedFieldValue, .elems []⟩, ⟨Label.maskedFieldValue, .elems [vv - fv]⟩,
       ⟨Label.maskedFieldValue, .bytes (le 32 (vv - fv).val)⟩] := by
  unfold fieldToWord
  refine viewD_program E me adv _ _ _ _ _ _ _ σ I vD _ maskSub [vv, fv] [] [vv - fv] [] hP.maskSub
    (by simp [hv, hf]) rfl (maskSub_run vv fv) rfl ?_
  refine viewD_openFieldThen E me adv _ _ _ σ _ _ [vv - fv] _ (by simp [Ideal.setFields, Ideal.setField]) ?_
  refine viewD_sayThen E me adv _ _ _ _ σ _ _ _ (by simp [length_le]) (fun r => ?_)
  split
  · exact TlsMpc.Node.Flows.Contacts.silent_prefix E me adv _
      (silent_locals (Silent.done _) _ (f2wTail_local n0 f0 m _)) _ _ _ _
  · exact TlsMpc.Node.Flows.Contacts.silent_prefix E me adv _ (Silent.abort _) _ _ _ _

/-- **P-F2W (a).** Two honest parties with a consistent mask end with the Boolean handle `n0 + 2`
holding the 255 bits of v's canonical value. -/
theorem f2w_honest (hW : WordLoaded E) (hP : ProgsLoaded E) (σA σB : Store) (I : Ideal) (vv fv : F) (wb : Bits)
    (hv : I.fields v.id = some vv) (hf : I.fields m.field.id = some fv) (hm : I.bools m.bits.id = some wb)
    (hlw : wb.length = W) (hcons : natOf wb = fv.val)
    (hb0 : m.bits.id ≠ n0) (hb2 : m.bits.id ≠ n0 + 2) :
    (jointRun E (fieldToWord n0 f0 v m) (fieldToWord n0 f0 v m) σA σB I).result = some (⟨n0 + 2⟩, ⟨n0 + 2⟩) ∧
      (jointRun E (fieldToWord n0 f0 v m) (fieldToWord n0 f0 v m) σA σB I).ideal.bools (n0 + 2) =
        some (word vv.val) := by
  unfold fieldToWord
  obtain ⟨r1, i1⟩ := jointRun_program E maskSubName 1 [v, m.field] [] [⟨f0⟩] Label.maskedFieldValue _ _ σA σB I
    maskSub [vv, fv] [] [vv - fv] [] hP.maskSub (by simp [hv, hf]) rfl (maskSub_run vv fv) rfl
  rw [r1, i1]
  obtain ⟨r2, i2⟩ := jointRun_openFieldThen E [⟨f0⟩] Label.maskedFieldValue (f2wRest n0 f0 m) (f2wRest n0 f0 m)
    σA σB (I.setFields [⟨f0⟩] [vv - fv]) [vv - fv] (by simp [Ideal.setFields, Ideal.setField])
  rw [r2, i2]
  simp only [f2wRest]
  obtain ⟨r3, i3⟩ := jointRun_sayThen E 32 Label.maskedFieldValue (le 32 (vv - fv).val) (le 32 (vv - fv).val)
    _ _ σA σB (I.setFields [⟨f0⟩] [vv - fv]) (length_le _ _) (length_le _ _)
  rw [r3, i3, if_pos rfl]
  have hl : (wb ++ word (vv - fv).val).length = modaddC.inWidth := by simp [hlw, modaddC, W]
  have hw : modaddC.inWidth = 510 := rfl
  have he : modaddC.eval = modaddEval := rfl
  have hval : modaddEval (wb ++ word (vv - fv).val) = word vv.val := by
    rw [modaddEval_pair' _ _ hlw (length_word _), natOf_word _ (by have := fval_lt (vv - fv); have := P_lt_two_pow; omega),
      hcons, addModSpec_canonical _ _ (fval_lt fv) (fval_lt _), fsub_val]
    congr 1
    have h1 := TlsMpc.WordMask.from_field_roundtrip vv.val fv.val (fval_lt vv) (fval_lt fv)
    rw [Nat.add_comm (P - fv.val)]
    exact h1
  have htail : runLocal E (f2wTail n0 f0 m (vv - fv)) ((I.setFields [⟨f0⟩] [vv - fv])) =
      some (((((((I.setFields [⟨f0⟩] [vv - fv]).setBool ⟨n0⟩ (word (vv - fv).val)).setBool ⟨n0 + 1⟩
        (wb ++ word (vv - fv).val)).setBool ⟨n0 + 2⟩ (word vv.val)).dropBool ⟨n0⟩).dropBool
        ⟨n0 + 1⟩).dropBool m.bits |>.dropField m.field |>.dropField ⟨f0⟩) := by
    simp [f2wTail, runLocal, localStep, idealStep, blankWire, InstrP.map, Ideal.setFields, Ideal.setField,
      Ideal.setBool, hm, hW.modadd, hb0, hw, runCopies_one modaddC _ hl, he, hval, hlw, W]
  obtain ⟨r4, i4⟩ := jointRun_locals E (.done (⟨n0 + 2⟩ : BoolH)) (.done (⟨n0 + 2⟩ : BoolH)) σA σB _
    (f2wTail_local n0 f0 m _) _ _ htail
  rw [r4, i4]
  refine ⟨rfl, ?_⟩
  simp [jointRun, Ideal.dropField, Ideal.dropBool, Ideal.setBool, Ne.symm hb2]

/-- **P-F2W (b).** For a fixed v, f ↦ v − f is a bijection of F (its own inverse: v − (v − f) = f):
with f uniform, the opened c is uniform. -/
theorem f2w_hides (vv : F) : (∀ f f' : F, vv - f = vv - f' → f = f') ∧ ∀ f : F, vv - (vv - f) = f := by
  refine ⟨fun f f' h => ?_, fun f => by grind⟩
  have : vv - (vv - f) = vv - (vv - f') := by rw [h]
  grind

end F2W

/-! ## Bits to field (P-PAIR, P-B2F) -/

/-- `x₀ ρ₀ x₁ ρ₁ …` from `x ‖ ρ` (n bits each). -/
def interleave (n : Nat) : List Nat := (List.range n).flatMap fun i => [i, n + i]

/-- After the opening: per bit, `1 − ρ` when the opened bit is 1, else `ρ − 0` (fresh handles
`f0 + 2 + i`), then the pairs and the temporaries freed. -/
def b2fTail (n0 f0 : Nat) (o : Bits) (ps : List BitPair) : List Instr :=
  [.fieldPublic ⟨f0⟩ (ofNat 1), .fieldPublic ⟨f0 + 1⟩ (ofNat 0)] ++
  (ps.zipIdx.map fun e =>
    if o.getD e.2 false then (.fieldSub ⟨f0 + 2 + e.2⟩ ⟨f0⟩ e.1.field : Instr)
    else .fieldSub ⟨f0 + 2 + e.2⟩ e.1.field ⟨f0 + 1⟩) ++
  frees ([⟨n0⟩, ⟨n0 + 1⟩, ⟨n0 + 2⟩, ⟨n0 + 3⟩] ++ ps.map (·.bit)) ++
  ps.map (fun q => (.freeField q.field : Instr)) ++ [.freeField ⟨f0⟩, .freeField ⟨f0 + 1⟩]

def b2fOuts (f0 n : Nat) : List FieldH := (List.range n).map fun i => ⟨f0 + 2 + i⟩

/-- The Boolean block before the opening. -/
def b2fBlock (n0 : Nat) (x : BoolH) (ps : List BitPair) : List Instr :=
  [.concat ⟨n0⟩ (ps.map (·.bit)), .concat ⟨n0 + 1⟩ [x, ⟨n0⟩], .pick ⟨n0 + 2⟩ ⟨n0 + 1⟩ (interleave ps.length),
   .run ⟨n0 + 3⟩ xorBitOpenName ps.length ⟨n0 + 2⟩]

/-- **Bits to field.** `x`: n private bits (n = the number of pairs, n ≥ 1). -/
def bitsToField (n0 f0 : Nat) (x : BoolH) (ps : List BitPair) : Script (List FieldH) :=
  seqs (b2fBlock n0 x ps) <|
  openThen ⟨n0 + 3⟩ Label.maskedBit fun o =>
  if o.length = ps.length then seqs (b2fTail n0 f0 o ps) (.done (b2fOuts f0 ps.length))
  else .abort "masked bit width"

theorem b2fTail_local (n0 f0 : Nat) (o : Bits) (ps : List BitPair) : ∀ i ∈ b2fTail n0 f0 o ps, isLocal i = true := by
  intro i hi
  simp only [b2fTail, frees, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hi
  rcases hi with ((((rfl | rfl) | ⟨e, -, rfl⟩) | ⟨g, -, rfl⟩) | ⟨q, -, rfl⟩) | rfl | rfl
  · rfl
  · rfl
  · split <;> rfl
  all_goals rfl

def b2fKinds : List TlsMpc.Node.RevealKind := [.maskedBit]

theorem b2f_reveals (n0 f0 : Nat) (x : BoolH) (ps : List BitPair) : Reveals b2fKinds (bitsToField n0 f0 x ps) := by
  unfold bitsToField
  refine every_seqs (every_openThen (LabelIn.of_mem (k := .maskedBit) (by simp [b2fKinds]) rfl) fun o => ?_) _
    (fun i hi => ?_)
  · split
    · exact every_seqs (Every.done _) _ (fun i hi => LabelIn.of_none (label_local i (b2fTail_local n0 f0 o ps i hi)))
    · exact Every.abort _
  · simp only [b2fBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact LabelIn.of_none rfl

/-- **T3 for bits to field.** Against any adversary, the adversary's view is at most one release,
labelled `maskedBit`: the value of the `xor-bit-open` output after the Boolean block, that is
o = x ⊕ ρ (`b2f_value`). -/
theorem b2f_disclosure (E : Env) (me : Party) (adv : Adversary) (n0 f0 : Nat) (x : BoolH) (ps : List BitPair)
    (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv (bitsToField n0 f0 x ps) σ I vD).viewD <+:
      [⟨Label.maskedBit, .bits (TlsMpc.Node.Flows.Contacts.openedAfter E (b2fBlock n0 x ps) ⟨n0 + 3⟩ I)⟩] := by
  unfold bitsToField
  refine TlsMpc.Node.Flows.Contacts.viewD_block_open E me adv _ (fun i hi => ?_) _ _ _ (fun o => ?_) σ I vD
  · simp only [b2fBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl
  · split
    · exact silent_locals (Silent.done _) _ (b2fTail_local n0 f0 o ps)
    · exact Silent.abort _

/-- **P-B2F (a), per bit.** For a consistent pair (its field value is the bit ρ) and the opened
o = x ⊕ ρ, the result `1 − ρ` (o = 1) or `ρ − 0` (o = 0) is the bit x. -/
theorem b2f_value (x ρ : Bool) :
    (if (x ^^ ρ) then ofNat 1 - X25519.bitValue ρ else X25519.bitValue ρ - ofNat 0) = X25519.bitValue x := by
  cases x <;> cases ρ <;> decide

/-- **P-B2F (b).** For a fixed x, ρ ↦ x ⊕ ρ is a bijection of the bits (its own inverse), so a
uniform ρ makes the opened bit uniform. -/
theorem b2f_hides (x : Bool) : (∀ ρ ρ' : Bool, (x ^^ ρ) = (x ^^ ρ') → ρ = ρ') ∧ ∀ o, (x ^^ (x ^^ o)) = o := by
  refine ⟨fun ρ ρ' h => ?_, fun o => ?_⟩ <;> cases x <;> simp_all

/-- The opened word, bit by bit, of the `xor-bit` copies on the interleaving: o_i = x_i ⊕ ρ_i. -/
theorem xorBit_copies (a b : Bool) : xorBitEval [a, b] = [a ^^ b] := rfl

/-- **P-B2F (c).** The pairs taken are not in the pool returned (`MaskPool.takeBits_fresh`), and
the script frees both of their handles. -/
theorem b2f_once (pool pool' : MaskPool) (ps : List BitPair) (n : Nat) (hd : pool.Distinct)
    (ht : pool.takeBits n = some (ps, pool')) (n0 f0 : Nat) (o : Bits) :
    (∀ q ∈ ps, q ∉ pool'.bits) ∧ ∀ q ∈ ps, (.freeBool q.bit : Instr) ∈ b2fTail n0 f0 o ps ∧
      (.freeField q.field : Instr) ∈ b2fTail n0 f0 o ps := by
  refine ⟨(MaskPool.takeBits_fresh hd ht).1, fun q hq => ⟨?_, ?_⟩⟩
  · simp only [b2fTail, frees, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inr ⟨q.bit, Or.inr ⟨q, hq, rfl⟩, rfl⟩))
  · simp only [b2fTail, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨q, hq, rfl⟩)

/-! ## Shared scalars as field bits (P-BITS) -/

def bitsA (f0 n : Nat) : List FieldH := (List.range n).map fun i => ⟨f0 + i⟩
def bitsB (f0 n : Nat) : List FieldH := (List.range n).map fun i => ⟨f0 + n + i⟩
def bitsChk (f0 n : Nat) : List FieldH := (List.range (2 * n)).map fun i => ⟨f0 + 2 * n + i⟩
def bitsPairs (f0 n : Nat) : List FieldH := (List.range n).flatMap fun i => [⟨f0 + i⟩, ⟨f0 + n + i⟩]
def bitsOuts (f0 n : Nat) : List FieldH := (List.range n).map fun i => ⟨f0 + 4 * n + i⟩

/-- **Shared bits** (`shared_scalar`, `shared_bits`): each party inputs its n local bits (from
its store slot `slot`, as coins); the bit checks of all 2n inputs are opened and must be 0; the
result is the field XOR. For the X25519 ladder the local bits are `swap_bit(share, step, top)` with
`top` set for party A only (`tls_kernels.h` `swap_bit`), and `X25519SwapBits.swapBit_shares` says
their XOR is the swap bit of the XORed scalar. -/
def sharedBits (f0 n slot : Nat) : Script (List FieldH) :=
  seq (.fieldInput (bitsA f0 n) (bitsB f0 n) .coins false slot) <|
  seq (.program bitCheckName (2 * n) (bitsA f0 n ++ bitsB f0 n) [] (bitsChk f0 n) Label.scalarBitChecks) <|
  openFieldThen (bitsChk f0 n) Label.scalarBitChecks fun z =>
  if z.all (· == 0) then
    seq (.program bitXorName n (bitsPairs f0 n) [] (bitsOuts f0 n) Label.scalarBitChecks) (.done (bitsOuts f0 n))
  else .abort "non-bit scalar contribution"

def bitsKinds : List TlsMpc.Node.RevealKind := [.scalarBitChecks]

theorem bits_reveals (f0 n slot : Nat) : Reveals bitsKinds (sharedBits f0 n slot) := by
  unfold sharedBits
  refine every_seq (LabelIn.of_none rfl) (every_seq (LabelIn.of_mem (k := .scalarBitChecks) (by simp [bitsKinds]) rfl)
    (every_openFieldThen (LabelIn.of_mem (k := .scalarBitChecks) (by simp [bitsKinds]) rfl) fun z => ?_))
  split
  · exact every_seq (LabelIn.of_mem (k := .scalarBitChecks) (by simp [bitsKinds]) rfl) (Every.done _)
  · exact Every.abort _

open TlsMpc.FieldDag.V3 (FieldInverse) in
/-- **P-BITS (a).** The checks `c·(c − 1)` of all inputs open to 0 iff every input of both parties
is 0 or 1 (with `FieldInverse`: no zero divisors; the converse of `FieldBits.bitCheck_bit`). -/
theorem bits_checks_zero_iff (hinv : FieldInverse) (cs : List F) :
    (cs.map fun c => c * (c - ofNat 1)).all (· == 0) = true ↔ ∀ c ∈ cs, c = 0 ∨ c = ofNat 1 := by
  simp only [List.all_map, List.all_eq_true, Function.comp_apply, beq_iff_eq]
  constructor
  · intro h c hc
    exact (TlsMpc.Node.Flows.Masks.bitCheck_zero_iff hinv c).mp (h c hc)
  · intro h c hc
    exact (TlsMpc.Node.Flows.Masks.bitCheck_zero_iff hinv c).mpr (h c hc)

/-- **P-BITS (b).** Honest inputs (the bits a_i of A and b_i of B, as 0/1) give, per position,
the field bit of a_i ⊕ b_i (`field-bit-xor`'s value, `bitXorValue_bits`). -/
theorem bits_xor (a b : Bits) :
    (List.zipWith (fun x y => bitXorValue (X25519.bitValue x) (X25519.bitValue y)) a b) =
      (List.zipWith (· ^^ ·) a b).map X25519.bitValue := by
  induction a generalizing b with
  | nil => rfl
  | cons x a _ =>
    cases b with
    | nil => rfl
    | cons y b => simp [List.zipWith_cons_cons, bitXorValue_bits]

/-- **P-BITS (c).** An honest party's checks are the constant 0 (`FieldBits.bitCheck_bit`): they
carry no information about its bits. -/
theorem bits_honest_checks (bs : Bits) :
    bs.map (fun x => X25519.bitValue x * (X25519.bitValue x - ofNat 1)) = bs.map fun _ => 0 := by
  apply List.map_congr_left
  intro x _
  cases x <;> decide

/-! ## Single use (P-W2F (c), P-F2W (c), P-B2F (c)) -/

/-- **The mask a conversion takes is not in the pool it returns** (`MaskPool.takeWord_fresh`), and
the conversion frees both of its handles at the end (`w2fTail`, `f2wTail`), so the shell refuses a
second use. -/
theorem w2f_once (pool pool' : MaskPool) (m : WordMask) (hd : pool.Distinct) (ht : pool.takeWord = some (m, pool'))
    (n0 f0 : Nat) (c : Nat) :
    m ∉ pool'.words ∧ (.freeBool m.bits : Instr) ∈ w2fTail n0 f0 m c ∧ (.freeField m.field : Instr) ∈ w2fTail n0 f0 m c :=
  ⟨(MaskPool.takeWord_fresh hd ht).1, by simp [w2fTail], by simp [w2fTail]⟩

theorem f2w_once (pool pool' : MaskPool) (m : WordMask) (hd : pool.Distinct) (ht : pool.takeWord = some (m, pool'))
    (n0 f0 : Nat) (c : F) :
    m ∉ pool'.words ∧ (.freeBool m.bits : Instr) ∈ f2wTail n0 f0 m c ∧ (.freeField m.field : Instr) ∈ f2wTail n0 f0 m c :=
  ⟨(MaskPool.takeWord_fresh hd ht).1, by simp [f2wTail], by simp [f2wTail]⟩

end TlsMpc.Node.Flows.Convert
