import TlsMpc.Node.Policy.ReceiveInvariant
import TlsMpc.Node.Policy.ReceiveStream

/-!
# T1 for responses, every field order (proof track P1, item 2)

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`Policy/ReceiveProofs.lean` proved the response scanner right on the server's layout (id, status,
message, body: `response_body_unrevealed`). Here: **every** field order, every byte string, with or
without `openBody`.

## The controller's view of a response (`RShape`)

While a response (`08 02`) arrives, the controller keeps its revealed bytes (`State.reply`: the
message's bytes with the body's content left out, unless `openBody`) and whether the body has been
passed over (`State.replySkipped`). `RShape ob H sk P` says what `H` and `sk` are after the message
bytes `[8, 2] ++ P`: the wrapper (`1a`, its length), then complete fields (`RFs`: id and status,
message and headers, at most one body, in any order and any number), then an unfinished field
(`RT`: nothing, a key, part of a varint, part of a message, header or inline body).

* `rshape_start`: after the kind bytes. `rshape_more`, `rshape_skip`: every byte the scanner
  accepts (`replyScan` says `more`), and every body it asks to pass over (`skip n`, then any `n`
  bytes), keeps the shape. With `payloadByte_reply_more`/`payloadByte_reply_skip`
  (`Policy/ReceiveInvariant.lean`) these are the controller's own steps.
* `rshape_classes`: nothing in `[8, 2] ++ P` is `error` in the reference (`message openBody
  false`), and every byte of `H` is a public byte of `P`.
* **`rshape_budget`**: from such a state, the run the controller reveals next (`replyBudget H`
  bytes, whatever they are) is public in the reference, except possibly its last byte(s) being
  the reference's first `error` (a bad key and the byte after it; the 11th byte of a varint).
  This is the response half of T1 at the message level, for every field order.
-/

namespace ReceiveReply

open PublicReceive ReceiveProofs
open ReceiveSpec (Class fill varintThen varintEnd varintValue VarintEnd)
open ReceiveStream (responseFields)

/-! ### The reference, field by field -/

theorem fillL {α : Type} (c : Class) (l : List α) : (fill c l).length = l.length := by simp [fill]

theorem varintThen_varint {v : List Byte} {n : Nat} (hv : Varint v n) (hl : v.length ≤ 10) (Z : List Byte)
    (next : Nat → List Byte → List Class) : varintThen (v ++ Z) next = fill .structure v ++ next n Z := by
  rw [varintThen_done (varintEnd_varint hv 10 Z hl), List.take_left' rfl, List.drop_left, varintValue_varint hv]

theorem rf_fuel (ob : Bool) (X : List Byte) (k : Nat) (h : X.length < k) :
    ReceiveSpec.response ob false k X = responseFields ob false X :=
  ReceiveStream.response_fuel ob false k _ X h (Nat.lt_succ_self _)

theorem rf_number (ob : Bool) {tag : Byte} {v : List Byte} {n : Nat} (ht : tag = 0x08 ∨ tag = 0x10)
    (hv : Varint v n) (hl : v.length ≤ 10) (Z : List Byte) :
    responseFields ob false (tag :: (v ++ Z)) = .structure :: (fill .structure v ++ responseFields ob false Z) := by
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons, if_pos ht, varintThen_varint hv hl,
    rf_fuel ob Z _ (by simp; omega)]
  rfl

theorem rf_delim (ob : Bool) (k : Class) {v c : List Byte} (hv : Varint v c.length) (hl : v.length ≤ 10)
    (Z : List Byte) (fuel : Nat) (hf : Z.length < fuel) :
    ReceiveSpec.delimitedThen false (v ++ (c ++ Z)) (fill k) (fun _ after => ReceiveSpec.response ob false fuel after) =
      fill .structure v ++ (fill k c ++ responseFields ob false Z) := by
  rw [ReceiveStream.delimitedThen_eq, varintThen_varint hv hl]
  unfold ReceiveStream.delimCont
  rw [if_neg (by simp), List.take_left' rfl, List.drop_left]
  dsimp only
  rw [rf_fuel ob Z fuel hf]

theorem rf_text (ob : Bool) {tag : Byte} {v c : List Byte} (ht : tag = 0x1a ∨ tag = 0x2a)
    (hv : Varint v c.length) (hl : v.length ≤ 10) (Z : List Byte) :
    responseFields ob false (tag :: (v ++ (c ++ Z))) =
      .structure :: (fill .structure v ++ (fill .text c ++ responseFields ob false Z)) := by
  have h1 : ¬ (tag = 0x08 ∨ tag = 0x10) := by rcases ht with rfl | rfl <;> decide
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons, if_neg h1, if_pos ht, rf_delim ob _ hv hl Z _ (by simp; omega)]
  rfl

theorem rf_body (ob : Bool) {v c : List Byte} (hv : Varint v c.length) (hl : v.length ≤ 10) (Z : List Byte) :
    responseFields ob false (0x22 :: (v ++ (c ++ Z))) =
      .structure :: (fill .structure v ++ (fill (if ob then .text else .body) c ++ responseFields ob false Z)) := by
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons, if_neg (by decide), if_neg (by decide), if_pos rfl,
    rf_delim ob _ hv hl Z _ (by simp; omega)]
  rfl

theorem rf_bad (ob : Bool) {tag : Byte} (ht : ¬ (tag = 0x08 ∨ tag = 0x10 ∨ tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22))
    (Z : List Byte) : responseFields ob false (tag :: Z) = .structure :: fill .error Z := by
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons,
    if_neg (fun h => ht (by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h))),
    if_neg (fun h => ht (by rcases h with h | h; exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inl h))))),
    if_neg (fun h => ht (Or.inr (Or.inr (Or.inr (Or.inr h)))))]

theorem rf_nil (ob : Bool) : responseFields ob false [] = [] := rfl

/-- The classes of a whole response message: the kind, the wrapper key and length, the fields. -/
theorem message_response (ob : Bool) {lw : List Byte} {m : Nat} (hw : Varint lw m) (hl : lw.length ≤ 10)
    (Z : List Byte) :
    ReceiveSpec.message ob false (8 :: 2 :: 0x1a :: (lw ++ Z)) =
      .kind :: .kind :: .structure :: (fill .structure lw ++ responseFields ob false Z) := by
  rw [ReceiveStream.message_eq, if_neg (by decide), if_pos ⟨rfl, rfl⟩]
  simp only [ReceiveSpec.wrapper, if_pos, varintThen_varint hw hl]

/-! ### Complete fields -/

/-- **Complete response fields**, in any order: `R` the revealed bytes, `F` the message's bytes,
`b` the body's length if there is a body (at most one: the controller refuses a second). A body's
content is among the revealed bytes only with `openBody`. -/
inductive RFs (ob : Bool) : List Byte → List Byte → Option Nat → Prop
  | nil : RFs ob [] [] none
  | number {tag : Byte} {v R F : List Byte} {n : Nat} {b : Option Nat} : (tag = 0x08 ∨ tag = 0x10) → Varint v n →
      v.length ≤ 10 → RFs ob R F b → RFs ob (tag :: (v ++ R)) (tag :: (v ++ F)) b
  | text {tag : Byte} {v c R F : List Byte} {b : Option Nat} : (tag = 0x1a ∨ tag = 0x2a) → Varint v c.length →
      v.length ≤ 10 → RFs ob R F b → RFs ob (tag :: (v ++ (c ++ R))) (tag :: (v ++ (c ++ F))) b
  | body {v c R F : List Byte} : Varint v c.length → v.length ≤ 10 → RFs ob R F none →
      RFs ob (0x22 :: (v ++ ((if ob then c else []) ++ R))) (0x22 :: (v ++ (c ++ F))) (some c.length)

/-- The classes of complete fields: none is `error`. -/
theorem rfs_classes {ob : Bool} {R F : List Byte} {b : Option Nat} (h : RFs ob R F b) (Z : List Byte) :
    ∃ C : List Class, responseFields ob false (F ++ Z) = C ++ responseFields ob false Z ∧ C.length = F.length ∧
      ∀ x ∈ C, x ≠ .error := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | @number tag v R F n b ht hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ C), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, rf_number ob ht hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx; rcases hx with rfl | ⟨_, _, rfl⟩ | hx <;> first | decide | exact hc x hx
  | @text tag v c R F b ht hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ (fill .text c ++ C)), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, List.append_assoc, rf_text ob ht hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx
      rcases hx with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | hx <;> first | decide | exact hc x hx
  | @body v c R F hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ (fill (if ob then .text else .body) c ++ C)), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, List.append_assoc, rf_body ob hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx
      rcases hx with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | hx
      · decide
      · decide
      · cases ob <;> decide
      · exact hc x hx

/-! ### One complete field; complete fields one after another -/

/-- One complete response field: revealed bytes, message bytes, the body's length if it is the body. -/
inductive RF (ob : Bool) : List Byte → List Byte → Option Nat → Prop
  | number {tag : Byte} {v : List Byte} {n : Nat} : (tag = 0x08 ∨ tag = 0x10) → Varint v n → v.length ≤ 10 →
      RF ob (tag :: v) (tag :: v) none
  | text {tag : Byte} {v c : List Byte} : (tag = 0x1a ∨ tag = 0x2a) → Varint v c.length → v.length ≤ 10 →
      RF ob (tag :: (v ++ c)) (tag :: (v ++ c)) none
  | body {v c : List Byte} : Varint v c.length → v.length ≤ 10 →
      RF ob (0x22 :: (v ++ (if ob then c else []))) (0x22 :: (v ++ c)) (some c.length)

theorem rfs_snoc {ob : Bool} {R F : List Byte} {b : Option Nat} (h : RFs ob R F b) {Rf Ff : List Byte}
    {bf : Option Nat} (hf : RF ob Rf Ff bf) (hb : b = none ∨ bf = none) : RFs ob (R ++ Rf) (F ++ Ff) (b.or bf) := by
  induction h with
  | nil =>
    cases hf with
    | number ht hv hl => simpa using RFs.number ht hv hl RFs.nil
    | text ht hv hl => simpa using RFs.text ht hv hl RFs.nil
    | body hv hl => simpa using RFs.body hv hl RFs.nil
  | number ht hv hl _ ih => simpa using RFs.number ht hv hl (ih hb)
  | text ht hv hl _ ih => simpa using RFs.text ht hv hl (ih hb)
  | body hv hl _ ih =>
    rcases hb with hb | hb
    · cases hb
    · subst hb
      simpa using RFs.body hv hl (ih (Or.inl rfl))

/-! ### Where the revealed bytes end: an unfinished field -/

/-- The budget `replyBudget` gives inside an id or status whose varint has `u` bytes so far. -/
def numBudget (u : List Byte) : Nat := if u = [] then 1 else min 3 (11 - u.length)

/-- **The unfinished field the revealed bytes end in**, with the budget `replyBudget` gives there,
and whether it is an inline body (`openBody`) still arriving: nothing (a field boundary: the next key
and the byte after it); an id or status key and part of its varint; a message, header or body key
and part of its length; part of a message or header; part of an inline body. -/
inductive RT (ob : Bool) : List Byte → Nat → Bool → Prop
  | boundary : RT ob [] 2 false
  | number {tag : Byte} {u : List Byte} : (tag = 0x08 ∨ tag = 0x10) → (∀ y ∈ u, 128 ≤ y.toNat) → u.length < 10 →
      RT ob (tag :: u) (numBudget u) false
  | lengthKey {tag : Byte} {u : List Byte} : (tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22) → (∀ y ∈ u, 128 ≤ y.toNat) →
      u.length < 10 → RT ob (tag :: u) 1 false
  | short {tag : Byte} {v c : List Byte} {count : Nat} : (tag = 0x1a ∨ tag = 0x2a) → Varint v count →
      v.length ≤ 10 → c.length < count → RT ob (tag :: (v ++ c)) (count - c.length) false
  | inline {v c : List Byte} {count : Nat} : ob = true → Varint v count → v.length ≤ 10 → c.length < count →
      RT ob (0x22 :: (v ++ c)) (count - c.length) true

/-- `State.replySkipped` as the fields say it: a body was passed over (not `openBody`, not empty). -/
def skOf (ob : Bool) (b : Option Nat) : Bool := !ob && b.any (fun m => decide (0 < m))

/-- **The controller's view of a response**, after the message bytes `[8, 2] ++ P`: its revealed bytes
`H` (`State.reply`) and `sk` (`State.replySkipped`). After the kind; inside the wrapper's length;
or after the wrapper, complete fields `RFs` and an unfinished one `RT` (an inline body still arriving
only when no body came before). -/
inductive RShape (ob : Bool) : List Byte → Bool → List Byte → Prop
  | kind : RShape ob [8, 2] false []
  | wrapper {u : List Byte} : (∀ y ∈ u, 128 ≤ y.toNat) → u.length < 10 →
      RShape ob (8 :: 2 :: 0x1a :: u) false (0x1a :: u)
  | fields {lw R F T : List Byte} {m e : Nat} {b : Option Nat} {nb : Bool} : Varint lw m → lw.length ≤ 10 →
      RFs ob R F b → RT ob T e nb → (nb = true → b = none) →
      RShape ob (8 :: 2 :: 0x1a :: (lw ++ (R ++ T))) (skOf ob b) (0x1a :: (lw ++ (F ++ T)))

/-! ### `replyScan`'s loop, one round at a time -/

theorem bad_tag_bools : ∀ y : Byte, ¬ (y = 0x08 ∨ y = 0x10 ∨ y = 0x1a ∨ y = 0x2a ∨ y = 0x22) →
    (y.toNat == 0x08 || y.toNat == 0x10) = false ∧ (y.toNat == 0x1a || y.toNat == 0x2a) = false ∧
      (y.toNat == 0x22) = false := by
  decide

theorem tag22_bools : ((0x22 : Byte).toNat == 0x08 || (0x22 : Byte).toNat == 0x10) = false ∧
    ((0x22 : Byte).toNat == 0x1a || (0x22 : Byte).toNat == 0x2a) = false ∧ ((0x22 : Byte).toNat == 0x22) = true := by
  decide

theorem rsb_end {bytes : List Byte} {sk ob : Bool} {x : Option (Need × ReplyFields)} {f : ReplyFields} {pos : Nat}
    (h : bytes.length ≤ pos) : replyScanBody bytes sk ob ⟨x, f, pos⟩ = .done ⟨some (.more, f), f, pos⟩ := by
  unfold replyScanBody; rw [if_pos h]

theorem rsb_bad {bytes rest : List Byte} {tag : Byte} {sk ob : Bool} {x : Option (Need × ReplyFields)}
    {f : ReplyFields} {pos : Nat} (h : bytes.drop pos = tag :: rest)
    (hb : ¬ (tag = 0x08 ∨ tag = 0x10 ∨ tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22)) :
    replyScanBody bytes sk ob ⟨x, f, pos⟩ = .done ⟨some (.malformed, f), f, pos⟩ := by
  obtain ⟨hg, -, hp, -⟩ := field_at h
  obtain ⟨b1, b2, b3⟩ := bad_tag_bools tag hb
  unfold replyScanBody
  simp only [hg, b1, b2, b3, ge_iff_le, hp, if_false, Bool.false_eq_true]

/-- After a key whose varint is not complete yet: more is needed. -/
theorem rsb_partial {bytes u : List Byte} {tag : Byte} {sk ob : Bool} {x : Option (Need × ReplyFields)}
    {f : ReplyFields} {pos : Nat} (ht : tag = 0x08 ∨ tag = 0x10 ∨ tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22)
    (hu : ∀ y ∈ u, 128 ≤ y.toNat) (hl : u.length < 10) (h : bytes.drop pos = tag :: u) :
    replyScanBody bytes sk ob ⟨x, f, pos⟩ = .done ⟨some (.more, f), f, pos⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_partial hu hd1
  unfold replyScanBody
  simp only [hg, hvar, varintTooLong_short hd1 hl, ge_iff_le, hp, if_false, Bool.false_eq_true]
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Inside a message or header whose length is known: more is needed. -/
theorem rsb_textShort {bytes v c : List Byte} {tag : Byte} {sk ob : Bool} {x : Option (Need × ReplyFields)}
    {f : ReplyFields} {pos count : Nat} (ht : tag = 0x1a ∨ tag = 0x2a) (hv : Varint v count) (hl : v.length ≤ 10)
    (hc : c.length < count) (h : bytes.drop pos = tag :: (v ++ c)) :
    replyScanBody bytes sk ob ⟨x, f, pos⟩ = .done ⟨some (.more, f), f, pos⟩ := by
  obtain ⟨hg, hd1, hp, hlen⟩ := field_at h
  simp only [List.length_append] at hlen
  have hvar := varintAt_varint hv hl hd1
  have hn : bytes.length < pos + 1 + v.length + count := by omega
  obtain ⟨t1, t2⟩ := rtag_text tag ht
  unfold replyScanBody
  simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true]

/-- A complete body field among the revealed bytes (its content too with `openBody`), not at the
moment it is to be passed over: the loop goes on after it. -/
theorem rsb_bodyField {bytes v rest : List Byte} {sk ob : Bool} {x : Option (Need × ReplyFields)} {f : ReplyFields}
    {pos count : Nat} (hv : Varint v count) (hl : v.length ≤ 10) (hf : f.body = none)
    (h : bytes.drop pos = 0x22 :: (v ++ rest))
    (hns : ¬ (pos + 1 + v.length = bytes.length ∧ sk = false ∧ ob = false ∧ 0 < count))
    (hin : ob = true → pos + 1 + v.length + count ≤ bytes.length) :
    replyScanBody bytes sk ob ⟨x, f, pos⟩ =
      .yield ⟨none, { f with body := some count }, if ob then pos + 1 + v.length + count else pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, t2, t3⟩ := tag22_bools
  have hs : (pos + 1 + v.length == bytes.length && !sk && !ob && decide (count > 0)) = false := by
    rw [Bool.eq_false_iff]; intro e
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at e
    exact hns ⟨e.1.1.1, e.1.1.2, e.1.2, e.2⟩
  have hi : (ob && decide (pos + 1 + v.length + count > bytes.length)) = false := by
    cases ob
    · rfl
    · simp only [Bool.true_and, decide_eq_false_iff_not]; have := hin rfl; omega
  unfold replyScanBody
  simp only [hg, hvar, hf, t1, t2, t3, hs, hi, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true,
    Option.isSome_none]

/-- A second body: refused once its length is complete. -/
theorem rsb_bodyTwice {bytes v rest : List Byte} {sk ob : Bool} {x : Option (Need × ReplyFields)} {f : ReplyFields}
    {pos count : Nat} (hv : Varint v count) (hl : v.length ≤ 10) (hf : f.body.isSome = true)
    (h : bytes.drop pos = 0x22 :: (v ++ rest)) :
    replyScanBody bytes sk ob ⟨x, f, pos⟩ = .done ⟨some (.malformed, f), f, pos⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, t2, t3⟩ := tag22_bools
  unfold replyScanBody
  simp only [hg, hvar, hf, t1, t2, t3, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true]

/-- Inside an inline body (`openBody`) whose length is known: more is needed. -/
theorem rsb_inlineShort {bytes v c : List Byte} {sk : Bool} {x : Option (Need × ReplyFields)} {f : ReplyFields}
    {pos count : Nat} (hv : Varint v count) (hl : v.length ≤ 10) (hf : f.body = none) (hc : c.length < count)
    (h : bytes.drop pos = 0x22 :: (v ++ c)) :
    replyScanBody bytes sk true ⟨x, f, pos⟩ =
      .done ⟨some (.more, { f with body := some count }), { f with body := some count }, pos⟩ := by
  obtain ⟨hg, hd1, hp, hlen⟩ := field_at h
  simp only [List.length_append] at hlen
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, t2, t3⟩ := tag22_bools
  have hs : (pos + 1 + v.length == bytes.length && !sk && !true && decide (count > 0)) = false := by simp
  have hi : (true && decide (pos + 1 + v.length + count > bytes.length)) = true := by
    simp only [Bool.true_and, decide_eq_true_eq]; omega
  unfold replyScanBody
  simp only [hg, hvar, hf, t1, t2, t3, hs, hi, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true,
    Option.isSome_none]

theorem bb_bodyField {bytes v rest : List Byte} {ob : Bool} {x : Option Nat} {pos count : Nat}
    (hv : Varint v count) (hl : v.length ≤ 10) (h : bytes.drop pos = 0x22 :: (v ++ rest))
    (hin : ob = true → pos + 1 + v.length + count ≤ bytes.length) :
    budgetBody bytes ob ⟨x, pos⟩ = .yield ⟨none, if ob then pos + 1 + v.length + count else pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, t2, t3⟩ := tag22_bools
  have hi : (ob && decide (pos + 1 + v.length + count > bytes.length)) = false := by
    cases ob
    · rfl
    · simp only [Bool.true_and, decide_eq_false_iff_not]; have := hin rfl; omega
  unfold budgetBody
  simp only [hg, hvar, t1, t2, t3, hi, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true]

theorem numberField_body (tag : Byte) (n : Nat) (f : ReplyFields) : (numberField tag n f).body = f.body := by
  unfold numberField; split <;> rfl

/-- **The scanner walks complete fields**: from their first byte, round after round, to their end,
having noted the body (if any). -/
theorem rfs_scan {ob : Bool} {R F : List Byte} {b : Option Nat} (h : RFs ob R F b) :
    ∀ (H T : List Byte) (p : Nat) (sk : Bool) (f : ReplyFields), H.drop p = R ++ T →
      (f.body = none ∨ b = none) → (∀ m, b = some m → ob = false → 0 < m → sk = true) →
      ∃ n f', n ≤ R.length ∧ Reaches (replyScanBody H sk ob) n ⟨none, f, p⟩ ⟨none, f', p + R.length⟩ ∧
        f'.body = b.or f.body := by
  induction h with
  | nil => intro H T p sk f _ _ _; exact ⟨0, f, Nat.le_refl _, rfl, rfl⟩
  | @number tag v R F n b ht hv hl _ ih =>
    intro H T p sk f hd hb hs
    have hd' : H.drop p = tag :: (v ++ (R ++ T)) := by rw [hd]; simp
    have hr := replyScanBody_number (x := none) (f := f) (b := sk) (i := ob) ht hv hl hd'
    obtain ⟨k, f', hk, hreach, hbody⟩ := ih H T (p + 1 + v.length) sk (numberField tag n f)
      (drop_number hd') (by rw [numberField_body]; exact hb) hs
    refine ⟨k + 1, f', by simp; omega, ⟨_, hr, ?_⟩, by rw [hbody, numberField_body]⟩
    rw [show p + (tag :: (v ++ R)).length = p + 1 + v.length + R.length by simp; omega]
    exact hreach
  | @text tag v c R F b ht hv hl _ ih =>
    intro H T p sk f hd hb hs
    have hd' : H.drop p = tag :: (v ++ (c ++ (R ++ T))) := by rw [hd]; simp
    have hr := replyScanBody_text (x := none) (f := f) (b := sk) (i := ob) ht hv hl hd'
    obtain ⟨k, f', hk, hreach, hbody⟩ := ih H T (p + 1 + v.length + c.length) sk f (drop_field hd') hb hs
    refine ⟨k + 1, f', by simp; omega, ⟨_, hr, ?_⟩, hbody⟩
    rw [show p + (tag :: (v ++ (c ++ R))).length = p + 1 + v.length + c.length + R.length by simp; omega]
    exact hreach
  | @body v c R F hv hl _ ih =>
    intro H T p sk f hd hb hs
    have hf : f.body = none := by rcases hb with hb | hb; exact hb; cases hb
    have hd' : H.drop p = 0x22 :: (v ++ ((if ob then c else []) ++ (R ++ T))) := by rw [hd]; simp
    have hlen := length_of_drop hd' (by simp)
    simp only [List.length_cons, List.length_append] at hlen
    have hr := rsb_bodyField (x := none) (sk := sk) (ob := ob) (f := f) hv hl hf hd'
      (by
        rintro ⟨e1, e2, e3, e4⟩
        have := hs c.length rfl e3 e4
        rw [this] at e2; cases e2)
      (by intro e; subst e; simp at hlen; omega)
    have hd2 : H.drop (if ob then p + 1 + v.length + c.length else p + 1 + v.length) = R ++ T := by
      cases ob
      · simpa using drop_number (rest := R ++ T) (by simpa using hd')
      · simpa using drop_field (rest := R ++ T) (by simpa using hd')
    obtain ⟨k, f', hk, hreach, hbody⟩ := ih H T _ sk { f with body := some c.length } hd2 (Or.inr rfl)
      (fun m e => by cases e)
    refine ⟨k + 1, f', by simp; omega, ⟨_, hr, ?_⟩, by rw [hbody]; rfl⟩
    have : (if ob then p + 1 + v.length + c.length else p + 1 + v.length) + R.length =
        p + (0x22 :: (v ++ ((if ob then c else []) ++ R))).length := by
      cases ob <;> simp <;> omega
    rw [← this]
    exact hreach

/-- **`replyBudget`'s loop walks complete fields** the same way. -/
theorem rfs_budget {ob : Bool} {R F : List Byte} {b : Option Nat} (h : RFs ob R F b) :
    ∀ (H T : List Byte) (p : Nat), H.drop p = R ++ T →
      ∃ n, n ≤ R.length ∧ Reaches (budgetBody H ob) n ⟨none, p⟩ ⟨none, p + R.length⟩ := by
  induction h with
  | nil => intro H T p _; exact ⟨0, Nat.le_refl _, rfl⟩
  | @number tag v R F n b ht hv hl _ ih =>
    intro H T p hd
    have hd' : H.drop p = tag :: (v ++ (R ++ T)) := by rw [hd]; simp
    have hr := budgetBody_number (x := none) (i := ob) ht hv hl hd'
    obtain ⟨k, hk, hreach⟩ := ih H T (p + 1 + v.length) (drop_number hd')
    refine ⟨k + 1, by simp; omega, ⟨_, hr, ?_⟩⟩
    rw [show p + (tag :: (v ++ R)).length = p + 1 + v.length + R.length by simp; omega]
    exact hreach
  | @text tag v c R F b ht hv hl _ ih =>
    intro H T p hd
    have hd' : H.drop p = tag :: (v ++ (c ++ (R ++ T))) := by rw [hd]; simp
    have hr := budgetBody_text (x := none) (i := ob) ht hv hl hd'
    obtain ⟨k, hk, hreach⟩ := ih H T (p + 1 + v.length + c.length) (drop_field hd')
    refine ⟨k + 1, by simp; omega, ⟨_, hr, ?_⟩⟩
    rw [show p + (tag :: (v ++ (c ++ R))).length = p + 1 + v.length + c.length + R.length by simp; omega]
    exact hreach
  | @body v c R F hv hl _ ih =>
    intro H T p hd
    have hd' : H.drop p = 0x22 :: (v ++ ((if ob then c else []) ++ (R ++ T))) := by rw [hd]; simp
    have hlen := length_of_drop hd' (by simp)
    simp only [List.length_cons, List.length_append] at hlen
    have hr := bb_bodyField (x := none) (ob := ob) hv hl hd' (by intro e; subst e; simp at hlen; omega)
    have hd2 : H.drop (if ob then p + 1 + v.length + c.length else p + 1 + v.length) = R ++ T := by
      cases ob
      · simpa using drop_number (rest := R ++ T) (by simpa using hd')
      · simpa using drop_field (rest := R ++ T) (by simpa using hd')
    obtain ⟨k, hk, hreach⟩ := ih H T _ hd2
    refine ⟨k + 1, by simp; omega, ⟨_, hr, ?_⟩⟩
    have : (if ob then p + 1 + v.length + c.length else p + 1 + v.length) + R.length =
        p + (0x22 :: (v ++ ((if ob then c else []) ++ R))).length := by
      cases ob <;> simp <;> omega
    rw [← this]
    exact hreach

/-! ### The unfinished field, one more byte -/

theorem varint_snoc : ∀ (u : List Byte), (∀ x ∈ u, 128 ≤ x.toNat) → ∀ (y : Byte), y.toNat < 128 →
    ∃ n, Varint (u ++ [y]) n
  | [], _, y, hy => ⟨_, Varint.last hy⟩
  | x :: u, hu, y, hy => by
    obtain ⟨n, hn⟩ := varint_snoc u (fun z hz => hu z (by simp [hz])) y hy
    exact ⟨_, Varint.cont (hu x (by simp)) hn⟩

theorem all_snoc {u : List Byte} {y : Byte} (hu : ∀ x ∈ u, 128 ≤ x.toNat) (hy : 128 ≤ y.toNat) :
    ∀ x ∈ u ++ [y], 128 ≤ x.toNat := by
  intro x hx; simp at hx; rcases hx with hx | rfl; exact hu x hx; exact hy

/-- After the byte the scanner accepts, the unfinished field goes on, or it is complete (the same
bytes revealed and in the message: not a body passed over). -/
abbrev MoreOut (ob : Bool) (T : List Byte) (b : Option Nat) : Prop :=
  (∃ e nb, RT ob T e nb ∧ (nb = true → b = none)) ∨
    (∃ bf, RF ob T T bf ∧ (b = none ∨ bf = none) ∧ skOf ob (b.or bf) = skOf ob b)

/-- The scanner asks to pass over a body of `n` bytes: `T` is its key and complete length. -/
abbrev SkipOut (ob : Bool) (T : List Byte) (b : Option Nat) (n : Nat) : Prop :=
  0 < n ∧ ob = false ∧ b = none ∧ ∃ v, T = 0x22 :: v ∧ Varint v n ∧ v.length ≤ 10

/-- What the scanner's loop answers from the unfinished field's first byte, `k + 2` rounds left. -/
abbrev TailAns (ob : Bool) (H : List Byte) (b : Option Nat) (f : ReplyFields) (p k : Nat) : Need :=
  (loopResult (loopG (replyScanBody H (skOf ob b) ob) (k + 1 + 1) ⟨none, f, p⟩)).1

/-- The conclusion of the step lemmas. -/
abbrev StepOK (ob : Bool) (T : List Byte) (b : Option Nat) (r : Need) : Prop :=
  (r = .more → MoreOut ob T b) ∧ (∀ n, r = .skip n → SkipOut ob T b n)

theorem stepOK_malformed (ob : Bool) (T : List Byte) (b : Option Nat) : StepOK ob T b .malformed :=
  ⟨fun h => (by cases h), fun n h => (by cases h)⟩

theorem step_boundary {ob : Bool} {H : List Byte} {p : Nat} {y : Byte} (hd : H.drop p = [y]) {f : ReplyFields}
    {b : Option Nat} (k : Nat) : StepOK ob [y] b (TailAns ob H b f p k) := by
  by_cases hn : y = 0x08 ∨ y = 0x10
  · have hr := rsb_partial (u := []) (sk := skOf ob b) (ob := ob) (x := none) (f := f)
      (by rcases hn with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) (by simp) (by simp) (by simpa using hd)
    unfold TailAns; rw [loopG_done _ hr]
    exact ⟨fun _ => Or.inl ⟨_, _, RT.number hn (by simp) (by simp), fun e => by cases e⟩, fun n h => by cases h⟩
  by_cases hl : y = 0x1a ∨ y = 0x2a ∨ y = 0x22
  · have hr := rsb_partial (u := []) (sk := skOf ob b) (ob := ob) (x := none) (f := f)
      (Or.inr (Or.inr hl)) (by simp) (by simp) (by simpa using hd)
    unfold TailAns; rw [loopG_done _ hr]
    exact ⟨fun _ => Or.inl ⟨_, _, RT.lengthKey hl (by simp) (by simp), fun e => by cases e⟩, fun n h => by cases h⟩
  · have hr := rsb_bad (rest := []) (sk := skOf ob b) (ob := ob) (x := none) (f := f) hd
      (fun h => by rcases h with h | h | h | h | h <;> simp_all)
    unfold TailAns; rw [loopG_done _ hr]
    exact stepOK_malformed ob _ b

theorem step_number {ob : Bool} {tag : Byte} {u : List Byte} (ht : tag = 0x08 ∨ tag = 0x10)
    (hu : ∀ x ∈ u, 128 ≤ x.toNat) (hl : u.length < 10) {H : List Byte} {p : Nat} {y : Byte}
    (hd : H.drop p = tag :: (u ++ [y])) {f : ReplyFields} {b : Option Nat} (k : Nat) :
    StepOK ob (tag :: (u ++ [y])) b (TailAns ob H b f p k) := by
  have hlen := length_of_drop hd (by simp)
  simp only [List.length_cons, List.length_append, List.length_nil] at hlen
  by_cases hy : y.toNat < 128
  · obtain ⟨n, hv⟩ := varint_snoc u hu y hy
    have hvl : (u ++ [y]).length ≤ 10 := by simp; omega
    have h1 := replyScanBody_number (x := none) (f := f) (b := skOf ob b) (i := ob) (rest := []) ht hv hvl
      (by simpa using hd)
    have h2 := rsb_end (bytes := H) (sk := skOf ob b) (ob := ob) (x := none) (f := numberField tag n f)
      (pos := p + 1 + (u ++ [y]).length) (by simp; omega)
    unfold TailAns; rw [loopG_yield _ h1, loopG_done _ h2]
    exact ⟨fun _ => Or.inr ⟨none, RF.number ht hv hvl, Or.inr rfl, by cases b <;> rfl⟩, fun n h => by cases h⟩
  by_cases h10 : u.length + 1 < 10
  · have hr := rsb_partial (u := u ++ [y]) (sk := skOf ob b) (ob := ob) (x := none) (f := f)
      (by rcases ht with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) (all_snoc hu (by omega)) (by simp; omega) hd
    unfold TailAns; rw [loopG_done _ hr]
    exact ⟨fun _ => Or.inl ⟨_, _, RT.number ht (all_snoc hu (by omega)) (by simp; omega), fun e => by cases e⟩,
      fun n h => by cases h⟩
  · have hd1 : H.drop (p + 1) = u ++ [y] := by rw [← List.drop_drop, hd]; rfl
    have hTL := tooLong_of_drop hd1 (by simp; omega) (by
      rw [List.take_of_length_le (by simp; omega)]; exact all_snoc hu (by omega))
    have hr := replyScanBody_tooLong (x := none) (f := f) (b := skOf ob b) (i := ob)
      (by rcases ht with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) hd hTL
    unfold TailAns; rw [loopG_done _ hr]
    exact stepOK_malformed ob _ b

theorem step_short {ob : Bool} {tag : Byte} {v c : List Byte} {count : Nat} (ht : tag = 0x1a ∨ tag = 0x2a)
    (hv : Varint v count) (hvl : v.length ≤ 10) (hc : c.length < count) {H : List Byte} {p : Nat} {y : Byte}
    (hd : H.drop p = tag :: (v ++ (c ++ [y]))) {f : ReplyFields} {b : Option Nat} (k : Nat) :
    StepOK ob (tag :: (v ++ (c ++ [y]))) b (TailAns ob H b f p k) := by
  have hlen := length_of_drop hd (by simp)
  simp only [List.length_cons, List.length_append, List.length_nil] at hlen
  by_cases he : c.length + 1 = count
  · have hv' : Varint v (c ++ [y]).length := by simpa [he] using hv
    have h1 := replyScanBody_text (x := none) (f := f) (b := skOf ob b) (i := ob) (rest := []) ht hv' hvl
      (by simpa using hd)
    have h2 := rsb_end (bytes := H) (sk := skOf ob b) (ob := ob) (x := none) (f := f)
      (pos := p + 1 + v.length + (c ++ [y]).length) (by simp; omega)
    unfold TailAns; rw [loopG_yield _ h1, loopG_done _ h2]
    exact ⟨fun _ => Or.inr ⟨none, RF.text ht hv' hvl, Or.inr rfl, by cases b <;> rfl⟩, fun n h => by cases h⟩
  · have hr := rsb_textShort (sk := skOf ob b) (ob := ob) (x := none) (f := f) ht hv hvl
      (show (c ++ [y]).length < count by simp; omega) hd
    unfold TailAns; rw [loopG_done _ hr]
    exact ⟨fun _ => Or.inl ⟨_, _, RT.short ht hv hvl (show (c ++ [y]).length < count by simp; omega),
      fun e => by cases e⟩, fun n h => by cases h⟩

theorem step_inline {ob : Bool} {v c : List Byte} {count : Nat} (hob : ob = true)
    (hv : Varint v count) (hvl : v.length ≤ 10) (hc : c.length < count) {H : List Byte} {p : Nat} {y : Byte}
    (hd : H.drop p = 0x22 :: (v ++ (c ++ [y]))) {f : ReplyFields} {b : Option Nat} (hfb : f.body = b)
    (hb : b = none) (k : Nat) :
    StepOK ob (0x22 :: (v ++ (c ++ [y]))) b (TailAns ob H b f p k) := by
  subst hob hb
  have hlen := length_of_drop hd (by simp)
  simp only [List.length_cons, List.length_append, List.length_nil] at hlen
  by_cases he : c.length + 1 = count
  · have hv' : Varint v (c ++ [y]).length := by simpa [he] using hv
    have h1 := rsb_bodyField (x := none) (f := f) (sk := skOf true none) (ob := true) (rest := c ++ [y]) hv hvl hfb hd
      (fun h => by cases h.2.2.1) (fun _ => by omega)
    have h2 := rsb_end (bytes := H) (sk := skOf true none) (ob := true) (x := none) (f := { f with body := some count })
      (pos := if true = true then p + 1 + v.length + count else p + 1 + v.length) (by simp; omega)
    unfold TailAns; rw [loopG_yield _ h1, loopG_done _ h2]
    refine ⟨fun _ => Or.inr ⟨some (c ++ [y]).length, ?_, Or.inl rfl, rfl⟩, fun n h => by cases h⟩
    simpa using RF.body (ob := true) hv' hvl
  · have hr := rsb_inlineShort (sk := skOf true none) (x := none) (f := f) hv hvl hfb
      (show (c ++ [y]).length < count by simp; omega) hd
    unfold TailAns; rw [loopG_done _ hr]
    exact ⟨fun _ => Or.inl ⟨_, _, RT.inline rfl hv hvl (show (c ++ [y]).length < count by simp; omega),
      fun _ => rfl⟩, fun n h => by cases h⟩

theorem step_lengthKey {ob : Bool} {tag : Byte} {u : List Byte} (ht : tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22)
    (hu : ∀ x ∈ u, 128 ≤ x.toNat) (hl : u.length < 10) {H : List Byte} {p : Nat} {y : Byte}
    (hd : H.drop p = tag :: (u ++ [y])) {f : ReplyFields} {b : Option Nat} (hfb : f.body = b) (k : Nat) :
    StepOK ob (tag :: (u ++ [y])) b (TailAns ob H b f p k) := by
  have hlen := length_of_drop hd (by simp)
  simp only [List.length_cons, List.length_append, List.length_nil] at hlen
  have htag : tag = 0x08 ∨ tag = 0x10 ∨ tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22 := Or.inr (Or.inr ht)
  by_cases hy : y.toNat < 128
  case neg =>
    by_cases h10 : u.length + 1 < 10
    · have hr := rsb_partial (u := u ++ [y]) (sk := skOf ob b) (ob := ob) (x := none) (f := f) htag
        (all_snoc hu (by omega)) (by simp; omega) hd
      unfold TailAns; rw [loopG_done _ hr]
      exact ⟨fun _ => Or.inl ⟨_, _, RT.lengthKey ht (all_snoc hu (by omega)) (by simp; omega), fun e => by cases e⟩,
        fun n h => by cases h⟩
    · have hd1 : H.drop (p + 1) = u ++ [y] := by rw [← List.drop_drop, hd]; rfl
      have hTL := tooLong_of_drop hd1 (by simp; omega) (by
        rw [List.take_of_length_le (by simp; omega)]; exact all_snoc hu (by omega))
      have hr := replyScanBody_tooLong (x := none) (f := f) (b := skOf ob b) (i := ob) htag hd hTL
      unfold TailAns; rw [loopG_done _ hr]
      exact stepOK_malformed ob _ b
  obtain ⟨n, hv⟩ := varint_snoc u hu y hy
  have hvl : (u ++ [y]).length ≤ 10 := by simp; omega
  have hvlen : (u ++ [y]).length = u.length + 1 := by simp
  generalize hV : u ++ [y] = v at hv hvl hd hlen hvlen
  have hd0 : H.drop p = tag :: (v ++ ([] ++ [])) := by simpa using hd
  have hend : ∀ (g : ReplyFields) (q : Nat), H.length ≤ q →
      replyScanBody H (skOf ob b) ob ⟨none, g, q⟩ = .done ⟨some (.more, g), g, q⟩ :=
    fun g q hq => rsb_end hq
  rcases ht with ht | ht | ht
  case inr.inr =>
    subst ht
    cases b with
    | some m =>
      have hr := rsb_bodyTwice (x := none) (sk := skOf ob (some m)) (ob := ob) (f := f) (rest := []) hv hvl
        (by rw [hfb]; rfl) (by simpa using hd)
      unfold TailAns; rw [loopG_done _ hr]
      exact stepOK_malformed ob _ _
    | none =>
      cases ob
      · by_cases hn : 0 < n
        · have hr := replyScanBody_skip (x := none) (f := f) hv hvl hn hfb (by simpa using hd)
          unfold TailAns; rw [show skOf false none = false from rfl, loopG_done _ hr]
          exact ⟨fun h => (by cases h), fun n' h => by
            simp only [loopResult, Need.skip.injEq] at h
            subst h
            exact ⟨hn, rfl, rfl, v, rfl, hv, hvl⟩⟩
        · have hn0 : n = 0 := by omega
          subst hn0
          have hv' : Varint v ([] : List Byte).length := hv
          have h1 := rsb_bodyField (x := none) (f := f) (sk := skOf false none) (ob := false) (rest := []) hv hvl hfb
            (by simpa using hd) (fun h => by omega) (fun e => by cases e)
          have h2 := hend { f with body := some 0 } (if false = true then p + 1 + v.length + 0 else p + 1 + v.length)
            (by simp; omega)
          unfold TailAns; rw [loopG_yield _ h1, loopG_done _ h2]
          refine ⟨fun _ => Or.inr ⟨some 0, ?_, Or.inl rfl, rfl⟩, fun n h => by cases h⟩
          simpa using RF.body (ob := false) hv' hvl
      · by_cases hn : 0 < n
        · have hr := rsb_inlineShort (sk := skOf true none) (x := none) (f := f) (c := []) hv hvl hfb hn
            (by simpa using hd)
          unfold TailAns; rw [loopG_done _ hr]
          exact ⟨fun _ => Or.inl ⟨_, _, by simpa using RT.inline (ob := true) (c := []) rfl hv hvl hn, fun _ => rfl⟩,
            fun n h => by cases h⟩
        · have hn0 : n = 0 := by omega
          subst hn0
          have hv' : Varint v ([] : List Byte).length := hv
          have h1 := rsb_bodyField (x := none) (f := f) (sk := skOf true none) (ob := true) (rest := []) hv hvl hfb
            (by simpa using hd) (fun h => by cases h.2.2.1) (fun _ => by omega)
          have h2 := hend { f with body := some 0 } (if true = true then p + 1 + v.length + 0 else p + 1 + v.length)
            (by simp; omega)
          unfold TailAns; rw [loopG_yield _ h1, loopG_done _ h2]
          refine ⟨fun _ => Or.inr ⟨some 0, ?_, Or.inl rfl, rfl⟩, fun n h => by cases h⟩
          simpa using RF.body (ob := true) hv' hvl
  all_goals
    have ht' : tag = 0x1a ∨ tag = 0x2a := by first | exact Or.inl ht | exact Or.inr ht
    by_cases hn : 0 < n
    · have hr := rsb_textShort (sk := skOf ob b) (ob := ob) (x := none) (f := f) (c := []) ht' hv hvl hn
        (by simpa using hd)
      unfold TailAns; rw [loopG_done _ hr]
      exact ⟨fun _ => Or.inl ⟨_, _, by simpa using RT.short (ob := ob) (c := []) ht' hv hvl hn, fun e => by cases e⟩,
        fun n h => by cases h⟩
    · have hn0 : n = 0 := by omega
      subst hn0
      have hv' : Varint v ([] : List Byte).length := hv
      have h1 := replyScanBody_text (x := none) (f := f) (b := skOf ob b) (i := ob) (rest := []) ht' hv' hvl hd0
      have h2 := hend f (p + 1 + v.length + ([] : List Byte).length) (by simp; omega)
      unfold TailAns; rw [loopG_yield _ h1, loopG_done _ h2]
      refine ⟨fun _ => Or.inr ⟨none, ?_, Or.inr rfl, by cases b <;> rfl⟩, fun n h => by cases h⟩
      simpa using RF.text (ob := ob) ht' hv' hvl

theorem tail_step {ob : Bool} {T : List Byte} {e : Nat} {nb : Bool} (ht : RT ob T e nb) {H : List Byte} {p : Nat}
    {y : Byte} (hd : H.drop p = T ++ [y]) {f : ReplyFields} {b : Option Nat} (hfb : f.body = b)
    (hnb : nb = true → b = none) (k : Nat) : StepOK ob (T ++ [y]) b (TailAns ob H b f p k) := by
  cases ht with
  | boundary => exact step_boundary hd k
  | number htag hu hl => exact step_number htag hu hl hd k
  | lengthKey htag hu hl => exact step_lengthKey htag hu hl hd hfb k
  | @short tag v c count htag hv hvl hc =>
    rw [show tag :: (v ++ c) ++ [y] = tag :: (v ++ (c ++ [y])) by simp] at hd ⊢
    exact step_short htag hv hvl hc hd k
  | @inline v c count hob hv hvl hc =>
    rw [show (0x22 : Byte) :: (v ++ c) ++ [y] = 0x22 :: (v ++ (c ++ [y])) by simp] at hd ⊢
    exact step_inline hob hv hvl hc hd hfb (hnb rfl) k

/-! ### `replyScan` on the controller's revealed bytes -/

theorem get_wrapper (lw : List Byte) : PublicReceive.get (8 :: 2 :: 0x1a :: lw) 2 = 0x1a := rfl

theorem head_ok (lw : List Byte) :
    ((8 :: 2 :: 0x1a :: lw : List Byte).take 2 == [8, 2] && PublicReceive.get (8 :: 2 :: 0x1a :: lw) 2 == 0x1a) = true := by
  rfl

/-- **`replyScan` on the revealed bytes of a response with complete fields**: its answer is the one the
unfinished field's rounds give, the complete fields having been walked. -/
theorem scan_fields {ob : Bool} {lw R F T : List Byte} {m : Nat} {b : Option Nat} (hw : Varint lw m)
    (hwl : lw.length ≤ 10) (hr : RFs ob R F b) :
    ∃ f k, f.body = b ∧ (replyScan (8 :: 2 :: 0x1a :: (lw ++ (R ++ T))) (skOf ob b) ob).1 =
      TailAns ob (8 :: 2 :: 0x1a :: (lw ++ (R ++ T))) b f (3 + lw.length + R.length) k := by
  generalize hH : (8 :: 2 :: 0x1a :: (lw ++ (R ++ T)) : List Byte) = H
  have hlen : H.length = 3 + lw.length + R.length + T.length := by rw [← hH]; simp; omega
  have hd3 : H.drop 3 = lw ++ (R ++ T) := by rw [← hH]; rfl
  have hvar := varintAt_varint (rest := R ++ T) hw hwl hd3
  have hdp : H.drop (3 + lw.length) = R ++ T := by rw [← List.drop_drop, hd3, List.drop_left]
  obtain ⟨n, f', hn, hreach, hbody⟩ := rfs_scan hr H T (3 + lw.length) (skOf ob b) {} hdp (Or.inl rfl)
    (fun m e e2 e3 => by subst e e2; simp [skOf, e3])
  refine ⟨f', H.length - 1 - n, by rw [hbody]; cases b <;> rfl, ?_⟩
  rw [replyScan_eq, if_neg (by omega), if_pos (by rw [← hH]; exact head_ok _), hvar]
  dsimp only
  rw [show H.length + 1 = n + (H.length - 1 - n + 1 + 1) by omega, loopG_reaches n _ _ _ hreach]

/-! ### The shape is kept -/

theorem rshape_fields_eq {ob : Bool} {lw R F T : List Byte} {m e : Nat} {b : Option Nat} {nb : Bool}
    (hw : Varint lw m) (hwl : lw.length ≤ 10) (hr : RFs ob R F b) (ht : RT ob T e nb) (hnb : nb = true → b = none)
    {H P : List Byte} {sk : Bool} (hH : H = 8 :: 2 :: 0x1a :: (lw ++ (R ++ T))) (hP : P = 0x1a :: (lw ++ (F ++ T)))
    (hsk : sk = skOf ob b) : RShape ob H sk P := by
  subst hH hP hsk; exact RShape.fields hw hwl hr ht hnb

/-- **Every byte the scanner accepts keeps the shape.** -/
theorem rshape_more {ob : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P) (y : Byte)
    (hm : (replyScan (H ++ [y]) sk ob).1 = .more) : RShape ob (H ++ [y]) sk (P ++ [y]) := by
  cases h with
  | kind =>
    by_cases hy : y = 0x1a
    · subst hy; exact RShape.wrapper (u := []) (by simp) (by simp)
    · exfalso
      have hb : ((([8, 2] ++ [y]) : List Byte).take 2 == [8, 2] && PublicReceive.get ([8, 2] ++ [y]) 2 == 0x1a) = false := by
        simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, beq_self_eq_true,
          Bool.true_and]
        exact beq_eq_false_iff_ne.mpr hy
      rw [replyScan_eq, if_neg (by simp), if_neg (by rw [hb]; simp)] at hm
      cases hm
  | wrapper hu hl =>
    rename_i u
    have hH : (8 :: 2 :: 0x1a :: u : List Byte) ++ [y] = 8 :: 2 :: 0x1a :: (u ++ [y]) := by simp
    rw [hH] at hm ⊢
    have hd3 : (8 :: 2 :: 0x1a :: (u ++ [y]) : List Byte).drop 3 = u ++ [y] := rfl
    by_cases hy : y.toNat < 128
    · obtain ⟨n, hv⟩ := varint_snoc u hu y hy
      have hvl : (u ++ [y]).length ≤ 10 := by simp; omega
      have e := RShape.fields (ob := ob) (R := []) (F := []) (T := []) hv hvl RFs.nil RT.boundary (fun e => by cases e)
      simpa [skOf] using e
    · by_cases h10 : u.length + 1 < 10
      · have := RShape.wrapper (ob := ob) (all_snoc hu (by omega)) (show (u ++ [y]).length < 10 by simp; omega)
        simpa using this
      · exfalso
        have hTL := tooLong_of_drop hd3 (by simp; omega) (by
          rw [List.take_of_length_le (by simp; omega)]; exact all_snoc hu (by omega))
        rw [replyScan_eq, if_neg (by simp), if_pos (head_ok _), varintAt_tooLong hTL] at hm
        dsimp only at hm
        rw [if_pos hTL] at hm
        cases hm
  | fields hw hwl hr ht hnb =>
    rename_i lw R F T m e b nb
    have hH : (8 :: 2 :: 0x1a :: (lw ++ (R ++ T)) : List Byte) ++ [y] = 8 :: 2 :: 0x1a :: (lw ++ (R ++ (T ++ [y]))) := by
      simp
    rw [hH] at hm ⊢
    obtain ⟨f, k, hfb, hs⟩ := scan_fields (T := T ++ [y]) hw hwl hr
    have hd : (8 :: 2 :: 0x1a :: (lw ++ (R ++ (T ++ [y]))) : List Byte).drop (3 + lw.length + R.length) = T ++ [y] := by
      rw [show 3 + lw.length + R.length = 3 + (lw.length + R.length) by omega, ← List.drop_drop]
      simp
    have hstep := tail_step ht hd hfb hnb k
    rw [hs] at hm
    rcases hstep.1 hm with ⟨e', nb', ht', hnb'⟩ | ⟨bf, hrf, hbb, hsk⟩
    · exact rshape_fields_eq hw hwl hr ht' (fun x => hnb' x) (by simp) (by simp) rfl
    · exact rshape_fields_eq (T := []) hw hwl (rfs_snoc hr hrf hbb) RT.boundary (fun x => by cases x)
        (by simp) (by simp) hsk.symm

/-- **A body the scanner asks to pass over keeps the shape**, whatever its `n` bytes. -/
theorem rshape_skip {ob : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P) (y : Byte)
    {n : Nat} (hm : (replyScan (H ++ [y]) sk ob).1 = .skip n) (B : List Byte) (hB : B.length = n) :
    RShape ob (H ++ [y]) true (P ++ y :: B) := by
  cases h with
  | kind =>
    exfalso
    by_cases hy : y = 0x1a
    · subst hy
      have e : (replyScan ([8, 2] ++ [0x1a]) false ob).1 = .more := by cases ob <;> rfl
      rw [e] at hm; cases hm
    · have hb : ((([8, 2] ++ [y]) : List Byte).take 2 == [8, 2] && PublicReceive.get ([8, 2] ++ [y]) 2 == 0x1a) = false := by
        simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, beq_self_eq_true,
          Bool.true_and]
        exact beq_eq_false_iff_ne.mpr hy
      rw [replyScan_eq, if_neg (by simp), if_neg (by rw [hb]; simp)] at hm
      cases hm
  | wrapper hu hl =>
    rename_i u
    exfalso
    have hH : (8 :: 2 :: 0x1a :: u : List Byte) ++ [y] = 8 :: 2 :: 0x1a :: (u ++ [y]) := by simp
    rw [hH] at hm
    have hd3 : (8 :: 2 :: 0x1a :: (u ++ [y]) : List Byte).drop 3 = u ++ [y] := rfl
    rw [replyScan_eq, if_neg (by simp), if_pos (head_ok _)] at hm
    by_cases hy : y.toNat < 128
    · obtain ⟨n', hv⟩ := varint_snoc u hu y hy
      have hvl : (u ++ [y]).length ≤ 10 := by simp; omega
      rw [varintAt_varint (rest := []) hv hvl (by rw [hd3, List.append_nil])] at hm
      dsimp only at hm
      rw [loopG_done _ (rsb_end (by simp; omega))] at hm
      cases hm
    · have hpart := varintAt_partial (all_snoc hu (by omega)) hd3
      rw [hpart] at hm
      dsimp only at hm
      split at hm <;> cases hm
  | fields hw hwl hr ht hnb =>
    rename_i lw R F T m e b nb
    have hH : (8 :: 2 :: 0x1a :: (lw ++ (R ++ T)) : List Byte) ++ [y] = 8 :: 2 :: 0x1a :: (lw ++ (R ++ (T ++ [y]))) := by
      simp
    rw [hH] at hm ⊢
    obtain ⟨f, k, hfb, hs⟩ := scan_fields (T := T ++ [y]) hw hwl hr
    have hd : (8 :: 2 :: 0x1a :: (lw ++ (R ++ (T ++ [y]))) : List Byte).drop (3 + lw.length + R.length) = T ++ [y] := by
      rw [show 3 + lw.length + R.length = 3 + (lw.length + R.length) by omega, ← List.drop_drop]
      simp
    have hstep := tail_step ht hd hfb hnb k
    rw [hs] at hm
    obtain ⟨hn, hob, hb, v, hT, hv, hvl⟩ := hstep.2 n hm
    subst hob hb
    have hv' : Varint v B.length := by rw [hB]; exact hv
    have hrf : RF false (0x22 :: v) (0x22 :: (v ++ B)) (some B.length) := by simpa using RF.body (ob := false) hv' hvl
    refine rshape_fields_eq (T := []) hw hwl (rfs_snoc hr hrf (Or.inl rfl)) RT.boundary (fun x => by cases x)
      (by rw [hT]; simp) ?_ ?_
    · have hP : (0x1a :: (lw ++ (F ++ T)) : List Byte) ++ y :: B = 0x1a :: (lw ++ (F ++ ((T ++ [y]) ++ B))) := by simp
      rw [hP, hT]; simp
    · simp [skOf, hB, hn]

/-! ### `replyBudget` on the controller's revealed bytes -/

theorem bb_end {bytes : List Byte} {ob : Bool} {x : Option Nat} {pos : Nat} (h : bytes.length ≤ pos) :
    budgetBody bytes ob ⟨x, pos⟩ = .done ⟨some 2, pos⟩ := by
  unfold budgetBody; rw [if_pos h]

/-- **The budget at the unfinished field** is the one `RT` records. -/
theorem tail_budget {ob : Bool} {T : List Byte} {e : Nat} {nb : Bool} (ht : RT ob T e nb) {H : List Byte} {p : Nat}
    (hd : H.drop p = T) (k : Nat) : budgetResult (loopG (budgetBody H ob) (k + 1) ⟨none, p⟩) = e := by
  cases ht with
  | boundary =>
    have : H.length ≤ p := by have := congrArg List.length hd; simp at this; omega
    rw [loopG_done _ (bb_end this)]; rfl
  | @number tag u htag hu hl =>
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    have hvar := varintAt_partial hu hd1
    have r : budgetBody H ob ⟨none, p⟩ = .done ⟨some (if p + 1 ≥ H.length then 1 else min 3 (11 - (H.length - (p + 1)))), p⟩ := by
      unfold budgetBody
      simp only [hg, hvar, rtag_number tag htag, ge_iff_le, hp, if_false, if_true]
    rw [loopG_done _ r]
    unfold budgetResult numBudget
    by_cases hu0 : u = []
    · subst hu0; simp at hlen; simp [hlen]
    · have : u.length ≠ 0 := fun e => hu0 (List.eq_nil_of_length_eq_zero e)
      simp only [hu0, if_false]
      rw [if_neg (by omega)]
      congr 2; omega
  | @lengthKey tag u htag hu hl =>
    obtain ⟨hg, hd1, hp, -⟩ := field_at hd
    have hvar := varintAt_partial hu hd1
    have r : budgetBody H ob ⟨none, p⟩ = .done ⟨some 1, p⟩ := by
      unfold budgetBody
      simp only [hg, hvar, ge_iff_le, hp, if_false]
      rcases htag with rfl | rfl | rfl <;> rfl
    rw [loopG_done _ r]; rfl
  | @short tag v c count htag hv hvl hc =>
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    simp only [List.length_append] at hlen
    have hvar := varintAt_varint hv hvl hd1
    have hn : H.length < p + 1 + v.length + count := by omega
    obtain ⟨t1, t2⟩ := rtag_text tag htag
    have r : budgetBody H ob ⟨none, p⟩ = .done ⟨some (p + 1 + v.length + count - H.length), p⟩ := by
      unfold budgetBody
      simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true]
    rw [loopG_done _ r]
    show p + 1 + v.length + count - H.length = count - c.length
    omega
  | @inline v c count hob hv hvl hc =>
    subst hob
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    simp only [List.length_append] at hlen
    have hvar := varintAt_varint hv hvl hd1
    obtain ⟨t1, t2, t3⟩ := tag22_bools
    have hi : (true && decide (p + 1 + v.length + count > H.length)) = true := by
      simp only [Bool.true_and, decide_eq_true_eq]; omega
    have r : budgetBody H true ⟨none, p⟩ = .done ⟨some (p + 1 + v.length + count - H.length), p⟩ := by
      unfold budgetBody
      simp only [hg, hvar, t1, t2, t3, hi, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true]
    rw [loopG_done _ r]
    show p + 1 + v.length + count - H.length = count - c.length
    omega

/-- The budget after complete fields. -/
theorem budget_fields {ob : Bool} {lw R F T : List Byte} {m e : Nat} {b : Option Nat} {nb : Bool}
    (hw : Varint lw m) (hwl : lw.length ≤ 10) (hr : RFs ob R F b) (ht : RT ob T e nb) :
    replyBudget (8 :: 2 :: 0x1a :: (lw ++ (R ++ T))) ob = e := by
  generalize hH : (8 :: 2 :: 0x1a :: (lw ++ (R ++ T)) : List Byte) = H
  have hlen : H.length = 3 + lw.length + R.length + T.length := by rw [← hH]; simp; omega
  have hd3 : H.drop 3 = lw ++ (R ++ T) := by rw [← hH]; rfl
  have hvar := varintAt_varint (rest := R ++ T) hw hwl hd3
  have hdp : H.drop (3 + lw.length) = R ++ T := by rw [← List.drop_drop, hd3, List.drop_left]
  obtain ⟨n, hn, hreach⟩ := rfs_budget hr H T (3 + lw.length) hdp
  have hdt : H.drop (3 + lw.length + R.length) = T := by
    rw [← List.drop_drop, hdp, List.drop_left]
  rw [replyBudget_eq, if_neg (by omega), hvar]
  dsimp only
  rw [show H.length + 1 = n + (H.length - n + 1) by omega, loopG_reaches n _ _ _ hreach]
  exact tail_budget ht hdt _

/-! ### The reference, after the revealed bytes -/

/-- Byte `q` of `C` may be revealed: it is public, or it is the first `error`. -/
def SafeAt (C : List Class) (q : Nat) : Prop :=
  ∃ c, C[q]? = some c ∧ (c.secret = false ∨ (c = .error ∧ ∀ j < q, C[j]? ≠ some .error))

theorem safeAt_append {A C : List Class} {q : Nat} (hA : ∀ x ∈ A, x ≠ .error) (h : SafeAt C q) :
    SafeAt (A ++ C) (A.length + q) := by
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨c, by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hc, ?_⟩
  rcases hs with hs | ⟨he, hj⟩
  · exact Or.inl hs
  · refine Or.inr ⟨he, fun j hj' => ?_⟩
    by_cases hjA : j < A.length
    · rw [List.getElem?_append_left hjA]
      intro e
      exact hA _ (List.mem_of_getElem? e) rfl
    · rw [List.getElem?_append_right (by omega)]
      exact hj _ (by omega)

theorem safeAt_public {C : List Class} {q : Nat} {c : Class} (h : C[q]? = some c) (hc : c.secret = false) :
    SafeAt C q := ⟨c, h, Or.inl hc⟩

theorem fill_get {α : Type} (k : Class) (l : List α) (q : Nat) (h : q < l.length) : (fill k l)[q]? = some k := by
  simp [fill, h]

theorem safeAt_fill {α : Type} {k : Class} (hk : k.secret = false) (l : List α) (q : Nat) (h : q < l.length) :
    SafeAt (fill k l) q := safeAt_public (fill_get k l q h) hk

theorem fill_noerr {α : Type} {k : Class} (hk : k ≠ .error) (l : List α) : ∀ x ∈ fill k l, x ≠ .error := by
  intro x hx; simp [fill] at hx; rw [← hx.2]; exact hk

theorem safeAt_prefix {A C : List Class} {q : Nat} (hq : q < A.length) (h : SafeAt A q) : SafeAt (A ++ C) q := by
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨c, by rw [List.getElem?_append_left hq]; exact hc, ?_⟩
  rcases hs with hs | ⟨he, hj⟩
  · exact Or.inl hs
  · exact Or.inr ⟨he, fun j hj' => by rw [List.getElem?_append_left (by omega)]; exact hj j hj'⟩

/-- The first class of `varintThen` on a non-empty list is `structure`. -/
theorem varintThen_head (x : Byte) (W : List Byte) (next : Nat → List Byte → List Class) :
    (varintThen (x :: W) next)[0]? = some .structure := by
  unfold varintThen
  cases hv : varintEnd 10 (x :: W) with
  | done m =>
    have := ReceiveStream.varintEnd_done_le 10 _ m hv
    simp only
    rw [List.getElem?_append_left (by rw [fillL, List.length_take]; simp; omega)]
    exact fill_get _ _ 0 (by simp; omega)
  | short => exact fill_get _ _ 0 (by simp)
  | tooLong =>
    simp only
    rw [List.getElem?_append_left (by rw [fillL, List.length_take]; simp; omega)]
    exact fill_get _ _ 0 (by simp)

/-- **A field boundary**: the next key and the byte after it are public, or the byte after a bad key is
the first `error`. -/
theorem rf_boundary (ob : Bool) (Z : List Byte) (q : Nat) (hq : q < 2) (hz : q < Z.length) :
    SafeAt (responseFields ob false Z) q := by
  match Z, q with
  | y :: W, 0 =>
    unfold responseFields; rw [ReceiveStream.response_cons]
    split
    · exact safeAt_public rfl rfl
    · split
      · exact safeAt_public rfl rfl
      · split
        · exact safeAt_public rfl rfl
        · exact safeAt_public rfl rfl
  | y :: x :: W, 1 =>
    unfold responseFields; rw [ReceiveStream.response_cons]
    split
    · exact safeAt_public (by rw [List.getElem?_cons_succ]; exact varintThen_head x W _) rfl
    · split
      · exact safeAt_public (by rw [List.getElem?_cons_succ, ReceiveStream.delimitedThen_eq]; exact varintThen_head x W _) rfl
      · split
        · exact safeAt_public (by rw [List.getElem?_cons_succ, ReceiveStream.delimitedThen_eq]; exact varintThen_head x W _) rfl
        · refine ⟨.error, by simp [fill], Or.inr ⟨rfl, fun j hj => ?_⟩⟩
          have : j = 0 := by omega
          subst this; simp
  | [y], 1 => simp at hz

theorem varintEnd_short_of : ∀ (a : Nat) (u : List Byte), (∀ x ∈ u, 128 ≤ x.toNat) → u.length < a →
    varintEnd a u = .short
  | 0, _, _, h => by omega
  | a + 1, [], _, _ => rfl
  | a + 1, x :: u, hu, hl => by
    rw [ReceiveStream.varintEnd_cons, if_neg (by have := hu x (by simp); omega),
      varintEnd_short_of a u (fun z hz => hu z (by simp [hz])) (by simp at hl; omega)]
    rfl

/-- Inside a varint whose `u` bytes so far all continue: the next `k` positions (as far as the 10th
byte) are `structure` while the varint goes on; `varint_run` below says what comes after. -/
theorem varint_pos {u : List Byte} (hu : ∀ x ∈ u, 128 ≤ x.toNat) (hl : u.length < 10) (Y : List Byte)
    (next : Nat → List Byte → List Class) (q : Nat) (_hq : u.length ≤ q) (hq10 : q < 10) (hqY : q < u.length + Y.length) :
    (∃ m, varintEnd 10 (u ++ Y) = .done m ∧ u.length < m ∧ (q < m → (varintThen (u ++ Y) next)[q]? = some .structure) ∧
      (m ≤ q → (varintThen (u ++ Y) next)[q]? = (next (varintValue ((u ++ Y).take m)) ((u ++ Y).drop m))[q - m]? ∧
        ∀ j < m, (varintThen (u ++ Y) next)[j]? = some .structure)) ∨
    (varintThen (u ++ Y) next)[q]? = some .structure := by
  have hs := varintEnd_short_of 10 u hu hl
  cases hv : varintEnd 10 (u ++ Y) with
  | done m =>
    have hm := ReceiveStream.varintEnd_append_short 10 u Y m hs hv
    have hle := ReceiveStream.varintEnd_done_le 10 _ m hv
    refine Or.inl ⟨m, rfl, hm, fun hqm => ?_, fun hmq => ⟨?_, fun j hj => ?_⟩⟩
    · rw [varintThen_done hv, List.getElem?_append_left (by rw [fillL, List.length_take]; omega)]
      exact fill_get _ _ _ (by rw [List.length_take]; omega)
    · rw [varintThen_done hv, List.getElem?_append_right (by rw [fillL, List.length_take]; omega), fillL,
        List.length_take, Nat.min_eq_left hle.2.1]
    · rw [varintThen_done hv, List.getElem?_append_left (by rw [fillL, List.length_take]; omega)]
      exact fill_get _ _ _ (by rw [List.length_take]; omega)
  | short =>
    exact Or.inr (by rw [varintThen_short hv]; exact fill_get _ _ _ (by simp; omega))
  | tooLong =>
    have hle := ReceiveStream.varintEnd_tooLong_le 10 _ hv
    exact Or.inr (by
      rw [varintThen_tooLong hv, List.getElem?_append_left (by rw [fillL, List.length_take]; omega)]
      exact fill_get _ _ _ (by rw [List.length_take]; omega))

theorem rf_cons_number (ob : Bool) {tag : Byte} (ht : tag = 0x08 ∨ tag = 0x10) (Z : List Byte) :
    responseFields ob false (tag :: Z) =
      .structure :: varintThen Z (fun _ after => ReceiveSpec.response ob false (Z.length + 1) after) := by
  unfold responseFields; rw [List.length_cons, ReceiveStream.response_cons, if_pos ht]

theorem rf_cons_delim (ob : Bool) {tag : Byte} (ht : tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22) (Z : List Byte) :
    ∃ k : Class, responseFields ob false (tag :: Z) =
      .structure :: varintThen Z (ReceiveStream.delimCont false (fill k)
        (fun _ after => ReceiveSpec.response ob false (Z.length + 1) after)) ∧
      (tag = 0x1a ∨ tag = 0x2a → k = .text) ∧ (tag = 0x22 → k = if ob then .text else .body) := by
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons]
  rcases ht with rfl | rfl | rfl
  · exact ⟨.text, by rw [if_neg (by decide), if_pos (Or.inl rfl)]; rfl, fun _ => rfl, fun h => by cases h⟩
  · exact ⟨.text, by rw [if_neg (by decide), if_pos (Or.inr rfl)]; rfl, fun _ => rfl, fun h => by cases h⟩
  · exact ⟨if ob then .text else .body, by rw [if_neg (by decide), if_neg (by decide), if_pos rfl]; rfl,
      fun h => (by rcases h with h | h <;> cases h), fun _ => rfl⟩

/-- **Inside an id or status**: the run `replyBudget` allows (`numBudget`) is public, or ends at the
first `error` (the byte after a bad key; the 11th byte of a varint). -/
theorem num_run {ob : Bool} {u : List Byte} (hu : ∀ x ∈ u, 128 ≤ x.toNat) (hl : u.length < 10) (Y : List Byte)
    (hY : Y.length ≤ numBudget u) (fuel : Nat) (hf : (u ++ Y).length < fuel) (i : Nat) (hi : i < Y.length) :
    SafeAt (varintThen (u ++ Y) (fun _ after => ReceiveSpec.response ob false fuel after)) (u.length + i) := by
  have hb : (u = [] → i = 0) ∧ i ≤ 2 ∧ u.length + i ≤ 10 := by
    unfold numBudget at hY
    by_cases hu0 : u = []
    · subst hu0; simp at hY; simp; omega
    · rw [if_neg hu0] at hY
      have : u.length ≠ 0 := fun e => hu0 (List.eq_nil_of_length_eq_zero e)
      refine ⟨fun e => absurd e hu0, by omega, by omega⟩
  have hs := varintEnd_short_of 10 u hu hl
  have hqY : u.length + i < (u ++ Y).length := by simp; omega
  cases hv : varintEnd 10 (u ++ Y) with
  | done m =>
    have hm := ReceiveStream.varintEnd_append_short 10 u Y m hs hv
    have hle := ReceiveStream.varintEnd_done_le 10 _ m hv
    rw [varintThen_done hv]
    by_cases hq : u.length + i < m
    · exact safeAt_prefix (by rw [fillL, List.length_take]; omega)
        (safeAt_fill rfl _ _ (by rw [List.length_take]; omega))
    · have e1 : u.length + i = (fill Class.structure ((u ++ Y).take m)).length + (u.length + i - m) := by
        rw [fillL, List.length_take]; omega
      rw [e1]
      apply safeAt_append (fill_noerr (by decide) _)
      rw [rf_fuel ob _ fuel (by simp only [List.length_drop]; omega)]
      apply rf_boundary ob _ _ (by
        rcases Nat.eq_zero_or_pos u.length with h0 | h0
        · have : u = [] := List.eq_nil_of_length_eq_zero h0
          have := hb.1 this; omega
        · omega) (by simp; omega)
  | short =>
    rw [varintThen_short hv]
    exact safeAt_fill rfl _ _ hqY
  | tooLong =>
    have hle := ReceiveStream.varintEnd_tooLong_le 10 _ hv
    rw [varintThen_tooLong hv]
    by_cases hq : u.length + i < 10
    · exact safeAt_prefix (by rw [fillL, List.length_take]; omega)
        (safeAt_fill rfl _ _ (by rw [List.length_take]; omega))
    · have hq10 : u.length + i = 10 := by omega
      rw [hq10]
      refine ⟨.error, ?_, Or.inr ⟨rfl, fun j hj => ?_⟩⟩
      · rw [List.getElem?_append_right (by rw [fillL, List.length_take]; omega), fillL, List.length_take,
          Nat.min_eq_left hle]
        exact fill_get _ _ _ (by simp; omega)
      · rw [List.getElem?_append_left (by rw [fillL, List.length_take]; omega),
          fill_get _ _ _ (by rw [List.length_take]; omega)]
        decide

theorem safeAt_cons {x : Class} (hx : x ≠ .error) {C : List Class} {q : Nat} (h : SafeAt C q) :
    SafeAt (x :: C) (q + 1) := by
  have := safeAt_append (A := [x]) (by simpa using hx) h
  simpa [Nat.add_comm] using this

/-- **The reference after the unfinished field**: every byte of the run `replyBudget` allows there
(`e`, whatever its bytes) is public, or is the first `error`. -/
theorem rt_run {ob : Bool} {T : List Byte} {e : Nat} {nb : Bool} (ht : RT ob T e nb) (Y : List Byte)
    (hY : Y.length ≤ e) (i : Nat) (hi : i < Y.length) :
    SafeAt (responseFields ob false (T ++ Y)) (T.length + i) := by
  cases ht with
  | boundary =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    exact rf_boundary ob Y i (by omega) hi
  | @number tag u htag hu hl =>
    rw [List.cons_append, rf_cons_number ob htag, List.length_cons,
      show u.length + 1 + i = (u.length + i) + 1 by omega]
    exact safeAt_cons (by decide) (num_run hu hl Y hY ((u ++ Y).length + 1) (by simp) i hi)
  | @lengthKey tag u htag hu hl =>
    obtain ⟨k, e1, -, -⟩ := rf_cons_delim ob htag (u ++ Y)
    rw [List.cons_append, e1, List.length_cons, show u.length + 1 + i = (u.length + i) + 1 by omega]
    apply safeAt_cons (by decide)
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    rcases varint_pos hu hl (y :: Y') _ u.length (Nat.le_refl _) hl (by simp) with ⟨m, -, hm, hlt, -⟩ | h
    · exact safeAt_public (hlt hm) rfl
    · exact safeAt_public h rfl
  | @short tag v c count htag hv hvl hc =>
    have htag' : tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22 := by
      rcases htag with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
    obtain ⟨k, e1, hk, -⟩ := rf_cons_delim ob htag' (v ++ (c ++ Y))
    have hk' := hk htag
    subst hk'
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    rw [if_neg (by simp)]
    rw [show (tag :: (v ++ c)).length + i = ((fill Class.structure v).length + (c.length + i)) + 1 by
      simp [fillL]; omega]
    apply safeAt_cons (by decide)
    apply safeAt_append (A := fill Class.structure v) (fill_noerr (by decide) _)
    apply safeAt_prefix (by rw [fillL, List.length_take]; simp; omega)
    exact safeAt_fill rfl _ _ (by rw [List.length_take]; simp; omega)
  | @inline v c count hob hv hvl hc =>
    subst hob
    obtain ⟨k, e1, -, hk⟩ := rf_cons_delim true (Or.inr (Or.inr rfl)) (v ++ (c ++ Y))
    have hk' := hk rfl
    simp only [if_true] at hk'
    subst hk'
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    rw [if_neg (by simp)]
    rw [show (0x22 :: (v ++ c) : List Byte).length + i = ((fill Class.structure v).length + (c.length + i)) + 1 by
      simp [fillL]; omega]
    apply safeAt_cons (by decide)
    apply safeAt_append (A := fill Class.structure v) (fill_noerr (by decide) _)
    apply safeAt_prefix (by rw [fillL, List.length_take]; simp; omega)
    exact safeAt_fill rfl _ _ (by rw [List.length_take]; simp; omega)

theorem response_nil (ob : Bool) (k : Nat) : ReceiveSpec.response ob false (k + 1) [] = [] := rfl

/-- Nothing in the unfinished field is `error`. -/
theorem rt_noerror {ob : Bool} {T : List Byte} {e : Nat} {nb : Bool} (ht : RT ob T e nb) :
    ∀ x ∈ responseFields ob false T, x ≠ .error := by
  cases ht with
  | boundary => intro x hx; simp [responseFields, ReceiveSpec.response] at hx
  | @number tag u htag hu hl =>
    rw [rf_cons_number ob htag, varintThen_short (varintEnd_short_of 10 u hu hl)]
    intro x hx; simp only [List.mem_cons] at hx
    rcases hx with rfl | hx; decide; exact fill_noerr (by decide) _ x hx
  | @lengthKey tag u htag hu hl =>
    obtain ⟨k, e1, -, -⟩ := rf_cons_delim ob htag u
    rw [e1, varintThen_short (varintEnd_short_of 10 u hu hl)]
    intro x hx; simp only [List.mem_cons] at hx
    rcases hx with rfl | hx; decide; exact fill_noerr (by decide) _ x hx
  | @short tag v c count htag hv hvl hc =>
    have htag' : tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22 := by
      rcases htag with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
    obtain ⟨k, e1, hk, -⟩ := rf_cons_delim ob htag' (v ++ c)
    have hk' := hk htag
    subst hk'
    rw [e1, show v ++ c = v ++ (c ++ []) by simp, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    rw [if_neg (by simp), List.drop_eq_nil_of_le (by simp; omega)]
    dsimp only
    rw [response_nil, List.append_nil]
    intro x hx; simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · decide
    · exact fill_noerr (by decide) _ x hx
    · exact fill_noerr (by decide) _ x hx
  | @inline v c count hob hv hvl hc =>
    subst hob
    obtain ⟨k, e1, -, hk⟩ := rf_cons_delim true (Or.inr (Or.inr rfl)) (v ++ c)
    have hk' := hk rfl
    simp only [if_true] at hk'
    subst hk'
    rw [e1, show v ++ c = v ++ (c ++ []) by simp, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    rw [if_neg (by simp), List.drop_eq_nil_of_le (by simp; omega)]
    dsimp only
    rw [response_nil, List.append_nil]
    intro x hx; simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · decide
    · exact fill_noerr (by decide) _ x hx
    · exact fill_noerr (by decide) _ x hx

/-! ### The response half of T1, at the message level -/

theorem message_kind (ob : Bool) (Z : List Byte) :
    ReceiveSpec.message ob false (8 :: 2 :: Z) = .kind :: .kind :: ReceiveSpec.wrapper 0x1a (responseFields ob false) Z := by
  match Z with
  | [] => rfl
  | _ :: _ => rw [ReceiveStream.message_eq, if_neg (by decide), if_pos ⟨rfl, rfl⟩]

theorem wrapper_cons (key k : Byte) (fields : List Byte → List Class) (rest : List Byte) :
    ReceiveSpec.wrapper key fields (k :: rest) =
      if k = key then .structure :: varintThen rest (fun _ after => fields after) else .structure :: fill .error rest :=
  rfl

/-- **Nothing the controller has seen of a response is `error` in the reference** (the controller
refuses at the byte that makes the reference's next byte `error`). -/
theorem rshape_noerror {ob : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P) :
    ∀ x ∈ ReceiveSpec.message ob false (8 :: 2 :: P), x ≠ .error := by
  rw [message_kind]
  cases h with
  | kind => intro x hx; simp [ReceiveSpec.wrapper] at hx; rcases hx with rfl | rfl <;> decide
  | wrapper hu hl =>
    rename_i u
    simp only [ReceiveSpec.wrapper, if_pos, varintThen_short (varintEnd_short_of 10 u hu hl)]
    intro x hx; simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · decide
    · decide
    · decide
    · exact fill_noerr (by decide) _ x hx
  | fields hw hwl hr ht hnb =>
    rename_i lw R F T m e b nb
    simp only [ReceiveSpec.wrapper, if_pos, varintThen_varint hw hwl]
    obtain ⟨C, eC, -, hC⟩ := rfs_classes hr T
    rw [eC]
    intro x hx; simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | rfl | rfl | hx | hx | hx
    · decide
    · decide
    · decide
    · exact fill_noerr (by decide) _ x hx
    · exact hC x hx
    · exact rt_noerror ht x hx

/-- **The response half of T1 at the message level (every field order, every byte string, with or
without `openBody`).** From any state the controller reaches inside a response (`RShape`), the run it
reveals next — `replyBudget H` bytes, whatever they turn out to be — consists of bytes the reference
(`ReceiveSpec.message openBody false`, the message as read so far) calls public, except that a byte may
be the reference's first `error` (the byte after a bad key, the 11th byte of a varint). -/
theorem rshape_budget {ob : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P) (Y : List Byte)
    (hY : Y.length ≤ replyBudget H ob) (i : Nat) (hi : i < Y.length) :
    SafeAt (ReceiveSpec.message ob false (8 :: 2 :: (P ++ Y))) (2 + P.length + i) := by
  rw [message_kind]
  cases h with
  | kind =>
    have hb : replyBudget [8, 2] ob = 2 := by rw [replyBudget_eq]; rfl
    rw [hb] at hY
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    rw [show 2 + i = i + 1 + 1 by omega]
    apply safeAt_cons (by decide); apply safeAt_cons (by decide)
    obtain ⟨y, W, rfl⟩ : ∃ y W, Y = y :: W := by
      cases Y with
      | nil => simp at hi
      | cons y W => exact ⟨y, W, rfl⟩
    cases i with
    | zero =>
      rw [wrapper_cons]; split
      · exact safeAt_public (c := .structure) rfl rfl
      · exact safeAt_public (c := .structure) rfl rfl
    | succ i =>
      have hi1 : i = 0 := by simp at hi hY; omega
      subst hi1
      obtain ⟨x, W', rfl⟩ : ∃ x W', W = x :: W' := by
        cases W with
        | nil => simp at hi
        | cons x W' => exact ⟨x, W', rfl⟩
      rw [wrapper_cons]; split
      · exact safeAt_public (c := .structure) (by rw [List.getElem?_cons_succ]; exact varintThen_head x W' _) rfl
      · refine ⟨.error, by simp [fill], Or.inr ⟨rfl, fun j hj => ?_⟩⟩
        have : j = 0 := by omega
        subst this; simp
  | wrapper hu hl =>
    rename_i u
    have hb : replyBudget (8 :: 2 :: 0x1a :: u) ob = 1 := by
      rw [replyBudget_eq, if_neg (by simp), varintAt_partial hu rfl]
    rw [hb] at hY
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    simp only [List.cons_append, List.length_cons, ReceiveSpec.wrapper, if_pos]
    rw [show 2 + (u.length + 1) + 0 = u.length + 1 + 1 + 1 by omega]
    apply safeAt_cons (by decide); apply safeAt_cons (by decide); apply safeAt_cons (by decide)
    rcases varint_pos hu hl (y :: Y') _ u.length (Nat.le_refl _) hl (by simp) with ⟨m, -, hm, hlt, -⟩ | h
    · exact safeAt_public (hlt hm) rfl
    · exact safeAt_public h rfl
  | fields hw hwl hr ht hnb =>
    rename_i lw R F T m e b nb
    rw [budget_fields hw hwl hr ht] at hY
    have hP : (0x1a :: (lw ++ (F ++ T)) : List Byte) ++ Y = 0x1a :: (lw ++ (F ++ (T ++ Y))) := by simp
    rw [hP]
    simp only [ReceiveSpec.wrapper, if_pos, varintThen_varint hw hwl]
    obtain ⟨C, eC, hCl, hC⟩ := rfs_classes hr (T ++ Y)
    rw [eC]
    rw [show 2 + (0x1a :: (lw ++ (F ++ T)) : List Byte).length + i =
      ((fill Class.structure lw).length + (C.length + (T.length + i))) + 1 + 1 + 1 by simp [fillL, hCl]; omega]
    apply safeAt_cons (by decide); apply safeAt_cons (by decide); apply safeAt_cons (by decide)
    apply safeAt_append (A := fill Class.structure lw) (fill_noerr (by decide) _)
    apply safeAt_append (A := C) hC
    exact rt_run ht Y hY i hi

/-- `replyBudget` is at least one byte in every state the controller reaches. -/
theorem rshape_budget_pos {ob : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P) :
    1 ≤ replyBudget H ob := by
  cases h with
  | kind => rw [replyBudget_eq, if_pos (by decide)]; decide
  | wrapper hu hl =>
    rename_i u
    rw [replyBudget_eq, if_neg (by simp), varintAt_partial hu rfl]
    exact Nat.le_refl 1
  | fields hw hwl hr ht hnb =>
    rw [budget_fields hw hwl hr ht]
    cases ht with
    | boundary => decide
    | number _ _ _ => unfold numBudget; split <;> omega
    | lengthKey _ _ _ => decide
    | short _ _ _ hc => omega
    | inline _ _ _ hc => omega

/-! ### The controller's steps

`payloadByte_reply_more`/`payloadByte_reply_skip` (`Policy/ReceiveInvariant.lean`) with `openBody` kept
(the same proofs, one more conjunct). -/

theorem payloadByte_reply_more' {s s' : State} {b : Byte} {flags : List Byte} {c : Bool}
    {f : ReplyFields} (hm : s.message = [8, 2])
    (hscan : replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) s.replySkipped s.openBody =
      (.more, f))
    (hok : payloadByte s b true false false flags = .ok (s', c)) :
    s'.skip = s.skip ∧ s'.reply = (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) ∧
      s'.replySkipped = s.replySkipped ∧ s'.message = [8, 2] ∧ s'.openBody = s.openBody := by
  unfold payloadByte at hok
  simp only [hm, l82_81, l82_82, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, pure_bind, ite_self,
    beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte, List.nil_append] at hok
  rcases ite_ok hok with hok | hok
  · rw [bind_ok_iff] at hok
    obtain ⟨r1, hfor, hrest⟩ := hok
    have hP := forIn_keeps (fun t => t.message = [8, 2] ∧ t.reply = s.reply ∧ t.replySkipped = s.replySkipped ∧
        t.openBody = s.openBody ∧ t.skip = s.skip) _
      (by
        intro x r0 r' hP0 e
        rcases ite_ok e with e | e
        · rcases ite_ok e with e | e
          · rcases ite_ok e with e | e
            · rcases ite_ok e with e | e
              · cases e; exact hP0
              · simp only [throw_bind_ex, throw_ok_iff] at e
            · cases e; exact hP0
          · simp only [throw_bind_ex, throw_ok_iff] at e
        · cases e; exact hP0)
      _ _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hfor
    obtain ⟨p1, p2, p3, p4, p5⟩ := hP
    simp only [p1, p2, p3, p4, hscan, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrest
    repeat' (first
      | (simp only [throw_bind_ex, throw_ok_iff] at hrest; done)
      | (cases hrest; exact ⟨by first | rfl | exact p5, rfl, by first | rfl | exact p3, by first | rfl | exact p1,
          by first | rfl | exact p4⟩)
      | (rcases ite_ok hrest with hrest | hrest))
  · simp only [hscan, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hok
    repeat' (first
      | (simp only [throw_bind_ex, throw_ok_iff] at hok; done)
      | (cases hok; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
      | (rcases ite_ok hok with hok | hok))

theorem payloadByte_reply_skip' {s s' : State} {b : Byte} {flags : List Byte} {c : Bool}
    {n : Nat} {f : ReplyFields} (hm : s.message = [8, 2])
    (hscan : replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) s.replySkipped s.openBody =
      (.skip n, f))
    (hok : payloadByte s b true false false flags = .ok (s', c)) :
    s'.skip = n ∧ s'.reply = (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) ∧
      s'.replySkipped = true ∧ s'.message = [8, 2] ∧ s'.openBody = s.openBody := by
  unfold payloadByte at hok
  simp only [hm, l82_81, l82_82, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, pure_bind, ite_self,
    beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte, List.nil_append] at hok
  rcases ite_ok hok with hok | hok
  · rw [bind_ok_iff] at hok
    obtain ⟨r1, hfor, hrest⟩ := hok
    have hP := forIn_keeps (fun t => t.message = [8, 2] ∧ t.reply = s.reply ∧ t.replySkipped = s.replySkipped ∧
        t.openBody = s.openBody) _
      (by
        intro x r0 r' hP0 e
        rcases ite_ok e with e | e
        · rcases ite_ok e with e | e
          · rcases ite_ok e with e | e
            · rcases ite_ok e with e | e
              · cases e; exact hP0
              · simp only [throw_bind_ex, throw_ok_iff] at e
            · cases e; exact hP0
          · simp only [throw_bind_ex, throw_ok_iff] at e
        · cases e; exact hP0)
      _ _ _ ⟨rfl, rfl, rfl, rfl⟩ hfor
    obtain ⟨p1, p2, p3, p4⟩ := hP
    simp only [p1, p2, p3, p4, hscan, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrest
    repeat' (first
      | (simp only [throw_bind_ex, throw_ok_iff] at hrest; done)
      | (cases hrest; exact ⟨rfl, rfl, rfl, by first | rfl | exact p1, by first | rfl | exact p4⟩)
      | (rcases ite_ok hrest with hrest | hrest))
  · simp only [hscan, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hok
    repeat' (first
      | (simp only [throw_bind_ex, throw_ok_iff] at hok; done)
      | (cases hok; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
      | (rcases ite_ok hok with hok | hok))

/-- **The controller inside a response** whose bytes after the kind so far are `P`: its revealed
bytes and flags have the shape `RShape` for `P` followed by whatever `skip` body bytes are still to
be passed over. -/
structure ReplyIn (s : State) (P : List Byte) : Prop where
  message : s.message = [8, 2]
  shape : ∀ B : List Byte, B.length = s.skip → RShape s.openBody s.reply s.replySkipped (P ++ B)

theorem rshape_ne {ob : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P) :
    H.isEmpty = false := by cases h <;> rfl

/-- **A revealed response byte keeps the controller inside the response's shape** (the message not
ending at it): the scanner asks for more, or to pass over a body (`skip := n`). -/
theorem payloadByte_replyIn {s s' : State} {P : List Byte} {y : Byte} {flags : List Byte} {c : Bool}
    (hs : ReplyIn s P) (h0 : s.skip = 0) (hok : payloadByte s y true false false flags = .ok (s', c)) :
    ReplyIn s' (P ++ [y]) ∧ s'.openBody = s.openBody := by
  have hsh := hs.shape [] (by simp [h0])
  rw [List.append_nil] at hsh
  have hne := rshape_ne hsh
  generalize hq : replyScan (s.reply ++ [y]) s.replySkipped s.openBody = q
  obtain ⟨need, f⟩ := q
  cases need with
  | more =>
    obtain ⟨k1, k2, k3, k4, k5⟩ := payloadByte_reply_more' (f := f) hs.message (by rw [hne]; exact hq) hok
    rw [hne] at k2
    refine ⟨⟨k4, fun B hB => ?_⟩, k5⟩
    rw [k1, h0] at hB
    rw [List.eq_nil_of_length_eq_zero hB, List.append_nil, k2, k3, k5]
    exact rshape_more hsh y (by rw [hq])
  | skip n =>
    obtain ⟨k1, k2, k3, k4, k5⟩ := payloadByte_reply_skip' (f := f) hs.message (by rw [hne]; exact hq) hok
    rw [hne] at k2
    refine ⟨⟨k4, fun B hB => ?_⟩, k5⟩
    rw [k2, k3, k5, List.append_assoc, List.singleton_append]
    exact rshape_skip hsh y (by rw [hq]) B (by rw [hB, k1])
  | malformed =>
    exfalso
    unfold payloadByte at hok
    simp only [hs.message, l82_81, l82_82, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
      Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
      decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, pure_bind, ite_self,
      beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte, List.nil_append] at hok
    rcases ite_ok hok with hok | hok
    · rw [bind_ok_iff] at hok
      obtain ⟨r1, hfor, hrest⟩ := hok
      have hP := forIn_keeps (fun t => t.message = [8, 2] ∧ t.reply = s.reply ∧ t.replySkipped = s.replySkipped ∧
          t.openBody = s.openBody) _
        (by
          intro x r0 r' hP0 e
          rcases ite_ok e with e | e
          · rcases ite_ok e with e | e
            · rcases ite_ok e with e | e
              · rcases ite_ok e with e | e
                · cases e; exact hP0
                · simp only [throw_bind_ex, throw_ok_iff] at e
              · cases e; exact hP0
            · simp only [throw_bind_ex, throw_ok_iff] at e
          · cases e; exact hP0)
        _ _ _ ⟨rfl, rfl, rfl, rfl⟩ hfor
      obtain ⟨p1, p2, p3, p4⟩ := hP
      simp only [p1, p2, p3, p4, hne, hq, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        throw_bind_ex, throw_ok_iff] at hrest
    · simp only [hne, hq, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte, throw_bind_ex,
        throw_ok_iff] at hok

/-- What `stepPassed` (one body byte passed over) keeps: `openBody`, the response's revealed bytes and
flags; `skip` is one less; or the message ends there (only at the body's last byte). -/
theorem stepPassed_keeps {s s' : State} {c : Bool} (h : stepPassed s = .ok (s', c)) :
    s'.openBody = s.openBody ∧ s'.skip = s.skip - 1 ∧
      ((s'.message = s.message ∧ s'.reply = s.reply ∧ s'.replySkipped = s.replySkipped) ∨
        (s'.message = [] ∧ s.skip - 1 = 0)) := by
  unfold stepPassed at h
  generalize TlsMpc.TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) = F at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  by_cases c1 : (s.upgraded && decide (s.skip > 0) && s.message == [8, 2]) = true
  · rw [if_pos c1] at h
    by_cases c2 : (PublicReceive.get F 0 == on && PublicReceive.get F 1 == on) = true
    · rw [if_pos c2] at h
      repeat' (split at h)
      all_goals (try simp only [reduceCtorEq] at h)
      all_goals (try (cases h; simp_all))
    · rw [if_neg c2] at h; cases h
  · rw [if_neg c1] at h; cases h

/-- **A passed-over body byte keeps the controller inside the response's shape**, whatever the byte. -/
theorem stepPassed_replyIn {s s' : State} {P : List Byte} {c : Bool} (hs : ReplyIn s P) (hk : 0 < s.skip)
    (hok : stepPassed s = .ok (s', c)) (y : Byte) :
    s'.openBody = s.openBody ∧ (s'.message = [8, 2] → ReplyIn s' (P ++ [y])) := by
  obtain ⟨k1, k2, k3⟩ := stepPassed_keeps hok
  refine ⟨k1, fun hm => ⟨hm, fun B hB => ?_⟩⟩
  rcases k3 with ⟨m1, m2, m3⟩ | ⟨m1, -⟩
  · rw [k1, m2, m3, List.append_assoc, List.singleton_append]
    exact hs.shape (y :: B) (by simp; omega)
  · rw [m1] at hm; cases hm

/-- Inside a response's payload (a data frame's payload byte comes next), the controller's run is at
most `max 1 (replyBudget reply openBody)`. -/
theorem budget_reply (s : State) (hu : s.upgraded = true) (h0 : (PublicReceive.get s.frame 0 == on) = false)
    (h2 : (PublicReceive.get s.frame 2 == on) = false) (h4 : (PublicReceive.get s.frame 4 == on) = true)
    (hr : (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0)
    (ho : (PublicReceive.get s.frame 7).toNat < 8) (hm : s.message = [8, 2]) :
    budget s ≤ max 1 (replyBudget s.reply s.openBody) := by
  unfold budget
  have hr' : ((PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne]; exact hr
  have h82 : (s.message == [8, 2]) = true := by rw [hm]; decide
  simp only [hu, h0, h2, h4, hr', h82, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, if_false, if_true, Nat.not_le.mpr ho]
  omega

/-- **The response half of T1 at the controller level (every field order, every byte string, with or
without `openBody`).** Inside a response whose bytes after the kind so far are `P` (`ReplyIn`, kept by
every revealed byte, `payloadByte_replyIn`, and every passed-over body byte, `stepPassed_replyIn`),
with nothing to pass over and a data frame's payload next, every byte of the run the controller
reveals (`budget s` bytes, whatever they are) is public in the reference's reading of the message,
or is its first `error`. -/
theorem reply_run_safe {s : State} {P : List Byte} (hs : ReplyIn s P) (hk : s.skip = 0) (hu : s.upgraded = true)
    (h0 : (PublicReceive.get s.frame 0 == on) = false) (h2 : (PublicReceive.get s.frame 2 == on) = false)
    (h4 : (PublicReceive.get s.frame 4 == on) = true)
    (hr : (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0)
    (ho : (PublicReceive.get s.frame 7).toNat < 8) (Y : List Byte) (hY : Y.length ≤ budget s)
    (i : Nat) (hi : i < Y.length) :
    SafeAt (ReceiveSpec.message s.openBody false (8 :: 2 :: (P ++ Y))) (2 + P.length + i) := by
  have hsh := hs.shape [] (by simp [hk])
  rw [List.append_nil] at hsh
  have hb := budget_reply s hu h0 h2 h4 hr ho hs.message
  have hp := rshape_budget_pos hsh
  exact rshape_budget hsh Y (by omega) i hi

end ReceiveReply
