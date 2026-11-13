import TlsMpc.Node.Policy.ReceiveRequestScan

/-!
# T1, item 2: complete messages (`complete = true`)

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

The reference classes the payload of a message's last frame, when the stream holds all of it, with
`complete = true` (`ReceiveSpec.delimitedThen`): a request's or response's length-delimited field whose
declared length runs past the end of the message makes every byte after the length `error`. The
message-level theorems of `Policy/ReceiveReply.lean` and `Policy/ReceiveRequestScan.lean` read the
message with `complete = false`. Here the same theorems for both values of `complete`:

* `openOf T`: what the field the controller's revealed bytes end in still declares and has not
  delivered (its length minus its content so far; 0 inside a key or a length). It is the controller's
  `replyMissing` (`replyMissing_fields`) and `fieldMissing` (`fieldMissing_open`) on those bytes, so
  `pendingField`, which `payloadByte` checks against the rest of the message's last frame at the byte
  that completes a length and at the last frame's header (`overrun`).
* `rshape_run_c`, `qshape_run_c`: the run the controller reveals inside a response or a request is
  public in `message ob c` of the whole message, with `complete = c`, provided (for `c = true`) the
  open field fits in the rest of the message (`openOf T ≤ ` what follows); every position of the run
  but the last is public, and the last is public or `error` (`Strong`: what the stream-level argument
  needs, since after an `error` every later byte of the stream is `error`).
* `rshape_noerr_c`, `qshape_noerr_c`: nothing the controller has accepted of the message is `error`.
-/

open TlsMpc

namespace ReceiveComplete

open PublicReceive ReceiveProofs ReceiveReply ReceiveRequestScan
open ReceiveSpec (Class fill varintThen varintEnd varintValue VarintEnd requestBody)
open ReceiveStream (responseFields requestFields)

/-! ### Positions -/

/-- Position `q` of `C` is public, or it is `error` and `last` holds. -/
def Strong (C : List Class) (q : Nat) (last : Prop) : Prop :=
  (∃ x, C[q]? = some x ∧ x.secret = false) ∨ (last ∧ C[q]? = some .error)

theorem strong_cons (x : Class) {C : List Class} {q : Nat} {last : Prop} (h : Strong C q last) :
    Strong (x :: C) (q + 1) last := by
  simpa [Strong] using h

theorem strong_append (A : List Class) {C : List Class} {q : Nat} {last : Prop} (h : Strong C q last) :
    Strong (A ++ C) (A.length + q) last := by
  unfold Strong at h ⊢
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact h

theorem strong_prefix {A C : List Class} {q : Nat} {last : Prop} (hq : q < A.length) (h : Strong A q last) :
    Strong (A ++ C) q last := by
  unfold Strong at h ⊢
  rw [List.getElem?_append_left hq]
  exact h

theorem strong_pub {C : List Class} {q : Nat} {x : Class} (last : Prop) (h : C[q]? = some x)
    (hx : x.secret = false) : Strong C q last := Or.inl ⟨x, h, hx⟩

theorem strong_fill {α : Type} {k : Class} (hk : k.secret = false) (l : List α) (q : Nat) (h : q < l.length)
    (last : Prop) : Strong (fill k l) q last := strong_pub last (fill_get k l q h) hk

theorem strong_of_pubAt {C : List Class} {q : Nat} (last : Prop) (h : PubAt C q) : Strong C q last := by
  obtain ⟨x, hx, hs⟩ := h; exact Or.inl ⟨x, hx, hs⟩

/-! ### What the open field still declares -/

/-- What the field the bytes `T` (a key, then its length and content so far) still declare and have not
delivered: the declared length minus the content so far; 0 while the length is not complete. -/
def openOf (T : List Byte) : Nat :=
  match varintAt T 1 with
  | some (count, next) => count - (T.length - next)
  | none => 0

theorem openOf_nil : openOf [] = 0 := rfl

theorem openOf_partial {tag : Byte} {u : List Byte} (hu : ∀ y ∈ u, 128 ≤ y.toNat) (_hl : u.length < 10) :
    openOf (tag :: u) = 0 := by
  unfold openOf
  rw [varintAt_partial hu (by rfl)]

theorem openOf_field {tag : Byte} {v cc : List Byte} {count : Nat} (hv : Varint v count) (hvl : v.length ≤ 10) :
    openOf (tag :: (v ++ cc)) = count - cc.length := by
  unfold openOf
  rw [varintAt_varint (rest := cc) hv hvl (by rfl)]
  simp only [List.length_cons, List.length_append]
  congr 1; omega

/-! ### `replyMissing` as a loop function -/

/-- One round of `replyMissing`'s loop. -/
def rmBody (bytes : List Byte) (inline : Bool) (r : MProd (Option Nat) Nat) : ForInStep (MProd (Option Nat) Nat) :=
  if r.snd ≥ bytes.length then .done ⟨some 0, r.snd⟩ else
  if ((get bytes r.snd).toNat == 0x08 || (get bytes r.snd).toNat == 0x10) then
    match varintAt bytes (r.snd + 1) with
    | some (_, next) => .yield ⟨none, next⟩
    | _ => .done ⟨some 0, r.snd⟩
  else if ((get bytes r.snd).toNat == 0x1a || (get bytes r.snd).toNat == 0x2a ||
      (inline && (get bytes r.snd).toNat == 0x22)) then
    match varintAt bytes (r.snd + 1) with
    | some (count, next) =>
      if next + count > bytes.length then .done ⟨some (next + count - bytes.length), r.snd⟩
      else .yield ⟨none, next + count⟩
    | _ => .done ⟨some 0, r.snd⟩
  else if (get bytes r.snd).toNat == 0x22 then
    match varintAt bytes (r.snd + 1) with
    | some (_, next) => .yield ⟨none, next⟩
    | _ => .done ⟨some 0, r.snd⟩
  else .done ⟨some 0, r.snd⟩

theorem replyMissing_eq (bytes : List Byte) (inline : Bool) : replyMissing bytes inline =
    if bytes.length < 3 then 0 else
    match varintAt bytes 3 with
    | some (_, first) => missingResult (loopG (rmBody bytes inline) (bytes.length + 1) ⟨none, first⟩)
    | none => 0 := by
  unfold replyMissing
  simp only [Id.run, forIn_range]
  by_cases h1 : bytes.length < 3
  · simp only [h1, if_true]; rfl
  · simp only [h1, if_false]
    cases hv : varintAt bytes 3 with
    | none => rfl
    | some v =>
      obtain ⟨_, first⟩ := v
      dsimp only
      rw [forIn_ignore (rmBody bytes inline) _ _ ?hf, List.length_range']
      · unfold missingResult
        generalize loopG (rmBody bytes inline) (bytes.length + 1) ⟨none, first⟩ = r
        obtain ⟨fst, snd⟩ := r
        cases fst <;> rfl
      · intro x r; rfl

theorem rm_number {bytes v rest : List Byte} {tag : Byte} {x : Option Nat} {pos n : Nat} {i : Bool}
    (ht : tag = 0x08 ∨ tag = 0x10) (hv : Varint v n) (hl : v.length ≤ 10) (h : bytes.drop pos = tag :: (v ++ rest)) :
    rmBody bytes i ⟨x, pos⟩ = .yield ⟨none, pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  unfold rmBody
  simp only [hg, hvar, rtag_number tag ht, ge_iff_le, hp, if_false, if_true]

theorem rm_text {bytes v c rest : List Byte} {tag : Byte} {x : Option Nat} {pos : Nat} {i : Bool}
    (ht : tag = 0x1a ∨ tag = 0x2a) (hv : Varint v c.length) (hl : v.length ≤ 10)
    (h : bytes.drop pos = tag :: (v ++ (c ++ rest))) :
    rmBody bytes i ⟨x, pos⟩ = .yield ⟨none, pos + 1 + v.length + c.length⟩ := by
  obtain ⟨hg, hd1, hp, hlen⟩ := field_at h
  simp only [List.length_append] at hlen
  have hvar := varintAt_varint hv hl hd1
  have hn : ¬ bytes.length < pos + 1 + v.length + c.length := by omega
  obtain ⟨t1, t2⟩ := rtag_text tag ht
  unfold rmBody
  simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true, Bool.true_or]

theorem rm_body {bytes v rest : List Byte} {ob : Bool} {x : Option Nat} {pos count : Nat}
    (hv : Varint v count) (hl : v.length ≤ 10) (h : bytes.drop pos = 0x22 :: (v ++ rest))
    (hin : ob = true → pos + 1 + v.length + count ≤ bytes.length) :
    rmBody bytes ob ⟨x, pos⟩ = .yield ⟨none, if ob then pos + 1 + v.length + count else pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, t2, t3⟩ := tag22_bools
  unfold rmBody
  cases ob
  · simp only [hg, hvar, t1, t2, t3, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true, Bool.false_and,
      Bool.or_false]
  · have hn : ¬ bytes.length < pos + 1 + v.length + count := by have := hin rfl; omega
    simp only [hg, hvar, t1, t2, t3, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true,
      Bool.true_and, Bool.false_or]

theorem rfs_missing {ob : Bool} {R F : List Byte} {b : Option Nat} (h : RFs ob R F b) :
    ∀ (H T : List Byte) (p : Nat), H.drop p = R ++ T →
      ∃ n, n ≤ R.length ∧ Reaches (rmBody H ob) n ⟨none, p⟩ ⟨none, p + R.length⟩ := by
  induction h with
  | nil => intro H T p _; exact ⟨0, Nat.le_refl _, rfl⟩
  | @number tag v R F n b ht hv hl _ ih =>
    intro H T p hd
    have hd' : H.drop p = tag :: (v ++ (R ++ T)) := by rw [hd]; simp
    have hr := rm_number (x := none) (i := ob) ht hv hl hd'
    obtain ⟨k, hk, hreach⟩ := ih H T (p + 1 + v.length) (drop_number hd')
    refine ⟨k + 1, by simp; omega, ⟨_, hr, ?_⟩⟩
    rw [show p + (tag :: (v ++ R)).length = p + 1 + v.length + R.length by simp; omega]
    exact hreach
  | @text tag v c R F b ht hv hl _ ih =>
    intro H T p hd
    have hd' : H.drop p = tag :: (v ++ (c ++ (R ++ T))) := by rw [hd]; simp
    have hr := rm_text (x := none) (i := ob) ht hv hl hd'
    obtain ⟨k, hk, hreach⟩ := ih H T (p + 1 + v.length + c.length) (drop_field hd')
    refine ⟨k + 1, by simp; omega, ⟨_, hr, ?_⟩⟩
    rw [show p + (tag :: (v ++ (c ++ R))).length = p + 1 + v.length + c.length + R.length by simp; omega]
    exact hreach
  | @body v c R F hv hl _ ih =>
    intro H T p hd
    have hd' : H.drop p = 0x22 :: (v ++ ((if ob then c else []) ++ (R ++ T))) := by rw [hd]; simp
    have hlen := length_of_drop hd' (by simp)
    simp only [List.length_cons, List.length_append] at hlen
    have hr := rm_body (x := none) (ob := ob) hv hl hd' (by intro e; subst e; simp at hlen; omega)
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

theorem rm_end {bytes : List Byte} {ob : Bool} {x : Option Nat} {pos : Nat} (h : bytes.length ≤ pos) :
    rmBody bytes ob ⟨x, pos⟩ = .done ⟨some 0, pos⟩ := by
  unfold rmBody; rw [if_pos h]

/-- **`replyMissing` at the unfinished field** is what that field still declares. -/
theorem tail_missing {ob : Bool} {T : List Byte} {e : Nat} {nb : Bool} (ht : RT ob T e nb) {H : List Byte} {p : Nat}
    (hd : H.drop p = T) (k : Nat) : missingResult (loopG (rmBody H ob) (k + 1) ⟨none, p⟩) = openOf T := by
  cases ht with
  | boundary =>
    have : H.length ≤ p := by have := congrArg List.length hd; simp at this; omega
    rw [loopG_done _ (rm_end this)]; rfl
  | @number tag u htag hu hl =>
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    have hvar := varintAt_partial hu hd1
    have r : rmBody H ob ⟨none, p⟩ = .done ⟨some 0, p⟩ := by
      unfold rmBody
      simp only [hg, hvar, rtag_number tag htag, ge_iff_le, hp, if_false, if_true]
    rw [loopG_done _ r, openOf_partial hu hl]; rfl
  | @lengthKey tag u htag hu hl =>
    obtain ⟨hg, hd1, hp, -⟩ := field_at hd
    have hvar := varintAt_partial hu hd1
    have r : rmBody H ob ⟨none, p⟩ = .done ⟨some 0, p⟩ := by
      unfold rmBody
      rcases htag with rfl | rfl | rfl
      · simp only [hg, hvar, ge_iff_le, hp, if_false]; rfl
      · simp only [hg, hvar, ge_iff_le, hp, if_false]; rfl
      · cases ob <;> simp only [hg, hvar, ge_iff_le, hp, if_false] <;> rfl
    rw [loopG_done _ r, openOf_partial hu hl]; rfl
  | @short tag v c count htag hv hvl hc =>
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    simp only [List.length_append] at hlen
    have hvar := varintAt_varint hv hvl hd1
    have hn : H.length < p + 1 + v.length + count := by omega
    obtain ⟨t1, t2⟩ := rtag_text tag htag
    have r : rmBody H ob ⟨none, p⟩ = .done ⟨some (p + 1 + v.length + count - H.length), p⟩ := by
      unfold rmBody
      simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true,
        Bool.true_or]
    rw [loopG_done _ r, openOf_field hv hvl]
    show p + 1 + v.length + count - H.length = count - c.length
    omega
  | @inline v c count hob hv hvl hc =>
    subst hob
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    simp only [List.length_append] at hlen
    have hvar := varintAt_varint hv hvl hd1
    obtain ⟨t1, t2, t3⟩ := tag22_bools
    have hn : H.length < p + 1 + v.length + count := by omega
    have r : rmBody H true ⟨none, p⟩ = .done ⟨some (p + 1 + v.length + count - H.length), p⟩ := by
      unfold rmBody
      simp only [hg, hvar, t1, t2, t3, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true,
        Bool.true_and, Bool.false_or]
    rw [loopG_done _ r, openOf_field hv hvl]
    show p + 1 + v.length + count - H.length = count - c.length
    omega

/-- **`replyMissing` on the controller's revealed bytes** is what the open field still declares. -/
theorem replyMissing_fields {ob : Bool} {lw R F T : List Byte} {m e : Nat} {b : Option Nat} {nb : Bool}
    (hw : Varint lw m) (hwl : lw.length ≤ 10) (hr : RFs ob R F b) (ht : RT ob T e nb) :
    replyMissing (8 :: 2 :: 0x1a :: (lw ++ (R ++ T))) ob = openOf T := by
  generalize hH : (8 :: 2 :: 0x1a :: (lw ++ (R ++ T)) : List Byte) = H
  have hlen : H.length = 3 + lw.length + R.length + T.length := by rw [← hH]; simp; omega
  have hd3 : H.drop 3 = lw ++ (R ++ T) := by rw [← hH]; rfl
  have hvar := varintAt_varint (rest := R ++ T) hw hwl hd3
  have hdp : H.drop (3 + lw.length) = R ++ T := by rw [← List.drop_drop, hd3, List.drop_left]
  obtain ⟨n, hn, hreach⟩ := rfs_missing hr H T (3 + lw.length) hdp
  have hdt : H.drop (3 + lw.length + R.length) = T := by
    rw [← List.drop_drop, hdp, List.drop_left]
  rw [replyMissing_eq, if_neg (by omega), hvar]
  dsimp only
  rw [show H.length + 1 = n + (H.length - n + 1) by omega, loopG_reaches n _ _ _ hreach]
  exact tail_missing ht hdt _

/-- `pendingField`'s part for a response, on every shape: what the open field still declares (0
after the kind and inside the wrapper's length). -/
theorem replyMissing_shape {ob : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P) :
    (∃ lw R F T m e b nb, H = 8 :: 2 :: 0x1a :: (lw ++ (R ++ T)) ∧ P = 0x1a :: (lw ++ (F ++ T)) ∧
      Varint lw m ∧ lw.length ≤ 10 ∧ RFs ob R F b ∧ RT ob T e nb ∧ replyMissing H ob = openOf T) ∨
    replyMissing H ob = 0 := by
  cases h with
  | kind => right; rw [replyMissing_eq]; rfl
  | wrapper hu hl =>
    right
    rename_i u
    rw [replyMissing_eq, if_neg (by simp), varintAt_partial hu rfl]
  | fields hw hwl hr ht hnb =>
    left
    exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, hw, hwl, hr, ht, replyMissing_fields hw hwl hr ht⟩

/-! ### Responses, field by field, for both values of `complete` -/

theorem rfc_fuel (ob c : Bool) (X : List Byte) (k : Nat) (h : X.length < k) :
    ReceiveSpec.response ob c k X = responseFields ob c X :=
  ReceiveStream.response_fuel ob c k _ X h (Nat.lt_succ_self _)

theorem rfc_number (ob c : Bool) {tag : Byte} {v : List Byte} {n : Nat} (ht : tag = 0x08 ∨ tag = 0x10)
    (hv : Varint v n) (hl : v.length ≤ 10) (Z : List Byte) :
    responseFields ob c (tag :: (v ++ Z)) = .structure :: (fill .structure v ++ responseFields ob c Z) := by
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons, if_pos ht, varintThen_varint hv hl,
    rfc_fuel ob c Z _ (by simp; omega)]
  rfl

theorem rfc_delim (ob c : Bool) (k : Class) {v cc : List Byte} (hv : Varint v cc.length) (hl : v.length ≤ 10)
    (Z : List Byte) (fuel : Nat) (hf : Z.length < fuel) :
    ReceiveSpec.delimitedThen c (v ++ (cc ++ Z)) (fill k) (fun _ after => ReceiveSpec.response ob c fuel after) =
      fill .structure v ++ (fill k cc ++ responseFields ob c Z) := by
  rw [ReceiveStream.delimitedThen_eq, varintThen_varint hv hl]
  unfold ReceiveStream.delimCont
  rw [if_neg (by simp), List.take_left' rfl, List.drop_left]
  dsimp only
  rw [rfc_fuel ob c Z fuel hf]

theorem rfc_text (ob c : Bool) {tag : Byte} {v cc : List Byte} (ht : tag = 0x1a ∨ tag = 0x2a)
    (hv : Varint v cc.length) (hl : v.length ≤ 10) (Z : List Byte) :
    responseFields ob c (tag :: (v ++ (cc ++ Z))) =
      .structure :: (fill .structure v ++ (fill .text cc ++ responseFields ob c Z)) := by
  have h1 : ¬ (tag = 0x08 ∨ tag = 0x10) := by rcases ht with rfl | rfl <;> decide
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons, if_neg h1, if_pos ht, rfc_delim ob c _ hv hl Z _ (by simp; omega)]
  rfl

theorem rfc_body (ob c : Bool) {v cc : List Byte} (hv : Varint v cc.length) (hl : v.length ≤ 10) (Z : List Byte) :
    responseFields ob c (0x22 :: (v ++ (cc ++ Z))) =
      .structure :: (fill .structure v ++ (fill (if ob then .text else .body) cc ++ responseFields ob c Z)) := by
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons, if_neg (by decide), if_neg (by decide), if_pos rfl,
    rfc_delim ob c _ hv hl Z _ (by simp; omega)]
  rfl

/-- The classes of complete fields, for both values of `complete`: none is `error`. -/
theorem rfsc_classes {ob : Bool} (c : Bool) {R F : List Byte} {b : Option Nat} (h : RFs ob R F b) (Z : List Byte) :
    ∃ C : List Class, responseFields ob c (F ++ Z) = C ++ responseFields ob c Z ∧ C.length = F.length ∧
      ∀ x ∈ C, x ≠ .error := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | @number tag v R F n b ht hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ C), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, rfc_number ob c ht hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx; rcases hx with rfl | ⟨_, _, rfl⟩ | hx <;> first | decide | exact hc x hx
  | @text tag v cc R F b ht hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ (fill .text cc ++ C)), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, List.append_assoc, rfc_text ob c ht hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx
      rcases hx with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | hx <;> first | decide | exact hc x hx
  | @body v cc R F hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ (fill (if ob then .text else .body) cc ++ C)), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, List.append_assoc, rfc_body ob c hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx
      rcases hx with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | hx
      · decide
      · decide
      · cases ob <;> decide
      · exact hc x hx

theorem rfc_cons_number (ob c : Bool) {tag : Byte} (ht : tag = 0x08 ∨ tag = 0x10) (Z : List Byte) :
    responseFields ob c (tag :: Z) =
      .structure :: varintThen Z (fun _ after => ReceiveSpec.response ob c (Z.length + 1) after) := by
  unfold responseFields; rw [List.length_cons, ReceiveStream.response_cons, if_pos ht]

theorem rfc_cons_delim (ob c : Bool) {tag : Byte} (ht : tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22) (Z : List Byte) :
    ∃ k : Class, responseFields ob c (tag :: Z) =
      .structure :: varintThen Z (ReceiveStream.delimCont c (fill k)
        (fun _ after => ReceiveSpec.response ob c (Z.length + 1) after)) ∧
      (tag = 0x1a ∨ tag = 0x2a → k = .text) ∧ (tag = 0x22 → k = if ob then .text else .body) := by
  unfold responseFields
  rw [List.length_cons, ReceiveStream.response_cons]
  rcases ht with rfl | rfl | rfl
  · exact ⟨.text, by rw [if_neg (by decide), if_pos (Or.inl rfl)]; rfl, fun _ => rfl, fun h => by cases h⟩
  · exact ⟨.text, by rw [if_neg (by decide), if_pos (Or.inr rfl)]; rfl, fun _ => rfl, fun h => by cases h⟩
  · exact ⟨if ob then .text else .body, by rw [if_neg (by decide), if_neg (by decide), if_pos rfl]; rfl,
      fun h => (by rcases h with h | h <;> cases h), fun _ => rfl⟩

/-- **A field boundary**: the next key is public; the byte after it is public, or `error` after a bad
key. -/
theorem rfc_boundary (ob c : Bool) (Z : List Byte) (q : Nat) (hq : q < 2) (hz : q < Z.length) :
    Strong (responseFields ob c Z) q (q = 1) := by
  match Z, q with
  | y :: W, 0 =>
    unfold responseFields; rw [ReceiveStream.response_cons]
    split
    · exact strong_pub _ rfl rfl
    · split
      · exact strong_pub _ rfl rfl
      · split
        · exact strong_pub _ rfl rfl
        · exact strong_pub _ rfl rfl
  | y :: x :: W, 1 =>
    unfold responseFields; rw [ReceiveStream.response_cons]
    split
    · exact strong_pub _ (by rw [List.getElem?_cons_succ]; exact varintThen_head x W _) rfl
    · split
      · have h1 := varintThen_head x W (ReceiveStream.delimCont c (fill .text)
          (fun _ after => ReceiveSpec.response ob c (y :: x :: W).length after))
        exact strong_pub _ (by rw [List.getElem?_cons_succ, ReceiveStream.delimitedThen_eq]; exact h1) rfl
      · split
        · have h1 := varintThen_head x W (ReceiveStream.delimCont c (fill (if ob then .text else .body))
            (fun _ after => ReceiveSpec.response ob c (y :: x :: W).length after))
          exact strong_pub _ (by rw [List.getElem?_cons_succ, ReceiveStream.delimitedThen_eq]; exact h1) rfl
        · exact Or.inr ⟨rfl, by simp [fill]⟩
  | [y], 1 => simp at hz

/-- **Inside an id or status**: the run (`numBudget`) is public but for its last byte, which may be
`error` (the byte after a bad key, the 11th byte of a varint). -/
theorem num_run_c {ob c : Bool} {u : List Byte} (hu : ∀ x ∈ u, 128 ≤ x.toNat) (hl : u.length < 10)
    (Y Z : List Byte) (hY : Y.length ≤ numBudget u) (fuel : Nat) (hf : (u ++ (Y ++ Z)).length < fuel) (i : Nat)
    (hi : i < Y.length) :
    Strong (varintThen (u ++ (Y ++ Z)) (fun _ after => ReceiveSpec.response ob c fuel after)) (u.length + i)
      (i + 1 = Y.length) := by
  have hb : (u = [] → i = 0 ∧ Y.length = 1 ∨ Y.length = 0) ∧ i ≤ 2 ∧ u.length + i ≤ 10 ∧
      (u ≠ [] → Y.length ≤ min 3 (11 - u.length)) := by
    unfold numBudget at hY
    by_cases hu0 : u = []
    · subst hu0; simp at hY; simp; omega
    · rw [if_neg hu0] at hY
      have : u.length ≠ 0 := fun e => hu0 (List.eq_nil_of_length_eq_zero e)
      exact ⟨fun e => absurd e hu0, by omega, by omega, fun _ => hY⟩
  have hs := varintEnd_short_of 10 u hu hl
  have hqY : u.length + i < (u ++ (Y ++ Z)).length := by simp; omega
  cases hv : varintEnd 10 (u ++ (Y ++ Z)) with
  | done m =>
    have hm := ReceiveStream.varintEnd_append_short 10 u (Y ++ Z) m hs hv
    have hle := ReceiveStream.varintEnd_done_le 10 _ m hv
    rw [varintThen_done hv]
    by_cases hq : u.length + i < m
    · exact strong_prefix (by rw [fillL, List.length_take]; omega)
        (strong_fill rfl _ _ (by rw [List.length_take]; omega) _)
    · have e1 : u.length + i = (fill Class.structure ((u ++ (Y ++ Z)).take m)).length + (u.length + i - m) := by
        rw [fillL, List.length_take]; omega
      rw [e1]
      apply strong_append
      rw [rfc_fuel ob c _ fuel (by simp only [List.length_drop]; omega)]
      have hq2 : u.length + i - m < 2 := by
        rcases Nat.eq_zero_or_pos u.length with h0 | h0
        · have : u = [] := List.eq_nil_of_length_eq_zero h0
          rcases hb.1 this with ⟨hi0, -⟩ | h1 <;> omega
        · omega
      have hlast := rfc_boundary ob c ((u ++ (Y ++ Z)).drop m) (u.length + i - m) hq2 (by simp; omega)
      unfold Strong at hlast ⊢
      rcases hlast with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨?_, h2⟩
        rcases Nat.eq_zero_or_pos u.length with h0 | h0
        · have : u = [] := List.eq_nil_of_length_eq_zero h0
          rcases hb.1 this with ⟨hi0, -⟩ | h1' <;> omega
        · have := hb.2.2.2 (fun e => by rw [e] at h0; simp at h0)
          omega
  | short =>
    rw [varintThen_short hv]
    exact strong_fill rfl _ _ hqY _
  | tooLong =>
    have hle := ReceiveStream.varintEnd_tooLong_le 10 _ hv
    rw [varintThen_tooLong hv]
    by_cases hq : u.length + i < 10
    · exact strong_prefix (by rw [fillL, List.length_take]; omega)
        (strong_fill rfl _ _ (by rw [List.length_take]; omega) _)
    · have hq10 : u.length + i = 10 := by omega
      rw [hq10]
      refine Or.inr ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos u.length with h0 | h0
        · have : u = [] := List.eq_nil_of_length_eq_zero h0
          rcases hb.1 this with ⟨hi0, -⟩ | h1 <;> omega
        · have := hb.2.2.2 (fun e => by rw [e] at h0; simp at h0)
          omega
      · rw [List.getElem?_append_right (by rw [fillL, List.length_take]; omega), fillL, List.length_take,
          Nat.min_eq_left hle]
        exact fill_get _ _ _ (by simp; omega)

/-- **The run after the unfinished field**, for both values of `complete`: public but for its last byte,
which may be `error`; with `complete`, provided the open field fits in what follows. -/
theorem rt_run_c {ob c : Bool} {T : List Byte} {e : Nat} {nb : Bool} (ht : RT ob T e nb) (Y Z : List Byte)
    (hY : Y.length ≤ e) (hfit : c = true → openOf T ≤ (Y ++ Z).length) (i : Nat) (hi : i < Y.length) :
    Strong (responseFields ob c (T ++ (Y ++ Z))) (T.length + i) (i + 1 = Y.length) := by
  cases ht with
  | boundary =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    have := rfc_boundary ob c (Y ++ Z) i (by omega) (by simp; omega)
    unfold Strong at this ⊢
    rcases this with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, h2⟩
  | @number tag u htag hu hl =>
    rw [List.cons_append, rfc_cons_number ob c htag, List.length_cons,
      show u.length + 1 + i = (u.length + i) + 1 by omega]
    exact strong_cons _ (num_run_c hu hl Y Z hY ((u ++ (Y ++ Z)).length + 1) (by simp) i hi)
  | @lengthKey tag u htag hu hl =>
    obtain ⟨k, e1, -, -⟩ := rfc_cons_delim ob c htag (u ++ (Y ++ Z))
    rw [List.cons_append, e1, List.length_cons, show u.length + 1 + i = (u.length + i) + 1 by omega]
    apply strong_cons
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    rcases varint_pos hu hl (y :: (Y' ++ Z)) _ u.length (Nat.le_refl _) hl (by simp) with ⟨m, -, hm, hlt, -⟩ | h
    · exact strong_pub _ (by simpa using hlt hm) rfl
    · exact strong_pub _ (by simpa using h) rfl
  | @short tag v cc count htag hv hvl hc =>
    have htag' : tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22 := by
      rcases htag with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
    obtain ⟨k, e1, hk, -⟩ := rfc_cons_delim ob c htag' (v ++ (cc ++ (Y ++ Z)))
    have hk' := hk htag
    subst hk'
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    have hfit' := fun e => (openOf_field (tag := tag) (cc := cc) hv hvl) ▸ hfit e
    rw [if_neg (by
      intro h
      have h2 := hfit' h.1
      simp only [List.length_append] at h h2
      omega)]
    rw [show (tag :: (v ++ cc)).length + i = ((fill Class.structure v).length + (cc.length + i)) + 1 by
      simp [fillL]; omega]
    apply strong_cons
    apply strong_append (A := fill Class.structure v)
    apply strong_prefix (by rw [fillL, List.length_take]; simp; omega)
    exact strong_fill rfl _ _ (by rw [List.length_take]; simp; omega) _
  | @inline v cc count hob hv hvl hc =>
    subst hob
    obtain ⟨k, e1, -, hk⟩ := rfc_cons_delim true c (Or.inr (Or.inr rfl)) (v ++ (cc ++ (Y ++ Z)))
    have hk' := hk rfl
    simp only [if_true] at hk'
    subst hk'
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    have hfit' := fun e => (openOf_field (tag := 0x22) (cc := cc) hv hvl) ▸ hfit e
    rw [if_neg (by
      intro h
      have h2 := hfit' h.1
      simp only [List.length_append] at h h2
      omega)]
    rw [show (0x22 :: (v ++ cc) : List Byte).length + i = ((fill Class.structure v).length + (cc.length + i)) + 1 by
      simp [fillL]; omega]
    apply strong_cons
    apply strong_append (A := fill Class.structure v)
    apply strong_prefix (by rw [fillL, List.length_take]; simp; omega)
    exact strong_fill rfl _ _ (by rw [List.length_take]; simp; omega) _

/-! ### No `error` in what was accepted -/

theorem noerr_take_append {A B : List Class} {m : Nat} (hA : ∀ x ∈ A, x ≠ .error)
    (hB : ∀ x ∈ B.take m, x ≠ .error) : ∀ x ∈ (A ++ B).take (A.length + m), x ≠ .error := by
  rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hA x h
  · exact hB x h

theorem noerr_cons {x : Class} (hx : x ≠ .error) {B : List Class} {m : Nat}
    (hB : ∀ y ∈ B.take m, y ≠ .error) : ∀ y ∈ (x :: B).take (m + 1), y ≠ .error := by
  intro y hy
  rw [List.take_succ_cons] at hy
  rcases List.mem_cons.mp hy with h | h
  · rw [h]; exact hx
  · exact hB y h

theorem noerr_of_prefix {A B : List Class} {m : Nat} (hm : m ≤ A.length) (hA : ∀ x ∈ A, x ≠ .error) :
    ∀ x ∈ (A ++ B).take m, x ≠ .error := by
  rw [List.take_append_of_le_length hm]
  intro x hx; exact hA x (List.mem_of_mem_take hx)

/-- Nothing of the unfinished field is `error` (with `complete`, provided it fits in what follows). -/
theorem rt_noerr_c {ob c : Bool} {T : List Byte} {e : Nat} {nb : Bool} (ht : RT ob T e nb) (R : List Byte)
    (hfit : c = true → openOf T ≤ R.length) :
    ∀ x ∈ (responseFields ob c (T ++ R)).take T.length, x ≠ .error := by
  cases ht with
  | boundary => intro x hx; simp at hx
  | @number tag u htag hu hl =>
    rw [List.cons_append, rfc_cons_number ob c htag, List.length_cons]
    apply noerr_cons (by decide)
    rw [ReceiveStream.varintThen_short_take (varintEnd_short_of 10 u hu hl)]
    exact fill_noerr (by decide) _
  | @lengthKey tag u htag hu hl =>
    obtain ⟨k, e1, -, -⟩ := rfc_cons_delim ob c htag (u ++ R)
    rw [List.cons_append, e1, List.length_cons]
    apply noerr_cons (by decide)
    rw [ReceiveStream.varintThen_short_take (varintEnd_short_of 10 u hu hl)]
    exact fill_noerr (by decide) _
  | @short tag v cc count htag hv hvl hc =>
    have htag' : tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22 := by
      rcases htag with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
    obtain ⟨k, e1, hk, -⟩ := rfc_cons_delim ob c htag' (v ++ (cc ++ R))
    have hk' := hk htag
    subst hk'
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    have hfit' := fun e => (openOf_field (tag := tag) (cc := cc) hv hvl) ▸ hfit e
    rw [if_neg (by
      intro h
      have h2 := hfit' h.1
      simp only [List.length_append] at h h2
      omega)]
    rw [show (tag :: (v ++ cc)).length = (v.length + cc.length) + 1 by
      simp only [List.length_cons, List.length_append]; try omega]
    apply noerr_cons (by decide)
    rw [← List.append_assoc]
    apply noerr_of_prefix (by simp [fillL]; omega)
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact fill_noerr (by decide) _ x h
    · exact fill_noerr (by decide) _ x h
  | @inline v cc count hob hv hvl hc =>
    subst hob
    obtain ⟨k, e1, -, hk⟩ := rfc_cons_delim true c (Or.inr (Or.inr rfl)) (v ++ (cc ++ R))
    have hk' := hk rfl
    simp only [if_true] at hk'
    subst hk'
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    have hfit' := fun e => (openOf_field (tag := 0x22) (cc := cc) hv hvl) ▸ hfit e
    rw [if_neg (by
      intro h
      have h2 := hfit' h.1
      simp only [List.length_append] at h h2
      omega)]
    rw [show (0x22 :: (v ++ cc) : List Byte).length = (v.length + cc.length) + 1 by
      simp only [List.length_cons, List.length_append]; try omega]
    apply noerr_cons (by decide)
    rw [← List.append_assoc]
    apply noerr_of_prefix (by simp [fillL]; omega)
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact fill_noerr (by decide) _ x h
    · exact fill_noerr (by decide) _ x h

theorem message_kind_c (ob c : Bool) (Z : List Byte) :
    ReceiveSpec.message ob c (8 :: 2 :: Z) = .kind :: .kind :: ReceiveSpec.wrapper 0x1a (responseFields ob c) Z := by
  match Z with
  | [] => rfl
  | _ :: _ => rw [ReceiveStream.message_eq, if_neg (by decide), if_pos ⟨rfl, rfl⟩]

/-- **The response half of T1 at the message level, for both values of `complete`.** From any state the
controller reaches inside a response (`RShape`), every byte of the run it reveals next but the last is
public in `message openBody c` of the whole message (`P ++ Y ++ Z`: the run `Y`, then the rest `Z`), and
the last is public or `error`; with `complete`, provided what the open field still declares
(`replyMissing`) fits in the rest of the message. -/
theorem rshape_run_c {ob c : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P)
    (Y Z : List Byte) (hY : Y.length ≤ replyBudget H ob) (hfit : c = true → replyMissing H ob ≤ (Y ++ Z).length)
    (i : Nat) (hi : i < Y.length) :
    Strong (ReceiveSpec.message ob c (8 :: 2 :: (P ++ (Y ++ Z)))) (2 + P.length + i) (i + 1 = Y.length) := by
  rw [message_kind_c]
  cases h with
  | kind =>
    have hb : replyBudget [8, 2] ob = 2 := by rw [replyBudget_eq]; rfl
    rw [hb] at hY
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    rw [show 2 + i = i + 1 + 1 by omega]
    apply strong_cons; apply strong_cons
    obtain ⟨y, W, rfl⟩ : ∃ y W, Y = y :: W := by
      cases Y with
      | nil => simp at hi
      | cons y W => exact ⟨y, W, rfl⟩
    cases i with
    | zero =>
      rw [List.cons_append, wrapper_cons]; split
      · exact strong_pub _ (x := .structure) rfl rfl
      · exact strong_pub _ (x := .structure) rfl rfl
    | succ i =>
      have hi1 : i = 0 := by simp at hi hY; omega
      subst hi1
      obtain ⟨x, W', rfl⟩ : ∃ x W', W = x :: W' := by
        cases W with
        | nil => simp at hi
        | cons x W' => exact ⟨x, W', rfl⟩
      rw [List.cons_append, wrapper_cons]; split
      · exact strong_pub _ (x := .structure) (by rw [List.getElem?_cons_succ]; exact varintThen_head x _ _) rfl
      · refine Or.inr ⟨by simp at hY ⊢; omega, by simp [fill]⟩
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
    apply strong_cons; apply strong_cons; apply strong_cons
    rcases varint_pos hu hl (y :: (Y' ++ Z)) _ u.length (Nat.le_refl _) hl (by simp) with ⟨m, -, hm, hlt, -⟩ | h
    · exact strong_pub _ (hlt hm) rfl
    · exact strong_pub _ h rfl
  | fields hw hwl hr ht hnb =>
    rename_i lw R F T m e b nb
    rw [budget_fields hw hwl hr ht] at hY
    have hP : (0x1a :: (lw ++ (F ++ T)) : List Byte) ++ (Y ++ Z) = 0x1a :: (lw ++ (F ++ (T ++ (Y ++ Z)))) := by simp
    rw [hP]
    simp only [ReceiveSpec.wrapper, if_pos, varintThen_varint hw hwl]
    obtain ⟨C, eC, hCl, hC⟩ := rfsc_classes c hr (T ++ (Y ++ Z))
    rw [eC]
    rw [show 2 + (0x1a :: (lw ++ (F ++ T)) : List Byte).length + i =
      ((fill Class.structure lw).length + (C.length + (T.length + i))) + 1 + 1 + 1 by simp [fillL, hCl]; omega]
    apply strong_cons; apply strong_cons; apply strong_cons
    apply strong_append
    apply strong_append
    exact rt_run_c ht Y Z hY (fun e => by rw [← replyMissing_fields hw hwl hr ht]; exact hfit e) i hi

/-- **Nothing the controller has accepted of a response is `error`**, for both values of `complete`
(with `complete`, provided the open field fits in the rest `R` of the message). -/
theorem rshape_noerr_c {ob c : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P)
    (R : List Byte) (hfit : c = true → replyMissing H ob ≤ R.length) :
    ∀ x ∈ (ReceiveSpec.message ob c (8 :: 2 :: (P ++ R))).take (2 + P.length), x ≠ .error := by
  rw [message_kind_c]
  cases h with
  | kind =>
    intro x hx
    simp only [List.nil_append, List.length_nil, Nat.add_zero, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  | wrapper hu hl =>
    rename_i u
    rw [show 2 + (0x1a :: u : List Byte).length = (u.length + 1) + 1 + 1 by simp; omega]
    apply noerr_cons (by decide); apply noerr_cons (by decide)
    simp only [List.cons_append, ReceiveSpec.wrapper, if_pos]
    apply noerr_cons (by decide)
    rw [ReceiveStream.varintThen_short_take (varintEnd_short_of 10 u hu hl)]
    exact fill_noerr (by decide) _
  | fields hw hwl hr ht hnb =>
    rename_i lw R' F T m e b nb
    have hP : (0x1a :: (lw ++ (F ++ T)) : List Byte) ++ R = 0x1a :: (lw ++ (F ++ (T ++ R))) := by simp
    rw [hP]
    simp only [ReceiveSpec.wrapper, if_pos, varintThen_varint hw hwl]
    obtain ⟨C, eC, hCl, hC⟩ := rfsc_classes c hr (T ++ R)
    rw [eC]
    rw [show 2 + (0x1a :: (lw ++ (F ++ T)) : List Byte).length =
      ((fill Class.structure lw).length + (C.length + T.length)) + 1 + 1 + 1 by simp [fillL, hCl]; omega]
    apply noerr_cons (by decide); apply noerr_cons (by decide); apply noerr_cons (by decide)
    apply noerr_take_append (fill_noerr (by decide) _)
    apply noerr_take_append hC
    exact rt_noerr_c ht R (fun e => by rw [← replyMissing_fields hw hwl hr ht]; exact hfit e)

/-- After the byte that completes a response body's length (the scanner asking to pass over the body),
nothing is left of a field among the revealed bytes: `replyMissing` is 0. -/
theorem rshape_skip_missing {ob : Bool} {H : List Byte} {sk : Bool} {P : List Byte} (h : RShape ob H sk P) (y : Byte)
    {n : Nat} (hm : (replyScan (H ++ [y]) sk ob).1 = .skip n) : replyMissing (H ++ [y]) ob = 0 := by
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
    have hv' : Varint v (List.replicate n (0 : Byte)).length := by rw [List.length_replicate]; exact hv
    have hrf : RF false (0x22 :: v) (0x22 :: (v ++ List.replicate n 0)) (some (List.replicate n (0 : Byte)).length) := by
      simpa using RF.body (ob := false) hv' hvl
    have e := replyMissing_fields hw hwl (rfs_snoc hr hrf (Or.inl rfl)) RT.boundary
    rw [hT, openOf_nil] at *
    simpa using e

/-! ### Requests, for both values of `complete` -/

/-- A request's fields from path `path`, with enough fuel. -/
def rqc (path : List Byte) (c : Bool) (X : List Byte) : List Class :=
  ReceiveSpec.request c (X.length + 1) path X

theorem rqc_fuel (path : List Byte) (c : Bool) (X : List Byte) (k : Nat) (h : X.length < k) :
    ReceiveSpec.request c k path X = rqc path c X :=
  ReceiveStream.request_fuel c k _ path X h (Nat.lt_succ_self _)

theorem rqc_number (c : Bool) {v : List Byte} {n : Nat} (hv : Varint v n) (hl : v.length ≤ 10) (path Z : List Byte) :
    rqc path c (0x20 :: (v ++ Z)) = .structure :: (fill .structure v ++ rqc path c Z) := by
  unfold rqc
  rw [List.length_cons, ReceiveStream.request_cons, if_pos rfl, varintThen_varint hv hl,
    rqc_fuel path c Z _ (by simp; omega)]
  rfl

theorem rqc_text (c : Bool) {tag : Byte} {v cc : List Byte} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a)
    (hv : Varint v cc.length) (hl : v.length ≤ 10) (path Z : List Byte) :
    rqc path c (tag :: (v ++ (cc ++ Z))) =
      .structure :: (fill .structure v ++ (fill .text cc ++ rqc (if tag = 0x12 then cc else path) c Z)) := by
  have h1 : ¬ tag = 0x20 := by rcases ht with rfl | rfl | rfl <;> decide
  unfold rqc
  rw [List.length_cons, ReceiveStream.request_cons, if_neg h1, if_pos ht, ReceiveStream.delimitedThen_eq,
    varintThen_varint hv hl]
  unfold ReceiveStream.delimCont
  rw [if_neg (by simp), List.take_left' rfl, List.drop_left]
  dsimp only
  rw [rqc_fuel _ c Z _ (by simp; omega)]
  rfl

theorem rqc_body (c : Bool) {v cc : List Byte} (hv : Varint v cc.length) (hl : v.length ≤ 10) (path Z : List Byte) :
    rqc path c (0x1a :: (v ++ (cc ++ Z))) = .structure :: (fill .structure v ++ (requestBody path cc ++ rqc path c Z)) := by
  unfold rqc
  rw [List.length_cons, ReceiveStream.request_cons, if_neg (by decide), if_neg (by decide), if_pos rfl,
    ReceiveStream.delimitedThen_eq, varintThen_varint hv hl]
  unfold ReceiveStream.delimCont
  rw [if_neg (by simp), List.take_left' rfl, List.drop_left]
  dsimp only
  rw [rqc_fuel _ c Z _ (by simp; omega)]
  rfl

theorem rqc_cons_number (c : Bool) (path Z : List Byte) :
    rqc path c (0x20 :: Z) = .structure :: varintThen Z (fun _ after => ReceiveSpec.request c (Z.length + 1) path after) := by
  unfold rqc; rw [List.length_cons, ReceiveStream.request_cons, if_pos rfl]

theorem rqc_cons_delim (c : Bool) {tag : Byte} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a)
    (path Z : List Byte) :
    ∃ (k : List Byte → List Class) (nx : List Byte → List Byte → List Class), rqc path c (tag :: Z) =
      .structure :: varintThen Z (ReceiveStream.delimCont c k nx) ∧
      (tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a → k = fill .text) := by
  unfold rqc
  rw [List.length_cons, ReceiveStream.request_cons]
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨_, _, by rw [if_neg (by decide), if_pos (Or.inl rfl), ReceiveStream.delimitedThen_eq], fun _ => rfl⟩
  · exact ⟨_, _, by rw [if_neg (by decide), if_pos (Or.inr (Or.inl rfl)), ReceiveStream.delimitedThen_eq],
      fun _ => rfl⟩
  · exact ⟨_, _, by rw [if_neg (by decide), if_pos (Or.inr (Or.inr rfl)), ReceiveStream.delimitedThen_eq],
      fun _ => rfl⟩
  · exact ⟨_, _, by rw [if_neg (by decide), if_neg (by decide), if_pos rfl, ReceiveStream.delimitedThen_eq],
      fun h => by rcases h with h | h | h <;> cases h⟩

/-- The classes of complete request fields, for both values of `complete`: none is `error`. -/
theorem qfsc_classes (c : Bool) {path R F path' : List Byte} {b : Option Nat} (h : QFs path R F b path')
    (Z : List Byte) :
    ∃ C : List Class, rqc path c (F ++ Z) = C ++ rqc path' c Z ∧ C.length = F.length ∧ NoErr C := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, by simp [NoErr]⟩
  | @number path v R F path' n b hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ C), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, rqc_number c hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx; rcases hx with rfl | ⟨_, _, rfl⟩ | hx <;> first | decide | exact hc x hx
  | @text path tag v cc R F path' b ht hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ (fill .text cc ++ C)), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, List.append_assoc, rqc_text c ht hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx
      rcases hx with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | hx <;> first | decide | exact hc x hx
  | @body path v cc R F path' hv hl hn _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ (requestBody path cc ++ C)), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, List.append_assoc, rqc_body c hv hl, e]; simp
    · simp [fillL, hl', ReceiveStream.requestBody_len path cc]
    · intro x hx; simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx | hx
      · decide
      · exact fill_noerr (by decide) _ x hx
      · exact hn x hx
      · exact hc x hx

theorem rqc_head (c : Bool) (path : List Byte) (y : Byte) (Z : List Byte) : (rqc path c (y :: Z))[0]? = some .structure := by
  unfold rqc; rw [List.length_cons, ReceiveStream.request_cons]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- **The run after the unfinished field of a request**, for both values of `complete`: public (with
`complete`, provided the open field fits in what follows). -/
theorem q_tail_run_c (c : Bool) {T : List Byte} {e : Nat} (ht : Tail T e) (Y Z : List Byte)
    (hY : Y.length ≤ max 1 (e - T.length)) (hfit : c = true → openOf T ≤ (Y ++ Z).length)
    (path : List Byte) (i : Nat) (hi : i < Y.length) : PubAt (rqc path c (T ++ (Y ++ Z))) (T.length + i) := by
  cases ht with
  | empty =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    have hi0 : i = 0 := by simp at hY; omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    exact ⟨_, rqc_head c path y _, rfl⟩
  | @unfinished tag u htag hu hl =>
    have hi0 : i = 0 := by simp at hY; omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    rw [List.cons_append, List.length_cons, show u.length + 1 + 0 = u.length + 1 by omega]
    have hvp : ∀ (nx : Nat → List Byte → List Class), (varintThen (u ++ y :: (Y' ++ Z)) nx)[u.length]? = some .structure := by
      intro nx
      rcases varint_pos hu hl (y :: (Y' ++ Z)) nx u.length (Nat.le_refl _) hl (by simp) with ⟨m, -, hm, hlt, -⟩ | h
      · exact hlt hm
      · exact h
    by_cases h20 : tag = 0x20
    · subst h20
      rw [show (y :: Y') ++ Z = y :: (Y' ++ Z) from rfl, rqc_cons_number]
      exact pubAt_cons _ ⟨_, hvp _, rfl⟩
    · have ht4 : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a := by
        rcases htag with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact absurd h h20
      obtain ⟨k, nx, e1, -⟩ := rqc_cons_delim c ht4 path (u ++ y :: (Y' ++ Z))
      rw [show (y :: Y') ++ Z = y :: (Y' ++ Z) from rfl, e1]
      exact pubAt_cons _ ⟨_, hvp _, rfl⟩
  | @short tag v cc count htag hv hvl hc =>
    have ht4 : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a := by
      rcases htag with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    obtain ⟨k, nx, e1, hk⟩ := rqc_cons_delim c ht4 path (v ++ (cc ++ (Y ++ Z)))
    have hk' := hk htag
    subst hk'
    simp only [List.length_cons, List.length_append] at hY
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    have hfit' := fun e => (openOf_field (tag := tag) (cc := cc) hv hvl) ▸ hfit e
    rw [if_neg (by
      intro h
      have h2 := hfit' h.1
      simp only [List.length_append] at h h2
      omega)]
    rw [show (tag :: (v ++ cc)).length + i = ((fill Class.structure v).length + (cc.length + i)) + 1 by
      simp [fillL]; omega]
    apply pubAt_cons
    apply pubAt_append
    apply pubAt_prefix (by rw [fillL, List.length_take]; simp; omega)
    exact pubAt_fill rfl _ _ (by rw [List.length_take]; simp; omega)

/-- Nothing of a request's unfinished field is `error` (with `complete`, provided it fits). -/
theorem q_tail_noerr_c (c : Bool) {T : List Byte} {e : Nat} (ht : Tail T e) (R : List Byte)
    (hfit : c = true → openOf T ≤ R.length) (path : List Byte) :
    ∀ x ∈ (rqc path c (T ++ R)).take T.length, x ≠ .error := by
  cases ht with
  | empty => intro x hx; simp at hx
  | @unfinished tag u htag hu hl =>
    rw [List.length_cons]
    by_cases h20 : tag = 0x20
    · subst h20
      rw [List.cons_append, rqc_cons_number]
      apply noerr_cons (by decide)
      rw [ReceiveStream.varintThen_short_take (varintEnd_short_of 10 u hu hl)]
      exact fill_noerr (by decide) _
    · have ht4 : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a := by
        rcases htag with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact absurd h h20
      obtain ⟨k, nx, e1, -⟩ := rqc_cons_delim c ht4 path (u ++ R)
      rw [List.cons_append, e1]
      apply noerr_cons (by decide)
      rw [ReceiveStream.varintThen_short_take (varintEnd_short_of 10 u hu hl)]
      exact fill_noerr (by decide) _
  | @short tag v cc count htag hv hvl hc =>
    have ht4 : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a := by
      rcases htag with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    obtain ⟨k, nx, e1, hk⟩ := rqc_cons_delim c ht4 path (v ++ (cc ++ R))
    have hk' := hk htag
    subst hk'
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    have hfit' := fun e => (openOf_field (tag := tag) (cc := cc) hv hvl) ▸ hfit e
    rw [if_neg (by
      intro h
      have h2 := hfit' h.1
      simp only [List.length_append] at h h2
      omega)]
    rw [show (tag :: (v ++ cc)).length = (v.length + cc.length) + 1 by
      simp only [List.length_cons, List.length_append]; try omega]
    apply noerr_cons (by decide)
    rw [← List.append_assoc]
    apply noerr_of_prefix (by simp [fillL]; omega)
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact fill_noerr (by decide) _ x h
    · exact fill_noerr (by decide) _ x h

theorem message_kind1_c (ob c : Bool) (Z : List Byte) :
    ReceiveSpec.message ob c (8 :: 1 :: Z) = .kind :: .kind :: ReceiveSpec.wrapper 0x12 (requestFields c) Z := by
  match Z with
  | [] => rfl
  | _ :: _ => rw [ReceiveStream.message_eq, if_pos ⟨rfl, rfl⟩]

theorem requestFields_rqc (c : Bool) (X : List Byte) : requestFields c X = rqc [] c X := rfl

/-! ### `fieldMissing`, exactly -/

theorem tail_missing_q {T : List Byte} {e : Nat} (ht : Tail T e) {H : List Byte} {p : Nat}
    (hd : H.drop p = T) (k : Nat) : missingResult (loopG (missingBody H) (k + 1) ⟨none, p⟩) = openOf T := by
  have hlen0 := congrArg List.length hd
  rw [List.length_drop] at hlen0
  cases ht with
  | empty =>
    have hle : H.length ≤ p := by simp at hlen0; omega
    rw [loopG_done _ (by unfold missingBody; rw [if_pos hle])]
    rfl
  | unfinished htag hu hl10 =>
    rename_i tag u
    have hlen := length_of_drop hd (by simp)
    simp only [List.length_cons] at hlen
    have hg := get_of_drop hd
    have hd1 : H.drop (p + 1) = u := by rw [← List.drop_drop, hd]; rfl
    have hvar := varintAt_partial hu hd1
    have hp : ¬ H.length ≤ p := by omega
    rw [loopG_done _ (by
      unfold missingBody
      simp only [hg, hvar, ge_iff_le, hp, if_false]
      rcases htag with rfl | rfl | rfl | rfl | rfl <;> rfl), openOf_partial hu hl10]
    rfl
  | short htag hv hl hc =>
    rename_i tag v c count
    have hlen := length_of_drop hd (by simp)
    simp only [List.length_cons, List.length_append] at hlen
    have hg := get_of_drop hd
    have hd1 : H.drop (p + 1) = v ++ c := by rw [← List.drop_drop, hd]; rfl
    have hvar := varintAt_varint hv hl hd1
    obtain ⟨-, t2⟩ := tag_cases tag htag
    have hp : ¬ H.length ≤ p := by omega
    have hn : H.length < p + 1 + v.length + count := by omega
    rw [loopG_done _ (by
      unfold missingBody
      simp only [hg, hvar, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true]
      rfl), openOf_field hv hl]
    simp only [missingResult]
    omega

/-- **`fieldMissing` on the controller's revealed bytes of a request** is what the open field still
declares. -/
theorem fieldMissing_open {lw R F T path : List Byte} {m e : Nat} {b : Option Nat} (hw : Varint lw m)
    (hwl : lw.length ≤ 10) (hr : QFs [] R F b path) (ht : Tail T e) :
    fieldMissing (8 :: 1 :: 0x12 :: (lw ++ (R ++ T))) = openOf T := by
  generalize hH : (8 :: 1 :: 0x12 :: (lw ++ (R ++ T)) : List Byte) = H
  have hlen : H.length = 3 + lw.length + R.length + T.length := by rw [← hH]; simp; omega
  have hd3 : H.drop 3 = lw ++ (R ++ T) := by rw [← hH]; rfl
  have hvar := varintAt_varint (rest := R ++ T) hw hwl hd3
  have hdp : H.drop (3 + lw.length) = R ++ T := by rw [← List.drop_drop, hd3, List.drop_left]
  obtain ⟨n, hn, hreach⟩ := qfs_missing hr H T (3 + lw.length) hdp
  have hdt : H.drop (3 + lw.length + R.length) = T := by rw [← List.drop_drop, hdp, List.drop_left]
  rw [fieldMissing_eq, if_neg (by omega), hvar]
  dsimp only
  rw [show H.length + 1 = n + (H.length - n + 1) by omega, loopG_reaches n _ _ _ hreach]
  exact tail_missing_q ht hdt _

/-! ### The request half, at the message level -/

/-- **The request half of T1 at the message level, for both values of `complete`.** From any state the
controller reaches inside a server request (`QShape`), the run it reveals next is public in
`message ob c` of the whole message (with `complete`, provided the open field fits). -/
theorem qshape_run_c {H : List Byte} {bs : Bool} {P : List Byte} (h : QShape H bs P) (ob c : Bool) (Y Z : List Byte)
    (hY : Y.length ≤ max 1 (fieldMissing H)) (hfit : c = true → fieldMissing H ≤ (Y ++ Z).length)
    (i : Nat) (hi : i < Y.length) :
    PubAt (ReceiveSpec.message ob c (8 :: 1 :: (P ++ (Y ++ Z)))) (2 + P.length + i) := by
  rw [message_kind1_c]
  cases h with
  | kind =>
    have hb : fieldMissing [8, 1] = 0 := by rw [fieldMissing_eq]; rfl
    rw [hb] at hY
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    simp only [List.nil_append, List.length_nil]
    apply pubAt_cons; apply pubAt_cons
    rw [List.cons_append, wrapper_cons]; split
    · exact ⟨.structure, rfl, rfl⟩
    · exact ⟨.structure, rfl, rfl⟩
  | wrapper hu hl =>
    rename_i u
    have hb : fieldMissing (8 :: 1 :: 0x12 :: u) = 0 := by
      rw [fieldMissing_eq, if_neg (by simp), varintAt_partial hu rfl]
    rw [hb] at hY
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    simp only [List.cons_append, List.length_cons]
    rw [wrapper_cons, if_pos rfl, show 2 + (u.length + 1) + 0 = u.length + 1 + 1 + 1 by omega]
    apply pubAt_cons; apply pubAt_cons; apply pubAt_cons
    rcases varint_pos hu hl (y :: (Y' ++ Z)) _ u.length (Nat.le_refl _) hl (by simp) with ⟨m, -, hm, hlt, -⟩ | h
    · exact ⟨_, hlt hm, rfl⟩
    · exact ⟨_, h, rfl⟩
  | fields hw hwl hr ht =>
    rename_i lw R F T path m e b
    have hfm := fieldMissing_fields hw hwl hr ht
    have hP : (0x12 :: (lw ++ (F ++ T)) : List Byte) ++ (Y ++ Z) = 0x12 :: (lw ++ (F ++ (T ++ (Y ++ Z)))) := by simp
    rw [hP, wrapper_cons, if_pos rfl, varintThen_varint hw hwl]
    obtain ⟨C, eC, hCl, -⟩ := qfsc_classes c hr (T ++ (Y ++ Z))
    show PubAt (_ :: _ :: _ :: (fill Class.structure lw ++ rqc [] c (F ++ (T ++ (Y ++ Z))))) _
    rw [eC]
    rw [show 2 + (0x12 :: (lw ++ (F ++ T)) : List Byte).length + i =
      ((fill Class.structure lw).length + (C.length + (T.length + i))) + 1 + 1 + 1 by simp [fillL, hCl]; omega]
    apply pubAt_cons; apply pubAt_cons; apply pubAt_cons
    apply pubAt_append
    apply pubAt_append
    exact q_tail_run_c c ht Y Z (by omega) (fun e => by rw [← fieldMissing_open hw hwl hr ht]; exact hfit e) path i hi

/-- **Nothing the controller has accepted of a request is `error`**, for both values of `complete`. -/
theorem qshape_noerr_c {H : List Byte} {bs : Bool} {P : List Byte} (h : QShape H bs P) (ob c : Bool) (R : List Byte)
    (hfit : c = true → fieldMissing H ≤ R.length) :
    ∀ x ∈ (ReceiveSpec.message ob c (8 :: 1 :: (P ++ R))).take (2 + P.length), x ≠ .error := by
  rw [message_kind1_c]
  cases h with
  | kind =>
    intro x hx
    simp only [List.nil_append, List.length_nil, Nat.add_zero, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  | wrapper hu hl =>
    rename_i u
    rw [show 2 + (0x12 :: u : List Byte).length = (u.length + 1) + 1 + 1 by simp; omega]
    apply noerr_cons (by decide); apply noerr_cons (by decide)
    simp only [List.cons_append]
    rw [wrapper_cons, if_pos rfl]
    apply noerr_cons (by decide)
    rw [ReceiveStream.varintThen_short_take (varintEnd_short_of 10 u hu hl)]
    exact fill_noerr (by decide) _
  | fields hw hwl hr ht =>
    rename_i lw R' F T path m e b
    have hP : (0x12 :: (lw ++ (F ++ T)) : List Byte) ++ R = 0x12 :: (lw ++ (F ++ (T ++ R))) := by simp
    rw [hP, wrapper_cons, if_pos rfl, varintThen_varint hw hwl]
    obtain ⟨C, eC, hCl, hC⟩ := qfsc_classes c hr (T ++ R)
    show ∀ x ∈ (_ :: _ :: _ :: (fill Class.structure lw ++ rqc [] c (F ++ (T ++ R)))).take _, x ≠ _
    rw [eC]
    rw [show 2 + (0x12 :: (lw ++ (F ++ T)) : List Byte).length =
      ((fill Class.structure lw).length + (C.length + T.length)) + 1 + 1 + 1 by simp [fillL, hCl]; omega]
    apply noerr_cons (by decide); apply noerr_cons (by decide); apply noerr_cons (by decide)
    apply noerr_take_append (fill_noerr (by decide) _)
    apply noerr_take_append hC
    exact q_tail_noerr_c c ht R (fun e => by rw [← fieldMissing_open hw hwl hr ht]; exact hfit e) path

/-- **A request's body, at the message level.** When the scanner asks to pass over a body of `n` bytes
at the byte `y` (the end of the body's length), the message's classes are: those of what came before
(no `error`), then the body's (`requestBody`, its path being the scanner's), then the fields after it;
with `complete`, provided the body fits in the rest of the message. -/
theorem qshape_body_c {H : List Byte} {bs : Bool} {P : List Byte} (h : QShape H bs P) (y : Byte) {n : Nat}
    (hm : (scan (H ++ [y]) bs).1 = .skip n) (ob c : Bool) (W : List Byte) (hfit : c = true → n ≤ W.length) :
    ∃ C : List Class, ReceiveSpec.message ob c (8 :: 1 :: (P ++ y :: W)) =
      C ++ (requestBody (scan (H ++ [y]) bs).2.path (W.take n) ++ rqc (scan (H ++ [y]) bs).2.path c (W.drop n)) ∧
      C.length = 2 + P.length + 1 ∧ NoErr C := by
  cases h with
  | kind =>
    exfalso
    by_cases hy : y = 0x12
    · subst hy
      have e : (scan ([8, 1] ++ [0x12]) false).1 = .more := rfl
      rw [e] at hm; cases hm
    · rw [scan_kind_bad hy] at hm; cases hm
  | wrapper hu hl =>
    rename_i u
    exfalso
    have hH : (8 :: 1 :: 0x12 :: u : List Byte) ++ [y] = 8 :: 1 :: 0x12 :: (u ++ [y]) := by simp
    rw [hH] at hm
    have hd3 : (8 :: 1 :: 0x12 :: (u ++ [y]) : List Byte).drop 3 = u ++ [y] := rfl
    rw [scan_eq, if_neg (by simp), if_pos (head1_ok _)] at hm
    by_cases hy : y.toNat < 128
    · obtain ⟨n', hv⟩ := varint_snoc u hu y hy
      have hvl : (u ++ [y]).length ≤ 10 := by simp; omega
      rw [varintAt_varint (rest := []) hv hvl (by rw [hd3, List.append_nil])] at hm
      dsimp only at hm
      rw [loopG_done _ (scanBody_end (by simp; omega))] at hm
      cases hm
    · have hpart := varintAt_partial (all_snoc hu (by omega)) hd3
      rw [hpart] at hm
      dsimp only at hm
      split at hm <;> cases hm
  | fields hw hwl hr ht =>
    rename_i lw R F T path m e b
    have hH : (8 :: 1 :: 0x12 :: (lw ++ (R ++ T)) : List Byte) ++ [y] = 8 :: 1 :: 0x12 :: (lw ++ (R ++ (T ++ [y]))) := by
      simp
    rw [hH] at hm ⊢
    obtain ⟨f, k, hfb, hfp, hs⟩ := scan_qfields (T := T ++ [y]) hw hwl hr
    have hd : (8 :: 1 :: 0x12 :: (lw ++ (R ++ (T ++ [y]))) : List Byte).drop (3 + lw.length + R.length) = T ++ [y] := by
      rw [show 3 + lw.length + R.length = 3 + (lw.length + R.length) by omega, ← List.drop_drop]
      simp
    have hstep := q_tail_step ht hd hfp hfb k
    rw [hs] at hm ⊢
    obtain ⟨hn, hb, hpath, v, hT, hv, hvl⟩ := hstep.2 n hm
    rw [hpath]
    have hTv : T.length = v.length := by have := congrArg List.length hT; simp at this; omega
    have hP : (0x12 :: (lw ++ (F ++ T)) : List Byte) ++ y :: W = 0x12 :: (lw ++ (F ++ (0x1a :: (v ++ W)))) := by
      rw [show (0x1a :: (v ++ W) : List Byte) = (T ++ [y]) ++ W by rw [hT]; simp]; simp
    rw [hP, message_kind1_c, wrapper_cons, if_pos rfl, varintThen_varint hw hwl]
    obtain ⟨C, eC, hCl, hC⟩ := qfsc_classes c hr (0x1a :: (v ++ W))
    rw [requestFields_rqc, eC]
    obtain ⟨kk, nx, e1, -⟩ := rqc_cons_delim c (Or.inr (Or.inr (Or.inr rfl))) path (v ++ W)
    have e1' : rqc path c (0x1a :: (v ++ W)) = .structure :: (fill .structure v ++
        (requestBody path (W.take n) ++ rqc path c (W.drop n))) := by
      unfold rqc
      rw [List.length_cons, ReceiveStream.request_cons, if_neg (by decide), if_neg (by decide), if_pos rfl,
        ReceiveStream.delimitedThen_eq, varintThen_varint hv hvl]
      unfold ReceiveStream.delimCont
      rw [if_neg (by intro h'; have := hfit h'.1; omega)]
      dsimp only
      rw [rqc_fuel _ c (W.drop n) _ (by simp; omega)]
      rfl
    rw [e1']
    refine ⟨.kind :: .kind :: .structure :: (fill .structure lw ++ (C ++ (.structure :: fill .structure v))),
      by simp, by simp [fillL, hCl]; omega, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | rfl | rfl | hx | hx | rfl | hx
    · decide
    · decide
    · decide
    · exact fill_noerr (by decide) _ x hx
    · exact hC x hx
    · decide
    · exact fill_noerr (by decide) _ x hx

end ReceiveComplete
