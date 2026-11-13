import TlsMpc.Node.Policy.ReceiveReply

/-!
# T1 for server requests' own fields, every field order (proof track P1, item 2)

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`Policy/ReceiveProofs.lean` proved the request scanner right on the server's layout (verb, path,
body: `request_body_unrevealed`). Here: **every** field order and every byte string, the body being a
delivered envelope or not.

## The controller's view of a server request (`QShape`)

While a server request (`08 01`) arrives, the controller keeps its revealed bytes (`State.request`:
the message's bytes with the body's content left out) and whether the body has been passed over
(`State.bodySkipped`). `QShape H bs P` says what `H` and `bs` are after the message bytes
`[8, 1] ++ P`: the wrapper (`12`, its length), complete fields (`QFs`: ids, verbs, paths, headers, at
most one body, any order and number; the reference's current path is tracked as it reads them), then
an unfinished field (`ReceiveProofs.Tail`: nothing, a key and part of its varint, part of a verb,
path or header).

* `qshape_more`, `qshape_skip`: every byte the scanner accepts, and every body it asks to pass over,
  keep the shape. A body is any bytes `B` whose classes in the reference (`requestBody path B`, the
  path being the scanner's) have no `error`: always so unless the path is `/api/v1/message`
  (`requestBody_noErr`); for a delivered envelope that is what its walk must establish
  (`Policy/ReceiveEnvelope.lean`, `Policy/ReceiveInvariant.lean`).
* **`qshape_run`**: from such a state, the run the controller reveals next (`max 1 (fieldMissing H)`
  bytes, whatever they are: the next byte, or the rest of a verb, path or header) is public in the
  reference (`ReceiveSpec.message _ false`). No allowance is needed inside a request.
* `request_run_safe`: the same at the controller level (`budget`), with `QIn` kept by
  `payloadByte`/`stepSkipped` on a body that is not a delivered envelope (`payloadByte_qIn`,
  `stepSkipped_qIn`).
-/

namespace ReceiveRequestScan

open PublicReceive ReceiveProofs ReceiveReply
open ReceiveSpec (Class fill varintThen varintEnd varintValue VarintEnd requestBody)

/-! ### The reference, field by field -/

/-- A request's fields as the reference reads them from path `path`, with enough fuel. -/
def rqf (path X : List Byte) : List Class := ReceiveSpec.request false (X.length + 1) path X

theorem rq_fuel (path X : List Byte) (k : Nat) (h : X.length < k) : ReceiveSpec.request false k path X = rqf path X :=
  ReceiveStream.request_fuel false k _ path X h (Nat.lt_succ_self _)

theorem rq_number {v : List Byte} {n : Nat} (hv : Varint v n) (hl : v.length ≤ 10) (path Z : List Byte) :
    rqf path (0x20 :: (v ++ Z)) = .structure :: (fill .structure v ++ rqf path Z) := by
  unfold rqf
  rw [List.length_cons, ReceiveStream.request_cons, if_pos rfl, varintThen_varint hv hl,
    rq_fuel path Z _ (by simp; omega)]
  rfl

theorem rq_text {tag : Byte} {v c : List Byte} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) (hv : Varint v c.length)
    (hl : v.length ≤ 10) (path Z : List Byte) :
    rqf path (tag :: (v ++ (c ++ Z))) =
      .structure :: (fill .structure v ++ (fill .text c ++ rqf (if tag = 0x12 then c else path) Z)) := by
  have h1 : ¬ tag = 0x20 := by rcases ht with rfl | rfl | rfl <;> decide
  unfold rqf
  rw [List.length_cons, ReceiveStream.request_cons, if_neg h1, if_pos ht, ReceiveStream.delimitedThen_eq,
    varintThen_varint hv hl]
  unfold ReceiveStream.delimCont
  rw [if_neg (by simp), List.take_left' rfl, List.drop_left]
  dsimp only
  rw [rq_fuel _ Z _ (by simp; omega)]
  rfl

theorem rq_body {v c : List Byte} (hv : Varint v c.length) (hl : v.length ≤ 10) (path Z : List Byte) :
    rqf path (0x1a :: (v ++ (c ++ Z))) = .structure :: (fill .structure v ++ (requestBody path c ++ rqf path Z)) := by
  unfold rqf
  rw [List.length_cons, ReceiveStream.request_cons, if_neg (by decide), if_neg (by decide), if_pos rfl,
    ReceiveStream.delimitedThen_eq, varintThen_varint hv hl]
  unfold ReceiveStream.delimCont
  rw [if_neg (by simp), List.take_left' rfl, List.drop_left]
  dsimp only
  rw [rq_fuel _ Z _ (by simp; omega)]
  rfl

theorem rq_cons_number (path Z : List Byte) :
    rqf path (0x20 :: Z) = .structure :: varintThen Z (fun _ after => ReceiveSpec.request false (Z.length + 1) path after) := by
  unfold rqf; rw [List.length_cons, ReceiveStream.request_cons, if_pos rfl]

theorem rq_cons_delim {tag : Byte} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a) (path Z : List Byte) :
    ∃ (k : List Byte → List Class) (nx : List Byte → List Byte → List Class), rqf path (tag :: Z) =
      .structure :: varintThen Z (ReceiveStream.delimCont false k nx) ∧
      (tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a → k = fill .text) := by
  unfold rqf
  rw [List.length_cons, ReceiveStream.request_cons]
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨_, _, by rw [if_neg (by decide), if_pos (Or.inl rfl), ReceiveStream.delimitedThen_eq], fun _ => rfl⟩
  · exact ⟨_, _, by rw [if_neg (by decide), if_pos (Or.inr (Or.inl rfl)), ReceiveStream.delimitedThen_eq],
      fun _ => rfl⟩
  · exact ⟨_, _, by rw [if_neg (by decide), if_pos (Or.inr (Or.inr rfl)), ReceiveStream.delimitedThen_eq],
      fun _ => rfl⟩
  · exact ⟨_, _, by rw [if_neg (by decide), if_neg (by decide), if_pos rfl, ReceiveStream.delimitedThen_eq],
      fun h => by rcases h with h | h | h <;> cases h⟩

/-- The classes of a whole server request: the kind, the wrapper key and length, the fields. -/
theorem message_request (ob : Bool) {lw : List Byte} {m : Nat} (hw : Varint lw m) (hl : lw.length ≤ 10)
    (Z : List Byte) :
    ReceiveSpec.message ob false (8 :: 1 :: 0x12 :: (lw ++ Z)) =
      .kind :: .kind :: .structure :: (fill .structure lw ++ rqf [] Z) := by
  rw [ReceiveStream.message_eq, if_pos ⟨rfl, rfl⟩, wrapper_cons, if_pos rfl, varintThen_varint hw hl]
  rfl

theorem message_kind1 (ob : Bool) (Z : List Byte) :
    ReceiveSpec.message ob false (8 :: 1 :: Z) =
      .kind :: .kind :: ReceiveSpec.wrapper 0x12 (ReceiveStream.requestFields false) Z := by
  match Z with
  | [] => rfl
  | _ :: _ => rw [ReceiveStream.message_eq, if_pos ⟨rfl, rfl⟩]

/-- No `error` among classes. -/
def NoErr (C : List Class) : Prop := ∀ x ∈ C, x ≠ .error

/-- The body of a request whose path is not `/api/v1/message` is `body` throughout: no `error`. -/
theorem requestBody_noErr {path : List Byte} (hp : path ≠ ReceiveSpec.messagePath) (B : List Byte) :
    NoErr (requestBody path B) := by
  unfold requestBody; rw [if_neg hp]; exact fill_noerr (by decide) B

/-! ### Complete fields -/

/-- One complete request field read from path `path`, leaving path `path'`: revealed bytes and message
bytes (the body's content is never among the revealed bytes), the body's length if it is the body. -/
inductive QF : List Byte → List Byte → List Byte → Option Nat → List Byte → Prop
  | number {path v : List Byte} {n : Nat} : Varint v n → v.length ≤ 10 → QF path (0x20 :: v) (0x20 :: v) none path
  | text {path : List Byte} {tag : Byte} {v c : List Byte} : (tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) →
      Varint v c.length → v.length ≤ 10 →
      QF path (tag :: (v ++ c)) (tag :: (v ++ c)) none (if tag = 0x12 then c else path)
  | body {path v c : List Byte} : Varint v c.length → v.length ≤ 10 → NoErr (requestBody path c) →
      QF path (0x1a :: v) (0x1a :: (v ++ c)) (some c.length) path

/-- **Complete request fields**, in any order, from path `path` to path `path'`; at most one body. -/
inductive QFs : List Byte → List Byte → List Byte → Option Nat → List Byte → Prop
  | nil {path : List Byte} : QFs path [] [] none path
  | number {path v R F path' : List Byte} {n : Nat} {b : Option Nat} : Varint v n → v.length ≤ 10 →
      QFs path R F b path' → QFs path (0x20 :: (v ++ R)) (0x20 :: (v ++ F)) b path'
  | text {path : List Byte} {tag : Byte} {v c R F path' : List Byte} {b : Option Nat} :
      (tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) → Varint v c.length → v.length ≤ 10 →
      QFs (if tag = 0x12 then c else path) R F b path' →
      QFs path (tag :: (v ++ (c ++ R))) (tag :: (v ++ (c ++ F))) b path'
  | body {path v c R F path' : List Byte} : Varint v c.length → v.length ≤ 10 → NoErr (requestBody path c) →
      QFs path R F none path' → QFs path (0x1a :: (v ++ R)) (0x1a :: (v ++ (c ++ F))) (some c.length) path'

theorem qfs_snoc {path R F path1 : List Byte} {b : Option Nat} (h : QFs path R F b path1) {Rf Ff path2 : List Byte}
    {bf : Option Nat} (hf : QF path1 Rf Ff bf path2) (hb : b = none ∨ bf = none) :
    QFs path (R ++ Rf) (F ++ Ff) (b.or bf) path2 := by
  induction h with
  | nil =>
    cases hf with
    | number hv hl => simpa using QFs.number hv hl QFs.nil
    | text ht hv hl => simpa using QFs.text ht hv hl QFs.nil
    | body hv hl hn => simpa using QFs.body hv hl hn QFs.nil
  | number hv hl _ ih => simpa using QFs.number hv hl (ih hf hb)
  | text ht hv hl _ ih => simpa using QFs.text ht hv hl (ih hf hb)
  | body hv hl hn _ ih =>
    rcases hb with hb | hb
    · cases hb
    · subst hb
      simpa using QFs.body hv hl hn (ih hf (Or.inl rfl))

theorem noErr_fill {α : Type} {k : Class} (hk : k ≠ .error) (l : List α) : NoErr (fill k l) := fill_noerr hk l

/-- The classes of complete fields have no `error`. -/
theorem qfs_classes {path R F path' : List Byte} {b : Option Nat} (h : QFs path R F b path') (Z : List Byte) :
    ∃ C : List Class, rqf path (F ++ Z) = C ++ rqf path' Z ∧ C.length = F.length ∧ NoErr C := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, by simp [NoErr]⟩
  | @number path v R F path' n b hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ C), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, rq_number hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx; rcases hx with rfl | ⟨_, _, rfl⟩ | hx <;> first | decide | exact hc x hx
  | @text path tag v c R F path' b ht hv hl _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ (fill .text c ++ C)), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, List.append_assoc, rq_text ht hv hl, e]; simp
    · simp [fillL, hl']
    · intro x hx; simp [fill] at hx
      rcases hx with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | hx <;> first | decide | exact hc x hx
  | @body path v c R F path' hv hl hn _ ih =>
    obtain ⟨C, e, hl', hc⟩ := ih
    refine ⟨.structure :: (fill .structure v ++ (requestBody path c ++ C)), ?_, ?_, ?_⟩
    · rw [List.cons_append, List.append_assoc, List.append_assoc, rq_body hv hl, e]; simp
    · simp [fillL, hl', ReceiveStream.requestBody_len path c]
    · intro x hx; simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx | hx
      · decide
      · exact fill_noerr (by decide) _ x hx
      · exact hn x hx
      · exact hc x hx

/-! ### `scan`'s and `fieldMissing`'s loops, one round at a time -/

theorem bad_req_bools : ∀ y : Byte, ¬ (y = 0x20 ∨ y = 0x0a ∨ y = 0x12 ∨ y = 0x2a ∨ y = 0x1a) →
    (y.toNat == 0x20) = false ∧ (y.toNat == 0x0a || y.toNat == 0x12 || y.toNat == 0x2a) = false ∧
      (y.toNat == 0x1a) = false := by
  decide

theorem tag20_bools : ((0x20 : Byte).toNat == 0x20) = true ∧
    ((0x20 : Byte).toNat == 0x0a || (0x20 : Byte).toNat == 0x12 || (0x20 : Byte).toNat == 0x2a) = false ∧
    ((0x20 : Byte).toNat == 0x20 || (0x20 : Byte).toNat == 0x1a) = true := by decide

theorem tag1a_bools : ((0x1a : Byte).toNat == 0x20) = false ∧
    ((0x1a : Byte).toNat == 0x0a || (0x1a : Byte).toNat == 0x12 || (0x1a : Byte).toNat == 0x2a) = false ∧
    ((0x1a : Byte).toNat == 0x1a) = true ∧ ((0x1a : Byte).toNat == 0x20 || (0x1a : Byte).toNat == 0x1a) = true := by
  decide

theorem scanBody_number {bytes v rest : List Byte} {bs : Bool} {x : Option (Need × Fields)} {f : Fields}
    {pos n : Nat} (hv : Varint v n) (hl : v.length ≤ 10) (h : bytes.drop pos = 0x20 :: (v ++ rest)) :
    scanBody bytes bs ⟨x, f, pos⟩ = .yield ⟨none, { f with id := some n }, pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, -, -⟩ := tag20_bools
  unfold scanBody
  simp only [hg, hvar, t1, ge_iff_le, hp, if_false, if_true]

theorem scanBody_bad {bytes rest : List Byte} {tag : Byte} {bs : Bool} {x : Option (Need × Fields)} {f : Fields}
    {pos : Nat} (h : bytes.drop pos = tag :: rest) (hb : ¬ (tag = 0x20 ∨ tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a)) :
    scanBody bytes bs ⟨x, f, pos⟩ = .done ⟨some (.malformed, f), f, pos⟩ := by
  obtain ⟨hg, -, hp, -⟩ := field_at h
  obtain ⟨b1, b2, b3⟩ := bad_req_bools tag hb
  unfold scanBody
  simp only [hg, b1, b2, b3, ge_iff_le, hp, if_false, Bool.false_eq_true]

theorem scanBody_bodyField {bytes v rest : List Byte} {bs : Bool} {x : Option (Need × Fields)} {f : Fields}
    {pos count : Nat} (hv : Varint v count) (hl : v.length ≤ 10) (hf : f.body = none)
    (h : bytes.drop pos = 0x1a :: (v ++ rest))
    (hns : ¬ (pos + 1 + v.length = bytes.length ∧ bs = false ∧ 0 < count)) :
    scanBody bytes bs ⟨x, f, pos⟩ = .yield ⟨none, { f with body := some count }, pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, t2, t3, -⟩ := tag1a_bools
  have hs : (pos + 1 + v.length == bytes.length && !bs && decide (count > 0)) = false := by
    rw [Bool.eq_false_iff]; intro e
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at e
    exact hns ⟨e.1.1, e.1.2, e.2⟩
  unfold scanBody
  simp only [hg, hvar, hf, t1, t2, t3, hs, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true,
    Option.isSome_none]

theorem scanBody_bodyTwice {bytes v rest : List Byte} {bs : Bool} {x : Option (Need × Fields)} {f : Fields}
    {pos count : Nat} (hv : Varint v count) (hl : v.length ≤ 10) (hf : f.body.isSome = true)
    (h : bytes.drop pos = 0x1a :: (v ++ rest)) :
    scanBody bytes bs ⟨x, f, pos⟩ = .done ⟨some (.malformed, f), f, pos⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, t2, t3, -⟩ := tag1a_bools
  unfold scanBody
  simp only [hg, hvar, hf, t1, t2, t3, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true]

theorem missingBody_numberish {bytes v rest : List Byte} {tag : Byte} {x : Option Nat} {pos n : Nat}
    (ht : tag = 0x20 ∨ tag = 0x1a) (hv : Varint v n) (hl : v.length ≤ 10) (h : bytes.drop pos = tag :: (v ++ rest)) :
    missingBody bytes ⟨x, pos⟩ = .yield ⟨none, pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  have t : (tag.toNat == 0x0a || tag.toNat == 0x12 || tag.toNat == 0x2a) = false ∧
      (tag.toNat == 0x20 || tag.toNat == 0x1a) = true := by rcases ht with rfl | rfl <;> decide
  unfold missingBody
  simp only [hg, hvar, t.1, t.2, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true]

theorem textField_path (tag : Byte) (c : List Byte) (f : Fields) (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) :
    (textField tag c f).path = (if tag = 0x12 then c else f.path) ∧ (textField tag c f).body = f.body := by
  unfold textField
  rcases ht with rfl | rfl | rfl <;> simp

/-- **The scanner walks complete request fields**, noting the path and the body. -/
theorem qfs_scan {path R F path' : List Byte} {b : Option Nat} (h : QFs path R F b path') :
    ∀ (H T : List Byte) (p : Nat) (bs : Bool) (f : Fields), H.drop p = R ++ T → f.path = path →
      (f.body = none ∨ b = none) → (∀ m, b = some m → 0 < m → bs = true) →
      ∃ n f', n ≤ R.length ∧ Reaches (scanBody H bs) n ⟨none, f, p⟩ ⟨none, f', p + R.length⟩ ∧
        f'.body = b.or f.body ∧ f'.path = path' := by
  induction h with
  | nil => intro H T p bs f _ hp _ _; exact ⟨0, f, Nat.le_refl _, rfl, rfl, hp⟩
  | @number path v R F path' n b hv hl _ ih =>
    intro H T p bs f hd hp hb hs
    have hd' : H.drop p = 0x20 :: (v ++ (R ++ T)) := by rw [hd]; simp
    have hr := scanBody_number (x := none) (f := f) (bs := bs) hv hl hd'
    obtain ⟨k, f', hk, hreach, hbody, hpath⟩ := ih H T (p + 1 + v.length) bs { f with id := some n }
      (drop_number hd') hp hb hs
    refine ⟨k + 1, f', by simp; omega, ⟨_, hr, ?_⟩, hbody, hpath⟩
    rw [show p + (0x20 :: (v ++ R)).length = p + 1 + v.length + R.length by simp; omega]
    exact hreach
  | @text path tag v c R F path' b ht hv hl _ ih =>
    intro H T p bs f hd hp hb hs
    have hd' : H.drop p = tag :: (v ++ (c ++ (R ++ T))) := by rw [hd]; simp
    have hr := scanBody_text (x := none) (f := f) (b := bs) ht hv hl hd'
    obtain ⟨tp, tb⟩ := textField_path tag c f ht
    obtain ⟨k, f', hk, hreach, hbody, hpath⟩ := ih H T (p + 1 + v.length + c.length) bs (textField tag c f)
      (drop_field hd') (by rw [tp, hp]) (by rw [tb]; exact hb) hs
    refine ⟨k + 1, f', by simp; omega, ⟨_, hr, ?_⟩, by rw [hbody, tb], hpath⟩
    rw [show p + (tag :: (v ++ (c ++ R))).length = p + 1 + v.length + c.length + R.length by simp; omega]
    exact hreach
  | @body path v c R F path' hv hl hn _ ih =>
    intro H T p bs f hd hp hb hs
    have hf : f.body = none := by rcases hb with hb | hb; exact hb; cases hb
    have hd' : H.drop p = 0x1a :: (v ++ (R ++ T)) := by rw [hd]; simp
    have hr := scanBody_bodyField (x := none) (bs := bs) (f := f) hv hl hf hd' (by
      rintro ⟨-, e2, e3⟩
      have := hs c.length rfl e3
      rw [this] at e2; cases e2)
    obtain ⟨k, f', hk, hreach, hbody, hpath⟩ := ih H T (p + 1 + v.length) bs { f with body := some c.length }
      (drop_number hd') hp (Or.inr rfl) (fun m e => by cases e)
    refine ⟨k + 1, f', by simp; omega, ⟨_, hr, ?_⟩, by rw [hbody]; rfl, hpath⟩
    rw [show p + (0x1a :: (v ++ R)).length = p + 1 + v.length + R.length by simp; omega]
    exact hreach

/-- **`fieldMissing`'s loop walks complete request fields** the same way. -/
theorem qfs_missing {path R F path' : List Byte} {b : Option Nat} (h : QFs path R F b path') :
    ∀ (H T : List Byte) (p : Nat), H.drop p = R ++ T →
      ∃ n, n ≤ R.length ∧ Reaches (missingBody H) n ⟨none, p⟩ ⟨none, p + R.length⟩ := by
  induction h with
  | nil => intro H T p _; exact ⟨0, Nat.le_refl _, rfl⟩
  | @number path v R F path' n b hv hl _ ih =>
    intro H T p hd
    have hd' : H.drop p = 0x20 :: (v ++ (R ++ T)) := by rw [hd]; simp
    have hr := missingBody_numberish (x := none) (Or.inl rfl) hv hl hd'
    obtain ⟨k, hk, hreach⟩ := ih H T (p + 1 + v.length) (drop_number hd')
    refine ⟨k + 1, by simp; omega, ⟨_, hr, ?_⟩⟩
    rw [show p + (0x20 :: (v ++ R)).length = p + 1 + v.length + R.length by simp; omega]
    exact hreach
  | @text path tag v c R F path' b ht hv hl _ ih =>
    intro H T p hd
    have hd' : H.drop p = tag :: (v ++ (c ++ (R ++ T))) := by rw [hd]; simp
    have hr := missingBody_text (x := none) ht hv hl hd'
    obtain ⟨k, hk, hreach⟩ := ih H T (p + 1 + v.length + c.length) (drop_field hd')
    refine ⟨k + 1, by simp; omega, ⟨_, hr, ?_⟩⟩
    rw [show p + (tag :: (v ++ (c ++ R))).length = p + 1 + v.length + c.length + R.length by simp; omega]
    exact hreach
  | @body path v c R F path' hv hl hn _ ih =>
    intro H T p hd
    have hd' : H.drop p = 0x1a :: (v ++ (R ++ T)) := by rw [hd]; simp
    have hr := missingBody_numberish (x := none) (Or.inr rfl) hv hl hd'
    obtain ⟨k, hk, hreach⟩ := ih H T (p + 1 + v.length) (drop_number hd')
    refine ⟨k + 1, by simp; omega, ⟨_, hr, ?_⟩⟩
    rw [show p + (0x1a :: (v ++ R)).length = p + 1 + v.length + R.length by simp; omega]
    exact hreach

/-! ### The unfinished field, one more byte -/

/-- `State.bodySkipped` as the fields say it: a non-empty body was passed over (or walked). -/
def skOfQ (b : Option Nat) : Bool := b.any (fun m => decide (0 < m))

/-- What the scanner's loop answers from the unfinished field's first byte. -/
abbrev QAns (H : List Byte) (bs : Bool) (f : Fields) (p k : Nat) : Need × Fields :=
  loopResult (loopG (scanBody H bs) (k + 1 + 1) ⟨none, f, p⟩)

/-- After the byte the scanner accepts, the unfinished field goes on or is complete; or the scanner
asks to pass over a body (`T` its key and complete length), its path being the reference's. -/
abbrev QStepOK (path T : List Byte) (b : Option Nat) (r : Need × Fields) : Prop :=
  (r.1 = .more → (∃ e, Tail T e) ∨
    (∃ bf path', QF path T T bf path' ∧ (b = none ∨ bf = none) ∧ skOfQ (b.or bf) = skOfQ b)) ∧
  (∀ n, r.1 = .skip n → 0 < n ∧ b = none ∧ r.2.path = path ∧ ∃ v, T = 0x1a :: v ∧ Varint v n ∧ v.length ≤ 10)

theorem qstep_malformed (path T : List Byte) (b : Option Nat) (f : Fields) :
    QStepOK path T b (loopResult ⟨some (.malformed, f), f, 0⟩) :=
  ⟨fun h => (by cases h), fun n h => (by cases h)⟩

theorem loopResult_done (a : Need × Fields) (f : Fields) (p : Nat) :
    loopResult (⟨some a, f, p⟩ : LoopState Fields) = a := rfl

theorem q_step_empty {H : List Byte} {p : Nat} {y : Byte} (hd : H.drop p = [y]) {f : Fields} {path : List Byte}
    {b : Option Nat} (k : Nat) : QStepOK path [y] b (QAns H (skOfQ b) f p k) := by
  by_cases hg : y = 0x20 ∨ y = 0x0a ∨ y = 0x12 ∨ y = 0x2a ∨ y = 0x1a
  · have ht : y = 0x0a ∨ y = 0x12 ∨ y = 0x2a ∨ y = 0x1a ∨ y = 0x20 := by
      rcases hg with h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    have hr := scanBody_partial (u := []) (b := skOfQ b) (x := none) (f := f) ht (by simp) (by simp)
      (by simpa using hd)
    unfold QAns; rw [loopG_done _ hr]
    exact ⟨fun _ => Or.inl ⟨_, Tail.unfinished ht (by simp) (by simp)⟩, fun n h => by cases h⟩
  · have hr := scanBody_bad (rest := []) (bs := skOfQ b) (x := none) (f := f) hd hg
    unfold QAns; rw [loopG_done _ hr]
    exact qstep_malformed path _ b f

theorem requestBody_nil (path : List Byte) : requestBody path [] = [] := by
  unfold requestBody; split <;> rfl

theorem q_step_unfinished {tag : Byte} {u : List Byte}
    (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a ∨ tag = 0x20)
    (hu : ∀ x ∈ u, 128 ≤ x.toNat) (hl : u.length < 10) {H : List Byte} {p : Nat} {y : Byte}
    (hd : H.drop p = tag :: (u ++ [y])) {f : Fields} {path : List Byte} (hfp : f.path = path)
    {b : Option Nat} (hfb : f.body = b) (k : Nat) :
    QStepOK path (tag :: (u ++ [y])) b (QAns H (skOfQ b) f p k) := by
  have hlen := length_of_drop hd (by simp)
  simp only [List.length_cons, List.length_append, List.length_nil] at hlen
  by_cases hy : y.toNat < 128
  case neg =>
    by_cases h10 : u.length + 1 < 10
    · have hr := scanBody_partial (u := u ++ [y]) (b := skOfQ b) (x := none) (f := f) ht
        (all_snoc hu (by omega)) (by simp; omega) hd
      unfold QAns; rw [loopG_done _ hr]
      exact ⟨fun _ => Or.inl ⟨_, Tail.unfinished ht (all_snoc hu (by omega)) (by simp; omega)⟩, fun n h => by cases h⟩
    · have hd1 : H.drop (p + 1) = u ++ [y] := by rw [← List.drop_drop, hd]; rfl
      have hTL := tooLong_of_drop hd1 (by simp; omega) (by
        rw [List.take_of_length_le (by simp; omega)]; exact all_snoc hu (by omega))
      have hr := scanBody_tooLong (x := none) (f := f) (b := skOfQ b) ht hd hTL
      unfold QAns; rw [loopG_done _ hr]
      exact qstep_malformed path _ b f
  obtain ⟨n, hv⟩ := varint_snoc u hu y hy
  have hvl : (u ++ [y]).length ≤ 10 := by simp; omega
  have hvlen : (u ++ [y]).length = u.length + 1 := by simp
  generalize hV : u ++ [y] = v at hv hvl hd hlen hvlen
  have hend : ∀ (g : Fields) (q : Nat), H.length ≤ q →
      scanBody H (skOfQ b) ⟨none, g, q⟩ = .done ⟨some (.more, g), g, q⟩ := fun g q hq => scanBody_end hq
  rcases ht with ht | ht | ht | ht | ht
  rotate_left 3
  · -- the body's key
    subst ht
    cases b with
    | some m =>
      have hr := scanBody_bodyTwice (x := none) (bs := skOfQ (some m)) (f := f) (rest := []) hv hvl
        (by rw [hfb]; rfl) (by simpa using hd)
      unfold QAns; rw [loopG_done _ hr]
      exact qstep_malformed path _ _ f
    | none =>
      by_cases hn : 0 < n
      · have hr := scanBody_skip (x := none) (f := f) hv hvl hn hfb (by simpa using hd)
        unfold QAns; rw [show skOfQ none = false from rfl, loopG_done _ hr]
        exact ⟨fun h => (by cases h), fun n' h => by
          simp only [loopResult_done, Need.skip.injEq] at h
          subst h
          exact ⟨hn, rfl, hfp, v, rfl, hv, hvl⟩⟩
      · have hn0 : n = 0 := by omega
        subst hn0
        have hv' : Varint v ([] : List Byte).length := hv
        have h1 := scanBody_bodyField (x := none) (f := f) (bs := skOfQ none) (rest := []) hv hvl hfb
          (by simpa using hd) (fun h => by omega)
        have h2 := hend { f with body := some 0 } (p + 1 + v.length) (by omega)
        unfold QAns; rw [loopG_yield _ h1, loopG_done _ h2]
        refine ⟨fun _ => Or.inr ⟨some 0, path, ?_, Or.inl rfl, rfl⟩, fun n h => by cases h⟩
        simpa using QF.body (path := path) hv' hvl (by rw [requestBody_nil]; intro x hx; cases hx)
  · -- the id
    subst ht
    have h1 := scanBody_number (x := none) (f := f) (bs := skOfQ b) (rest := []) hv hvl (by simpa using hd)
    have h2 := hend { f with id := some n } (p + 1 + v.length) (by omega)
    unfold QAns; rw [loopG_yield _ h1, loopG_done _ h2]
    exact ⟨fun _ => Or.inr ⟨none, path, QF.number hv hvl, Or.inr rfl, by cases b <;> rfl⟩, fun n h => by cases h⟩
  all_goals
    have ht' : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a := by
      first | exact Or.inl ht | exact Or.inr (Or.inl ht) | exact Or.inr (Or.inr ht)
    by_cases hn : 0 < n
    · have hr := scanBody_text_more (x := none) (f := f) (b := skOfQ b) (c := []) ht' hv hvl hn (by simpa using hd)
      unfold QAns; rw [loopG_done _ hr]
      exact ⟨fun _ => Or.inl ⟨_, by simpa using Tail.short (c := []) ht' hv hvl hn⟩, fun n h => by cases h⟩
    · have hn0 : n = 0 := by omega
      subst hn0
      have hv' : Varint v ([] : List Byte).length := hv
      have h1 := scanBody_text (x := none) (f := f) (b := skOfQ b) (rest := []) ht' hv' hvl (by simpa using hd)
      have h2 := hend (textField tag [] f) (p + 1 + v.length + ([] : List Byte).length) (by simp; omega)
      unfold QAns; rw [loopG_yield _ h1, loopG_done _ h2]
      refine ⟨fun _ => Or.inr ⟨none, if tag = 0x12 then [] else path, ?_, Or.inr rfl, by cases b <;> rfl⟩,
        fun n h => by cases h⟩
      simpa using QF.text (path := path) ht' hv' hvl

theorem q_step_short {tag : Byte} {v c : List Byte} {count : Nat} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a)
    (hv : Varint v count) (hvl : v.length ≤ 10) (hc : c.length < count) {H : List Byte} {p : Nat} {y : Byte}
    (hd : H.drop p = tag :: (v ++ (c ++ [y]))) {f : Fields} {path : List Byte} {b : Option Nat} (k : Nat) :
    QStepOK path (tag :: (v ++ (c ++ [y]))) b (QAns H (skOfQ b) f p k) := by
  have hlen := length_of_drop hd (by simp)
  simp only [List.length_cons, List.length_append, List.length_nil] at hlen
  by_cases he : c.length + 1 = count
  · have hv' : Varint v (c ++ [y]).length := by simpa [he] using hv
    have h1 := scanBody_text (x := none) (f := f) (b := skOfQ b) (rest := []) ht hv' hvl (by simpa using hd)
    have h2 := scanBody_end (bytes := H) (b := skOfQ b) (x := none) (f := textField tag (c ++ [y]) f)
      (pos := p + 1 + v.length + (c ++ [y]).length) (by simp; omega)
    unfold QAns; rw [loopG_yield _ h1, loopG_done _ h2]
    exact ⟨fun _ => Or.inr ⟨none, _, QF.text ht hv' hvl, Or.inr rfl, by cases b <;> rfl⟩, fun n h => by cases h⟩
  · have hr := scanBody_text_more (x := none) (f := f) (b := skOfQ b) ht hv hvl
      (show (c ++ [y]).length < count by simp; omega) hd
    unfold QAns; rw [loopG_done _ hr]
    exact ⟨fun _ => Or.inl ⟨_, Tail.short ht hv hvl (show (c ++ [y]).length < count by simp; omega)⟩,
      fun n h => by cases h⟩

theorem q_tail_step {T : List Byte} {e : Nat} (ht : Tail T e) {H : List Byte} {p : Nat} {y : Byte}
    (hd : H.drop p = T ++ [y]) {f : Fields} {path : List Byte} (hfp : f.path = path) {b : Option Nat}
    (hfb : f.body = b) (k : Nat) : QStepOK path (T ++ [y]) b (QAns H (skOfQ b) f p k) := by
  cases ht with
  | empty => exact q_step_empty hd k
  | unfinished htag hu hl => exact q_step_unfinished htag hu hl hd hfp hfb k
  | @short tag v c count htag hv hvl hc =>
    rw [show tag :: (v ++ c) ++ [y] = tag :: (v ++ (c ++ [y])) by simp] at hd ⊢
    exact q_step_short htag hv hvl hc hd k

/-! ### The controller's view of a server request -/

/-- **The controller's view of a server request**, after the message bytes `[8, 1] ++ P`: its revealed
bytes `H` (`State.request`) and `bs` (`State.bodySkipped`). After the kind; inside the wrapper's
length; or after the wrapper, complete fields `QFs` (read from the empty path) and an unfinished one. -/
inductive QShape : List Byte → Bool → List Byte → Prop
  | kind : QShape [8, 1] false []
  | wrapper {u : List Byte} : (∀ y ∈ u, 128 ≤ y.toNat) → u.length < 10 → QShape (8 :: 1 :: 0x12 :: u) false (0x12 :: u)
  | fields {lw R F T path : List Byte} {m e : Nat} {b : Option Nat} : Varint lw m → lw.length ≤ 10 →
      QFs [] R F b path → Tail T e →
      QShape (8 :: 1 :: 0x12 :: (lw ++ (R ++ T))) (skOfQ b) (0x12 :: (lw ++ (F ++ T)))

theorem head1_ok (lw : List Byte) :
    ((8 :: 1 :: 0x12 :: lw : List Byte).take 2 == [8, 1] && PublicReceive.get (8 :: 1 :: 0x12 :: lw) 2 == 0x12) = true := by
  rfl

/-- **`scan` on the revealed bytes of a request with complete fields**: the unfinished field's rounds
give its answer, the complete fields having been walked (body and path noted). -/
theorem scan_qfields {lw R F T path : List Byte} {m : Nat} {b : Option Nat} (hw : Varint lw m)
    (hwl : lw.length ≤ 10) (hr : QFs [] R F b path) :
    ∃ f k, f.body = b ∧ f.path = path ∧ scan (8 :: 1 :: 0x12 :: (lw ++ (R ++ T))) (skOfQ b) =
      QAns (8 :: 1 :: 0x12 :: (lw ++ (R ++ T))) (skOfQ b) f (3 + lw.length + R.length) k := by
  generalize hH : (8 :: 1 :: 0x12 :: (lw ++ (R ++ T)) : List Byte) = H
  have hlen : H.length = 3 + lw.length + R.length + T.length := by rw [← hH]; simp; omega
  have hd3 : H.drop 3 = lw ++ (R ++ T) := by rw [← hH]; rfl
  have hvar := varintAt_varint (rest := R ++ T) hw hwl hd3
  have hdp : H.drop (3 + lw.length) = R ++ T := by rw [← List.drop_drop, hd3, List.drop_left]
  obtain ⟨n, f', hn, hreach, hbody, hpath⟩ := qfs_scan hr H T (3 + lw.length) (skOfQ b) {} hdp rfl (Or.inl rfl)
    (fun m e e2 => by subst e; simp [skOfQ, e2])
  refine ⟨f', H.length - 1 - n, by rw [hbody]; cases b <;> rfl, hpath, ?_⟩
  rw [scan_eq, if_neg (by omega), if_pos (by rw [← hH]; exact head1_ok _), hvar]
  dsimp only
  rw [show H.length + 1 = n + (H.length - 1 - n + 1 + 1) by omega, loopG_reaches n _ _ _ hreach]

theorem qshape_fields_eq {lw R F T path : List Byte} {m e : Nat} {b : Option Nat} (hw : Varint lw m)
    (hwl : lw.length ≤ 10) (hr : QFs [] R F b path) (ht : Tail T e) {H P : List Byte} {bs : Bool}
    (hH : H = 8 :: 1 :: 0x12 :: (lw ++ (R ++ T))) (hP : P = 0x12 :: (lw ++ (F ++ T))) (hbs : bs = skOfQ b) :
    QShape H bs P := by
  subst hH hP hbs; exact QShape.fields hw hwl hr ht

theorem scan_kind_bad {y : Byte} (hy : y ≠ 0x12) (bs : Bool) : (scan ([8, 1] ++ [y]) bs).1 = .malformed := by
  have hb : ((([8, 1] ++ [y]) : List Byte).take 2 == [8, 1] && PublicReceive.get ([8, 1] ++ [y]) 2 == 0x12) = false := by
    simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, beq_self_eq_true,
      Bool.true_and]
    exact beq_eq_false_iff_ne.mpr hy
  rw [scan_eq, if_neg (by simp), if_neg (by rw [hb]; simp)]

/-- **Every byte the scanner accepts keeps the shape.** -/
theorem qshape_more {H : List Byte} {bs : Bool} {P : List Byte} (h : QShape H bs P) (y : Byte)
    (hm : (scan (H ++ [y]) bs).1 = .more) : QShape (H ++ [y]) bs (P ++ [y]) := by
  cases h with
  | kind =>
    by_cases hy : y = 0x12
    · subst hy; exact QShape.wrapper (u := []) (by simp) (by simp)
    · rw [scan_kind_bad hy] at hm; cases hm
  | wrapper hu hl =>
    rename_i u
    have hH : (8 :: 1 :: 0x12 :: u : List Byte) ++ [y] = 8 :: 1 :: 0x12 :: (u ++ [y]) := by simp
    rw [hH] at hm ⊢
    have hd3 : (8 :: 1 :: 0x12 :: (u ++ [y]) : List Byte).drop 3 = u ++ [y] := rfl
    by_cases hy : y.toNat < 128
    · obtain ⟨n, hv⟩ := varint_snoc u hu y hy
      have hvl : (u ++ [y]).length ≤ 10 := by simp; omega
      have e := QShape.fields (R := []) (F := []) (T := []) hv hvl (QFs.nil (path := [])) Tail.empty
      simpa [skOfQ] using e
    · by_cases h10 : u.length + 1 < 10
      · have := QShape.wrapper (all_snoc hu (by omega)) (show (u ++ [y]).length < 10 by simp; omega)
        simpa using this
      · exfalso
        have hTL := tooLong_of_drop hd3 (by simp; omega) (by
          rw [List.take_of_length_le (by simp; omega)]; exact all_snoc hu (by omega))
        rw [scan_eq, if_neg (by simp), if_pos (head1_ok _), varintAt_tooLong hTL] at hm
        dsimp only at hm
        rw [if_pos hTL] at hm
        cases hm
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
    rw [hs] at hm
    rcases hstep.1 hm with ⟨e', ht'⟩ | ⟨bf, path', hqf, hbb, hsk⟩
    · exact qshape_fields_eq hw hwl hr ht' (by simp) (by simp) rfl
    · exact qshape_fields_eq (T := []) hw hwl (qfs_snoc hr hqf hbb) Tail.empty (by simp) (by simp) hsk.symm

/-- **A body the scanner asks to pass over keeps the shape**, whatever its `n` bytes, provided the
reference finds no `error` in them (`requestBody_noErr`: always, unless the path is `/api/v1/message`). -/
theorem qshape_skip {H : List Byte} {bs : Bool} {P : List Byte} (h : QShape H bs P) (y : Byte) {n : Nat}
    (hm : (scan (H ++ [y]) bs).1 = .skip n) (B : List Byte) (hB : B.length = n)
    (hne : NoErr (requestBody (scan (H ++ [y]) bs).2.path B)) : QShape (H ++ [y]) true (P ++ y :: B) := by
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
    rw [hH] at hm hne ⊢
    obtain ⟨f, k, hfb, hfp, hs⟩ := scan_qfields (T := T ++ [y]) hw hwl hr
    have hd : (8 :: 1 :: 0x12 :: (lw ++ (R ++ (T ++ [y]))) : List Byte).drop (3 + lw.length + R.length) = T ++ [y] := by
      rw [show 3 + lw.length + R.length = 3 + (lw.length + R.length) by omega, ← List.drop_drop]
      simp
    have hstep := q_tail_step ht hd hfp hfb k
    rw [hs] at hm hne
    obtain ⟨hn, hb, hpath, v, hT, hv, hvl⟩ := hstep.2 n hm
    subst hb
    rw [hpath] at hne
    have hv' : Varint v B.length := by rw [hB]; exact hv
    have hqf : QF path (0x1a :: v) (0x1a :: (v ++ B)) (some B.length) path := QF.body hv' hvl hne
    refine qshape_fields_eq (T := []) hw hwl (qfs_snoc hr hqf (Or.inl rfl)) Tail.empty (by rw [hT]; simp) ?_ ?_
    · have hP : (0x12 :: (lw ++ (F ++ T)) : List Byte) ++ y :: B = 0x12 :: (lw ++ (F ++ ((T ++ [y]) ++ B))) := by simp
      rw [hP, hT]; simp
    · simp [skOfQ, hB, hn]

/-! ### The runs: `fieldMissing` against the reference -/

/-- Byte `q` of `C` is public. -/
def PubAt (C : List Class) (q : Nat) : Prop := ∃ c, C[q]? = some c ∧ c.secret = false

theorem pubAt_append (A : List Class) {C : List Class} {q : Nat} (h : PubAt C q) : PubAt (A ++ C) (A.length + q) := by
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨c, by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hc, hs⟩

theorem pubAt_cons (x : Class) {C : List Class} {q : Nat} (h : PubAt C q) : PubAt (x :: C) (q + 1) := by
  have := pubAt_append [x] h
  simpa [Nat.add_comm] using this

theorem pubAt_prefix {A C : List Class} {q : Nat} (hq : q < A.length) (h : PubAt A q) : PubAt (A ++ C) q := by
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨c, by rw [List.getElem?_append_left hq]; exact hc, hs⟩

theorem pubAt_fill {α : Type} {k : Class} (hk : k.secret = false) (l : List α) (q : Nat) (h : q < l.length) :
    PubAt (fill k l) q := ⟨k, fill_get k l q h, hk⟩

theorem rq_head (path : List Byte) (y : Byte) (Z : List Byte) : (rqf path (y :: Z))[0]? = some .structure := by
  unfold rqf; rw [List.length_cons, ReceiveStream.request_cons]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- **The reference after the unfinished field**: the run the controller may reveal there (one byte,
or the rest of a verb, path or header) is public. -/
theorem q_tail_run {T : List Byte} {e : Nat} (ht : Tail T e) (Y : List Byte) (hY : Y.length ≤ max 1 (e - T.length))
    (path : List Byte) (i : Nat) (hi : i < Y.length) : PubAt (rqf path (T ++ Y)) (T.length + i) := by
  cases ht with
  | empty =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    have hi0 : i = 0 := by simp at hY; omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    exact ⟨_, rq_head path y Y', rfl⟩
  | @unfinished tag u htag hu hl =>
    have hi0 : i = 0 := by simp at hY; omega
    subst hi0
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hi
      | cons y Y' => exact ⟨y, Y', rfl⟩
    rw [List.cons_append, List.length_cons, show u.length + 1 + 0 = u.length + 1 by omega]
    have hvp : ∀ (nx : Nat → List Byte → List Class), (varintThen (u ++ y :: Y') nx)[u.length]? = some .structure := by
      intro nx
      rcases varint_pos hu hl (y :: Y') nx u.length (Nat.le_refl _) hl (by simp) with ⟨m, -, hm, hlt, -⟩ | h
      · exact hlt hm
      · exact h
    by_cases h20 : tag = 0x20
    · subst h20
      rw [rq_cons_number]
      exact pubAt_cons _ ⟨_, hvp _, rfl⟩
    · have ht4 : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a := by
        rcases htag with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact absurd h h20
      obtain ⟨k, nx, e1, -⟩ := rq_cons_delim ht4 path (u ++ y :: Y')
      rw [e1]
      exact pubAt_cons _ ⟨_, hvp _, rfl⟩
  | @short tag v c count htag hv hvl hc =>
    have ht4 : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a := by
      rcases htag with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    obtain ⟨k, nx, e1, hk⟩ := rq_cons_delim ht4 path (v ++ (c ++ Y))
    have hk' := hk htag
    subst hk'
    simp only [List.length_cons, List.length_append] at hY
    rw [List.cons_append, List.append_assoc, e1, varintThen_varint hv hvl]
    unfold ReceiveStream.delimCont
    rw [if_neg (by simp)]
    rw [show (tag :: (v ++ c)).length + i = ((fill Class.structure v).length + (c.length + i)) + 1 by
      simp [fillL]; omega]
    apply pubAt_cons
    apply pubAt_append
    apply pubAt_prefix (by rw [fillL, List.length_take]; simp; omega)
    exact pubAt_fill rfl _ _ (by rw [List.length_take]; simp; omega)

theorem fieldMissing_fields {lw R F T path : List Byte} {m e : Nat} {b : Option Nat} (hw : Varint lw m)
    (hwl : lw.length ≤ 10) (hr : QFs [] R F b path) (ht : Tail T e) :
    fieldMissing (8 :: 1 :: 0x12 :: (lw ++ (R ++ T))) ≤ e - T.length := by
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
  have := missing_tail (m := H.length - n) (by rw [hdt]; exact ht)
  omega

/-- **The request half of T1 at the message level (every field order, every byte string).** From any
state the controller reaches inside a server request (`QShape`), the run it reveals next
(`max 1 (fieldMissing H)` bytes, whatever they are) is public in the reference's reading of the message
(`ReceiveSpec.message _ false`). -/
theorem qshape_run {H : List Byte} {bs : Bool} {P : List Byte} (h : QShape H bs P) (ob : Bool) (Y : List Byte)
    (hY : Y.length ≤ max 1 (fieldMissing H)) (i : Nat) (hi : i < Y.length) :
    PubAt (ReceiveSpec.message ob false (8 :: 1 :: (P ++ Y))) (2 + P.length + i) := by
  rw [message_kind1]
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
    rw [wrapper_cons]; split
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
    rcases varint_pos hu hl (y :: Y') _ u.length (Nat.le_refl _) hl (by simp) with ⟨m, -, hm, hlt, -⟩ | h
    · exact ⟨_, hlt hm, rfl⟩
    · exact ⟨_, h, rfl⟩
  | fields hw hwl hr ht =>
    rename_i lw R F T path m e b
    have hfm := fieldMissing_fields hw hwl hr ht
    have hP : (0x12 :: (lw ++ (F ++ T)) : List Byte) ++ Y = 0x12 :: (lw ++ (F ++ (T ++ Y))) := by simp
    rw [hP, wrapper_cons, if_pos rfl, varintThen_varint hw hwl]
    obtain ⟨C, eC, hCl, -⟩ := qfs_classes hr (T ++ Y)
    show PubAt (_ :: _ :: _ :: (fill Class.structure lw ++ rqf [] (F ++ (T ++ Y)))) _
    rw [eC]
    rw [show 2 + (0x12 :: (lw ++ (F ++ T)) : List Byte).length + i =
      ((fill Class.structure lw).length + (C.length + (T.length + i))) + 1 + 1 + 1 by simp [fillL, hCl]; omega]
    apply pubAt_cons; apply pubAt_cons; apply pubAt_cons
    apply pubAt_append
    apply pubAt_append
    exact q_tail_run ht Y (by omega) path i hi

/-! ### The controller's steps -/

/-- **The controller inside a server request** whose bytes after the kind so far are `P`, no delivered
envelope being walked: its revealed bytes and flags have the shape `QShape` for `P` followed by whatever
`skip` body bytes are still to be passed over. -/
structure QIn (s : State) (P : List Byte) : Prop where
  message : s.message = [8, 1]
  inner : s.inner = none
  shape : ∀ B : List Byte, B.length = s.skip → QShape s.request s.bodySkipped (P ++ B)

theorem qshape_ne {H : List Byte} {bs : Bool} {P : List Byte} (h : QShape H bs P) : H.isEmpty = false := by
  cases h <;> rfl

theorem messagePath_beq (p : List Byte) :
    (p == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = false ↔
      p ≠ ReceiveSpec.messagePath := by
  rw [beq_eq_false_iff_ne]; rfl

/-- **A revealed request byte keeps the controller inside the request's shape** (the message not ending
at it, no envelope starting at it): the scanner asks for more, or to pass over a body whose path is not
`/api/v1/message` (`skip := n`). (At a `/api/v1/message` body the controller walks the envelope instead:
`payloadByte_request_envelope`.) -/
theorem payloadByte_qIn {s s' : State} {P : List Byte} {y : Byte} {flags : List Byte} {c : Bool}
    (hs : QIn s P) (h0 : s.skip = 0)
    (henv : ∀ n, (scan (s.request ++ [y]) s.bodySkipped).1 = .skip n →
      (scan (s.request ++ [y]) s.bodySkipped).2.path ≠ ReceiveSpec.messagePath)
    (hok : payloadByte s y true false false flags = .ok (s', c)) : QIn s' (P ++ [y]) := by
  have hsh := hs.shape [] (by simp [h0])
  rw [List.append_nil] at hsh
  have hne := qshape_ne hsh
  generalize hq : scan (s.request ++ [y]) s.bodySkipped = q at henv
  obtain ⟨need, f⟩ := q
  cases need with
  | more =>
    obtain ⟨k1, k2, k3⟩ := payloadByte_request_more (f := f) hs.message hs.inner (by rw [hne]; exact hq) hok
    obtain ⟨k4, k5, k6⟩ := k3 rfl
    rw [hne] at k4
    refine ⟨k5, k2, fun B hB => ?_⟩
    rw [k1, h0] at hB
    rw [List.eq_nil_of_length_eq_zero hB, List.append_nil, k4, k6]
    exact qshape_more hsh y (by rw [hq])
  | skip n =>
    have hp := henv n rfl
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := payloadByte_request_skip (f := f) hs.message hs.inner (by rw [hne]; exact hq)
      ((messagePath_beq f.path).mpr hp) hok
    rw [hne] at k6
    refine ⟨k4, k3, fun B hB => ?_⟩
    rw [k6, k5, List.append_assoc, List.singleton_append]
    exact qshape_skip hsh y (by rw [hq]) B (by rw [hB, k1]) (by rw [hq]; exact requestBody_noErr hp B)
  | malformed =>
    exact absurd hok (payloadByte_request_malformed hs.message hs.inner (by rw [hne]; exact hq) s' c)

/-- What `stepSkipped` (one body byte passed over, no envelope being walked) keeps: the request's
revealed bytes and flags; `skip` is one less; or the message ends there (only at the body's last byte). -/
theorem stepSkipped_keeps {s s' : State} (hi : s.inner = none) (h : stepSkipped s = .ok s') :
    s'.skip = s.skip - 1 ∧ s'.inner = none ∧
      ((s'.message = s.message ∧ s'.request = s.request ∧ s'.bodySkipped = s.bodySkipped) ∨
        (s'.message = [] ∧ s.skip - 1 = 0)) := by
  unfold stepSkipped at h
  generalize TlsMpc.TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) = F at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, hi] at h
  by_cases c1 : (s.upgraded && decide (s.skip > 0) && s.message == [8, 1]) = true
  · rw [if_pos c1] at h
    by_cases c2 : (PublicReceive.get F 0 == on && PublicReceive.get F 1 == on) = true
    · rw [if_pos c2] at h
      repeat' (split at h)
      all_goals (try simp only [reduceCtorEq] at h)
      all_goals (try (cases h; simp_all))
    · rw [if_neg c2] at h; cases h
  · rw [if_neg c1] at h; cases h

/-- **A passed-over body byte keeps the controller inside the request's shape**, whatever the byte. -/
theorem stepSkipped_qIn {s s' : State} {P : List Byte} (hs : QIn s P) (hk : 0 < s.skip)
    (hok : stepSkipped s = .ok s') (y : Byte) : s'.message = [8, 1] → QIn s' (P ++ [y]) := by
  obtain ⟨k1, k2, k3⟩ := stepSkipped_keeps hs.inner hok
  intro hm
  refine ⟨hm, k2, fun B hB => ?_⟩
  rcases k3 with ⟨m1, m2, m3⟩ | ⟨m1, -⟩
  · rw [m2, m3, List.append_assoc, List.singleton_append]
    exact hs.shape (y :: B) (by simp; omega)
  · rw [m1] at hm; cases hm

/-- **The request half of T1 at the controller level (every field order, every byte string).** Inside a
server request whose bytes after the kind so far are `P` (`QIn`, kept by `payloadByte_qIn` and
`stepSkipped_qIn`), with nothing to pass over and a data frame's payload next, every byte of the run the
controller reveals (`budget s` bytes, whatever they are) is public in the reference. -/
theorem request_run_safe {s : State} {P : List Byte} (hs : QIn s P) (hk : s.skip = 0) (hu : s.upgraded = true)
    (h0 : (PublicReceive.get s.frame 0 == on) = false) (h2 : (PublicReceive.get s.frame 2 == on) = false)
    (h4 : (PublicReceive.get s.frame 4 == on) = true)
    (hr : (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0)
    (ho : (PublicReceive.get s.frame 7).toNat < 8) (ob : Bool) (Y : List Byte) (hY : Y.length ≤ budget s)
    (i : Nat) (hi : i < Y.length) :
    PubAt (ReceiveSpec.message ob false (8 :: 1 :: (P ++ Y))) (2 + P.length + i) := by
  have hsh := hs.shape [] (by simp [hk])
  rw [List.append_nil] at hsh
  have hb := budget_request s hu h0 h2 h4 hr ho hs.message
  exact qshape_run hsh ob Y (by omega) i hi

end ReceiveRequestScan
