import TlsMpc.Node.Policy.ReceiveSpec

/-!
# T1's reference, byte by byte (proof track P1, item 1)

New file; it changes no definition, imports only `Policy/ReceiveSpec.lean`, and no emitter or
executable imports it. Standard axioms only.

`ReceiveSpec.classifyFrames` is a recursive function of the whole stream: a data frame's payload
bytes get their classes from the whole message read so far (`message openBody complete (msg ++
payload)`, then `drop msg.length`), and whether that message is `complete` depends on whether the
stream holds the whole of its last frame. The controller reads the stream one byte at a time. This
file gives the reference the same shape and proves it is the same function.

## Causality: a byte's class depends only on the bytes before it (and the message's length)

`Causal c f`: `f` classifies a list of bytes; for any `A`, the classes of `A`'s bytes in `f (A ++ B)`
do not depend on `B`, or (`c = true`) depend on `B` only through its length. Proved for every piece
of the reference (`varintThen_causal`, `delimitedThen_causal`, `envelope_causal`, `request_causal`,
`response_causal`, `wrapper_causal`, `message_causal`): with `complete = false` the classes of a
message's bytes are those of its prefix (`message_prefix`); with `complete = true` they depend also
on how many bytes follow (a length running past the end makes what follows it `error`). The
recursion's `fuel` never matters once it exceeds the bytes (`envelope_fuel`, `request_fuel`,
`response_fuel`). Each classifier keeps lengths (`*_len`).

## The byte-by-byte reader (`Stream`)

`Stream.step openBody st b left` reads one byte `b` of the frames, `left` being how many bytes of the
stream follow it, and returns its class and the next state; `Stream.run` folds it over a stream. The
state is the frame layer's (`Phase`: which header byte is next, or how much payload is left) and the
message's payload so far. A payload byte of a data frame gets the class of its last position in
`message openBody complete (msg ++ [b] ++ pad)`, `pad` being zeros standing for the rest of the
frame when the message is `complete` (none otherwise: `Stream.payloadClass`). `left` is used once
per frame, at its last header byte: `complete` is FIN and "the stream holds the whole frame"; it
changes a class only when the stream ends inside the message's last frame.

`Stream.classes` adds `failClosed`'s sticky error (`Stream.stepF`, the `bad` flag).

**`classifyFrames_stream`**: `ReceiveSpec.classifyFrames openBody bytes = Stream.classes openBody
bytes` for every byte string. **`classify_stream`**: the same for `ReceiveSpec.classify`, with the
upgrade response's head read byte by byte too (`Head`, the CR LF CR LF matcher).
-/

namespace ReceiveStream

open ReceiveSpec

/-! ### `fill` -/

theorem fill_length {α : Type} (c : Class) (l : List α) : (fill c l).length = l.length := by simp [fill]

theorem fill_take {α : Type} (c : Class) (l : List α) (k : Nat) : (fill c l).take k = fill c (l.take k) := by
  simp [fill, List.map_take]

theorem fill_append {α : Type} (c : Class) (l m : List α) : fill c (l ++ m) = fill c l ++ fill c m := by
  simp [fill]

/-! ### Varints at the head of an appended list -/

/-- `varintEnd`'s answer one byte further on. -/
def bump : VarintEnd → VarintEnd
  | .done n => .done (n + 1)
  | o => o

theorem varintEnd_cons (a : Nat) (b : Byte) (rest : List Byte) :
    varintEnd (a + 1) (b :: rest) = if b.toNat < 128 then .done 1 else bump (varintEnd a rest) := by
  simp only [varintEnd]
  cases varintEnd a rest <;> rfl

theorem varintEnd_done_le : ∀ (a : Nat) (E : List Byte) (n : Nat), varintEnd a E = .done n →
    1 ≤ n ∧ n ≤ E.length ∧ n ≤ a
  | 0, _, _, h => by simp [varintEnd] at h
  | _ + 1, [], _, h => by simp [varintEnd] at h
  | a + 1, b :: rest, n, h => by
    rw [varintEnd_cons] at h
    split at h
    · cases h; simp
    · cases hv : varintEnd a rest with
      | done m =>
        rw [hv] at h; cases h
        have := varintEnd_done_le a rest m hv
        simp; omega
      | short => rw [hv] at h; cases h
      | tooLong => rw [hv] at h; cases h

theorem varintEnd_short_lt : ∀ (a : Nat) (E : List Byte), varintEnd a E = .short → E.length < a
  | 0, _, h => by simp [varintEnd] at h
  | _ + 1, [], _ => by simp
  | a + 1, b :: rest, h => by
    rw [varintEnd_cons] at h
    split at h
    · cases h
    · cases hv : varintEnd a rest with
      | done m => rw [hv] at h; cases h
      | short => have := varintEnd_short_lt a rest hv; simp; omega
      | tooLong => rw [hv] at h; cases h

theorem varintEnd_tooLong_le : ∀ (a : Nat) (E : List Byte), varintEnd a E = .tooLong → a ≤ E.length
  | 0, _, _ => by simp
  | _ + 1, [], h => by simp [varintEnd] at h
  | a + 1, b :: rest, h => by
    rw [varintEnd_cons] at h
    split at h
    · cases h
    · cases hv : varintEnd a rest with
      | done m => rw [hv] at h; cases h
      | short => rw [hv] at h; cases h
      | tooLong => have := varintEnd_tooLong_le a rest hv; simp; omega

theorem varintEnd_append_done : ∀ (a : Nat) (A B : List Byte) (n : Nat), varintEnd a A = .done n →
    varintEnd a (A ++ B) = .done n
  | 0, _, _, _, h => by simp [varintEnd] at h
  | _ + 1, [], _, _, h => by simp [varintEnd] at h
  | a + 1, b :: rest, B, n, h => by
    rw [varintEnd_cons] at h
    rw [List.cons_append, varintEnd_cons]
    split at h
    · rw [if_pos (by assumption)]; exact h
    · rw [if_neg (by assumption)]
      cases hv : varintEnd a rest with
      | done m => rw [hv] at h; cases h; rw [varintEnd_append_done a rest B m hv]; rfl
      | short => rw [hv] at h; cases h
      | tooLong => rw [hv] at h; cases h

theorem varintEnd_append_tooLong : ∀ (a : Nat) (A B : List Byte), varintEnd a A = .tooLong →
    varintEnd a (A ++ B) = .tooLong
  | 0, _, _, _ => by simp [varintEnd]
  | _ + 1, [], _, h => by simp [varintEnd] at h
  | a + 1, b :: rest, B, h => by
    rw [varintEnd_cons] at h
    rw [List.cons_append, varintEnd_cons]
    split at h
    · cases h
    · rw [if_neg (by assumption)]
      cases hv : varintEnd a rest with
      | done m => rw [hv] at h; cases h
      | short => rw [hv] at h; cases h
      | tooLong => rw [varintEnd_append_tooLong a rest B hv]; rfl

theorem varintEnd_append_short : ∀ (a : Nat) (A B : List Byte) (n : Nat), varintEnd a A = .short →
    varintEnd a (A ++ B) = .done n → A.length < n
  | 0, _, _, _, h, _ => by simp [varintEnd] at h
  | _ + 1, [], _, n, _, h2 => (varintEnd_done_le _ _ n h2).1
  | a + 1, b :: rest, B, n, h, h2 => by
    rw [varintEnd_cons] at h
    rw [List.cons_append, varintEnd_cons] at h2
    split at h
    · cases h
    · rw [if_neg (by assumption)] at h2
      cases hv : varintEnd a rest with
      | done m => rw [hv] at h; cases h
      | tooLong => rw [hv] at h; cases h
      | short =>
        cases hv2 : varintEnd a (rest ++ B) with
        | done m =>
          rw [hv2] at h2; cases h2
          have := varintEnd_append_short a rest B m hv hv2
          simp; omega
        | short => rw [hv2] at h2; cases h2
        | tooLong => rw [hv2] at h2; cases h2

/-! ### Lengths and causality -/

/-- `f` gives one class per byte. -/
def LenP (f : List Byte → List Class) : Prop := ∀ X, (f X).length = X.length

/-- **The classes of `A`'s bytes do not depend on what follows `A`** (with `c = true`: only on how
many bytes follow). -/
def Causal (c : Bool) (f : List Byte → List Class) : Prop :=
  ∀ A B B' : List Byte, (c = true → B.length = B'.length) →
    (f (A ++ B)).take A.length = (f (A ++ B')).take A.length

theorem causal_of_false {c : Bool} {f : List Byte → List Class} (h : Causal false f) : Causal c f :=
  fun A B B' _ => h A B B' (fun e => by cases e)

theorem fill_len (k : Class) : LenP (fill k) := fun X => fill_length k X

theorem fill_causal (c : Bool) (k : Class) : Causal c (fill k) := by
  intro A B B' _
  rw [fill_take, fill_take, List.take_left' rfl, List.take_left' rfl]

theorem varintThen_len {next : Nat → List Byte → List Class} (h : ∀ v, LenP (next v)) :
    LenP (fun X => varintThen X next) := by
  intro X
  simp only [varintThen]
  cases hv : varintEnd 10 X with
  | done n =>
    have := varintEnd_done_le 10 X n hv
    rw [List.length_append, fill_length, List.length_take, h, List.length_drop]
    omega
  | short => simp only [fill_length]
  | tooLong => simp only [List.length_append, fill_length, List.length_take, List.length_drop]; omega

/-- With a varint unfinished in `A`, all of `A` is `structure`. -/
theorem varintThen_short_take {A : List Byte} (hA : varintEnd 10 A = .short) (B : List Byte)
    (next : Nat → List Byte → List Class) :
    (varintThen (A ++ B) next).take A.length = fill .structure A := by
  have hlt := varintEnd_short_lt 10 A hA
  simp only [varintThen]
  cases hv : varintEnd 10 (A ++ B) with
  | done n =>
    have hn := varintEnd_append_short 10 A B n hA hv
    have hle := varintEnd_done_le 10 (A ++ B) n hv
    rw [List.take_append_of_le_length (by rw [fill_length, List.length_take]; omega), fill_take,
      List.take_take, Nat.min_eq_left (by omega), List.take_left' rfl]
  | short => rw [fill_take, List.take_left' rfl]
  | tooLong =>
    rw [List.take_append_of_le_length (by rw [fill_length, List.length_take]; simp; omega), fill_take,
      List.take_take, Nat.min_eq_left (by omega), List.take_left' rfl]

theorem varintThen_causal {c : Bool} {next : Nat → List Byte → List Class} (h : ∀ v, Causal c (next v)) :
    Causal c (fun X => varintThen X next) := by
  intro A B B' hB
  simp only
  cases hA : varintEnd 10 A with
  | done n =>
    have hle := varintEnd_done_le 10 A n hA
    simp only [varintThen, varintEnd_append_done 10 A B n hA, varintEnd_append_done 10 A B' n hA,
      List.take_append_of_le_length hle.2.1, List.drop_append_of_le_length hle.2.1, List.take_append,
      fill_length, List.length_take, Nat.min_eq_left hle.2.1]
    congr 1
    have := h (varintValue (A.take n)) (A.drop n) B B' hB
    simpa only [List.length_drop] using this
  | short => rw [varintThen_short_take hA, varintThen_short_take hA]
  | tooLong =>
    have hle := varintEnd_tooLong_le 10 A hA
    simp only [varintThen, varintEnd_append_tooLong 10 A B hA, varintEnd_append_tooLong 10 A B' hA,
      List.take_append_of_le_length hle, List.drop_append_of_le_length hle, List.take_append,
      fill_length, List.length_take, fill_append]
    have : A.length - min 10 A.length - (List.drop 10 A).length = 0 := by simp; omega
    rw [this]
    simp

/-- `next` is called only on lists shorter than the varint's input. -/
theorem varintThen_congr {X : List Byte} {next next' : Nat → List Byte → List Class}
    (h : ∀ v r, r.length < X.length → next v r = next' v r) : varintThen X next = varintThen X next' := by
  simp only [varintThen]
  cases hv : varintEnd 10 X with
  | done n =>
    have := varintEnd_done_le 10 X n hv
    simp only
    rw [h _ _ (by simp; omega)]
  | short => rfl
  | tooLong => rfl

/-! ### Length-delimited fields -/

/-- What `delimitedThen` does once the length is read. -/
def delimCont (c : Bool) (content : List Byte → List Class) (next : List Byte → List Byte → List Class)
    (length : Nat) (after : List Byte) : List Class :=
  if c = true ∧ after.length < length then fill .error after
  else content (after.take length) ++ next (after.take length) (after.drop length)

theorem delimitedThen_eq (c : Bool) (X : List Byte) (content : List Byte → List Class)
    (next : List Byte → List Byte → List Class) :
    delimitedThen c X content next = varintThen X (delimCont c content next) := rfl

theorem delimCont_len {c : Bool} {content : List Byte → List Class} {next : List Byte → List Byte → List Class}
    (hc : LenP content) (hn : ∀ v, LenP (next v)) (L : Nat) : LenP (delimCont c content next L) := by
  intro X
  unfold delimCont
  split
  · exact fill_length _ _
  · rw [List.length_append, hc, hn, List.length_take, List.length_drop]; omega

theorem delimitedThen_len {c : Bool} {content : List Byte → List Class} {next : List Byte → List Byte → List Class}
    (hc : LenP content) (hn : ∀ v, LenP (next v)) : LenP (fun X => delimitedThen c X content next) :=
  varintThen_len (delimCont_len hc hn)

theorem delimCont_causal {c : Bool} {content : List Byte → List Class} {next : List Byte → List Byte → List Class}
    (hc : LenP content) (hcc : Causal c content) (hn : ∀ v, Causal c (next v)) (L : Nat) :
    Causal c (delimCont c content next L) := by
  intro A B B' hB
  unfold delimCont
  have same : (c = true ∧ (A ++ B).length < L) ↔ (c = true ∧ (A ++ B').length < L) := by
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; simp only [List.length_append] at h2 ⊢; rw [← hB h1]; exact h2
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; simp only [List.length_append] at h2 ⊢; rw [hB h1]; exact h2
  by_cases e : c = true ∧ (A ++ B).length < L
  · rw [if_pos e, if_pos (same.mp e)]
    exact fill_causal c .error A B B' hB
  · rw [if_neg e, if_neg (fun e' => e (same.mpr e'))]
    by_cases hL : L ≤ A.length
    · simp only [List.take_append_of_le_length hL, List.drop_append_of_le_length hL, List.take_append]
      rw [hc (A.take L), List.length_take, Nat.min_eq_left hL]
      congr 1
      have := hn (A.take L) (A.drop L) B B' hB
      simpa only [List.length_drop] using this
    · have hA : ∀ Z : List Byte, (A ++ Z).take L = A ++ Z.take (L - A.length) := by
        intro Z; rw [List.take_append, List.take_of_length_le (by omega)]
      rw [hA B, hA B', List.take_append_of_le_length (by rw [hc]; simp),
        List.take_append_of_le_length (by rw [hc]; simp)]
      apply hcc
      intro e
      simp only [List.length_take, hB e]

theorem delimitedThen_causal {c : Bool} {content : List Byte → List Class} {next : List Byte → List Byte → List Class}
    (hc : LenP content) (hcc : Causal c content) (hn : ∀ v, Causal c (next v)) :
    Causal c (fun X => delimitedThen c X content next) :=
  varintThen_causal (delimCont_causal hc hcc hn)

theorem delimitedThen_congr {c : Bool} {X : List Byte} {content : List Byte → List Class}
    {next next' : List Byte → List Byte → List Class}
    (h : ∀ v r, r.length < X.length → next v r = next' v r) :
    delimitedThen c X content next = delimitedThen c X content next' := by
  rw [delimitedThen_eq, delimitedThen_eq]
  apply varintThen_congr
  intro L after hl
  unfold delimCont
  split
  · rfl
  · rw [h _ _ (by simp; omega)]

/-- A fixed-width payload, then `g`. -/
theorem fixed_len {k : Class} {m : Nat} {g : List Byte → List Class} (hg : LenP g) :
    LenP (fun after => fill k (after.take m) ++ g (after.drop m)) := by
  intro X; rw [List.length_append, fill_length, List.length_take, hg, List.length_drop]; omega

theorem fixed_causal {c : Bool} {k : Class} {m : Nat} {g : List Byte → List Class} (hg : Causal c g) :
    Causal c (fun after => fill k (after.take m) ++ g (after.drop m)) := by
  intro A B B' hB
  simp only
  by_cases hm : m ≤ A.length
  · simp only [List.take_append_of_le_length hm, List.drop_append_of_le_length hm, List.take_append,
      fill_length, List.length_take, Nat.min_eq_left hm]
    congr 1
    have := hg (A.drop m) B B' hB
    simpa only [List.length_drop] using this
  · have e : ∀ Z : List Byte, (fill k ((A ++ Z).take m) ++ g ((A ++ Z).drop m)).take A.length = fill k A := by
      intro Z
      rw [List.take_append_of_le_length (by rw [fill_length, List.length_take]; simp; omega), fill_take,
        List.take_take, Nat.min_eq_left (by omega), List.take_left' rfl]
    rw [e B, e B']

/-! ### Envelopes -/

/-- An envelope field after its key. -/
def envNext (fuel key : Nat) (after : List Byte) : List Class :=
  match key % 8 with
  | 0 => varintThen after fun _ rest => envelope fuel rest
  | 1 => fill .envelope (after.take 8) ++ envelope fuel (after.drop 8)
  | 5 => fill .envelope (after.take 4) ++ envelope fuel (after.drop 4)
  | 2 => delimitedThen false after (fill .envelope) fun _ rest => envelope fuel rest
  | _ => fill .error after

theorem envelope_cons (fuel : Nat) (e : Byte) (es : List Byte) :
    envelope (fuel + 1) (e :: es) = varintThen (e :: es) (envNext fuel) := rfl

theorem envelope_len : ∀ fuel, LenP (envelope fuel)
  | 0 => fun X => fill_length _ X
  | fuel + 1 => by
    intro X
    cases X with
    | nil => rfl
    | cons e es =>
      rw [envelope_cons]
      apply varintThen_len
      intro key after
      unfold envNext
      split
      · exact varintThen_len (fun _ => envelope_len fuel) after
      · exact fixed_len (envelope_len fuel) after
      · exact fixed_len (envelope_len fuel) after
      · exact delimitedThen_len (fill_len _) (fun _ => envelope_len fuel) after
      · exact fill_length _ _

theorem envelope_causal : ∀ fuel, Causal false (envelope fuel)
  | 0 => fill_causal false .error
  | fuel + 1 => by
    intro A B B' hB
    cases A with
    | nil => rfl
    | cons a A' =>
      simp only [List.cons_append, envelope_cons]
      have hv : Causal false (fun X => varintThen X (envNext fuel)) := by
        apply varintThen_causal
        intro key
        intro A B B' hB
        unfold envNext
        split
        · exact varintThen_causal (fun _ => envelope_causal fuel) A B B' hB
        · exact fixed_causal (envelope_causal fuel) A B B' hB
        · exact fixed_causal (envelope_causal fuel) A B B' hB
        · exact delimitedThen_causal (fill_len _) (fill_causal _ _) (fun _ => envelope_causal fuel) A B B' hB
        · exact fill_causal false .error A B B' hB
      have := hv (a :: A') B B' hB
      simpa only [List.cons_append] using this

theorem envelope_fuel : ∀ f1 f2 (X : List Byte), X.length < f1 → X.length < f2 → envelope f1 X = envelope f2 X
  | 0, _, _, h, _ => by omega
  | _ + 1, 0, _, _, h => by omega
  | f1 + 1, f2 + 1, X, h1, h2 => by
    cases X with
    | nil => rfl
    | cons e es =>
      rw [envelope_cons, envelope_cons]
      apply varintThen_congr
      intro key after hl
      simp only [List.length_cons] at h1 h2 hl
      unfold envNext
      split
      · apply varintThen_congr
        intro _ r hr
        exact envelope_fuel f1 f2 r (by omega) (by omega)
      · rw [envelope_fuel f1 f2 _ (by simp; omega) (by simp; omega)]
      · rw [envelope_fuel f1 f2 _ (by simp; omega) (by simp; omega)]
      · apply delimitedThen_congr
        intro _ r hr
        exact envelope_fuel f1 f2 r (by omega) (by omega)
      · rfl

/-- The classifier of a request's body, as `requestBody` runs it, with any fuel above the length. -/
theorem requestBody_len (path : List Byte) : LenP (requestBody path) := by
  intro X; unfold requestBody; split
  · exact envelope_len _ X
  · exact fill_length _ _

theorem requestBody_causal (path : List Byte) : Causal false (requestBody path) := by
  intro A B B' hB
  unfold requestBody
  split
  · have N := A.length + B.length + B'.length + 1
    rw [envelope_fuel _ (A.length + B.length + B'.length + 1) _ (by simp) (by simp; omega),
      envelope_fuel _ (A.length + B.length + B'.length + 1) (A ++ B') (by simp) (by simp; omega)]
    exact envelope_causal _ A B B' hB
  · exact fill_causal false .body A B B' hB

/-! ### Requests and responses -/

theorem request_cons (c : Bool) (fuel : Nat) (path : List Byte) (key : Byte) (rest : List Byte) :
    request c (fuel + 1) path (key :: rest) =
      if key = 0x20 then .structure :: varintThen rest fun _ after => request c fuel path after
      else if key = 0x0a ∨ key = 0x12 ∨ key = 0x2a then
        .structure :: delimitedThen c rest (fill .text) fun content after =>
          request c fuel (if key = 0x12 then content else path) after
      else if key = 0x1a then
        .structure :: delimitedThen c rest (requestBody path) fun _ after => request c fuel path after
      else .structure :: fill .error rest := rfl

theorem request_len (c : Bool) : ∀ fuel path, LenP (request c fuel path)
  | 0, _ => fun X => fill_length _ X
  | fuel + 1, path => by
    intro X
    cases X with
    | nil => rfl
    | cons key rest =>
      rw [request_cons]
      split
      · simp only [List.length_cons]; rw [varintThen_len (fun _ => request_len c fuel path) rest]
      · split
        · simp only [List.length_cons]
          rw [delimitedThen_len (fill_len _) (fun v => request_len c fuel _) rest]
        · split
          · simp only [List.length_cons]
            rw [delimitedThen_len (requestBody_len _) (fun _ => request_len c fuel path) rest]
          · simp [fill_length]

/-- Peel a key off both sides of a `Causal` goal. -/
theorem causal_cons {c : Bool} {f : List Byte → List Class} (h : Causal c f) (k : Class)
    (_key : Byte) (A B B' : List Byte) (hB : c = true → B.length = B'.length) :
    (k :: f (A ++ B)).take (A.length + 1) = (k :: f (A ++ B')).take (A.length + 1) := by
  simp only [List.take_succ_cons, h A B B' hB]

theorem request_causal (c : Bool) : ∀ fuel path, Causal c (request c fuel path)
  | 0, _ => fill_causal c .error
  | fuel + 1, path => by
    intro A B B' hB
    cases A with
    | nil => rfl
    | cons key A' =>
      simp only [List.cons_append, request_cons, List.length_cons]
      split
      · exact causal_cons (varintThen_causal (fun _ => request_causal c fuel path)) _ key A' B B' hB
      · split
        · exact causal_cons (delimitedThen_causal (fill_len _) (fill_causal _ _)
            (fun v => request_causal c fuel _)) _ key A' B B' hB
        · split
          · exact causal_cons (delimitedThen_causal (requestBody_len _) (causal_of_false (requestBody_causal _))
              (fun v => request_causal c fuel _)) _ key A' B B' hB
          · exact causal_cons (fill_causal c .error) _ key A' B B' hB

theorem request_fuel (c : Bool) : ∀ f1 f2 path (X : List Byte), X.length < f1 → X.length < f2 →
    request c f1 path X = request c f2 path X
  | 0, _, _, _, h, _ => by omega
  | _ + 1, 0, _, _, _, h => by omega
  | f1 + 1, f2 + 1, path, X, h1, h2 => by
    cases X with
    | nil => rfl
    | cons key rest =>
      simp only [List.length_cons] at h1 h2
      rw [request_cons, request_cons]
      split
      · congr 1
        apply varintThen_congr
        intro _ r hr
        exact request_fuel c f1 f2 path r (by omega) (by omega)
      · split
        · congr 1
          apply delimitedThen_congr
          intro _ r hr
          exact request_fuel c f1 f2 _ r (by omega) (by omega)
        · split
          · congr 1
            apply delimitedThen_congr
            intro _ r hr
            exact request_fuel c f1 f2 path r (by omega) (by omega)
          · rfl

theorem response_cons (ob c : Bool) (fuel : Nat) (key : Byte) (rest : List Byte) :
    response ob c (fuel + 1) (key :: rest) =
      if key = 0x08 ∨ key = 0x10 then
        .structure :: varintThen rest fun _ after => response ob c fuel after
      else if key = 0x1a ∨ key = 0x2a then
        .structure :: delimitedThen c rest (fill .text) fun _ after => response ob c fuel after
      else if key = 0x22 then
        .structure :: delimitedThen c rest (fill (if ob then .text else .body)) fun _ after =>
          response ob c fuel after
      else .structure :: fill .error rest := rfl

theorem response_len (ob c : Bool) : ∀ fuel, LenP (response ob c fuel)
  | 0 => fun X => fill_length _ X
  | fuel + 1 => by
    intro X
    cases X with
    | nil => rfl
    | cons key rest =>
      rw [response_cons]
      split
      · simp only [List.length_cons]; rw [varintThen_len (fun _ => response_len ob c fuel) rest]
      · split
        · simp only [List.length_cons]
          rw [delimitedThen_len (fill_len _) (fun v => response_len ob c fuel) rest]
        · split
          · simp only [List.length_cons]
            rw [delimitedThen_len (fill_len _) (fun _ => response_len ob c fuel) rest]
          · simp [fill_length]

theorem response_causal (ob c : Bool) : ∀ fuel, Causal c (response ob c fuel)
  | 0 => fill_causal c .error
  | fuel + 1 => by
    intro A B B' hB
    cases A with
    | nil => rfl
    | cons key A' =>
      simp only [List.cons_append, response_cons, List.length_cons]
      split
      · exact causal_cons (varintThen_causal (fun _ => response_causal ob c fuel)) _ key A' B B' hB
      · split
        · exact causal_cons (delimitedThen_causal (fill_len _) (fill_causal _ _)
            (fun v => response_causal ob c fuel)) _ key A' B B' hB
        · split
          · exact causal_cons (delimitedThen_causal (fill_len _) (fill_causal _ _)
              (fun v => response_causal ob c fuel)) _ key A' B B' hB
          · exact causal_cons (fill_causal c .error) _ key A' B B' hB

theorem response_fuel (ob c : Bool) : ∀ f1 f2 (X : List Byte), X.length < f1 → X.length < f2 →
    response ob c f1 X = response ob c f2 X
  | 0, _, _, h, _ => by omega
  | _ + 1, 0, _, _, h => by omega
  | f1 + 1, f2 + 1, X, h1, h2 => by
    cases X with
    | nil => rfl
    | cons key rest =>
      simp only [List.length_cons] at h1 h2
      rw [response_cons, response_cons]
      split
      · congr 1
        apply varintThen_congr
        intro _ r hr
        exact response_fuel ob c f1 f2 r (by omega) (by omega)
      · split
        · congr 1
          apply delimitedThen_congr
          intro _ r hr
          exact response_fuel ob c f1 f2 r (by omega) (by omega)
        · split
          · congr 1
            apply delimitedThen_congr
            intro _ r hr
            exact response_fuel ob c f1 f2 r (by omega) (by omega)
          · rfl

/-! ### Messages -/

/-- A request's fields as `message` reads them. -/
def requestFields (c : Bool) (fields : List Byte) : List Class := request c (fields.length + 1) [] fields

/-- A response's fields as `message` reads them. -/
def responseFields (ob c : Bool) (fields : List Byte) : List Class := response ob c (fields.length + 1) fields

theorem requestFields_len (c : Bool) : LenP (requestFields c) := fun X => request_len c _ _ X

theorem responseFields_len (ob c : Bool) : LenP (responseFields ob c) := fun X => response_len ob c _ X

theorem requestFields_causal (c : Bool) : Causal c (requestFields c) := by
  intro A B B' hB
  unfold requestFields
  rw [request_fuel c _ (A.length + B.length + B'.length + 1) [] _ (by simp) (by simp; omega),
    request_fuel c _ (A.length + B.length + B'.length + 1) [] (A ++ B') (by simp) (by simp; omega)]
  exact request_causal c _ [] A B B' hB

theorem responseFields_causal (ob c : Bool) : Causal c (responseFields ob c) := by
  intro A B B' hB
  unfold responseFields
  rw [response_fuel ob c _ (A.length + B.length + B'.length + 1) _ (by simp) (by simp; omega),
    response_fuel ob c _ (A.length + B.length + B'.length + 1) (A ++ B') (by simp) (by simp; omega)]
  exact response_causal ob c _ A B B' hB

theorem wrapper_len (key : Byte) {fields : List Byte → List Class} (hf : LenP fields) :
    LenP (wrapper key fields) := by
  intro X
  cases X with
  | nil => rfl
  | cons k rest =>
    simp only [wrapper]
    split
    · simp only [List.length_cons]; rw [varintThen_len (fun _ => hf) rest]
    · simp [fill_length]

theorem wrapper_causal (c : Bool) (key : Byte) {fields : List Byte → List Class} (hf : Causal c fields) :
    Causal c (wrapper key fields) := by
  intro A B B' hB
  cases A with
  | nil => rfl
  | cons k A' =>
    simp only [List.cons_append, wrapper, List.length_cons]
    split
    · exact causal_cons (varintThen_causal (fun _ => hf)) _ k A' B B' hB
    · exact causal_cons (fill_causal c .error) _ k A' B B' hB

theorem message_eq (ob c : Bool) (a b : Byte) (rest : List Byte) :
    message ob c (a :: b :: rest) =
      if a = 8 ∧ b = 1 then .kind :: .kind :: wrapper 0x12 (requestFields c) rest
      else if a = 8 ∧ b = 2 then .kind :: .kind :: wrapper 0x1a (responseFields ob c) rest
      else .kind :: .kind :: fill .unknown rest := rfl

theorem message_short (ob c : Bool) (X : List Byte) (h : X.length < 2) : message ob c X = fill .kind X := by
  match X, h with
  | [], _ => rfl
  | [_], _ => rfl

theorem message_len (ob c : Bool) : LenP (message ob c) := by
  intro X
  match X with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    rw [message_eq]
    split
    · simp only [List.length_cons]; rw [wrapper_len _ (requestFields_len c) rest]
    · split
      · simp only [List.length_cons]; rw [wrapper_len _ (responseFields_len ob c) rest]
      · simp [fill_length]

theorem message_take1 (ob c : Bool) (a : Byte) (B : List Byte) : (message ob c (a :: B)).take 1 = [.kind] := by
  match B with
  | [] => rfl
  | b :: rest =>
    rw [message_eq]
    split
    · rfl
    · split <;> rfl

theorem message_causal (ob c : Bool) : Causal c (message ob c) := by
  intro A B B' hB
  match A with
  | [] => rfl
  | [a] => simp only [List.cons_append, List.nil_append, List.length_singleton, message_take1]
  | a :: b :: A' =>
    simp only [List.cons_append, message_eq, List.length_cons]
    split
    · simp only [List.take_succ_cons, wrapper_causal c _ (requestFields_causal c) A' B B' hB]
    · split
      · simp only [List.take_succ_cons, wrapper_causal c _ (responseFields_causal ob c) A' B B' hB]
      · simp only [List.take_succ_cons, fill_causal c .unknown A' B B' hB]

/-- **With `complete = false`, a message's classes are its prefixes' classes.** -/
theorem message_prefix (ob : Bool) (A B : List Byte) :
    (message ob false (A ++ B)).take A.length = message ob false A := by
  have := message_causal ob false A B [] (fun e => by cases e)
  rw [this, List.append_nil, List.take_of_length_le (Nat.le_of_eq (message_len ob false A))]

/-- A byte's class from the bytes up to it and how many follow it in the message: position `j` of
`message ob c X` is that of `X.take (j + 1)` padded with `pad` (any bytes; as many as `X` has after
`j` when `c = true`, none needed otherwise). -/
theorem message_at (ob c : Bool) (X pad : List Byte) (j : Nat) (hj : j < X.length)
    (hp : c = true → pad.length = X.length - (j + 1)) :
    (message ob c X)[j]? = (message ob c (X.take (j + 1) ++ pad))[j]? := by
  have e := message_causal ob c (X.take (j + 1)) (X.drop (j + 1)) pad
    (fun e => by rw [hp e, List.length_drop])
  rw [List.take_append_drop] at e
  have h1 := congrArg (fun l => l[j]?) e
  simp only [List.getElem?_take, List.length_take, Nat.min_eq_left (show j + 1 ≤ X.length by omega),
    show j < j + 1 by omega, if_true] at h1
  exact h1

/-! ### The frames, byte by byte -/

namespace Stream

/-- Where the reader is in the frame layer. -/
inductive Phase where
  /-- A frame's first header byte is next. -/
  | first
  /-- Its second header byte (the first was `b0`). -/
  | second (b0 : Byte)
  /-- The high byte of a 16-bit length. -/
  | extHi (b0 : Byte)
  /-- Its low byte. -/
  | extLo (b0 hi : Byte)
  /-- `left` payload bytes still to come (`left ≥ 1`); `complete`: the message is complete (its
  last frame, all of it in the stream). -/
  | payload (control fin complete : Bool) (left : Nat)
  /-- After a malformed header byte: every byte is `error`. -/
  | dead

structure St where
  phase : Phase
  /-- The binary message in progress: its payload so far, the current frame's included. -/
  msg : List Byte
  /-- A binary message is in progress (its last frame had FIN clear). -/
  fragmented : Bool

def isControl (b0 : Byte) : Bool := decide (b0.toNat % 16 = 8 ∨ b0.toNat % 16 = 9 ∨ b0.toNat % 16 = 10)

def finOf (b0 : Byte) : Bool := decide (128 ≤ b0.toNat)

/-- `frames`' test of a first header byte. -/
def headerFits (b0 : Byte) (fragmented : Bool) : Prop :=
  b0.toNat / 16 % 8 = 0 ∧ ((b0.toNat % 16 = 2 ∧ !fragmented) ∨ (b0.toNat % 16 = 0 ∧ fragmented) ∨
    (isControl b0 ∧ finOf b0))

instance (b0 : Byte) (fragmented : Bool) : Decidable (headerFits b0 fragmented) := by
  unfold headerFits; infer_instance

/-- `frames`' test of a second header byte. -/
def secondBad (b0 b1 : Byte) : Prop :=
  128 ≤ b1.toNat ∨ b1.toNat % 128 = 127 ∨ (isControl b0 ∧ b1.toNat % 128 = 126)

instance (b0 b1 : Byte) : Decidable (secondBad b0 b1) := by unfold secondBad; infer_instance

/-- The end of a frame: a control frame leaves the message as it was; a data frame with FIN ends it;
one without leaves it in progress. -/
def endFrame (control fin : Bool) (st : St) : St :=
  if control then { st with phase := .first }
  else if fin then { phase := .first, msg := [], fragmented := false }
  else { phase := .first, msg := st.msg, fragmented := true }

/-- After a frame's last header byte, its payload being `length` bytes and `left` bytes of the
stream following: the message is complete if FIN is set and the stream holds the whole frame. -/
def startPayload (b0 : Byte) (length left : Nat) (st : St) : St :=
  if length = 0 then endFrame (isControl b0) (finOf b0) st
  else { st with phase := .payload (isControl b0) (finOf b0) (finOf b0 && decide (length ≤ left)) length }

/-- A data payload byte's class: its position in the message read so far, padded with zeros to the
end of the frame when the message is complete (`message_at`: the padding's bytes do not matter). -/
def payloadClass (ob complete : Bool) (msg : List Byte) (b : Byte) (left : Nat) : Class :=
  ((message ob complete (msg ++ b :: List.replicate (if complete then left - 1 else 0) 0))[msg.length]?).getD .error

/-- **One byte.** `left`: how many bytes of the stream follow `b` (used only at a frame's last
header byte). -/
def step (ob : Bool) (st : St) (b : Byte) (left : Nat) : Class × St :=
  match st.phase with
  | .dead => (.error, st)
  | .first => if headerFits b st.fragmented then (.frameHeader, { st with phase := .second b })
      else (.frameHeader, { st with phase := .dead })
  | .second b0 =>
    if secondBad b0 b then (.frameHeader, { st with phase := .dead })
    else if b.toNat % 128 = 126 then (.frameHeader, { st with phase := .extHi b0 })
    else (.frameHeader, startPayload b0 (b.toNat % 128) left st)
  | .extHi b0 => (.frameHeader, { st with phase := .extLo b0 b })
  | .extLo b0 hi =>
    if word hi b < 126 then (.frameHeader, { st with phase := .dead })
    else (.frameHeader, startPayload b0 (word hi b) left st)
  | .payload ctl fin cpl n =>
    let c := if ctl then Class.control else payloadClass ob cpl st.msg b n
    let msg := if ctl then st.msg else st.msg ++ [b]
    if n ≤ 1 then (c, endFrame ctl fin { st with msg }) else (c, { st with msg, phase := .payload ctl fin cpl (n - 1) })

/-- The classes of a stream of frames, read byte by byte. -/
def run (ob : Bool) : St → List Byte → List Class
  | _, [] => []
  | st, b :: rest => (step ob st b rest.length).1 :: run ob (step ob st b rest.length).2 rest

theorem run_cons (ob : Bool) (st : St) (b : Byte) (rest : List Byte) :
    run ob st (b :: rest) = (step ob st b rest.length).1 :: run ob (step ob st b rest.length).2 rest := rfl

theorem run_dead (ob : Bool) (msg : List Byte) (fr : Bool) : ∀ rest : List Byte,
    run ob ⟨.dead, msg, fr⟩ rest = fill .error rest
  | [] => rfl
  | b :: rest => by rw [run_cons]; simp only [step]; rw [run_dead ob msg fr rest]; rfl

/-! ### Agreement with `frames` -/

/-- `frames`' payload part, as a function. -/
def payloadRef (ob : Bool) (fuel : Nat) (msg : List Byte) (fragmented : Bool) (b0 : Byte) (length : Nat)
    (rest : List Byte) : List Class :=
  let bytes := rest.take length
  let classes := if isControl b0 then fill .control bytes
    else (message ob (finOf b0 && decide (bytes.length = length)) (msg ++ bytes)).drop msg.length
  let next : List Byte × Bool :=
    if isControl b0 then (msg, fragmented) else if finOf b0 then ([], false) else (msg ++ bytes, true)
  classes ++ (if bytes.length < length then [] else frames ob fuel next.1 next.2 (rest.drop length))

theorem frames_cons (ob : Bool) (fuel : Nat) (msg : List Byte) (fragmented : Bool) (b0 : Byte) (rest : List Byte) :
    frames ob (fuel + 1) msg fragmented (b0 :: rest) =
      if ¬headerFits b0 fragmented then .frameHeader :: fill .error rest else
      match rest with
      | [] => [.frameHeader]
      | b1 :: rest =>
        if secondBad b0 b1 then .frameHeader :: .frameHeader :: fill .error rest else
        if b1.toNat % 128 = 126 then
          match rest with
          | hi :: lo :: rest =>
            if word hi lo < 126 then [.frameHeader, .frameHeader, .frameHeader, .frameHeader] ++ fill .error rest
            else [.frameHeader, .frameHeader, .frameHeader, .frameHeader] ++
              payloadRef ob fuel msg fragmented b0 (word hi lo) rest
          | short => .frameHeader :: .frameHeader :: fill .frameHeader short
        else [.frameHeader, .frameHeader] ++ payloadRef ob fuel msg fragmented b0 (b1.toNat % 128) rest := by
  simp only [frames, headerFits, secondBad, isControl, finOf, payloadRef, List.append_assoc]
  rfl

theorem take_succ_of_getElem? {W : List Byte} {i : Nat} {b : Byte} (hb : W[i]? = some b) :
    W.take (i + 1) = W.take i ++ [b] := by
  rw [List.take_add_one, hb]; rfl

/-- **A payload byte's class, byte by byte, is its class in the whole message.** -/
theorem payloadClass_eq (ob cpl : Bool) (msg0 W : List Byte) (i length : Nat) (b : Byte)
    (hb : W[i]? = some b) (hW : cpl = true → W.length = length) :
    payloadClass ob cpl (msg0 ++ W.take i) b (length - i) =
      (((message ob cpl (msg0 ++ W)).drop msg0.length)[i]?).getD .error := by
  have hi : i < W.length := by
    rcases Nat.lt_or_ge i W.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hb; cases hb
  have e := message_at ob cpl (msg0 ++ W) (List.replicate (if cpl then length - i - 1 else 0) 0)
    (msg0.length + i) (by simp; omega)
    (fun e => by rw [if_pos e, List.length_replicate, List.length_append, hW e]; omega)
  have ht : (msg0 ++ W).take (msg0.length + i + 1) = msg0 ++ W.take i ++ [b] := by
    rw [Nat.add_assoc, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      take_succ_of_getElem? hb, List.append_assoc]
  rw [ht] at e
  unfold payloadClass
  rw [List.getElem?_drop, e, List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The classes `frames` gives a frame's payload. -/
def payloadClasses (ob : Bool) (msg0 : List Byte) (b0 : Byte) (length : Nat) (rest : List Byte) : List Class :=
  if isControl b0 then fill .control (rest.take length)
  else (message ob (finOf b0 && decide ((rest.take length).length = length)) (msg0 ++ rest.take length)).drop msg0.length

theorem payloadClasses_len (ob : Bool) (msg0 : List Byte) (b0 : Byte) (length : Nat) (rest : List Byte) :
    (payloadClasses ob msg0 b0 length rest).length = (rest.take length).length := by
  unfold payloadClasses
  split
  · exact fill_length _ _
  · rw [List.length_drop, message_len, List.length_append]; omega

/-- **A frame's payload, byte by byte**: from the state with `j` payload bytes left, the reader gives
the rest of `frames`' classes for the payload, then (if the stream holds the whole frame) whatever
it gives from the frame's end (`K`). -/
theorem payload_run (ob : Bool) (msg0 : List Byte) (frag : Bool) (b0 : Byte) (length : Nat)
    (rest : List Byte) (K : List Class)
    (hK : length ≤ rest.length → run ob (endFrame (isControl b0) (finOf b0)
      ⟨.first, if isControl b0 then msg0 else msg0 ++ rest.take length, frag⟩) (rest.drop length) = K) :
    ∀ j, 0 < j → j ≤ length →
      run ob ⟨.payload (isControl b0) (finOf b0) (finOf b0 && decide (length ≤ rest.length)) j,
        if isControl b0 then msg0 else msg0 ++ rest.take (length - j), frag⟩ (rest.drop (length - j)) =
      (payloadClasses ob msg0 b0 length rest).drop (length - j) ++
        (if (rest.take length).length < length then [] else K)
  | 0, h, _ => by omega
  | j + 1, _, hj => by
    have hlen := payloadClasses_len ob msg0 b0 length rest
    cases hr : rest.drop (length - (j + 1)) with
    | nil =>
      have h1 : rest.length ≤ length - (j + 1) := by
        have := congrArg List.length hr; simp at this; omega
      have hd : (payloadClasses ob msg0 b0 length rest).drop (length - (j + 1)) = [] :=
        List.drop_eq_nil_of_le (by rw [hlen, List.length_take]; omega)
      have hl : (rest.take length).length < length := by rw [List.length_take]; omega
      rw [hd, if_pos hl]
      rfl
    | cons b R' =>
      have hi : length - (j + 1) < rest.length := by
        have := congrArg List.length hr; simp at this; omega
      have hb0 : rest[length - (j + 1)]? = some b := by
        have := congrArg (fun l => l[0]?) hr
        simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using this
      have hb : (rest.take length)[length - (j + 1)]? = some b := by
        rw [List.getElem?_take, if_pos (by omega)]; exact hb0
      have hR' : R' = rest.drop (length - (j + 1) + 1) := by
        have := congrArg List.tail hr
        simp only [List.tail_cons, List.tail_drop] at this
        exact this.symm
      have hcpl : (finOf b0 && decide (length ≤ rest.length)) =
          (finOf b0 && decide ((rest.take length).length = length)) := by
        congr 1; simp only [List.length_take]; apply decide_eq_decide.mpr; omega
      have hmsg : msg0 ++ rest.take (length - (j + 1)) ++ [b] = msg0 ++ rest.take (length - j) := by
        have e := take_succ_of_getElem? hb
        rw [List.take_take, Nat.min_eq_left (by omega), List.take_take, Nat.min_eq_left (by omega)] at e
        rw [show length - j = length - (j + 1) + 1 by omega, e, List.append_assoc]
      have hclass : (if isControl b0 then Class.control
          else payloadClass ob (finOf b0 && decide (length ≤ rest.length))
            (if isControl b0 then msg0 else msg0 ++ rest.take (length - (j + 1))) b (j + 1)) =
          ((payloadClasses ob msg0 b0 length rest)[length - (j + 1)]?).getD .error := by
        unfold payloadClasses
        by_cases hc : isControl b0 = true
        · simp only [hc, if_true]
          rw [fill, List.getElem?_map, hb]; rfl
        · simp only [hc, Bool.false_eq_true, if_false]
          rw [hcpl]
          have := payloadClass_eq ob (finOf b0 && decide ((rest.take length).length = length)) msg0
            (rest.take length) (length - (j + 1)) length b hb
            (fun e => by simp only [Bool.and_eq_true, decide_eq_true_eq] at e; exact e.2)
          rw [List.take_take, Nat.min_eq_left (by omega), show length - (length - (j + 1)) = j + 1 by omega] at this
          exact this
      have hdrop : (payloadClasses ob msg0 b0 length rest).drop (length - (j + 1)) =
          ((payloadClasses ob msg0 b0 length rest)[length - (j + 1)]?).getD .error ::
            (payloadClasses ob msg0 b0 length rest).drop (length - j) := by
        have hlt : length - (j + 1) < (payloadClasses ob msg0 b0 length rest).length := by
          rw [hlen, List.length_take]; omega
        rw [List.drop_eq_getElem_cons hlt, List.getElem?_eq_getElem hlt, show length - j = length - (j + 1) + 1 by omega]
        rfl
      have hmsg' : (if isControl b0 = true then (if isControl b0 = true then msg0 else msg0 ++ rest.take (length - (j + 1)))
          else (if isControl b0 = true then msg0 else msg0 ++ rest.take (length - (j + 1))) ++ [b]) =
          (if isControl b0 = true then msg0 else msg0 ++ rest.take (length - j)) := by
        by_cases hc : isControl b0 = true
        · simp only [hc, if_true]
        · simp only [hc, Bool.false_eq_true, if_false]; exact hmsg
      rw [run_cons, hdrop, List.cons_append]
      simp only [step]
      by_cases hj0 : j = 0
      · subst hj0
        rw [if_pos (Nat.le_refl _)]
        dsimp only
        rw [hclass, hmsg']
        congr 1
        have hl : ¬ (rest.take length).length < length := by rw [List.length_take]; omega
        have hd : (payloadClasses ob msg0 b0 length rest).drop (length - 0) = [] :=
          List.drop_eq_nil_of_le (by rw [hlen, List.length_take]; omega)
        rw [if_neg hl, hd, List.nil_append, ← hK (by omega), hR', show length - (0 + 1) + 1 = length by omega,
          Nat.sub_zero]
        rfl
      · rw [if_neg (by omega)]
        dsimp only
        rw [hclass, hmsg']
        congr 1
        have ih := payload_run ob msg0 frag b0 length rest K hK j (by omega) (by omega)
        rw [← ih, hR', show length - (j + 1) + 1 = length - j by omega, Nat.add_sub_cancel]

/-- The message and fragmentation after a frame, as `frames` computes them. -/
def nextOf (msg : List Byte) (fragmented : Bool) (b0 : Byte) (bytes : List Byte) : List Byte × Bool :=
  if isControl b0 then (msg, fragmented) else if finOf b0 then ([], false) else (msg ++ bytes, true)

theorem endFrame_next (p : Phase) (msg : List Byte) (frag : Bool) (b0 : Byte) (bytes : List Byte) :
    endFrame (isControl b0) (finOf b0) ⟨p, if isControl b0 then msg else msg ++ bytes, frag⟩ =
      ⟨.first, (nextOf msg frag b0 bytes).1, (nextOf msg frag b0 bytes).2⟩ := by
  unfold endFrame nextOf
  by_cases hc : isControl b0 = true
  · simp only [hc, if_true]
  · by_cases hf : finOf b0 = true
    · simp only [hc, hf, Bool.false_eq_true, if_false, if_true]
    · simp only [hc, hf, Bool.false_eq_true, if_false]

theorem payloadRef_eq (ob : Bool) (fuel : Nat) (msg : List Byte) (fragmented : Bool) (b0 : Byte) (length : Nat)
    (rest : List Byte) :
    payloadRef ob fuel msg fragmented b0 length rest =
      payloadClasses ob msg b0 length rest ++ (if (rest.take length).length < length then [] else
        frames ob fuel (nextOf msg fragmented b0 (rest.take length)).1
          (nextOf msg fragmented b0 (rest.take length)).2 (rest.drop length)) := rfl

/-- **After a frame's header**, the reader gives `frames`' classes for the payload and what follows. -/
theorem start_run (ob : Bool) (fuel : Nat) (p : Phase) (msg : List Byte) (frag : Bool) (b0 : Byte) (length : Nat)
    (rest : List Byte)
    (IH : ∀ msg frag (bytes : List Byte), bytes.length < fuel → frames ob fuel msg frag bytes = run ob ⟨.first, msg, frag⟩ bytes)
    (hfuel : rest.length < fuel) :
    run ob (startPayload b0 length rest.length ⟨p, msg, frag⟩) rest = payloadRef ob fuel msg frag b0 length rest := by
  rw [payloadRef_eq]
  unfold startPayload
  by_cases h0 : length = 0
  · subst h0
    rw [if_pos rfl]
    have hc : payloadClasses ob msg b0 0 rest = [] := by
      have := payloadClasses_len ob msg b0 0 rest
      simp only [List.take_zero, List.length_nil] at this
      exact List.eq_nil_of_length_eq_zero this
    rw [hc, List.nil_append, if_neg (by simp), List.drop_zero, IH _ _ _ hfuel]
    have := endFrame_next p msg frag b0 []
    simp only [List.append_nil, ite_self] at this
    rw [List.take_zero, ← this]
  · rw [if_neg h0]
    have hK : length ≤ rest.length → run ob (endFrame (isControl b0) (finOf b0)
        ⟨.first, if isControl b0 then msg else msg ++ rest.take length, frag⟩) (rest.drop length) =
        frames ob fuel (nextOf msg frag b0 (rest.take length)).1
          (nextOf msg frag b0 (rest.take length)).2 (rest.drop length) := by
      intro _
      rw [endFrame_next, IH _ _ _ (by simp; omega)]
    have := payload_run ob msg frag b0 length rest _ hK length (by omega) (Nat.le_refl _)
    simp only [Nat.sub_self, List.drop_zero, List.take_zero, List.append_nil, ite_self] at this
    exact this

/-- **The reader agrees with `frames`**, for every stream of frames, from any message state. -/
theorem frames_run (ob : Bool) : ∀ fuel msg frag (bytes : List Byte), bytes.length < fuel →
    frames ob fuel msg frag bytes = run ob ⟨.first, msg, frag⟩ bytes
  | 0, _, _, _, h => by omega
  | fuel + 1, msg, frag, [], _ => rfl
  | fuel + 1, msg, frag, b0 :: rest, hl => by
    have IH := frames_run ob fuel
    simp only [List.length_cons] at hl
    rw [frames_cons, run_cons]
    simp only [step]
    by_cases hf : headerFits b0 frag
    case neg =>
      rw [if_pos hf, if_neg hf, run_dead]
    rw [if_neg (not_not_intro hf), if_pos hf]
    match rest, hl with
    | [], _ => rfl
    | b1 :: rest', hl =>
      simp only [List.length_cons] at hl
      rw [run_cons]
      simp only [step]
      by_cases hs : secondBad b0 b1
      · rw [if_pos hs, if_pos hs, run_dead]
      rw [if_neg hs, if_neg hs]
      by_cases h126 : b1.toNat % 128 = 126
      · rw [if_pos h126, if_pos h126]
        match rest', hl with
        | [], _ => rfl
        | [hi], _ => rfl
        | hi :: lo :: rest'', hl =>
          simp only [List.length_cons] at hl
          rw [run_cons, run_cons]
          simp only [step]
          by_cases hw : word hi lo < 126
          · rw [if_pos hw, if_pos hw, run_dead]; rfl
          · rw [if_neg hw, if_neg hw]
            simp only [List.cons_append, List.nil_append]
            rw [start_run ob fuel _ msg frag b0 _ rest'' IH (by omega)]
      · rw [if_neg h126, if_neg h126]
        simp only [List.cons_append, List.nil_append]
        rw [start_run ob fuel _ msg frag b0 _ rest' IH (by omega)]

theorem run_len (ob : Bool) : ∀ (st : St) (bytes : List Byte), (run ob st bytes).length = bytes.length
  | _, [] => rfl
  | st, b :: rest => by rw [run_cons, List.length_cons, run_len ob _ rest, List.length_cons]

/-! ### `failClosed`, byte by byte -/

/-- One byte, with `failClosed`'s sticky error: `bad` once a byte has been `error`. -/
def stepF (ob : Bool) (st : St × Bool) (b : Byte) (left : Nat) : Class × (St × Bool) :=
  if st.2 then (.error, st)
  else ((step ob st.1 b left).1, ((step ob st.1 b left).2, decide ((step ob st.1 b left).1 = .error)))

def runF (ob : Bool) : St × Bool → List Byte → List Class
  | _, [] => []
  | st, b :: rest => (stepF ob st b rest.length).1 :: runF ob (stepF ob st b rest.length).2 rest

/-- The initial state: a frame boundary, no message in progress, no error. -/
def init : St × Bool := (⟨.first, [], false⟩, false)

/-- **The reference classifier, byte by byte.** -/
def classes (ob : Bool) (bytes : List Byte) : List Class := runF ob init bytes

theorem runF_bad (ob : Bool) (st : St) : ∀ rest : List Byte, runF ob (st, true) rest = fill .error rest
  | [] => rfl
  | b :: rest => by
    simp only [runF, stepF, if_true]
    rw [runF_bad ob st rest]; rfl

theorem failClosed_cons (c : Class) (L : List Class) :
    failClosed (c :: L) = if c = .error then .error :: fill .error L else c :: failClosed L := by
  cases c <;> rfl

theorem fill_error_of_len {L : List Class} {M : List Byte} (h : L.length = M.length) :
    fill Class.error L = fill Class.error M := by
  apply List.ext_getElem (by simp [fill, h])
  intro i h1 h2; simp [fill]

theorem runF_run (ob : Bool) : ∀ (st : St) (bytes : List Byte), runF ob (st, false) bytes = failClosed (run ob st bytes)
  | _, [] => rfl
  | st, b :: rest => by
    rw [run_cons, failClosed_cons]
    simp only [runF, stepF, Bool.false_eq_true, if_false]
    by_cases he : (step ob st b rest.length).1 = .error
    · rw [if_pos he, he, decide_eq_true rfl, runF_bad, fill_error_of_len (run_len ob _ rest)]
    · rw [if_neg he, decide_eq_false he, runF_run ob _ rest]

/-- **`classifyFrames` is the byte-by-byte reader**, for every byte string. -/
theorem classifyFrames_stream (ob : Bool) (bytes : List Byte) : classifyFrames ob bytes = classes ob bytes := by
  unfold classifyFrames classes init
  rw [frames_run ob _ [] false bytes (Nat.lt_succ_self _), runF_run]

end Stream

/-! ### The upgrade response's head, byte by byte -/

namespace Head

/-- The terminator CR LF CR LF. -/
def term : List Byte := [13, 10, 13, 10]

/-- Its first `k` bytes. -/
def pre (k : Nat) : List Byte := term.take k

/-- How many bytes of the terminator the bytes read so far end with, after one more byte (`k ≤ 3`;
4: the head is complete). The same count as the controller's `State.terminator`. -/
def next (k : Nat) (b : Byte) : Nat :=
  if b = (if k % 2 = 0 then 13 else 10) then k + 1 else if b = 13 then 1 else 0

/-- From count `k`, the number of bytes up to and including the end of the head. -/
def find : Nat → List Byte → Option Nat
  | _, [] => none
  | k, b :: rest => if next k b = 4 then some 1 else (find (next k b) rest).map (· + 1)

theorem headLength_term (s : List Byte) : headLength (13 :: 10 :: 13 :: 10 :: s) = some 4 := by
  simp [headLength]

theorem headLength_cons (b : Byte) (s : List Byte) (h : ¬ term <+: (b :: s)) :
    headLength (b :: s) = (headLength s).map (· + 1) := by
  rw [headLength]
  intro tail hb hs
  apply h
  rw [hb, hs]
  exact ⟨tail, rfl⟩

theorem not_term_prefix {b : Byte} {s : List Byte} (hb : b ≠ 13) : ¬ term <+: (b :: s) := by
  intro h
  have := (List.cons_prefix_cons.mp h).1
  exact hb this.symm

theorem headLength_pre (k : Nat) (hk : k ≤ 3) : headLength (pre k) = none := by
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem map_add (o : Option Nat) (a b : Nat) : (o.map (· + a)).map (· + b) = o.map (· + (a + b)) := by
  cases o <;> simp [Nat.add_assoc]

/-- **The head's end, found byte by byte**: from the count `k` (the bytes read end with the first
`k` bytes of CR LF CR LF), `find` gives `headLength` of those `k` bytes and the rest. -/
theorem headLength_find : ∀ (s : List Byte) (k : Nat), k ≤ 3 → headLength (pre k ++ s) = (find k s).map (· + k)
  | [], k, hk => by rw [List.append_nil, headLength_pre k hk]; rfl
  | b :: s, k, hk => by
    have ih := fun k hk => headLength_find s k hk
    have e13 : (13 : Byte) ≠ 10 := by decide
    have e10 : (10 : Byte) ≠ 13 := by decide
    match k, hk with
    | 0, _ =>
      by_cases hb : b = 13
      · subst hb
        rw [find, show next 0 13 = 1 by decide, if_neg (by decide), show pre 0 ++ 13 :: s = pre 1 ++ s from rfl,
          ih 1 (by omega)]
        repeat rw [map_add]
        try rfl
      · have hn : next 0 b = 0 := by unfold next; rw [if_pos (by decide : 0 % 2 = 0), if_neg hb, if_neg hb]
        rw [find, hn, if_neg (by decide), show pre 0 ++ b :: s = b :: s from rfl,
          headLength_cons b s (not_term_prefix hb), show s = pre 0 ++ s from rfl, ih 0 (by omega)]
        repeat rw [map_add]
        try rfl
    | 1, _ =>
      by_cases hb : b = 10
      · subst hb
        rw [find, show next 1 10 = 2 by decide, if_neg (by decide), show pre 1 ++ 10 :: s = pre 2 ++ s from rfl,
          ih 2 (by omega)]
        repeat rw [map_add]
        try rfl
      · by_cases hb13 : b = 13
        · subst hb13
          have hc : ¬ term <+: (13 :: 13 :: s) := by
            intro h; have := (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).1; exact e10 this
          rw [find, show next 1 13 = 1 by decide, if_neg (by decide), show pre 1 ++ 13 :: s = 13 :: 13 :: s from rfl,
            headLength_cons _ _ hc, show (13 :: s : List Byte) = pre 1 ++ s from rfl, ih 1 (by omega)]
          repeat rw [map_add]
          try rfl
        · have hn : next 1 b = 0 := by
            unfold next; rw [if_neg (by decide : ¬ 1 % 2 = 0), if_neg hb, if_neg hb13]
          have hc : ¬ term <+: (13 :: b :: s) := by
            intro h; have := (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).1; exact hb this.symm
          rw [find, hn, if_neg (by decide), show pre 1 ++ b :: s = 13 :: b :: s from rfl, headLength_cons _ _ hc,
            headLength_cons b s (not_term_prefix hb13), show s = pre 0 ++ s from rfl, ih 0 (by omega)]
          repeat rw [map_add]
          try rfl
    | 2, _ =>
      by_cases hb : b = 13
      · subst hb
        rw [find, show next 2 13 = 3 by decide, if_neg (by decide), show pre 2 ++ 13 :: s = pre 3 ++ s from rfl,
          ih 3 (by omega)]
        repeat rw [map_add]
        try rfl
      · have hn : next 2 b = 0 := by unfold next; rw [if_pos (by decide : 2 % 2 = 0), if_neg hb, if_neg hb]
        have hc1 : ¬ term <+: (13 :: 10 :: b :: s) := by
          intro h
          have := (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).2).1
          exact hb this.symm
        have hc2 : ¬ term <+: (10 :: b :: s) := not_term_prefix e10
        rw [find, hn, if_neg (by decide), show pre 2 ++ b :: s = 13 :: 10 :: b :: s from rfl, headLength_cons _ _ hc1,
          headLength_cons _ _ hc2, headLength_cons b s (not_term_prefix hb), show s = pre 0 ++ s from rfl,
          ih 0 (by omega)]
        repeat rw [map_add]
        try rfl
    | 3, _ =>
      by_cases hb : b = 10
      · subst hb
        rw [find, show next 3 10 = 4 by decide, if_pos rfl]
        exact headLength_term s
      · have hc1 : ¬ term <+: (13 :: 10 :: 13 :: b :: s) := by
          intro h
          have := (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp
            (List.cons_prefix_cons.mp h).2).2).2).1
          exact hb this.symm
        have hc2 : ¬ term <+: (10 :: 13 :: b :: s) := not_term_prefix e10
        have hc3 : ¬ term <+: (13 :: b :: s) := by
          intro h; have := (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp h).2).1; exact hb this.symm
        rw [show pre 3 ++ b :: s = 13 :: 10 :: 13 :: b :: s from rfl, headLength_cons _ _ hc1,
          headLength_cons _ _ hc2, headLength_cons _ _ hc3]
        by_cases hb13 : b = 13
        · subst hb13
          rw [find, show next 3 13 = 1 by decide, if_neg (by decide), show (13 :: s : List Byte) = pre 1 ++ s from rfl,
            ih 1 (by omega)]
          repeat rw [map_add]
          try rfl
        · have hn : next 3 b = 0 := by
            unfold next; rw [if_neg (by decide : ¬ 3 % 2 = 0), if_neg hb, if_neg hb13]
          rw [find, hn, if_neg (by decide), headLength_cons b s (not_term_prefix hb13), show s = pre 0 ++ s from rfl,
            ih 0 (by omega)]
          repeat rw [map_add]
          try rfl

/-- `headLength`, found byte by byte from the start. -/
theorem headLength_eq (s : List Byte) : headLength s = find 0 s := by
  have := headLength_find s 0 (by omega)
  simp only [pre, List.take_zero, List.nil_append] at this
  rw [this]; cases find 0 s <;> rfl

end Head

/-! ### The whole stream, byte by byte -/

/-- Before the head's end (`head k`: the bytes read end with `k` bytes of CR LF CR LF), or in the
frames (with `failClosed`'s flag). -/
inductive AllSt where
  | head (k : Nat)
  | frames (st : Stream.St × Bool)

def stepAll (ob : Bool) (st : AllSt) (b : Byte) (left : Nat) : Class × AllSt :=
  match st with
  | .head k => (.head, if Head.next k b = 4 then .frames Stream.init else .head (Head.next k b))
  | .frames s => ((Stream.stepF ob s b left).1, .frames (Stream.stepF ob s b left).2)

def runAll (ob : Bool) : AllSt → List Byte → List Class
  | _, [] => []
  | st, b :: rest => (stepAll ob st b rest.length).1 :: runAll ob (stepAll ob st b rest.length).2 rest

/-- **`ReceiveSpec.classify`, byte by byte from the upgrade response's first byte.** -/
def classifyStream (ob : Bool) (stream : List Byte) : List Class := runAll ob (.head 0) stream

theorem runAll_frames (ob : Bool) : ∀ (s : Stream.St × Bool) (bytes : List Byte),
    runAll ob (.frames s) bytes = Stream.runF ob s bytes
  | _, [] => rfl
  | s, b :: rest => by
    simp only [runAll, stepAll, Stream.runF]
    rw [runAll_frames ob _ rest]

theorem runAll_head (ob : Bool) : ∀ (s : List Byte) (k : Nat),
    runAll ob (.head k) s = match Head.find k s with
      | none => fill .head s
      | some n => fill .head (s.take n) ++ Stream.classes ob (s.drop n)
  | [], k => rfl
  | b :: s, k => by
    simp only [runAll, stepAll, Head.find]
    by_cases h4 : Head.next k b = 4
    · simp only [h4, if_true, runAll_frames]
      rfl
    · simp only [h4, if_false]
      rw [runAll_head ob s (Head.next k b)]
      cases Head.find (Head.next k b) s with
      | none => rfl
      | some n => rfl

/-- **`classify` is the byte-by-byte reader**, for every stream. -/
theorem classify_stream (ob : Bool) (stream : List Byte) : classify ob stream = classifyStream ob stream := by
  unfold classify classifyStream
  rw [runAll_head, Head.headLength_eq]
  cases Head.find 0 stream with
  | none => rfl
  | some n => dsimp only; rw [Stream.classifyFrames_stream]

end ReceiveStream
