import TlsMpc.Node.Policy.ReceiveSimFrame

/-!
# T1, item 1 (the controller's steps, as functions)

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`PublicReceive.payloadByte` is a `do` block with mutable state, a loop (the response parser's feed)
and join points; unfolded, it is too large for `split`. Here it is cut into pieces, by definition
(`payloadByte_eq`, `rfl`): `pbReply` (a response's own fields), `pbRequest` (a server request's own
fields, or its delivered envelope), `pbCheck` (no field may run past the end of its message), `pbDone`
(the message's end). The response parser's loop (`TlsChatResponse.runByte`) changes only the
response parser's fields (`response`, `pending`) and, through `complete`, `status`, `retryAfter`,
`body`; `norm` forgets those five. **`payloadByte_spec`**: whenever `payloadByte` succeeds, `pbSpec`
(the same without the response parser) succeeds with the same state up to those five fields.

Also: `frameByte` once upgraded only replaces `frame`, `control`, `rollback` (`frameByte_upgraded`);
`stepPassed` and `stepSkipped` as functions of their frame step (`stepPassed_spec`,
`stepSkipped_spec`).
-/

open TlsMpc TlsMpc.Signal

namespace ReceiveSimByte

open PublicReceive ReceiveProofs

/-! ### `payloadByte`, in pieces -/

def pbDone (message : List Byte) (done complete : Bool) (s : State) : Except String (State × Bool) :=
  if done = true then
    if (s.skip == 0 && s.inner.isNone) = true then
      if (pendingField s == 0) = true then
        if (message == [8, 1]) = true then
          pure ({ s with
            requests := s.requests ++ [s.request], message := [], held := none, request := [],
            bodySkipped := false, reply := [], replySkipped := false }, complete)
        else
          pure ({ s with
            message := [], held := none, request := [], bodySkipped := false, reply := [],
            replySkipped := false }, complete)
      else throw "a field runs past the end of its message"
    else throw "server request ended inside its body"
  else pure (s, complete)

/-- The overrun test of `payloadByte`. -/
def overrun (s : State) : Bool :=
  get s.frame 4 == on && get s.frame 8 == on && decide ((get s.frame 7).toNat < 8) &&
      decide (pendingField s > (get s.frame 10).toNat * 256 + (get s.frame 11).toNat)

def pbCheck (message : List Byte) (done complete : Bool) (s : State) : Except String (State × Bool) :=
  if (get s.frame 4 == on && get s.frame 8 == on && decide ((get s.frame 7).toNat < 8) &&
      decide (pendingField s > (get s.frame 10).toNat * 256 + (get s.frame 11).toNat)) = true then
    throw "a field runs past the end of its message"
  else pbDone message done complete s

def pbRequest (message : List Byte) (byte : Byte) (data done complete : Bool) (s : State) :
    Except String (State × Bool) :=
  if (data && message == [8, 1]) = true then
    match s.inner with
    | some (header, passed, remaining) =>
      if remaining > 0 then
        envelopeAdvance s (header ++ [byte]) passed (remaining - 1) >>= fun s => pbCheck message done complete s
      else throw "envelope state"
    | none =>
      match scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [byte]) s.bodySkipped with
      | (.malformed, _) => throw "malformed server request"
      | (.skip count, fields) =>
        if (fields.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = true then
          envelopeAdvance { s with
              request := if s.request.isEmpty = true then [8, 1] else s.request ++ [byte],
              bodySkipped := true } [] 0 count >>= fun s => pbCheck message done complete s
        else pbCheck message done complete { s with
              request := if s.request.isEmpty = true then [8, 1] else s.request ++ [byte],
              skip := count, capture := false, bodySkipped := true }
      | (.more, _) => pbCheck message done complete { s with
              request := if s.request.isEmpty = true then [8, 1] else s.request ++ [byte] }
  else pbCheck message done complete s

def pbReply (message : List Byte) (byte : Byte) (data done complete : Bool) (s : State) :
    Except String (State × Bool) :=
  if (data && message == [8, 2]) = true then
    match replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte]) s.replySkipped s.openBody with
    | (.malformed, _) => throw "malformed service response"
    | (.skip count, fields) =>
      if complete = true then
        pbRequest message byte data done complete { s with
            reply := if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte],
            skip := count, capture := false,
            collect := s.fetch.isSome && fields.id == s.fetch && fields.status == some 200, replySkipped := true,
            bundle := if (s.fetch.isSome && fields.id == s.fetch && fields.status == some 200) = true then some count
              else s.bundle,
            status := (replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte]) true
              s.openBody).2.status.getD 0,
            retryAfter := if s.openBody = true then none
              else retryAfterOf (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte]),
            body := if s.openBody = true then replyBody (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte])
              else [] }
      else
        pbRequest message byte data done complete { s with
            reply := if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte],
            skip := count, capture := false,
            collect := s.fetch.isSome && fields.id == s.fetch && fields.status == some 200, replySkipped := true,
            bundle := if (s.fetch.isSome && fields.id == s.fetch && fields.status == some 200) = true then some count
              else s.bundle }
    | (.more, _) =>
      if complete = true then
        pbRequest message byte data done complete { s with
            reply := if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte],
            status := (replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte]) true
              s.openBody).2.status.getD 0,
            retryAfter := if s.openBody = true then none
              else retryAfterOf (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte]),
            body := if s.openBody = true then replyBody (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte])
              else [] }
      else
        pbRequest message byte data done complete { s with
            reply := if s.reply.isEmpty = true then [8, 2] else s.reply ++ [byte] }
  else pbRequest message byte data done complete s

/-- The response parser's loop body, as `payloadByte` has it. -/
def pbFeedBody (x : List Byte × Byte) (r : MProd Bool State) : Except String (ForInStep (MProd Bool State)) :=
  match x with
  | (entry, value) =>
    if r.snd.pending = true then
      let out := TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast fast capacity
        (r.snd.response ++ entry ++ [value])
      if (get out 0 == on) = true then
        if (get out 1 == on) = true then
          if (get out 2 == on || r.snd.lenient) = true then
            pure (ForInStep.yield ⟨true, { r.snd with response := [], pending := false }⟩)
          else throw "service response was not a success"
        else pure (ForInStep.yield ⟨r.fst, { r.snd with response := out.drop 6 }⟩)
      else throw "service response rejected or not correlated"
    else pure (ForInStep.yield ⟨r.fst, r.snd⟩)

/-- The message after the byte (its first two payload bytes). -/
def msgAfter (s : State) (byte : Byte) (data : Bool) : List Byte :=
  if (data && decide (s.message.length < 2)) = true then s.message ++ [byte] else s.message

/-- The state `payloadByte` starts its pieces from. -/
def pbStart (s : State) (byte : Byte) (data first : Bool) (flags : List Byte) : State :=
  { s with
    message := msgAfter s byte data,
    held := if first = true then some (flags, byte) else if (msgAfter s byte data).length ≥ 2 then none
      else s.held }

def feedOf (s : State) (byte : Byte) (data first : Bool) (flags : List Byte) : List (List Byte × Byte) :=
  if (!data) = true then [(flags, byte)]
  else if first = true then []
  else if (msgAfter s byte data == [8, 2]) = true then
    (if (s.message.length == 1) = true then s.held.toList else []) ++ [(flags, byte)]
  else []

def kindOK (m : List Byte) : Bool := decide (m.length < 2) || m == [8, 2] || m == [8, 1]

/-- **`payloadByte`, in pieces** (by definition). -/
theorem payloadByte_eq (s : State) (byte : Byte) (data done first : Bool) (flags : List Byte) :
    payloadByte s byte data done first flags =
      if kindOK (msgAfter s byte data) = true then
        if (first && done) = true then throw "one-byte message"
        else
          let go := fun (t : State) =>
            if t.pending = true then
              forIn (feedOf s byte data first flags) (⟨false, t⟩ : MProd Bool State) pbFeedBody >>= fun r =>
                match r with
                | ⟨complete, t⟩ => pbReply (msgAfter s byte data) byte data done complete t
            else pbReply (msgAfter s byte data) byte data done false t
          if ((pbStart s byte data first flags).pending && s.message.length == 1 &&
              msgAfter s byte data == [8, 1]) = true then
            go { pbStart s byte data first flags with response := (pbStart s byte data first flags).rollback }
          else go (pbStart s byte data first flags)
      else throw "server-initiated message of an unknown kind: not revealed further" := by
  rfl

/-! ### What the reveal policy reads of the state -/

/-- The fields the reveal policy and the frame layer read. -/
structure View where
  message : List Byte
  request : List Byte
  bodySkipped : Bool
  skip : Nat
  inner : Option (List Byte × Nat × Nat)
  reply : List Byte
  replySkipped : Bool
  frame : List Byte
  upgraded : Bool
  terminator : Nat
  openBody : Bool

def view (t : State) : View :=
  ⟨t.message, t.request, t.bodySkipped, t.skip, t.inner, t.reply, t.replySkipped, t.frame, t.upgraded,
    t.terminator, t.openBody⟩

theorem view_fields {t u : State} (h : view t = view u) :
    t.message = u.message ∧ t.request = u.request ∧ t.bodySkipped = u.bodySkipped ∧ t.skip = u.skip ∧
    t.inner = u.inner ∧ t.reply = u.reply ∧ t.replySkipped = u.replySkipped ∧ t.frame = u.frame ∧
    t.upgraded = u.upgraded ∧ t.terminator = u.terminator ∧ t.openBody = u.openBody := by
  simp only [view, View.mk.injEq] at h
  exact h

/-- `pendingField` reads only the view. -/
def pendingV (v : View) : Nat :=
  if v.message == [8, 1] then
    match v.inner with
    | some (_, _, remaining) => remaining
    | none => if v.skip > 0 then v.skip else fieldMissing v.request
  else if v.message == [8, 2] then
    if v.skip > 0 then v.skip else replyMissing v.reply v.openBody
  else 0

theorem pendingField_view (t : State) : pendingField t = pendingV (view t) := rfl

theorem pendingField_congr {t u : State} (h : view t = view u) : pendingField t = pendingField u := by
  rw [pendingField_view, pendingField_view, h]

theorem throw_ok {α : Type} {e : String} {a : α} (h : (throw e : Except String α) = .ok a) : False := by
  cases h

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {v : β} (h : (x >>= f) = .ok v) :
    ∃ a, x = .ok a ∧ f a = .ok v := (bind_ok_iff x f v).mp h

/-- What `envelopeAdvance` changes of the view: the walk and `skip`. -/
theorem envelopeAdvance_view {t s2 : State} {H : List Byte} {p r : Nat} (h : envelopeAdvance t H p r = .ok s2) :
    view s2 = { view t with inner := s2.inner, skip := s2.skip } := by
  unfold envelopeAdvance at h
  generalize envelopeScan H p = q at h
  obtain ⟨need, kind, content⟩ := q
  cases need with
  | malformed => cases h
  | more b =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    by_cases hr : (r == 0) = true
    · rw [if_pos hr] at h
      cases b
      · cases h
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        cases h; rfl
    · rw [if_neg hr] at h; cases h; rfl
  | pass n c =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    by_cases hle : n ≤ r
    · simp only [hle, if_true] at h; cases h; rfl
    · simp only [hle, if_false] at h; cases h

/-! ### The pieces, one at a time -/

/-- The message's end. -/
theorem pbDone_view {m : List Byte} {dn c c' : Bool} {t s' : State} (h : pbDone m dn c t = .ok (s', c')) :
    c' = c ∧ ((dn = false ∧ view s' = view t) ∨
      (dn = true ∧ t.skip = 0 ∧ t.inner = none ∧ pendingField t = 0 ∧
        view s' = { view t with
          message := [], request := [], bodySkipped := false, reply := [], replySkipped := false })) := by
  unfold pbDone at h
  by_cases h1 : dn = true
  · rw [if_pos h1] at h
    by_cases h2 : (t.skip == 0 && t.inner.isNone) = true
    · rw [if_pos h2] at h
      by_cases h3 : (pendingField t == 0) = true
      · rw [if_pos h3] at h
        simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h2 h3
        by_cases h4 : (m == [8, 1]) = true
        · rw [if_pos h4] at h; cases h; exact ⟨rfl, Or.inr ⟨h1, h2.1, h2.2, h3, rfl⟩⟩
        · rw [if_neg h4] at h; cases h; exact ⟨rfl, Or.inr ⟨h1, h2.1, h2.2, h3, rfl⟩⟩
      · rw [if_neg h3] at h; exact (throw_ok h).elim
    · rw [if_neg h2] at h; exact (throw_ok h).elim
  · rw [if_neg h1] at h; cases h; exact ⟨rfl, Or.inl ⟨by simpa using h1, rfl⟩⟩

theorem pbCheck_view {m : List Byte} {dn c c' : Bool} {t s' : State} (h : pbCheck m dn c t = .ok (s', c')) :
    overrun t = false ∧ pbDone m dn c t = .ok (s', c') := by
  unfold pbCheck at h
  by_cases hc : overrun t = true
  · unfold overrun at hc; rw [if_pos hc] at h; exact (throw_ok h).elim
  · refine ⟨by simpa using hc, ?_⟩
    unfold overrun at hc; rw [if_neg hc] at h; exact h

/-- The request's revealed bytes after the byte. -/
def reqAfter (t : State) (y : Byte) : List Byte := if t.request.isEmpty = true then [8, 1] else t.request ++ [y]

/-- The response's revealed bytes after the byte. -/
def repAfter (t : State) (y : Byte) : List Byte := if t.reply.isEmpty = true then [8, 2] else t.reply ++ [y]

/-- What a server request's byte does (no envelope being walked): the scanner asks for more; or to pass
over a body that is not a delivered envelope; or the envelope's walk starts. -/
inductive ReqStep (t : State) (y : Byte) (t2 : State) : Prop
  | more : (scan (reqAfter t y) t.bodySkipped).1 = .more → view t2 = { view t with request := reqAfter t y } →
      ReqStep t y t2
  | skip {n : Nat} {f : Fields} : scan (reqAfter t y) t.bodySkipped = (.skip n, f) →
      (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = false →
      view t2 = { view t with request := reqAfter t y, skip := n, bodySkipped := true } → ReqStep t y t2
  | env {n : Nat} {f : Fields} : scan (reqAfter t y) t.bodySkipped = (.skip n, f) →
      (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = true →
      envelopeAdvance { t with request := reqAfter t y, bodySkipped := true } [] 0 n = .ok t2 → ReqStep t y t2

theorem pbRequest_view {m : List Byte} {y : Byte} {data dn c c' : Bool} {t s' : State}
    (h : pbRequest m y data dn c t = .ok (s', c')) :
    ∃ t2, pbCheck m dn c t2 = .ok (s', c') ∧
      (((data && m == [8, 1]) = false ∧ t2 = t) ∨
       ((data && m == [8, 1]) = true ∧
        ((∃ hd p r, t.inner = some (hd, p, r) ∧ 0 < r ∧ envelopeAdvance t (hd ++ [y]) p (r - 1) = .ok t2) ∨
         (t.inner = none ∧ ReqStep t y t2)))) := by
  unfold pbRequest at h
  by_cases h1 : (data && m == [8, 1]) = true
  · rw [if_pos h1] at h
    cases hi : t.inner with
    | some v =>
      obtain ⟨hd, p, r⟩ := v
      rw [hi] at h
      simp only at h
      by_cases hr : r > 0
      · rw [if_pos hr] at h
        obtain ⟨s2, hadv, hk⟩ := bind_ok h
        exact ⟨s2, hk, Or.inr ⟨h1, Or.inl ⟨hd, p, r, rfl, hr, hadv⟩⟩⟩
      · rw [if_neg hr] at h; exact (throw_ok h).elim
    | none =>
      rw [hi] at h
      simp only at h
      generalize hq : scan (if t.request.isEmpty = true then [8, 1] else t.request ++ [y]) t.bodySkipped = q at h
      obtain ⟨need, f⟩ := q
      cases need with
      | malformed => exact (throw_ok h).elim
      | skip count =>
        simp only at h
        by_cases hp : (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = true
        · rw [if_pos hp] at h
          obtain ⟨s2, hadv, hk⟩ := bind_ok h
          exact ⟨s2, hk, Or.inr ⟨h1, Or.inr ⟨rfl, ReqStep.env hq hp hadv⟩⟩⟩
        · rw [if_neg hp] at h
          exact ⟨_, h, Or.inr ⟨h1, Or.inr ⟨rfl, ReqStep.skip hq (by simpa using hp)
            (by simp only [view, reqAfter, hi])⟩⟩⟩
      | more =>
        simp only at h
        exact ⟨_, h, Or.inr ⟨h1, Or.inr ⟨rfl, ReqStep.more (by rw [reqAfter, hq])
          (by simp only [view, reqAfter, hi])⟩⟩⟩
  · rw [if_neg h1] at h
    exact ⟨t, h, Or.inl ⟨by simpa using h1, rfl⟩⟩

/-- What a response's byte does: the scanner asks for more, or to pass over the body. -/
inductive RepStep (t : State) (y : Byte) (t1 : State) : Prop
  | more : (replyScan (repAfter t y) t.replySkipped t.openBody).1 = .more →
      view t1 = { view t with reply := repAfter t y } → RepStep t y t1
  | skip {n : Nat} : (replyScan (repAfter t y) t.replySkipped t.openBody).1 = .skip n →
      view t1 = { view t with reply := repAfter t y, skip := n, replySkipped := true } → RepStep t y t1

theorem pbReply_view {m : List Byte} {y : Byte} {data dn c c' : Bool} {t s' : State}
    (h : pbReply m y data dn c t = .ok (s', c')) :
    ∃ t1, pbRequest m y data dn c t1 = .ok (s', c') ∧
      (((data && m == [8, 2]) = false ∧ t1 = t) ∨ ((data && m == [8, 2]) = true ∧ RepStep t y t1)) := by
  unfold pbReply at h
  by_cases h1 : (data && m == [8, 2]) = true
  · rw [if_pos h1] at h
    generalize hq : replyScan (if t.reply.isEmpty = true then [8, 2] else t.reply ++ [y]) t.replySkipped t.openBody
      = q at h
    obtain ⟨need, f⟩ := q
    cases need with
    | malformed => exact (throw_ok h).elim
    | skip count =>
      simp only at h
      have hs : (replyScan (repAfter t y) t.replySkipped t.openBody).1 = .skip count := by rw [repAfter, hq]
      by_cases hc : c = true
      · rw [if_pos hc] at h
        exact ⟨_, h, Or.inr ⟨h1, RepStep.skip hs rfl⟩⟩
      · rw [if_neg hc] at h
        exact ⟨_, h, Or.inr ⟨h1, RepStep.skip hs rfl⟩⟩
    | more =>
      simp only at h
      have hs : (replyScan (repAfter t y) t.replySkipped t.openBody).1 = .more := by rw [repAfter, hq]
      by_cases hc : c = true
      · rw [if_pos hc] at h
        exact ⟨_, h, Or.inr ⟨h1, RepStep.more hs rfl⟩⟩
      · rw [if_neg hc] at h
        exact ⟨_, h, Or.inr ⟨h1, RepStep.more hs rfl⟩⟩
  · rw [if_neg h1] at h
    exact ⟨t, h, Or.inl ⟨by simpa using h1, rfl⟩⟩

/-- The response parser's loop changes only `response` and `pending`. -/
theorem feed_view (L : List (List Byte × Byte)) : ∀ (init r : MProd Bool State),
    forIn L init pbFeedBody = .ok r → view r.snd = view init.snd
  | init, r, h => by
    have := forIn_keeps (fun t => view t = view init.snd) pbFeedBody (by
      intro x r0 r' hP e
      obtain ⟨entry, value⟩ := x
      unfold pbFeedBody at e
      simp only at e
      by_cases g1 : r0.snd.pending = true
      · rw [if_pos g1] at e
        by_cases g2 : (get (TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast fast capacity
            (r0.snd.response ++ entry ++ [value])) 0 == on) = true
        · rw [if_pos g2] at e
          by_cases g3 : (get (TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast fast capacity
              (r0.snd.response ++ entry ++ [value])) 1 == on) = true
          · rw [if_pos g3] at e
            by_cases g4 : (get (TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast fast capacity
                (r0.snd.response ++ entry ++ [value])) 2 == on || r0.snd.lenient) = true
            · rw [if_pos g4] at e; cases e; exact hP
            · rw [if_neg g4] at e; exact (throw_ok e).elim
          · rw [if_neg g3] at e; cases e; exact hP
        · rw [if_neg g2] at e; exact (throw_ok e).elim
      · rw [if_neg g1] at e; cases e; exact hP) L init r rfl h
    exact this

/-- **`payloadByte` on its view.** When it succeeds, the kind of the message (its first two payload bytes,
`msgAfter`) is a request's, a response's, or not known yet; it is not a one-byte message; and the state
goes through `pbReply` from a state with the view of `pbStart` (the response parser's loop changes
nothing of the view). -/
theorem payloadByte_view {s s' : State} {y : Byte} {data done first : Bool} {flags : List Byte} {c : Bool}
    (h : payloadByte s y data done first flags = .ok (s', c)) :
    kindOK (msgAfter s y data) = true ∧ (first && done) = false ∧
      ∃ t c0, view t = view (pbStart s y data first flags) ∧
        pbReply (msgAfter s y data) y data done c0 t = .ok (s', c) := by
  rw [payloadByte_eq] at h
  by_cases h1 : kindOK (msgAfter s y data) = true
  · rw [if_pos h1] at h
    by_cases h2 : (first && done) = true
    · rw [if_pos h2] at h; exact (throw_ok h).elim
    · rw [if_neg h2] at h
      refine ⟨h1, by simpa using h2, ?_⟩
      simp only at h
      have go : ∀ t : State, view t = view (pbStart s y data first flags) →
          (if t.pending = true then
            forIn (feedOf s y data first flags) (⟨false, t⟩ : MProd Bool State) pbFeedBody >>= fun r =>
              pbReply (msgAfter s y data) y data done r.fst r.snd
          else pbReply (msgAfter s y data) y data done false t) = .ok (s', c) →
          ∃ t c0, view t = view (pbStart s y data first flags) ∧
            pbReply (msgAfter s y data) y data done c0 t = .ok (s', c) := by
        intro t ht e
        by_cases hp : t.pending = true
        · rw [if_pos hp] at e
          obtain ⟨r, hr, hk⟩ := bind_ok e
          have hv := feed_view _ _ r hr
          exact ⟨r.snd, r.fst, hv.trans ht, hk⟩
        · rw [if_neg hp] at e
          exact ⟨t, false, ht, e⟩
      by_cases h3 : ((pbStart s y data first flags).pending && s.message.length == 1 &&
          msgAfter s y data == [8, 1]) = true
      · rw [if_pos h3] at h
        exact go { pbStart s y data first flags with response := (pbStart s y data first flags).rollback } rfl h
      · rw [if_neg h3] at h; exact go _ rfl h
  · rw [if_neg h1] at h; exact (throw_ok h).elim

/-! ### `frameByte`, `stepPassed`, `stepSkipped` -/

/-- **`frameByte` once upgraded**: the frame parser's output is valid, the event is its first 8 bytes,
the state its rest; nothing else of the view changes; nothing was being passed over. -/
theorem frameByte_view {s s1 : State} {b : Byte} {ev : List Byte} (hu : s.upgraded = true)
    (h : frameByte s b = .ok (s1, ev)) :
    s.skip = 0 ∧ get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b])) 0 = on ∧
      ev = (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b])).take 8 ∧
      view s1 = { view s with frame := (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b])).drop 8 } := by
  rw [frameByte_split, frameUpgrade_eq, bind_ok_iff] at h
  obtain ⟨⟨a, s0⟩, h1, h2⟩ := h
  unfold upgradePart at h1
  rw [if_pos hu] at h1
  cases h1
  unfold frameRest at h2
  by_cases g1 : (s.skip == 0) = true
  case neg => simp only [g1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h2
  simp only [g1, ↓reduceIte, pure_bind] at h2
  have h0 : s.skip = 0 := by simpa using g1
  by_cases g2 : (s.pending && s.message.isEmpty && PublicReceive.get s.frame 0 == on) = true
  · simp only [g2, ↓reduceIte] at h2
    by_cases g3 : (get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b])) 0 == on) = true
    · simp only [g3, ↓reduceIte, pure_bind] at h2
      cases h2
      exact ⟨h0, by simpa using g3, rfl, rfl⟩
    · simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h2
  · simp only [g2, Bool.false_eq_true, ↓reduceIte] at h2
    by_cases g3 : (get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b])) 0 == on) = true
    · simp only [g3, ↓reduceIte, pure_bind] at h2
      cases h2
      exact ⟨h0, by simpa using g3, rfl, rfl⟩
    · simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h2

/-- **`stepPassed`**: a response body byte passed over. The frame parser ran on a zero, its output is
valid and a data payload byte; `skip` is one less; at the message's end (only at the body's last byte)
the response is reset. -/
theorem stepPassed_view {s s' : State} {c : Bool} (h : stepPassed s = .ok (s', c)) :
    s.upgraded = true ∧ 0 < s.skip ∧ s.message = [8, 2] ∧
      get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 0 = on ∧
      get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 1 = on ∧
      (((get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 5 == on) = false ∧
        view s' = { view s with
          frame := (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])).drop 8,
          skip := s.skip - 1 }) ∨
       ((get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 5 == on) = true ∧ s.skip - 1 = 0 ∧
        view s' = { view s with
          frame := (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])).drop 8,
          skip := 0, message := [], reply := [], replySkipped := false })) := by
  unfold stepPassed at h
  generalize hF : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) = F at h ⊢
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  by_cases c1 : (s.upgraded && decide (s.skip > 0) && s.message == [8, 2]) = true
  · rw [if_pos c1] at h
    have c1' := c1
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1'
    obtain ⟨⟨hu, hpos⟩, hm⟩ := c1'
    by_cases c2 : (PublicReceive.get F 0 == on && PublicReceive.get F 1 == on) = true
    · rw [if_pos c2] at h
      have c2' := c2
      simp only [Bool.and_eq_true, beq_iff_eq] at c2'
      refine ⟨hu, hpos, hm, c2'.1, c2'.2, ?_⟩
      repeat' (split at h)
      all_goals (try simp only [reduceCtorEq] at h)
      all_goals (try (cases h))
      all_goals first
        | (exact Or.inl ⟨by simp_all, rfl⟩)
        | (refine Or.inr ⟨by simp_all, by simp_all, ?_⟩; simp_all [view])
        | skip
    · rw [if_neg c2] at h; cases h
  · rw [if_neg c1] at h; cases h

/-- **`stepSkipped`, no envelope being walked**: a request body byte passed over. -/
theorem stepSkipped_none {s s' : State} (hi : s.inner = none) (h : stepSkipped s = .ok s') :
    s.upgraded = true ∧ 0 < s.skip ∧ s.message = [8, 1] ∧
      get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 0 = on ∧
      get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 1 = on ∧
      (((get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 5 == on) = false ∧
        view s' = { view s with
          frame := (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])).drop 8,
          skip := s.skip - 1 }) ∨
       ((get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 5 == on) = true ∧ s.skip - 1 = 0 ∧
        view s' = { view s with
          frame := (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])).drop 8,
          skip := 0, message := [], request := [], bodySkipped := false })) := by
  unfold stepSkipped at h
  generalize hF : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) = F at h ⊢
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, hi] at h
  by_cases c1 : (s.upgraded && decide (s.skip > 0) && s.message == [8, 1]) = true
  · rw [if_pos c1] at h
    have c1' := c1
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1'
    obtain ⟨⟨hu, hpos⟩, hm⟩ := c1'
    by_cases c2 : (PublicReceive.get F 0 == on && PublicReceive.get F 1 == on) = true
    · rw [if_pos c2] at h
      have c2' := c2
      simp only [Bool.and_eq_true, beq_iff_eq] at c2'
      refine ⟨hu, hpos, hm, c2'.1, c2'.2, ?_⟩
      repeat' (split at h)
      all_goals (try simp only [reduceCtorEq] at h)
      all_goals (try (cases h))
      all_goals first
        | (refine Or.inl ⟨?_, ?_⟩ <;> simp_all [view]; done)
        | (refine Or.inr ⟨?_, ?_, ?_⟩ <;> simp_all [view]; done)
        | skip
    · rw [if_neg c2] at h; cases h
  · rw [if_neg c1] at h; cases h

/-- **`stepSkipped`, an envelope being walked**: the payload byte passed over; at the payload's last
byte the walk goes on (`envelopeAdvance`), else only the body bytes left go down by one. -/
theorem stepSkipped_some {s s' : State} {hd : List Byte} {p r : Nat} (hi : s.inner = some (hd, p, r))
    (h : stepSkipped s = .ok s') :
    s.upgraded = true ∧ 0 < s.skip ∧ s.message = [8, 1] ∧ 0 < r ∧
      get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 0 = on ∧
      get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 1 = on ∧
      ∃ t2, ((s.skip - 1 ≠ 0 ∧ view t2 = { view s with
              frame := (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])).drop 8,
              skip := s.skip - 1, inner := some (hd, p, r - 1) }) ∨
            (s.skip - 1 = 0 ∧ ∃ t, view t = { view s with
              frame := (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])).drop 8, skip := 0 } ∧
              envelopeAdvance t hd (p + 1) (r - 1) = .ok t2)) ∧
        (((get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 5 == on) = false ∧ view s' = view t2) ∨
         ((get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 5 == on) = true ∧ t2.skip = 0 ∧
          t2.inner = none ∧ view s' = { view t2 with message := [], request := [], bodySkipped := false })) := by
  unfold stepSkipped at h
  generalize hF : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) = F at h ⊢
  by_cases g1 : (s.upgraded && decide (s.skip > 0) && s.message == [8, 1]) = true
  case neg =>
    simp only [g1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  have g1' := g1
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at g1'
  obtain ⟨⟨hu, hpos⟩, hmsg⟩ := g1'
  by_cases g2 : (PublicReceive.get F 0 == on && PublicReceive.get F 1 == on) = true
  case neg =>
    simp only [g1, g2, Bool.false_eq_true, ↓reduceIte, pure_bind, throw_bind_ex, throw_ok_iff] at h
  have g2' := g2
  simp only [Bool.and_eq_true, beq_iff_eq] at g2'
  simp only [g1, g2, ↓reduceIte, pure_bind, hi] at h
  by_cases hr : 0 < r
  case neg =>
    simp only [hr, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  refine ⟨hu, hpos, hmsg, hr, g2'.1, g2'.2, ?_⟩
  simp only [hr, ↓reduceIte, pure_bind] at h
  by_cases hk : s.skip - 1 = 0
  · simp only [hk, beq_self_eq_true, ↓reduceIte] at h
    rw [bind_ok_iff] at h
    obtain ⟨s2, hadv, hrest⟩ := h
    refine ⟨s2, Or.inr ⟨hk, _, ?_, hadv⟩, ?_⟩
    · simp only [view, hk, hi]
    by_cases g5 : (PublicReceive.get F 5 == on) = true
    · simp only [g5, ↓reduceIte] at hrest
      by_cases g6 : (s2.skip == 0 && s2.inner.isNone) = true
      · simp only [g6, ↓reduceIte, pure_bind] at hrest
        cases hrest
        simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at g6
        exact Or.inr ⟨g5, g6.1, g6.2, rfl⟩
      · simp only [g6, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hrest
    · simp only [g5, Bool.false_eq_true, ↓reduceIte] at hrest
      cases hrest
      exact Or.inl ⟨by simpa using g5, rfl⟩
  · have hk' : (s.skip - 1 == 0) = false := by simp only [beq_eq_false_iff_ne]; exact hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte] at h
    by_cases g5 : (PublicReceive.get F 5 == on) = true
    · simp only [g5, hk', Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte, throw_bind_ex,
        throw_ok_iff] at h
    · simp only [g5, Bool.false_eq_true, ↓reduceIte] at h
      cases h
      exact ⟨_, Or.inl ⟨hk, rfl⟩, Or.inl ⟨by simpa using g5, rfl⟩⟩

end ReceiveSimByte

