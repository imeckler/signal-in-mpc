import TlsMpc.Node.Policy.Receive

open TlsMpc TlsMpc.Signal

namespace PublicReceive

/-- The body of `step` before the split (commit 1ae43e3), verbatim. -/
def stepOld (s : State) (byte : Byte) : Except String (State × Bool) := do
  let (activity, s) ← if s.upgraded then pure (on, s) else do
    let out := TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte])
    unless get out 0 == on do throw "WebSocket upgrade response rejected"
    let expected : Byte := if s.terminator % 2 == 0 then 13 else 10
    let terminator := if byte == expected then s.terminator + 1 else if byte == 13 then 1 else 0
    -- The upgrade parser and this count must agree on where the headers end.
    unless (get out 1 == on) == (terminator == 4) do throw "upgrade response headers ended unexpectedly"
    pure (get out 2, { s with upgrade := out.drop 3, upgraded := get out 1 == on, terminator })
  unless s.skip == 0 do throw "a request body byte was revealed"
  let s := if s.pending && s.message.isEmpty && get s.frame 0 == on then { s with rollback := s.response } else s
  let wasFirst := s.message.length == 1
  -- The general frame parser: server requests are data frames too.
  let frame := TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [activity, byte])
  unless get frame 0 == on do throw "WebSocket frame rejected"
  let control := TlsWebSocketControl.run PublicReceive.fast (s.control ++ [get frame 2, get frame 6, get frame 7, byte])
  let data := get frame 1 == on
  let done := get frame 5 == on
  let first := data && s.message.length == 0
  let message := if data && s.message.length < 2 then s.message ++ [byte] else s.message
  unless message.length < 2 || message == [8, 2] || message == [8, 1] do
    throw "server-initiated message of an unknown kind: not revealed further"
  if first && done then throw "one-byte message"
  let flags := [get frame 1, get frame 3, get frame 5]
  -- What the response parser sees: everything except the payload of a request. The first
  -- payload byte waits until the second shows which kind of message this is.
  let feed : List (List Byte × Byte) :=
    if !data then [(flags, byte)]
    else if first then []
    else if message == [8, 2] then (if s.message.length == 1 then s.held.toList else []) ++ [(flags, byte)]
    else []
  let mut s := { s with frame := frame.drop 8, control, message,
                        held := if first then some (flags, byte) else if message.length ≥ 2 then none else s.held }
  let mut complete := false
  -- A server request arriving while a response is awaited: its header bytes were not the
  -- response's.
  if s.pending && wasFirst && message == [8, 1] then s := { s with response := s.rollback }
  if s.pending then
    for (entry, value) in feed do
      if s.pending then
        let out := TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast PublicReceive.fast capacity
          (s.response ++ entry ++ [value])
        unless get out 0 == on do throw "service response rejected or not correlated"
        s := { s with response := out.drop 6 }
        if get out 1 == on then
          unless get out 2 == on || s.lenient do throw "service response was not a success"
          complete := true
          s := { s with pending := false, response := [] }
  if data && message == [8, 2] then
    -- The response's own fields, walked in the clear: its body is passed over, never revealed.
    let reply := if s.reply.isEmpty then [8, 2] else s.reply ++ [byte]
    s := { s with reply }
    match replyScan reply s.replySkipped s.openBody with
    | (.malformed, _) => throw "malformed service response"
    | (.skip count, fields) =>
      -- Kept for the engines only if this is the 200 to the pending prekey fetch.
      let wanted := s.fetch.isSome && fields.id == s.fetch && fields.status == some 200
      s := { s with skip := count, capture := false, collect := wanted, replySkipped := true,
                    bundle := if wanted then some count else s.bundle }
    | (.more, _) => pure ()
    if complete then s := { s with status := ((replyScan s.reply true s.openBody).2.status).getD 0,
                                   retryAfter := if s.openBody then none else retryAfterOf s.reply,
                                   body := if s.openBody then replyBody s.reply else [] }
  if data && message == [8, 1] then
    match s.inner with
    | some (header, passed, remaining) =>
      unless remaining > 0 do throw "envelope state"
      s ← envelopeAdvance s (header ++ [byte]) passed (remaining - 1)
    | none =>
      let request := if s.request.isEmpty then [8, 1] else s.request ++ [byte]
      s := { s with request }
      match scan request s.bodySkipped with
      | (.malformed, _) => throw "malformed server request"
      | (.skip count, fields) =>
        -- A delivered message's body is walked; any other body is passed over whole.
        if fields.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat) then
          s ← envelopeAdvance { s with bodySkipped := true } [] 0 count
        else s := { s with skip := count, capture := false, bodySkipped := true }
      | (.more, _) => pure ()
  if get s.frame 4 == on && get s.frame 8 == on && (get s.frame 7).toNat < 8 &&
      pendingField s > (get s.frame 10).toNat * 256 + (get s.frame 11).toNat then
    throw "a field runs past the end of its message"
  if done then
    unless s.skip == 0 && s.inner.isNone do throw "server request ended inside its body"
    unless pendingField s == 0 do throw "a field runs past the end of its message"
    if message == [8, 1] then s := { s with requests := s.requests ++ [s.request] }
    s := { s with message := [], held := none, request := [], bodySkipped := false, reply := [], replySkipped := false }
  return (s, complete)

theorem get_take8 (l : List Byte) (i : Nat) (h : i < 8) : get (l.take 8) i = get l i := by
  unfold get
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, if_true]

theorem get_take8_1 (l : List Byte) : get (l.take 8) 1 = get l 1 := get_take8 l 1 (by decide)
theorem get_take8_3 (l : List Byte) : get (l.take 8) 3 = get l 3 := get_take8 l 3 (by decide)
theorem get_take8_5 (l : List Byte) : get (l.take 8) 5 = get l 5 := get_take8 l 5 (by decide)

theorem ite_bind' {α β : Type} {c : Prop} [Decidable c] (x y : Except String α) (f : α → Except String β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by split <;> rfl

theorem throw_bind' {α β : Type} (e : String) (f : α → Except String β) :
    ((throw e : Except String α) >>= f) = throw e := rfl

/-- The upgrade part, with its continuation. -/
def upg {β : Type} (s : State) (byte : Byte) (k : Byte → State → Except String β) : Except String β := do
  let (activity, s) ← if s.upgraded then pure (on, s) else do
    let out := TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte])
    unless get out 0 == on do throw "WebSocket upgrade response rejected"
    let expected : Byte := if s.terminator % 2 == 0 then 13 else 10
    let terminator := if byte == expected then s.terminator + 1 else if byte == 13 then 1 else 0
    -- The upgrade parser and this count must agree on where the headers end.
    unless (get out 1 == on) == (terminator == 4) do throw "upgrade response headers ended unexpectedly"
    pure (get out 2, { s with upgrade := out.drop 3, upgraded := get out 1 == on, terminator })
  k activity s

/-- `stepOld` from `let data` on (verbatim). -/
def oldAfter (s : State) (byte : Byte) (frame control : List Byte) : Except String (State × Bool) := do
  let wasFirst := s.message.length == 1
  let data := get frame 1 == on
  let done := get frame 5 == on
  let first := data && s.message.length == 0
  let message := if data && s.message.length < 2 then s.message ++ [byte] else s.message
  unless message.length < 2 || message == [8, 2] || message == [8, 1] do
    throw "server-initiated message of an unknown kind: not revealed further"
  if first && done then throw "one-byte message"
  let flags := [get frame 1, get frame 3, get frame 5]
  let feed : List (List Byte × Byte) :=
    if !data then [(flags, byte)]
    else if first then []
    else if message == [8, 2] then (if s.message.length == 1 then s.held.toList else []) ++ [(flags, byte)]
    else []
  let mut s := { s with frame := frame.drop 8, control, message,
                        held := if first then some (flags, byte) else if message.length ≥ 2 then none else s.held }
  let mut complete := false
  if s.pending && wasFirst && message == [8, 1] then s := { s with response := s.rollback }
  if s.pending then
    for (entry, value) in feed do
      if s.pending then
        let out := TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast PublicReceive.fast capacity
          (s.response ++ entry ++ [value])
        unless get out 0 == on do throw "service response rejected or not correlated"
        s := { s with response := out.drop 6 }
        if get out 1 == on then
          unless get out 2 == on || s.lenient do throw "service response was not a success"
          complete := true
          s := { s with pending := false, response := [] }
  if data && message == [8, 2] then
    let reply := if s.reply.isEmpty then [8, 2] else s.reply ++ [byte]
    s := { s with reply }
    match replyScan reply s.replySkipped s.openBody with
    | (.malformed, _) => throw "malformed service response"
    | (.skip count, fields) =>
      let wanted := s.fetch.isSome && fields.id == s.fetch && fields.status == some 200
      s := { s with skip := count, capture := false, collect := wanted, replySkipped := true,
                    bundle := if wanted then some count else s.bundle }
    | (.more, _) => pure ()
    if complete then s := { s with status := ((replyScan s.reply true s.openBody).2.status).getD 0,
                                   retryAfter := if s.openBody then none else retryAfterOf s.reply,
                                   body := if s.openBody then replyBody s.reply else [] }
  if data && message == [8, 1] then
    match s.inner with
    | some (header, passed, remaining) =>
      unless remaining > 0 do throw "envelope state"
      s ← envelopeAdvance s (header ++ [byte]) passed (remaining - 1)
    | none =>
      let request := if s.request.isEmpty then [8, 1] else s.request ++ [byte]
      s := { s with request }
      match scan request s.bodySkipped with
      | (.malformed, _) => throw "malformed server request"
      | (.skip count, fields) =>
        if fields.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat) then
          s ← envelopeAdvance { s with bodySkipped := true } [] 0 count
        else s := { s with skip := count, capture := false, bodySkipped := true }
      | (.more, _) => pure ()
  if get s.frame 4 == on && get s.frame 8 == on && (get s.frame 7).toNat < 8 &&
      pendingField s > (get s.frame 10).toNat * 256 + (get s.frame 11).toNat then
    throw "a field runs past the end of its message"
  if done then
    unless s.skip == 0 && s.inner.isNone do throw "server request ended inside its body"
    unless pendingField s == 0 do throw "a field runs past the end of its message"
    if message == [8, 1] then s := { s with requests := s.requests ++ [s.request] }
    s := { s with message := [], held := none, request := [], bodySkipped := false, reply := [], replySkipped := false }
  return (s, complete)

/-- `stepOld` after the upgrade part. -/
def oldMid (s : State) (byte activity : Byte) : Except String (State × Bool) := do
  unless s.skip == 0 do throw "a request body byte was revealed"
  let s := if s.pending && s.message.isEmpty && get s.frame 0 == on then { s with rollback := s.response } else s
  let frame := TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [activity, byte])
  unless get frame 0 == on do throw "WebSocket frame rejected"
  let control := TlsWebSocketControl.run PublicReceive.fast (s.control ++ [get frame 2, get frame 6, get frame 7, byte])
  oldAfter s byte frame control

/-- `frameByte` after the upgrade part. -/
def newMid (s : State) (byte activity : Byte) : Except String (State × List Byte) := do
  unless s.skip == 0 do throw "a request body byte was revealed"
  let s := if s.pending && s.message.isEmpty && get s.frame 0 == on then { s with rollback := s.response } else s
  let frame := TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [activity, byte])
  unless get frame 0 == on do throw "WebSocket frame rejected"
  let control := TlsWebSocketControl.run PublicReceive.fast (s.control ++ [get frame 2, get frame 6, get frame 7, byte])
  return ({ s with frame := frame.drop 8, control }, frame.take 8)

/-- `step`'s continuation after `frameByte`. -/
def K (byte : Byte) (r : State × List Byte) : Except String (State × Bool) :=
  payloadByte r.1 byte (get r.2 1 == on) (get r.2 5 == on) ((get r.2 1 == on) && r.1.message.length == 0)
    [get r.2 1, get r.2 3, get r.2 5]

theorem old_split (s : State) (byte : Byte) : stepOld s byte = upg s byte (fun a s1 => oldMid s1 byte a) := rfl

theorem frame_split (s : State) (byte : Byte) : frameByte s byte = upg s byte (fun a s1 => newMid s1 byte a) := rfl

theorem step_split (s : State) (byte : Byte) : step s byte = frameByte s byte >>= K byte := rfl

theorem upg_bind {β γ : Type} (s : State) (byte : Byte) (k : Byte → State → Except String β)
    (f : β → Except String γ) : upg s byte k >>= f = upg s byte (fun a s1 => k a s1 >>= f) := by
  unfold upg
  cases s.upgraded
  · simp only [Bool.false_eq_true, ↓reduceIte]
    generalize TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte]) = out
    by_cases h1 : (get out 0 == on) = true
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals rfl
    · simp only [h1, Bool.not_false, ↓reduceIte]; rfl
  · rfl

theorem after_eq (s : State) (byte : Byte) (F control : List Byte) :
    payloadByte { s with frame := F.drop 8, control } byte (get F 1 == on) (get F 5 == on)
      ((get F 1 == on) && s.message.length == 0) [get F 1, get F 3, get F 5] = oldAfter s byte F control := rfl

theorem mid_eq (s : State) (byte a : Byte) : newMid s byte a >>= K byte = oldMid s byte a := by
  unfold newMid oldMid
  by_cases h1 : (s.skip == 0) = true
  · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize (if (s.pending && s.message.isEmpty && get s.frame 0 == on) = true then
      { s with rollback := s.response } else s) = s2
    generalize TlsWebSocketFrame.runByte PublicReceive.fast capacity (s2.frame ++ [a, byte]) = F
    by_cases h2 : (get F 0 == on) = true
    · simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      show K byte ({ s2 with frame := F.drop 8, control := _ }, F.take 8) = _
      unfold K
      dsimp only
      rw [get_take8_1, get_take8_3, get_take8_5]
      exact after_eq s2 byte F _
    · simp only [h2, Bool.not_false, ↓reduceIte]; rfl
  · simp only [h1, Bool.not_false, ↓reduceIte]; rfl

/-- **The split computes the same function.** -/
theorem step_eq (s : State) (byte : Byte) : step s byte = stepOld s byte := by
  rw [step_split, frame_split, upg_bind, old_split]
  congr 1
  funext a s1
  exact mid_eq s1 byte a

end PublicReceive

#print axioms PublicReceive.step_eq
