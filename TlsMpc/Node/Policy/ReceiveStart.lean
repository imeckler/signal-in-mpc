import TlsMpc.Node.Policy.ReceiveSession
import TlsMpc.Node.Policy.ReceiveHead

/-!
# T1 from the first byte of a connection (PROOF_GAPS.md D1)

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`ReceiveLoop.t1_all` starts after the upgrade (`{ start accept with upgraded := true }`, against
`ReceiveSpec.classifyFrames`). A fresh connection starts in `PublicReceive.start accept`, not upgraded:
the server first sends the HTTP upgrade response's head, up to CR LF CR LF, then WebSocket frames, and
a record may hold the end of the head and the first frames. This file joins the two phases, against
the full reference `ReceiveSpec.classify` (head, then frames), in its byte-by-byte form
`ReceiveStream.classifyStream` (`runAll` from `.head 0`: `classify_stream`).

**The session's start states** (`Session/*.lean`): `readUpgrade` (`Pool.lean`, the recovery path's
connections) `{ start expected with lenient := true }`; `openCircuits` (`Pool.lean`) and `Send.lean`
`{ start accept with lenient := c.exportPath.isSome }`; `Receive.lean` `start accept`; the
registration ceremony (`Ceremony.lean`) `{ start accept with lenient := true, openBody := true }`.
Every one is `{ PublicReceive.start accept with lenient, openBody }` for some `accept`, `lenient`,
`openBody`, which is what the theorems below take. Between records the session applies `replies`
(and, during the upgrade, nothing else; afterwards `requests := []`, `expect`, the fetch fields).

**The two lemmas D1 asked for** (about the deployed `frameByte` / `payloadByte` / `step`):

* (i) **`frameByte_head`**: before the upgrade, while the upgrade parser has not completed (its
  serialised state's completion byte, index 6, is not 255; true at `start` and kept by every byte that
  does not complete it: `upgradeByte`), the upgrade parser's activity byte is not 255, so the frame
  parser gets an inactive byte: it either refuses it or leaves its state exactly as it was, and its
  event says "not data, not the end of a message" (`frameIdle`, `frameRefuses`). So the head's bytes
  leave the frame parser at its start state, a frame boundary.
* (ii) **`payloadByte_head`**: `payloadByte` on a byte that is not data and does not end a message keeps
  the whole view (`upgraded`, `terminator`, the frame state, the clean message side) and the upgrade
  parser's state.

**The relation.** `HeadSim ob s k` (before the upgrade: not upgraded, `terminator = k ≤ 3`, frame parser
at its start state, no message, nothing tracked, the upgrade parser not completed); `SimAll` is
`HeadSim` against the reference's `.head k` and `ReceiveSim.Sim` against `.frames st`. `headStep`:
every accepted byte keeps it, and the byte that completes CR LF CR LF gives the frame-phase `Sim` at
`Stream.init` (`simBoundary`). `headWindow`: a run before the upgrade (at most `budget s = 4 - k`
bytes) is all `head` in the reference (`headRunAll`), and can complete the head only at its last byte.

**The loop.** `loopStart_good` is `ReceiveLoop.loop_good` over `SimAll` (the head phase; the frame
phase is `loop_good` itself), `sessionStart_good` the session's records (`sessionGo`, the deployed
`RecordLoop.run` through `loop_sub`), with steps between records that keep the view and the upgrade
parser's state (`KeepsHead`; the session's steps do: `keepsHead_afterRecord`, `keepsHead_expect`,
`keepsHead_pure`, `keepsHead_bind`).

**`t1_start`**: for every `accept`, `lenient`, `openBody`, every stream cut into records in any way,
every stream position the session's record loop reveals on a fresh connection is allowed by
`ReceiveSpec.classify openBody` or is its first `error`. Assumptions: the engines are `Faithful` (D8)
and the steps between records keep the view and the upgrade parser's state. `t1_start_model`: the same
for the model loop (`streamRun`).
-/

open TlsMpc TlsMpc.Signal

namespace ReceiveStart

open PublicReceive ReceiveProofs ReceiveStream ReceiveSimByte ReceiveSim ReceiveLoop
open TlsMpc.KernelSpecs.ParseWebSocketFrame (Shaped mb eq_mb not_ones not_zero and_zero_r and_zero_l
  and_ones_r and_ones_l stateBytes_length readState_stateBytes step_shaped start_boundary)

/-! ### Bytes -/

theorem and_on {x y : Byte} (h : fast.and x y = on) : y = on := by
  rw [PublicReceive.PassOver.fast_and] at h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_and] at h1
  have h2 : x.toNat &&& y.toNat ≤ y.toNat := Nat.and_le_right
  have h3 := y.isLt
  have h4 : (on : Byte).toNat = 255 := rfl
  rw [h4] at h1
  apply BitVec.eq_of_toNat_eq
  rw [h4]
  omega

theorem get_conv (xs : List Byte) (i : Nat) : TlsWebSocketUpgrade.get fast xs i = PublicReceive.get xs i := by
  unfold TlsWebSocketUpgrade.get PublicReceive.get
  rw [List.getD_eq_getElem?_getD, PublicReceive.PassOver.fast_const]
  rfl

theorem get_take7 (U : List Byte) : PublicReceive.get (U.take 7) 6 = PublicReceive.get U 6 := by
  unfold PublicReceive.get
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
  rfl

theorem get_cons2 (a b c : Byte) (L : List Byte) : PublicReceive.get (a :: b :: c :: L) 2 = c := rfl
theorem get_cons1 (a b c : Byte) (L : List Byte) : PublicReceive.get (a :: b :: c :: L) 1 = b := rfl
theorem drop_cons3 (a b c : Byte) (L : List Byte) : (a :: b :: c :: L).drop 3 = L := rfl

/-! ### The upgrade parser: its activity byte before it completes -/

/-- `runByte`'s pieces (its `let`s, named). -/
def upgS (raw : List Byte) : TlsWebSocketUpgrade.State Byte :=
  TlsWebSocketUpgrade.readState fast (raw.take TlsWebSocketUpgrade.stateSize)

def upgActive (raw : List Byte) : Byte := TlsWebSocketUpgrade.get fast raw (TlsWebSocketUpgrade.stateSize + 28)

def upgNext (raw : List Byte) : TlsWebSocketUpgrade.State Byte :=
  TlsWebSocketUpgrade.stateSelect fast (TlsWebSocketUpgrade.eq fast (upgActive raw) 255)
    (TlsWebSocketUpgrade.step fast ((raw.drop TlsWebSocketUpgrade.stateSize).take 28) 0 (upgS raw)
      (TlsWebSocketUpgrade.get fast raw (TlsWebSocketUpgrade.stateSize + 29))) (upgS raw)

def upgValid (raw : List Byte) : Byte :=
  fast.and (upgNext raw).valid (TlsWebSocketUpgrade.either fast (TlsWebSocketUpgrade.eq fast (upgActive raw) 0)
    (TlsWebSocketUpgrade.eq fast (upgActive raw) 255))

theorem upg_runByte (raw : List Byte) : TlsWebSocketUpgrade.runByte fast raw =
    upgValid raw :: TlsWebSocketUpgrade.get fast (upgNext raw).phases 6 ::
      fast.and (upgValid raw) (fast.and (upgActive raw) (TlsWebSocketUpgrade.get fast (upgS raw).phases 6)) ::
      TlsWebSocketUpgrade.stateBytes { upgNext raw with valid := upgValid raw } := by
  unfold TlsWebSocketUpgrade.runByte
  rfl

theorem stateSize_ge : 7 ≤ TlsWebSocketUpgrade.stateSize := by
  unfold TlsWebSocketUpgrade.stateSize; omega

theorem upgS_phases (raw : List Byte) : (upgS raw).phases = (raw.take TlsWebSocketUpgrade.stateSize).take 7 := rfl

theorem step_phases_len (e : List Byte) (o : Nat) (s : TlsWebSocketUpgrade.State Byte) (x : Byte) :
    (TlsWebSocketUpgrade.step fast e o s x).phases.length = 7 := rfl

theorem upgNext_phases_len (raw : List Byte) (h : 7 ≤ raw.length) : (upgNext raw).phases.length = 7 := by
  unfold upgNext
  simp only [TlsWebSocketUpgrade.stateSelect, TlsWebSocketUpgrade.choose, List.length_zipWith, step_phases_len,
    upgS_phases, List.length_take]
  have := stateSize_ge
  omega

/-- The serialised upgrade state starts with its phases. -/
theorem upg_stateBytes (R : TlsWebSocketUpgrade.State Byte) :
    TlsWebSocketUpgrade.stateBytes R = R.phases ++ ([R.valid] ++ R.status ++ [R.reason] ++ R.name.flatten ++
      [R.nameNonempty] ++ R.kinds ++ R.seen ++ TlsWebSocketUpgrade.tokenBytes R.upgrade ++
      TlsWebSocketUpgrade.tokenBytes R.connection ++ R.accept ++
      [R.acceptLeading, R.acceptTrailing, R.consumedHi, R.consumedLo]) := by
  unfold TlsWebSocketUpgrade.stateBytes
  simp only [List.append_assoc]

/-- **The upgrade parser before it completes.** If the serialised state `U` (at least 7 bytes) has not
completed (its byte 6, the completion phase, is not 255), then on any byte the activity byte it hands the
frame parser is not 255, and the new serialised state's byte 6 is the completion output (byte 1). -/
theorem upgradeByte (U A : List Byte) (x : Byte) (hU : 7 ≤ U.length) (h6 : PublicReceive.get U 6 ≠ on) :
    PublicReceive.get (TlsWebSocketUpgrade.runByte fast (U ++ A ++ [on, x])) 2 ≠ on ∧
    7 ≤ ((TlsWebSocketUpgrade.runByte fast (U ++ A ++ [on, x])).drop 3).length ∧
    PublicReceive.get ((TlsWebSocketUpgrade.runByte fast (U ++ A ++ [on, x])).drop 3) 6 =
      PublicReceive.get (TlsWebSocketUpgrade.runByte fast (U ++ A ++ [on, x])) 1 := by
  rw [upg_runByte, get_cons2, get_cons1, drop_cons3]
  have hlen : 7 ≤ (U ++ A ++ [on, x]).length := by simp only [List.length_append]; omega
  have hp6 : TlsWebSocketUpgrade.get fast (upgS (U ++ A ++ [on, x])).phases 6 = PublicReceive.get U 6 := by
    rw [upgS_phases, List.take_take, Nat.min_eq_left stateSize_ge, List.append_assoc,
      List.take_append_of_le_length hU, get_conv, get_take7]
  have hR := upgNext_phases_len (U ++ A ++ [on, x]) hlen
  refine ⟨fun e => h6 (hp6 ▸ and_on (and_on e)), ?_, ?_⟩
  · rw [upg_stateBytes, List.length_append]
    show 7 ≤ (upgNext (U ++ A ++ [on, x])).phases.length + _
    omega
  · rw [upg_stateBytes, get_conv]
    show PublicReceive.get ((upgNext (U ++ A ++ [on, x])).phases ++ _) 6 = _
    rw [get_app_left _ _ 6 (by omega)]

/-- The upgrade parser's starting state has not completed. -/
theorem start_upgrade :
    7 ≤ (TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start fast)).length ∧
    PublicReceive.get (TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start fast)) 6 ≠ on := by
  have hl : (TlsWebSocketUpgrade.start fast).phases.length = 7 := rfl
  rw [upg_stateBytes]
  refine ⟨by rw [List.length_append, hl]; omega, ?_⟩
  rw [get_app_left _ _ 6 (by rw [hl]; omega)]
  decide

/-! ### The frame parser on an inactive byte -/

theorem stateSelect_zero (yes no : TlsWebSocketFrame.State Byte) (hy : Shaped yes) (hn : Shaped no) :
    TlsWebSocketFrame.stateSelect fast 0#8 yes no = no := by
  obtain ⟨y5, y8⟩ := hy
  obtain ⟨n5, n8⟩ := hn
  simp only [TlsWebSocketFrame.stateSelect, PublicReceive.PassOver.select_zero',
    PublicReceive.PassOver.choose_zero yes.phases no.phases (by omega),
    PublicReceive.PassOver.choose_zero yes.utfPhases no.utfPhases (by omega)]

/-- **An inactive byte** (activity 0): the frame parser's state is unchanged, its event is empty. -/
theorem frameIdle (cap : Nat) (S : TlsWebSocketFrame.State Byte) (h : Shaped S) (x : Byte) :
    TlsWebSocketFrame.runByte fast cap (TlsWebSocketFrame.stateBytes S ++ [0#8, x]) =
      S.valid :: ([0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++ TlsWebSocketFrame.stateBytes S) := by
  have hl := stateBytes_length S h
  unfold TlsWebSocketFrame.runByte
  have t : (TlsWebSocketFrame.stateBytes S ++ [0#8, x]).take TlsWebSocketFrame.stateSize =
      TlsWebSocketFrame.stateBytes S := by
    rw [TlsWebSocketFrame.stateSize, ← hl, List.take_left]
  have g1 : TlsWebSocketUpgrade.get fast (TlsWebSocketFrame.stateBytes S ++ [0#8, x]) TlsWebSocketFrame.stateSize =
      0#8 := by
    simp [TlsWebSocketUpgrade.get, TlsWebSocketFrame.stateSize, hl]
  have g2 : TlsWebSocketUpgrade.get fast (TlsWebSocketFrame.stateBytes S ++ [0#8, x])
      (TlsWebSocketFrame.stateSize + 1) = x := by
    simp [TlsWebSocketUpgrade.get, TlsWebSocketFrame.stateSize, hl]
  have e255 : TlsWebSocketUpgrade.eq fast 0#8 255 = 0#8 := by rw [eq_mb]; rfl
  have e0 : TlsWebSocketUpgrade.eq fast 0#8 0 = 255#8 := by rw [eq_mb]; rfl
  simp only [t, g1, g2, readState_stateBytes S h, e255, e0,
    stateSelect_zero _ _ (step_shaped cap S x h) h, TlsWebSocketUpgrade.either, not_ones, not_zero,
    and_zero_r, and_zero_l, and_ones_r, ByteAuth.release, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  try rfl

/-- **An activity byte that is neither 0 nor 255**: the frame parser's validity byte is 0. -/
theorem frameRefuses (cap : Nat) (S : TlsWebSocketFrame.State Byte) (h : Shaped S) {a : Byte} (h0 : a ≠ 0)
    (h1 : a ≠ on) (x : Byte) :
    PublicReceive.get (TlsWebSocketFrame.runByte fast cap (TlsWebSocketFrame.stateBytes S ++ [a, x])) 0 = 0 := by
  have hl := stateBytes_length S h
  have g1 : TlsWebSocketUpgrade.get fast (TlsWebSocketFrame.stateBytes S ++ [a, x]) TlsWebSocketFrame.stateSize =
      a := by
    simp [TlsWebSocketUpgrade.get, TlsWebSocketFrame.stateSize, hl]
  have e0 : TlsWebSocketUpgrade.eq fast a 0 = 0#8 := by
    rw [eq_mb]
    have : (a == BitVec.ofNat 8 0) = false := beq_eq_false_iff_ne.mpr h0
    rw [this]; rfl
  have e255 : TlsWebSocketUpgrade.eq fast a 255 = 0#8 := by
    rw [eq_mb]
    have : (a == BitVec.ofNat 8 255) = false := beq_eq_false_iff_ne.mpr h1
    rw [this]; rfl
  unfold TlsWebSocketFrame.runByte
  simp only [g1, e0, e255, TlsWebSocketUpgrade.either, not_zero, and_ones_l, not_ones, and_zero_r]
  rfl

/-! ### Lemma (i): `frameByte` before the upgrade -/

/-- `upgradePart` before the upgrade, the upgrade parser not completed: the activity byte is not 255;
if the byte does not complete it either, the new state has not completed. -/
theorem upgradePart_head {s s0 : State} {b a : Byte} (hu : s.upgraded = false) (hl : 7 ≤ s.upgrade.length)
    (h6 : PublicReceive.get s.upgrade 6 ≠ on) (h : upgradePart s b = .ok (a, s0)) :
    a ≠ on ∧ (s0.upgraded = false → 7 ≤ s0.upgrade.length ∧ PublicReceive.get s0.upgrade 6 ≠ on) := by
  have key := upgradeByte s.upgrade s.accept b hl h6
  unfold upgradePart at h
  simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
  generalize TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, b]) = out at h key
  by_cases g0 : (PublicReceive.get out 0 == on) = true
  case neg => simp only [g0, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  simp only [g0, ↓reduceIte, pure_bind] at h
  rcases ite_ok h with h | h
  · cases h
    refine ⟨key.1, fun hf => ⟨key.2.1, ?_⟩⟩
    rw [key.2.2]
    simpa using hf
  · simp only [throw_bind_ex, throw_ok_iff] at h

/-- `frameRest` on a byte whose activity is not 255, from a shaped frame state: the frame state and the
whole view are kept, and the event says "not data, not the end of a message". -/
theorem frameRest_head {s s2 : State} {b a : Byte} {ev : List Byte} {S : TlsWebSocketFrame.State Byte}
    (hS : Shaped S) (hf : s.frame = TlsWebSocketFrame.stateBytes S) (ha : a ≠ on)
    (h : frameRest s b a = .ok (s2, ev)) :
    view s2 = view s ∧ s2.upgrade = s.upgrade ∧ PublicReceive.get ev 1 = 0 ∧ PublicReceive.get ev 5 = 0 := by
  have hF : ∀ F, TlsWebSocketFrame.runByte fast capacity (s.frame ++ [a, b]) = F → PublicReceive.get F 0 = on →
      F.drop 8 = s.frame ∧ PublicReceive.get (F.take 8) 1 = 0 ∧ PublicReceive.get (F.take 8) 5 = 0 := by
    intro F e g
    rw [hf] at e ⊢
    by_cases ha0 : a = 0
    · subst ha0
      rw [show (0 : Byte) = 0#8 from rfl, frameIdle capacity S hS b] at e
      subst e
      exact ⟨rfl, rfl, rfl⟩
    · have hb := frameRefuses capacity S hS ha0 ha b
      rw [e] at hb
      rw [hb] at g
      exact absurd g (by decide)
  unfold frameRest at h
  by_cases g1 : (s.skip == 0) = true
  case neg => simp only [g1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  simp only [g1, ↓reduceIte, pure_bind] at h
  by_cases g2 : (s.pending && s.message.isEmpty && PublicReceive.get s.frame 0 == on) = true
  · simp only [g2, ↓reduceIte] at h
    generalize hFe : TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [a, b]) = F at h
    by_cases g3 : (PublicReceive.get F 0 == on) = true
    case neg => simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
    simp only [g3, ↓reduceIte] at h
    cases h
    obtain ⟨d, e1, e5⟩ := hF F hFe (beq_iff_eq.mp g3)
    exact ⟨by simp only [view, d], rfl, e1, e5⟩
  · simp only [g2, Bool.false_eq_true, ↓reduceIte] at h
    generalize hFe : TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [a, b]) = F at h
    by_cases g3 : (PublicReceive.get F 0 == on) = true
    case neg => simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
    simp only [g3, ↓reduceIte] at h
    cases h
    obtain ⟨d, e1, e5⟩ := hF F hFe (beq_iff_eq.mp g3)
    exact ⟨by simp only [view, d], rfl, e1, e5⟩

/-- **Before the upgrade** (the controller's state not upgraded, its count `k ≤ 3`, frame parser at its
start state, no message, nothing tracked; the upgrade parser not completed). -/
structure HeadSim (ob : Bool) (s : State) (k : Nat) : Prop where
  up : s.upgraded = false
  term : s.terminator = k
  le : k ≤ 3
  openBody : s.openBody = ob
  frame : s.frame = TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start fast capacity)
  message : s.message = []
  clean : Clean s
  upLen : 7 ≤ s.upgrade.length
  up6 : PublicReceive.get s.upgrade 6 ≠ on

/-- **Lemma (i): the head's bytes leave the frame parser at its start state.** Before the upgrade,
`frameByte` keeps the whole view but `upgraded` and `terminator` (which move as the reference's matcher
does: `ReceiveHead.frameByte_terminator`), so the frame parser stays at its start state (a frame
boundary); the byte's event is neither data nor the end of a message; and unless the byte completed the
upgrade, the upgrade parser has still not completed. -/
theorem frameByte_head {ob : Bool} {s s1 : State} {b : Byte} {ev : List Byte} {k : Nat} (hs : HeadSim ob s k)
    (h : frameByte s b = .ok (s1, ev)) :
    view s1 = { view s with upgraded := s1.upgraded, terminator := s1.terminator } ∧
      s1.terminator = Head.next k b ∧ (s1.upgraded = true ↔ Head.next k b = 4) ∧
      PublicReceive.get ev 1 = 0 ∧ PublicReceive.get ev 5 = 0 ∧
      (s1.upgraded = false → 7 ≤ s1.upgrade.length ∧ PublicReceive.get s1.upgrade 6 ≠ on) := by
  obtain ⟨t1, t2⟩ := ReceiveHead.frameByte_terminator hs.up h
  rw [hs.term] at t1 t2
  rw [frameByte_split, frameUpgrade_eq, bind_ok_iff] at h
  obtain ⟨⟨a, s0⟩, h1, h2⟩ := h
  obtain ⟨ha, hinv⟩ := upgradePart_head hs.up hs.upLen hs.up6 h1
  obtain ⟨u, ud, t, rfl⟩ := upgradePart_ok h1
  dsimp only at h2
  obtain ⟨hv, hupg, e1, e5⟩ := frameRest_head (start_boundary capacity).1 (by exact hs.frame) ha h2
  have eu : s1.upgraded = ud := congrArg View.upgraded hv
  have et : s1.terminator = t := congrArg View.terminator hv
  refine ⟨?_, t1, t2, e1, e5, fun hf => ?_⟩
  · rw [hv, eu, et]; rfl
  · rw [hupg]; exact hinv (eu ▸ hf)

/-! ### Lemma (ii): `payloadByte` on a byte that is not data -/

/-- The response parser's loop keeps the upgrade parser's state. -/
theorem feed_upgrade (L : List (List Byte × Byte)) (init r : MProd Bool State)
    (h : forIn L init pbFeedBody = .ok r) : r.snd.upgrade = init.snd.upgrade :=
  forIn_keeps (fun t => t.upgrade = init.snd.upgrade) pbFeedBody (by
    intro x r0 r' hP e
    obtain ⟨entry, value⟩ := x
    unfold pbFeedBody at e
    simp only at e
    by_cases g1 : r0.snd.pending = true
    · rw [if_pos g1] at e
      by_cases g2 : (PublicReceive.get (TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast fast capacity
          (r0.snd.response ++ entry ++ [value])) 0 == on) = true
      · rw [if_pos g2] at e
        by_cases g3 : (PublicReceive.get (TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast fast capacity
            (r0.snd.response ++ entry ++ [value])) 1 == on) = true
        · rw [if_pos g3] at e
          by_cases g4 : (PublicReceive.get (TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast fast capacity
              (r0.snd.response ++ entry ++ [value])) 2 == on || r0.snd.lenient) = true
          · rw [if_pos g4] at e; cases e; exact hP
          · rw [if_neg g4] at e; exact (throw_ok e).elim
        · rw [if_neg g3] at e; cases e; exact hP
      · rw [if_neg g2] at e; exact (throw_ok e).elim
    · rw [if_neg g1] at e; cases e; exact hP) L init r rfl h

/-- `payloadByte_view`, also keeping the upgrade parser's state. -/
theorem payloadByte_keep {s s' : State} {y : Byte} {data done first : Bool} {flags : List Byte} {c : Bool}
    (h : payloadByte s y data done first flags = .ok (s', c)) :
    ∃ t c0, view t = view (pbStart s y data first flags) ∧ t.upgrade = s.upgrade ∧
      pbReply (msgAfter s y data) y data done c0 t = .ok (s', c) := by
  rw [payloadByte_eq] at h
  by_cases h1 : kindOK (msgAfter s y data) = true
  · rw [if_pos h1] at h
    by_cases h2 : (first && done) = true
    · rw [if_pos h2] at h; exact (throw_ok h).elim
    · rw [if_neg h2] at h
      simp only at h
      have go : ∀ t : State, view t = view (pbStart s y data first flags) → t.upgrade = s.upgrade →
          (if t.pending = true then
            forIn (feedOf s y data first flags) (⟨false, t⟩ : MProd Bool State) pbFeedBody >>= fun r =>
              pbReply (msgAfter s y data) y data done r.fst r.snd
          else pbReply (msgAfter s y data) y data done false t) = .ok (s', c) →
          ∃ t c0, view t = view (pbStart s y data first flags) ∧ t.upgrade = s.upgrade ∧
            pbReply (msgAfter s y data) y data done c0 t = .ok (s', c) := by
        intro t ht hu e
        by_cases hp : t.pending = true
        · rw [if_pos hp] at e
          obtain ⟨r, hr, hk⟩ := ReceiveSimByte.bind_ok e
          exact ⟨r.snd, r.fst, (feed_view _ _ r hr).trans ht, (feed_upgrade _ _ r hr).trans hu, hk⟩
        · rw [if_neg hp] at e
          exact ⟨t, false, ht, hu, e⟩
      by_cases h3 : ((pbStart s y data first flags).pending && s.message.length == 1 &&
          msgAfter s y data == [8, 1]) = true
      · rw [if_pos h3] at h
        exact go { pbStart s y data first flags with response := (pbStart s y data first flags).rollback } rfl rfl h
      · rw [if_neg h3] at h; exact go _ rfl rfl h
  · rw [if_neg h1] at h; exact (throw_ok h).elim

/-- **Lemma (ii): `payloadByte` on a byte that is neither data nor the end of a message keeps the whole
view** (so `upgraded`, `terminator`, the frame state and the message side) **and the upgrade parser's
state**. -/
theorem payloadByte_head {s s' : State} {y : Byte} {first : Bool} {flags : List Byte} {c : Bool}
    (h : payloadByte s y false false first flags = .ok (s', c)) : view s' = view s ∧ s'.upgrade = s.upgrade := by
  obtain ⟨t, c0, hv, hu, e⟩ := payloadByte_keep h
  obtain ⟨t1, e1, hc1⟩ := pbReply_view e
  have ht1 : t1 = t := by
    rcases hc1 with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · simp at h1
  subst ht1
  obtain ⟨t2, e2, hc2⟩ := pbRequest_view e1
  have ht2 : t2 = t1 := by
    rcases hc2 with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact h2
    · simp at h2
  subst ht2
  obtain ⟨-, e3⟩ := pbCheck_view e2
  simp only [pbDone, Bool.false_eq_true, if_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e3
  obtain ⟨rfl, -⟩ := e3
  refine ⟨hv.trans ?_, hu⟩
  have hm : (pbStart s y false first flags).message = s.message := by simp [pbStart, msgAfter]
  unfold view
  rw [hm]
  rfl

/-! ### One byte before the upgrade -/

theorem fields_of {s t : State} {u : Bool} {k : Nat} (h : view t = { view s with upgraded := u, terminator := k }) :
    t.upgraded = u ∧ t.terminator = k ∧ t.openBody = s.openBody ∧ t.frame = s.frame ∧ t.message = s.message ∧
      (Clean s → Clean t) :=
  ⟨congrArg View.upgraded h, congrArg View.terminator h, congrArg View.openBody h, congrArg View.frame h,
    congrArg View.message h, fun c => ⟨(congrArg View.skip h).trans c.skip, (congrArg View.inner h).trans c.inner,
      (congrArg View.reply h).trans c.reply, (congrArg View.replySkipped h).trans c.replySkipped,
      (congrArg View.request h).trans c.request, (congrArg View.bodySkipped h).trans c.bodySkipped⟩⟩

/-- At a frame boundary with nothing tracked, once upgraded: the frame-phase relation at the reference's
initial state (as `ReceiveLoop.start_sim`). -/
theorem simBoundary {ob : Bool} {t : State} (hu : t.upgraded = true) (hob : t.openBody = ob)
    (hf : t.frame = TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start fast capacity)) (hm : t.message = [])
    (hc : Clean t) (n : Nat) : Sim ob t Stream.init n :=
  ⟨rfl, hu, hob, ⟨TlsWebSocketFrame.start fast capacity, hf,
    ⟨(start_boundary capacity).1, rfl, (start_boundary capacity).2⟩⟩, MsgSim.empty hm hc, trivial⟩

/-- **Every byte the controller accepts before the upgrade**: the byte that completes CR LF CR LF gives
the frame-phase relation at the reference's initial state; any other keeps `HeadSim` with the reference's
count. -/
theorem headStep {ob : Bool} {s s' : State} {b : Byte} {c : Bool} {k : Nat} (hs : HeadSim ob s k)
    (h : step s b = .ok (s', c)) :
    (Head.next k b = 4 → ∀ n, Sim ob s' Stream.init n) ∧ (Head.next k b ≠ 4 → HeadSim ob s' (Head.next k b)) := by
  obtain ⟨s1, ev, h1, -, h2⟩ := step_ok h
  obtain ⟨hv1, ht, hup, e1, e5, hinv⟩ := frameByte_head hs h1
  rw [e1, e5] at h2
  have z : ((0 : Byte) == on) = false := by decide
  rw [z, Bool.false_and] at h2
  obtain ⟨hv2, hu2⟩ := payloadByte_head h2
  rw [hv1] at hv2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fields_of hv2
  refine ⟨fun h4 n => simBoundary (f1.trans (hup.mpr h4)) (f3.trans hs.openBody) (f4.trans hs.frame)
    (f5.trans hs.message) (f6 hs.clean) n, fun h4 => ?_⟩
  have hu1 : s1.upgraded = false := by
    cases e : s1.upgraded
    · rfl
    · exact absurd (hup.mp e) h4
  obtain ⟨l7, g6⟩ := hinv hu1
  have hle := ReceiveHead.next_le k b
  have hk := hs.le
  exact ⟨f1.trans hu1, f2.trans ht, by omega, f3.trans hs.openBody, f4.trans hs.frame, f5.trans hs.message,
    f6 hs.clean, by rw [hu2]; exact l7, by rw [hu2]; exact g6⟩

/-! ### The relation over both phases -/

/-- The controller's state against the reference's, before the upgrade (`.head k`) or after (`.frames st`). -/
def SimAll (ob : Bool) (s : State) : AllSt → Nat → Prop
  | .head k, _ => HeadSim ob s k
  | .frames st, n => Sim ob s st n

/-- The reference's classes `C` of the whole stream (head included), seen from stream position `p`. -/
def GA (ob : Bool) (C : List ReceiveSpec.Class) (p : Nat) (a : AllSt) (W : List Byte) : Prop :=
  ∃ Cp : List ReceiveSpec.Class, C = Cp ++ runAll ob a W ∧ Cp.length = p ∧ ∀ x ∈ Cp, x ≠ .error

theorem ga_frames {ob : Bool} {C : List ReceiveSpec.Class} {p : Nat} {st : Stream.St × Bool} {W : List Byte} :
    GA ob C p (.frames st) W ↔ G ob C p st W := by
  unfold GA G; rw [runAll_frames]

theorem ga_head_step {ob : Bool} {C : List ReceiveSpec.Class} {p k : Nat} {b : Byte} {W : List Byte}
    (h : GA ob C p (.head k) (b :: W)) :
    GA ob C (p + 1) (if Head.next k b = 4 then .frames Stream.init else .head (Head.next k b)) W := by
  obtain ⟨Cp, hC, hl, hn⟩ := h
  refine ⟨Cp ++ [.head], ?_, by rw [List.length_append, hl]; rfl, ?_⟩
  · rw [hC, List.append_assoc]; rfl
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hn x h
    · rw [List.mem_singleton.mp h]; decide

/-- Before the head's end, from count `k`, the next `4 - k` bytes are all `head`. -/
theorem headRunAll (ob : Bool) : ∀ (Y Z : List Byte) (k : Nat), k ≤ 3 → Y.length ≤ 4 - k →
    ∀ i < Y.length, (runAll ob (.head k) (Y ++ Z))[i]? = some .head
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | b :: Y', Z, k, hk, hY, i, hi => by
    rw [List.cons_append]
    show ((stepAll ob (.head k) b (Y' ++ Z).length).1 ::
      runAll ob (stepAll ob (.head k) b (Y' ++ Z).length).2 (Y' ++ Z))[i]? = some .head
    cases i with
    | zero => rfl
    | succ i =>
      have hY' : Y'.length + 1 ≤ 4 - k := by simpa using hY
      have hi' : i < Y'.length := by simpa using hi
      have hle := ReceiveHead.next_le k b
      have h4 : Head.next k b ≠ 4 := by omega
      simp only [stepAll, if_neg h4, List.getElem?_cons_succ]
      exact headRunAll ob Y' Z (Head.next k b) (by omega) (by omega) i hi'

theorem good_head {ob : Bool} {C : List ReceiveSpec.Class} {p k : Nat} {W : List Byte}
    (hg : GA ob C p (.head k) W) (hk : k ≤ 3) (Y Z : List Byte) (hW : W = Y ++ Z) (hY : Y.length ≤ 4 - k)
    (i : Nat) (hi : i < Y.length) : Good C (p + i) := by
  obtain ⟨Cp, hC, hl, -⟩ := hg
  left
  unfold ReceiveSpec.allowedIn
  rw [hC, List.getElem?_append_right (by omega), show p + i - Cp.length = i by omega, hW,
    headRunAll ob Y Z k hk hY i hi]
  rfl

theorem headSim_congr {ob : Bool} {s t : State} {k : Nat} (hv : view s = view t) (hu : s.upgrade = t.upgrade)
    (h : HeadSim ob s k) : HeadSim ob t k := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ := view_fields hv
  exact ⟨m9.symm.trans h.up, m10.symm.trans h.term, h.le, m11.symm.trans h.openBody, m8.symm.trans h.frame,
    m1.symm.trans h.message, ⟨m4.symm.trans h.clean.skip, m5.symm.trans h.clean.inner,
      m6.symm.trans h.clean.reply, m7.symm.trans h.clean.replySkipped, m2.symm.trans h.clean.request,
      m3.symm.trans h.clean.bodySkipped⟩, by rw [← hu]; exact h.upLen, by rw [← hu]; exact h.up6⟩

theorem simAll_congr {ob : Bool} {s t : State} {a : AllSt} {n : Nat} (hv : view s = view t)
    (hu : s.upgrade = t.upgrade) (h : SimAll ob s a n) : SimAll ob t a n := by
  cases a with
  | head k => exact headSim_congr hv hu h
  | frames st => exact sim_congr hv h

theorem mayReveal_head {ob : Bool} {s : State} {k : Nat} (hs : HeadSim ob s k) : mayReveal s = true := by
  unfold mayReveal; rw [hs.clean.skip, hs.message]; rfl

/-- **A run before the upgrade** (at most `4 - k` bytes, checked by `stepWindow`): the relation is kept,
and if the run completes CR LF CR LF (only its last byte can), the frame-phase relation holds after it. -/
theorem headWindow {ob : Bool} {C : List ReceiveSpec.Class} : ∀ (Y : List Byte) {s s' : State} {k p : Nat}
    {W : List Byte}, HeadSim ob s k → Y.length ≤ 4 - k → GA ob C p (.head k) (Y ++ W) → stepWindow s Y = .ok s' →
    ∃ a', SimAll ob s' a' W.length ∧ GA ob C (p + Y.length) a' W
  | [], s, s', k, p, W, hs, _, hg, h => by
    cases h
    exact ⟨.head k, hs, hg⟩
  | b :: rest, s, s', k, p, W, hs, hY, hg, h => by
    unfold stepWindow at h
    cases h1 : step s b with
    | error err => rw [h1] at h; cases h
    | ok rr =>
      obtain ⟨next, c⟩ := rr
      rw [h1] at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      have hst := headStep hs h1
      have hg1 := ga_head_step (W := rest ++ W) hg
      have hle := ReceiveHead.next_le k b
      have hk := hs.le
      have hYl : rest.length + 1 ≤ 4 - k := by simpa using hY
      split at h
      · next he =>
        cases h
        have hr : rest = [] := List.isEmpty_iff.mp he
        subst hr
        by_cases h4 : Head.next k b = 4
        · rw [if_pos h4] at hg1
          exact ⟨.frames Stream.init, hst.1 h4 W.length, hg1⟩
        · rw [if_neg h4] at hg1
          exact ⟨.head (Head.next k b), hst.2 h4, hg1⟩
      · next he =>
        split at h
        · have h1r : 1 ≤ rest.length := by
            cases rest with
            | nil => simp at he
            | cons _ _ => simp
          have h4 : Head.next k b ≠ 4 := by omega
          rw [if_neg h4] at hg1
          obtain ⟨a', hs', hg'⟩ := headWindow rest (hst.2 h4) (by omega) hg1 h
          refine ⟨a', hs', ?_⟩
          rw [show p + (b :: rest).length = p + 1 + rest.length by simp; omega]
          exact hg'
        · cases h

/-! ### One record, both phases -/

/-- **`loop_good` over both phases.** The record loop keeps `SimAll`, and every position it reveals is
allowed (with the one-byte allowance) in the reference's classes `C` of the whole stream, head included. -/
theorem loopStart_good {ob : Bool} {C : List ReceiveSpec.Class} : ∀ (fuel : Nat) (s : State) (r : List Byte)
    (o base : Nat) (acc : List Nat) (a : AllSt) (Wr : List Byte),
    r.length + 1 ≤ fuel + o → o ≤ r.length → SimAll ob s a (r.drop o ++ Wr).length →
    GA ob C (base + o) a (r.drop o ++ Wr) → (∀ q ∈ acc, Good C q) →
    (∀ q ∈ (recordLoop fuel s r o base acc).1, Good C q) ∧
      (∀ s', (recordLoop fuel s r o base acc).2 = .ok s' →
        ∃ a', SimAll ob s' a' Wr.length ∧ GA ob C (base + r.length) a' Wr)
  | fuel, s, r, o, base, acc, .frames st, Wr, hf, ho, hs, hg, hacc => by
    have hL := loop_good fuel s r o base acc st Wr hf ho hs (ga_frames.mp hg) hacc
    refine ⟨hL.1, fun s' h => ?_⟩
    obtain ⟨st', h1, h2⟩ := hL.2 s' h
    exact ⟨.frames st', h1, ga_frames.mpr h2⟩
  | 0, _, _, _, _, _, .head _, _, hf, ho, _, _, _ => by omega
  | fuel + 1, s, r, o, base, acc, .head k, Wr, hf, ho, hs, hg, hacc => by
    have hs' : HeadSim ob s k := hs
    unfold recordLoop
    by_cases hlt : o < r.length
    · rw [if_pos hlt]
      have hsk : ¬ s.skip > 0 := by rw [hs'.clean.skip]; omega
      rw [if_neg hsk]
      have hmr := mayReveal_head hs'
      rw [if_neg (by simp [hmr])]
      dsimp only
      have hb : budget s = 4 - k := by
        rw [ReceiveHead.budget_head s hs'.up, hs'.term, Nat.min_eq_left hs'.le]
      have hYk : ((r.drop o).take (budget s)).length ≤ 4 - k := by
        rw [← hb]; exact List.length_take_le _ _
      have hYZ : r.drop o ++ Wr = (r.drop o).take (budget s) ++ ((r.drop o).drop (budget s) ++ Wr) := by
        rw [← List.append_assoc, List.take_append_drop]
      have hYl : ((r.drop o).take (budget s)).length ≤ r.length - o := by
        rw [List.length_take, List.length_drop]; exact Nat.min_le_right _ _
      have hacc' : ∀ q ∈ acc ++ (List.range ((r.drop o).take (budget s)).length).map (base + o + ·),
          Good C q := by
        intro q hq
        rcases List.mem_append.mp hq with h | h
        · exact hacc q h
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
          exact good_head hg hs'.le _ _ hYZ hYk i (List.mem_range.mp hi)
      split
      · exact ⟨hacc', fun _ h => by cases h⟩
      · next hemp =>
        split
        · exact ⟨hacc', fun _ h => by cases h⟩
        · next s2 h2 =>
          rw [hYZ] at hg
          obtain ⟨a', hs'', hg''⟩ := headWindow _ hs' hYk hg h2
          rw [drop_run r o (budget s)] at hs'' hg''
          have hne : ((r.drop o).take (budget s)).length ≠ 0 := by
            intro e0
            exact hemp (List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero e0))
          exact loopStart_good fuel { s2 with envelopes := [] } r (o + ((r.drop o).take (budget s)).length) base
            _ a' Wr (by omega) (by omega) (simAll_congr (s := s2) rfl rfl hs'') (by rw [← Nat.add_assoc]; exact hg'')
            hacc'
    · rw [if_neg hlt]
      have ho' : o = r.length := by omega
      subst ho'
      refine ⟨hacc, fun s' h => ?_⟩
      cases h
      rw [List.drop_length, List.nil_append] at hg
      exact ⟨.head k, hs', hg⟩

/-! ### Every record: the model loop, and the loop the session runs -/

theorem goStart_good {ob : Bool} {C : List ReceiveSpec.Class} : ∀ (records : List (List Byte)) (s : State)
    (base : Nat) (acc : List Nat) (a : AllSt), SimAll ob s a records.flatten.length →
    GA ob C base a records.flatten → (∀ q ∈ acc, Good C q) → ∀ q ∈ (streamRun.go s records base acc).1, Good C q
  | [], _, _, _, _, _, _, hacc, q, hq => hacc q hq
  | r :: rs, s, base, acc, a, hs, hg, hacc, q, hq => by
    rw [List.flatten_cons] at hs hg
    have hL := loopStart_good (r.length + 1) s r 0 base acc a rs.flatten (by omega) (by omega)
      (by rw [List.drop_zero]; exact hs) (by rw [List.drop_zero, Nat.add_zero]; exact hg) hacc
    unfold streamRun.go at hq
    split at hq
    · next acc1 e h1 => rw [h1] at hL; exact hL.1 q hq
    · next acc1 s1 h1 =>
      rw [h1] at hL
      obtain ⟨a', hs', hg'⟩ := hL.2 s1 rfl
      exact goStart_good rs s1 (base + r.length) acc1 a' hs' hg' hL.1 q hq

/-- A step between records keeps the view and the upgrade parser's state (before the upgrade, the
latter decides the activity byte the frame parser gets). -/
def KeepsHead (f : State → Except String State) : Prop :=
  ∀ s s', f s = .ok s' → view s' = view s ∧ s'.upgrade = s.upgrade

theorem keepsHead_keeps {f : State → Except String State} (h : KeepsHead f) : Keeps f :=
  fun s s' e => (h s s' e).1

theorem keepsHead_pure (f : State → State) (h : ∀ s, view (f s) = view s ∧ (f s).upgrade = s.upgrade) :
    KeepsHead (fun s => .ok (f s)) :=
  fun s s' e => by cases e; exact h s

theorem keepsHead_bind {f g : State → Except String State} (hf : KeepsHead f) (hg : KeepsHead g) :
    KeepsHead (fun s => f s >>= g) := by
  intro s s' h
  obtain ⟨t, ht, hg'⟩ := ReceiveLoop.bind_ok h
  obtain ⟨a1, a2⟩ := hf s t ht
  obtain ⟨b1, b2⟩ := hg t s' hg'
  exact ⟨b1.trans a1, b2.trans a2⟩

/-- The session's step after a record (`replies`, then `requests := []`). -/
theorem keepsHead_afterRecord (masks : List (List Byte)) :
    KeepsHead (fun s => (replies s masks).map (fun p => { p.1 with requests := [] })) := by
  intro s s' h
  dsimp only at h
  cases hr : replies s masks with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨t, fr⟩ := p
    rw [hr] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    rw [replies_state hr]
    exact ⟨rfl, rfl⟩

/-- `replies` alone (the session's step between records during the upgrade, `Pool.readUpgrade`). -/
theorem keepsHead_replies (masks : List (List Byte)) :
    KeepsHead (fun s => (replies s masks).map (fun p => p.1)) := by
  intro s s' h
  dsimp only at h
  cases hr : replies s masks with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨t, fr⟩ := p
    rw [hr] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    rw [replies_state hr]
    exact ⟨rfl, rfl⟩

theorem keepsHead_expect (id : Nat) : KeepsHead (fun s => .ok (expect s id)) :=
  keepsHead_pure _ (fun s => ⟨(view_expect s id).symm, by
    unfold expect
    generalize TlsChatResponse.stateBytes _ _ = R
    rfl⟩)

theorem sessionStart_good {ob : Bool} {C : List ReceiveSpec.Class} {β : Type}
    {O : Nat → List Byte → RecordLoop.Ops RevealM β} {g : Nat → State → Except String State}
    (hO : ∀ base r, Faithful r base (O base r)) (hg : ∀ i, KeepsHead (g i)) :
    ∀ (records : List (List Byte)) (s : State) (i base : Nat) (acc : List Nat) (a : AllSt),
      SimAll ob s a records.flatten.length → GA ob C base a records.flatten → (∀ q ∈ acc, Good C q) →
      ∀ q ∈ (sessionGo O g s records i base acc).1, Good C q
  | [], _, _, _, _, _, _, _, hacc, q, hq => hacc q hq
  | r :: rs, s, i, base, acc, a, hs, hg0, hacc, q, hq => by
    rw [List.flatten_cons] at hs hg0
    have hL := loopStart_good (r.length + 1) s r 0 base acc a rs.flatten (by omega) (by omega)
      (by rw [List.drop_zero]; exact hs) (by rw [List.drop_zero, Nat.add_zero]; exact hg0) hacc
    have hS := loop_sub (hO base r) (r.length + 1) s false 0 acc
    unfold sessionGo at hq
    rw [run_eq (hO base r)] at hq
    revert hq hS
    rcases RecordLoop.loop (O base r) (r.length + 1) s false 0 r.length acc with ⟨res, acc1⟩
    intro hS hq
    cases res with
    | error e => exact hL.1 q (hS.1 q hq)
    | ok p =>
      obtain ⟨s1, c1⟩ := p
      have hsub : ∀ q ∈ acc1, Good C q := fun q h => hL.1 q (hS.1 q h)
      obtain ⟨a', hs', hg'⟩ := hL.2 s1 (hS.2 s1 c1 rfl)
      simp only at hq
      split at hq
      · exact hsub q hq
      · next s2 h2 =>
        obtain ⟨hv, hu⟩ := hg i s1 s2 h2
        exact sessionStart_good hO hg rs s2 (i + 1) (base + r.length) acc1 a'
          (simAll_congr hv.symm hu.symm hs') hg' hsub q hq

/-! ### The fresh connection -/

/-- The session's start states (header) satisfy `HeadSim` at count 0. -/
theorem start_head (ob : Bool) (accept : List Byte) (lenient : Bool) :
    HeadSim ob { PublicReceive.start accept with lenient := lenient, openBody := ob } 0 :=
  ⟨rfl, rfl, by omega, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, start_upgrade.1, start_upgrade.2⟩

theorem ga_start (ob : Bool) (stream : List Byte) : GA ob (ReceiveSpec.classify ob stream) 0 (.head 0) stream :=
  ⟨[], by rw [classify_stream]; rfl, rfl, by simp⟩

/-- `ReceiveProofs.T1` with the full reference (`classify`: the upgrade response's head, then the frames)
in place of `classifyFrames`. -/
def T1Full (openBody : Bool) (s : State) (records : List (List Byte)) : Prop :=
  ∀ q ∈ (streamRun s records).1,
    ReceiveSpec.allowedIn (ReceiveSpec.classify openBody records.flatten) q = true ∨
      ReceiveSpec.firstError (ReceiveSpec.classify openBody records.flatten) = some q

/-- **T1 from the first byte, about the model loop** (`streamRun`), from the session's start states. -/
theorem t1_start_model : ∀ (openBody : Bool) (accept : List Byte) (lenient : Bool) (records : List (List Byte)),
    T1Full openBody { PublicReceive.start accept with lenient := lenient, openBody } records :=
  fun openBody accept lenient records q hq =>
    goStart_good records _ 0 [] (.head 0) (start_head openBody accept lenient) (ga_start openBody _) (by simp) q hq

/-- **T1 from the first byte of a connection, about the loop the session runs** (`RecordLoop.run`, the
policy core of `Session/Common.lean`'s `record`), from the start states the session uses
(`{ PublicReceive.start accept with lenient, openBody }`, header): over every stream (the upgrade
response's head, then frames) cut into records in any way (a record may end inside the head, and hold
the end of the head and the first frames), with any steps between records that keep the view and the
upgrade parser's state (`KeepsHead`: `replies`, `requests := []`, `expect`, and compositions), every
stream position the loop has the engines reveal is allowed by `ReceiveSpec.classify openBody`, or is its
first `error`. Assumption: the engines' operations are `Faithful` (D8). -/
theorem t1_start (openBody : Bool) (accept : List Byte) (lenient : Bool) (records : List (List Byte))
    {β : Type} (O : Nat → List Byte → RecordLoop.Ops RevealM β) (hO : ∀ base r, Faithful r base (O base r))
    (g : Nat → State → Except String State) (hg : ∀ i, KeepsHead (g i)) :
    ∀ q ∈ (sessionRun O g { PublicReceive.start accept with lenient := lenient, openBody } records).1,
      ReceiveSpec.allowedIn (ReceiveSpec.classify openBody records.flatten) q = true ∨
        ReceiveSpec.firstError (ReceiveSpec.classify openBody records.flatten) = some q :=
  fun q hq => sessionStart_good hO hg records _ 0 0 [] (.head 0) (start_head openBody accept lenient)
    (ga_start openBody _) (by simp) q hq

end ReceiveStart
