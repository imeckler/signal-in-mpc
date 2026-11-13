import TlsMpc.Node.Policy.ReceiveSimByte
import TlsMpc.Node.Policy.ReceiveComplete
import TlsMpc.Node.Policy.ReceiveEnvDone

/-!
# T1, item 1: the controller simulates the byte-by-byte reference

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`Sim ob s st n`: the controller's state `s` (after the upgrade) is at the reference's position `st`
(`ReceiveStream.Stream.St` with `failClosed`'s flag), `n` stream bytes not yet read:

* no byte read so far was `error` (`bad = false`);
* the frame parser's state is at the reference's frame position (`ReceiveSimFrame.FrameSim`);
* the message side (`MsgSim`): between messages, nothing tracked; after one payload byte, that byte;
  inside a response, `ReplyIn`; inside a server request, `QIn`, or a delivered envelope being walked
  (`EnvSim`: the walk so far is `envWalk`'s, the request's revealed bytes end at the body's length);
* `Fits`: in a message's last frame, when the stream holds all of it, what the open field still
  declares (`pendingField`) fits in the rest of the frame (the controller's `overrun` check).

`sim_step` (every byte the controller accepts) and `sim_pass` (every byte it passes over) keep `Sim`.
-/

open TlsMpc TlsMpc.Signal

namespace ReceiveSim

open PublicReceive ReceiveProofs ReceiveStream ReceiveSimFrame ReceiveSimByte ReceiveComplete
open ReceiveReply ReceiveRequestScan
open TlsMpc.KernelSpecs.ParseWebSocketFrame (P mb dat ctl Shaped eventBytes runByte_active step_shaped)

/-! ### The relation -/

/-- Nothing of a message is being tracked. -/
structure Clean (s : State) : Prop where
  skip : s.skip = 0
  inner : s.inner = none
  reply : s.reply = []
  replySkipped : s.replySkipped = false
  request : s.request = []
  bodySkipped : s.bodySkipped = false

/-- **A delivered envelope being walked**: the request's revealed bytes `H0 ++ [y]` end at the body's
length (`n`, a `/api/v1/message` body), the body's bytes so far are `E0`, and the walk so far is
`envWalk`'s (`L`), from where the controller is (`EnvAt s hd p k r`, `r` body bytes left). -/
structure EnvAtP (s : State) (Pre : List Byte) (y : Byte) (E0 H0 : List Byte) (bs : Bool) (n : Nat)
    (hd : List Byte) (p k r : Nat) (L : List Bool) : Prop where
  shape : QShape H0 bs Pre
  request : s.request = H0 ++ [y]
  bodySkipped : s.bodySkipped = true
  scanSkip : (scan (H0 ++ [y]) bs).1 = .skip n
  path : (scan (H0 ++ [y]) bs).2.path = ReceiveSpec.messagePath
  at_ : EnvAt s hd p k r
  rpos : 0 < r
  len : E0.length + r = n
  walk : ∀ X, envWalk [] 0 0 (E0 ++ X) = L ++ envWalk hd p k X
  walkLen : L.length = E0.length

def EnvSim (s : State) (P : List Byte) : Prop :=
  ∃ Pre y E0 H0 bs n hd p k r L, P = Pre ++ y :: E0 ∧ EnvAtP s Pre y E0 H0 bs n hd p k r L

/-- **The message side.** -/
inductive MsgSim (s : State) : List Byte → Prop
  | empty : s.message = [] → Clean s → MsgSim s []
  | one {a : Byte} : s.message = [a] → Clean s → MsgSim s [a]
  | reply {P : List Byte} : ReplyIn s P → s.request = [] → s.bodySkipped = false → s.inner = none →
      (0 < s.skip → replyMissing s.reply s.openBody = 0) → MsgSim s (8 :: 2 :: P)
  | request {P : List Byte} : QIn s P → s.reply = [] → s.replySkipped = false →
      (0 < s.skip → fieldMissing s.request = 0) → MsgSim s (8 :: 1 :: P)
  | env {P : List Byte} : EnvSim s P → s.reply = [] → s.replySkipped = false → MsgSim s (8 :: 1 :: P)

/-- In a message's last frame, complete in the stream: the open field fits in the rest of the frame. -/
def Fits (s : State) : Stream.Phase → Prop
  | .payload false _ true k => pendingField s ≤ k
  | _ => True

/-- **The controller's state `s` simulates the reference's `st`**, `n` stream bytes not yet read. -/
structure Sim (ob : Bool) (s : State) (st : Stream.St × Bool) (n : Nat) : Prop where
  bad : st.2 = false
  up : s.upgraded = true
  openBody : s.openBody = ob
  frame : ∃ S, s.frame = TlsWebSocketFrame.stateBytes S ∧ FrameSim S st.1 n
  msg : MsgSim s st.1.msg
  fits : Fits s st.1.phase

/-! ### Depending only on the view -/

/-! Fields from a view equation. -/
theorem vMessage {t : State} {v : View} (h : view t = v) : t.message = v.message := congrArg View.message h
theorem vRequest {t : State} {v : View} (h : view t = v) : t.request = v.request := congrArg View.request h
theorem vBodySkipped {t : State} {v : View} (h : view t = v) : t.bodySkipped = v.bodySkipped :=
  congrArg View.bodySkipped h
theorem vSkip {t : State} {v : View} (h : view t = v) : t.skip = v.skip := congrArg View.skip h
theorem vInner {t : State} {v : View} (h : view t = v) : t.inner = v.inner := congrArg View.inner h
theorem vReply {t : State} {v : View} (h : view t = v) : t.reply = v.reply := congrArg View.reply h
theorem vReplySkipped {t : State} {v : View} (h : view t = v) : t.replySkipped = v.replySkipped :=
  congrArg View.replySkipped h
theorem vFrame {t : State} {v : View} (h : view t = v) : t.frame = v.frame := congrArg View.frame h
theorem vUpgraded {t : State} {v : View} (h : view t = v) : t.upgraded = v.upgraded := congrArg View.upgraded h
theorem vOpenBody {t : State} {v : View} (h : view t = v) : t.openBody = v.openBody := congrArg View.openBody h

/-- The fields of the message side. -/
structure MsgEq (s t : State) : Prop where
  message : s.message = t.message
  request : s.request = t.request
  bodySkipped : s.bodySkipped = t.bodySkipped
  skip : s.skip = t.skip
  inner : s.inner = t.inner
  reply : s.reply = t.reply
  replySkipped : s.replySkipped = t.replySkipped
  openBody : s.openBody = t.openBody

theorem msgEq_of_view {s t : State} (h : view s = view t) : MsgEq s t := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, -, -, -, m11⟩ := view_fields h
  exact ⟨m1, m2, m3, m4, m5, m6, m7, m11⟩

theorem msgEq_frame {s t : State} {F : List Byte} (h : view t = { view s with frame := F }) : MsgEq s t :=
  ⟨(vMessage h).symm, (vRequest h).symm, (vBodySkipped h).symm, (vSkip h).symm, (vInner h).symm, (vReply h).symm,
    (vReplySkipped h).symm, (vOpenBody h).symm⟩

theorem pendingField_msgEq {s t : State} (h : MsgEq s t) : pendingField s = pendingField t := by
  unfold pendingField; rw [h.message, h.inner, h.skip, h.request, h.reply, h.openBody]

theorem clean_congr {s t : State} (h : MsgEq s t) (hc : Clean s) : Clean t :=
  ⟨h.skip ▸ hc.skip, h.inner ▸ hc.inner, h.reply ▸ hc.reply, h.replySkipped ▸ hc.replySkipped,
    h.request ▸ hc.request, h.bodySkipped ▸ hc.bodySkipped⟩

theorem replyIn_congr {s t : State} {P : List Byte} (h : MsgEq s t) (hr : ReplyIn s P) : ReplyIn t P :=
  ⟨h.message ▸ hr.message, fun B hB => by
    rw [← h.reply, ← h.replySkipped, ← h.openBody]; exact hr.shape B (by rw [hB, h.skip])⟩

theorem qIn_congr {s t : State} {P : List Byte} (h : MsgEq s t) (hq : QIn s P) : QIn t P :=
  ⟨h.message ▸ hq.message, h.inner ▸ hq.inner, fun B hB => by
    rw [← h.request, ← h.bodySkipped]; exact hq.shape B (by rw [hB, h.skip])⟩

theorem envAt_congr {s t : State} {hd : List Byte} {p k r : Nat} (h : MsgEq s t) (he : EnvAt s hd p k r) :
    EnvAt t hd p k r :=
  ⟨h.message ▸ he.message, h.inner ▸ he.inner, h.skip ▸ he.skip, he.le, h.request ▸ he.missing⟩

theorem envSim_congr {s t : State} {P : List Byte} (h : MsgEq s t) (he : EnvSim s P) : EnvSim t P := by
  obtain ⟨Pre, y, E0, H0, bs, n, hd, p, k, r, L, hP, hA⟩ := he
  exact ⟨Pre, y, E0, H0, bs, n, hd, p, k, r, L, hP, hA.shape, h.request ▸ hA.request,
    h.bodySkipped ▸ hA.bodySkipped, hA.scanSkip, hA.path, envAt_congr h hA.at_, hA.rpos, hA.len, hA.walk,
    hA.walkLen⟩

theorem msgSim_congr {s t : State} {P : List Byte} (h : MsgEq s t) (hm : MsgSim s P) : MsgSim t P := by
  cases hm with
  | empty a b => exact .empty (h.message ▸ a) (clean_congr h b)
  | one a b => exact .one (h.message ▸ a) (clean_congr h b)
  | reply a b c d e =>
    refine .reply (replyIn_congr h a) (h.request ▸ b) (h.bodySkipped ▸ c) (h.inner ▸ d) ?_
    intro hp; rw [← h.reply, ← h.openBody]; exact e (by rw [h.skip]; exact hp)
  | request a b c d =>
    refine .request (qIn_congr h a) (h.reply ▸ b) (h.replySkipped ▸ c) ?_
    intro hp; rw [← h.request]; exact d (by rw [h.skip]; exact hp)
  | env a b c => exact .env (envSim_congr h a) (h.reply ▸ b) (h.replySkipped ▸ c)

/-- `Sim` depends on the controller's state only through its view (so the record loop's
`envelopes := []`, the session's `replies`, `requests := []`, `expect` between records keep it). -/
theorem sim_congr {ob : Bool} {s t : State} {st : Stream.St × Bool} {n : Nat} (h : view s = view t)
    (hs : Sim ob s st n) : Sim ob t st n := by
  have hm := msgEq_of_view h
  obtain ⟨-, -, -, -, -, -, -, m8, m9, -, -⟩ := view_fields h
  refine ⟨hs.bad, m9 ▸ hs.up, hm.openBody ▸ hs.openBody, by rw [← m8]; exact hs.frame,
    msgSim_congr hm hs.msg, ?_⟩
  have hf := hs.fits
  unfold Fits at hf ⊢
  rw [← pendingField_msgEq hm]
  exact hf

/-! ### The frame side of `step` -/

theorem get_eventBytes0 (e : TlsWebSocketFrame.Event Byte) :
    PublicReceive.get (eventBytes e) 0 = e.state.valid := rfl

theorem get_eventBytes1 (e : TlsWebSocketFrame.Event Byte) :
    PublicReceive.get (eventBytes e) 1 = fast.and e.state.valid e.data := rfl

theorem get_eventBytes5 (e : TlsWebSocketFrame.Event Byte) :
    PublicReceive.get (eventBytes e) 5 = fast.and e.state.valid e.messageDone := rfl

theorem get_app_left (A B : List Byte) (i : Nat) (h : i < A.length) :
    PublicReceive.get (A ++ B) i = PublicReceive.get A i := by
  unfold PublicReceive.get; rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem mb_beq_on (x : Bool) : (mb x == on) = x := by cases x <;> rfl

theorem and_on' (x : Byte) : fast.and on x = x := ReceiveSimFrame.and_on x

/-- **`step`'s frame side under `Sim`**: the frame parser moves to the reference's next position; the
byte is a data payload byte, and ends a message, exactly when the reference says so; `payloadByte` is
then given those flags. -/
theorem step_frame {ob : Bool} {s s' : State} {st1 : Stream.St} {n : Nat} {b : Byte} {c : Bool}
    (hs : Sim ob s (st1, false) (n + 1)) (h : step s b = .ok (s', c)) :
    ∃ S' s1 flags, FrameSim S' (Stream.step ob st1 b n).2 n ∧
      view s1 = { view s with frame := TlsWebSocketFrame.stateBytes S' } ∧ s.skip = 0 ∧
      payloadByte s1 b (dataOf st1.phase) (endOf st1.phase b) (dataOf st1.phase && s.message.length == 0) flags =
        .ok (s', c) := by
  obtain ⟨s1, ev, h1, -, h2⟩ := step_ok h
  obtain ⟨S, hS, hfs⟩ := hs.frame
  obtain ⟨hk, hv, hev, hview⟩ := frameByte_view hs.up h1
  have hrun : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b]) =
      eventBytes (TlsWebSocketFrame.step fast capacity S b) ++
        TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.step fast capacity S b).state := by
    rw [hS]; exact runByte_active capacity S hfs.shaped b
  rw [hrun] at hv hev hview
  have hlen := TlsMpc.KernelSpecs.ParseWebSocketFrame.eventBytes_length (TlsWebSocketFrame.step fast capacity S b)
  rw [get_app_left _ _ 0 (by omega), get_eventBytes0] at hv
  rw [List.take_left' hlen] at hev
  rw [List.drop_left' hlen] at hview
  obtain ⟨hfs', hd, hdn⟩ := frame_sim_step ob hfs hv
  refine ⟨_, s1, [PublicReceive.get ev 1, PublicReceive.get ev 3, PublicReceive.get ev 5], hfs', hview, hk, ?_⟩
  have e1 : (PublicReceive.get ev 1 == on) = dataOf st1.phase := by
    rw [hev, get_eventBytes1, hv, and_on', hd, mb_beq_on]
  have e5 : (PublicReceive.get ev 5 == on) = endOf st1.phase b := by
    rw [hev, get_eventBytes5, hv, and_on', hdn, mb_beq_on]
  have em : s1.message = s.message := vMessage hview
  rw [e1, e5, em] at h2
  exact h2

/-! ### The reference's step -/

/-- A byte that is not a data payload byte (a header byte, a control frame's payload byte), the reference
not entering its error state at it: public, and the message is kept, or ends (an empty final data frame). -/
theorem stream_nodata (ob : Bool) (st : Stream.St) (b : Byte) (n : Nat) (hd : dataOf st.phase = false)
    (hst : st.phase ≠ .dead) (hnd : (Stream.step ob st b n).2.phase ≠ .dead) :
    (Stream.step ob st b n).1.secret = false ∧ (Stream.step ob st b n).1 ≠ .error ∧
      (Stream.step ob st b n).2.msg = (if endOf st.phase b then [] else st.msg) := by
  obtain ⟨phase, msg, fr⟩ := st
  simp only at hd hst hnd ⊢
  have fh : ReceiveSpec.Class.frameHeader ≠ .error := by decide
  cases phase with
  | dead => exact absurd rfl hst
  | first =>
    simp only [Stream.step] at hnd ⊢
    split <;> exact ⟨rfl, fh, rfl⟩
  | second b0 =>
    simp only [Stream.step] at hnd ⊢
    by_cases hb : Stream.secondBad b0 b
    · rw [if_pos hb] at hnd; exact absurd rfl hnd
    rw [if_neg hb]
    by_cases h126 : b.toNat % 128 = 126
    · rw [if_pos h126]
      have : (b.toNat % 128 == 0) = false := by simp; omega
      exact ⟨rfl, fh, by simp [endOf, this]⟩
    · rw [if_neg h126]
      refine ⟨rfl, fh, ?_⟩
      unfold Stream.startPayload
      by_cases hz : b.toNat % 128 = 0
      · rw [if_pos hz]
        have hz' : (b.toNat % 128 == 0) = true := by simp [hz]
        unfold Stream.endFrame
        cases hc : Stream.isControl b0 <;> cases hf : Stream.finOf b0 <;> simp [endOf, hz', hc, hf]
      · rw [if_neg hz]
        have hz' : (b.toNat % 128 == 0) = false := by simp [hz]
        simp [endOf, hz']
  | extHi b0 =>
    simp only [Stream.step]
    exact ⟨rfl, fh, rfl⟩
  | extLo b0 hi =>
    simp only [Stream.step] at hnd ⊢
    by_cases hw : ReceiveSpec.word hi b < 126
    · rw [if_pos hw] at hnd; exact absurd rfl hnd
    rw [if_neg hw]
    refine ⟨rfl, fh, ?_⟩
    unfold Stream.startPayload
    rw [if_neg (by omega)]
    rfl
  | payload c f cpl k =>
    simp only [dataOf, Bool.not_eq_false'] at hd
    subst hd
    simp only [Stream.step, if_true]
    have ct : ReceiveSpec.Class.control ≠ .error := by decide
    by_cases hk : k ≤ 1
    · rw [if_pos hk]
      refine ⟨rfl, ct, ?_⟩
      unfold Stream.endFrame; simp [endOf]
    · rw [if_neg hk]
      exact ⟨rfl, ct, by simp [endOf]⟩

/-- A data payload byte: its class is `payloadClass`; the message grows by it, or ends at it. -/
theorem stream_data (ob : Bool) (msg : List Byte) (fr f cpl : Bool) (k : Nat) (b : Byte) (n : Nat) (hk1 : 1 ≤ k) :
    (Stream.step ob ⟨.payload false f cpl k, msg, fr⟩ b n).1 = Stream.payloadClass ob cpl msg b k ∧
      (Stream.step ob ⟨.payload false f cpl k, msg, fr⟩ b n).2.msg = (if (f && k == 1) = true then [] else msg ++ [b]) := by
  simp only [Stream.step, Bool.false_eq_true, if_false]
  refine ⟨by split <;> rfl, ?_⟩
  by_cases hk : k ≤ 1
  · rw [if_pos hk]
    unfold Stream.endFrame
    have hk1' : k = 1 := by omega
    subst hk1'; cases f <;> simp
  · rw [if_neg hk]
    have : (k == 1) = false := by simp; omega
    simp [this]

theorem frame_gets {S : FState} (h : Shaped S) :
    PublicReceive.get (TlsWebSocketFrame.stateBytes S) 4 = S.phases.getD 4 0 ∧
    PublicReceive.get (TlsWebSocketFrame.stateBytes S) 7 = S.opcode ∧
    PublicReceive.get (TlsWebSocketFrame.stateBytes S) 8 = S.fin ∧
    PublicReceive.get (TlsWebSocketFrame.stateBytes S) 10 = S.high ∧
    PublicReceive.get (TlsWebSocketFrame.stateBytes S) 11 = S.low := by
  obtain ⟨h5, -⟩ := h
  obtain ⟨a, b, c, d, e, hp⟩ := TlsMpc.KernelSpecs.ParseWebSocketFrame.len5 S.phases h5
  unfold TlsWebSocketFrame.stateBytes
  rw [hp]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The overrun check gives `Fits`**: in a data frame's payload with FIN, `pendingField` is at most what
is left of the frame. -/
theorem fits_of_overrun {S : FState} {st : Stream.St} {n : Nat} {t : State} {f : Bool} {k : Nat}
    (hfs : FrameSim S st n) (hp : st.phase = .payload false f true k)
    (hframe : t.frame = TlsWebSocketFrame.stateBytes S) (ho : overrun t = false) : pendingField t ≤ k := by
  have hph := hfs.phase
  rw [hp] at hph
  obtain ⟨hP, hk, -, -, -, hlt, hfin, hcpl, -⟩ := hph
  have hf : f = true := by
    cases f
    · simp at hcpl
    · rfl
  subst hf
  obtain ⟨g4, g7, g8, g10, g11⟩ := frame_gets hfs.shaped
  unfold overrun at ho
  rw [hframe, g4, g7, g8, g10, g11, hP, hfin] at ho
  have hl : S.opcode.toNat < 8 := hlt.mpr rfl
  simp only [P, List.getD_cons_succ, List.getD_cons_zero, beq_self_eq_true, mb_beq_on, Bool.true_and,
    decide_eq_true_eq] at ho
  unfold TlsWebSocketFrame.wordValue at hk
  simp only [hl, decide_true, Bool.true_and, decide_eq_false_iff_not, Nat.not_lt] at ho
  omega

/-! ### `payloadByte`, end to end -/

/-- **`payloadByte` in steps**: the kind is known or not yet; not a one-byte message; the response's
fields (`RepStep`), then the request's (`ReqStep`, or the envelope's walk), then no overrun, then the
message's end. -/
theorem pb_chain {s1 s' : State} {b : Byte} {data done first : Bool} {flags : List Byte} {c : Bool}
    (h : payloadByte s1 b data done first flags = .ok (s', c)) :
    kindOK (msgAfter s1 b data) = true ∧ (first && done) = false ∧
    ∃ t t1 t2, view t = { view s1 with message := msgAfter s1 b data } ∧
      (((data && msgAfter s1 b data == [8, 2]) = false ∧ t1 = t) ∨
        ((data && msgAfter s1 b data == [8, 2]) = true ∧ RepStep t b t1)) ∧
      (((data && msgAfter s1 b data == [8, 1]) = false ∧ t2 = t1) ∨
       ((data && msgAfter s1 b data == [8, 1]) = true ∧
        ((∃ hd p r, t1.inner = some (hd, p, r) ∧ 0 < r ∧ envelopeAdvance t1 (hd ++ [b]) p (r - 1) = .ok t2) ∨
         (t1.inner = none ∧ ReqStep t1 b t2)))) ∧
      overrun t2 = false ∧
      ((done = false ∧ view s' = view t2) ∨
       (done = true ∧ t2.skip = 0 ∧ t2.inner = none ∧ pendingField t2 = 0 ∧
        view s' = { view t2 with
          message := [], request := [], bodySkipped := false, reply := [], replySkipped := false })) := by
  obtain ⟨hk, hf, t, c0, ht, hr⟩ := payloadByte_view h
  refine ⟨hk, hf, ?_⟩
  obtain ⟨t1, hq, hrep⟩ := pbReply_view hr
  obtain ⟨t2, hc, hreq⟩ := pbRequest_view hq
  obtain ⟨ho, hd⟩ := pbCheck_view hc
  obtain ⟨-, hdone⟩ := pbDone_view hd
  exact ⟨t, t1, t2, ht, hrep, hreq, ho, hdone⟩

/-- The end of `payloadByte`: the message goes on (`done = false`) or is reset. -/
def DoneOK (done : Bool) (t2 s' : State) : Prop :=
  (done = false ∧ view s' = view t2) ∨
  (done = true ∧ t2.skip = 0 ∧ t2.inner = none ∧ pendingField t2 = 0 ∧
    view s' = { view t2 with message := [], request := [], bodySkipped := false, reply := [], replySkipped := false })

theorem doneOK_frame {done : Bool} {t2 s' : State} (h : DoneOK done t2 s') :
    s'.frame = t2.frame ∧ s'.upgraded = t2.upgraded ∧ s'.openBody = t2.openBody := by
  rcases h with ⟨-, e⟩ | ⟨-, -, -, -, e⟩
  · exact ⟨vFrame e, vUpgraded e, vOpenBody e⟩
  · exact ⟨vFrame e, vUpgraded e, vOpenBody e⟩

theorem doneOK_pending {done : Bool} {t2 s' : State} (h : DoneOK done t2 s') : pendingField s' ≤ pendingField t2 := by
  rcases h with ⟨-, e⟩ | ⟨-, -, -, -, e⟩
  · rw [pendingField_msgEq (msgEq_of_view e)]; exact Nat.le_refl _
  · have : pendingField s' = 0 := by
      unfold pendingField; rw [vMessage e]; rfl
    omega

theorem doneOK_clean {t2 s' : State} (h : DoneOK true t2 s') : s'.message = [] ∧ Clean s' := by
  rcases h with ⟨e, -⟩ | ⟨-, h1, h2, -, e⟩
  · cases e
  · exact ⟨vMessage e, vSkip e ▸ h1, vInner e ▸ h2, vReply e, vReplySkipped e, vRequest e, vBodySkipped e⟩

/-- **`Fits` after a byte**: from the overrun check (or the message's end). -/
theorem fits_finish {S' : FState} {st' : Stream.St} {n : Nat} {done : Bool} {t2 s' : State}
    (hfs' : FrameSim S' st' n) (hframe : t2.frame = TlsWebSocketFrame.stateBytes S') (ho : overrun t2 = false)
    (hd : DoneOK done t2 s') : Fits s' st'.phase := by
  unfold Fits
  split
  · next f k hp =>
    have := fits_of_overrun hfs' hp hframe ho
    have := doneOK_pending hd
    omega
  · trivial

/-- **A header byte or a control frame's payload byte keeps `Sim`.** -/
theorem sim_step_nodata {ob : Bool} {s s' : State} {st1 : Stream.St} {n : Nat} {b : Byte} {c : Bool}
    (hs : Sim ob s (st1, false) (n + 1)) (h : step s b = .ok (s', c)) (hd : dataOf st1.phase = false) :
    Sim ob s' (Stream.stepF ob (st1, false) b n).2 n := by
  obtain ⟨S', s1, flags, hfs', hv1, hk, hpb⟩ := step_frame hs h
  rw [hd, Bool.false_and] at hpb
  obtain ⟨-, -, t, t1, t2, ht, hrep, hreq, ho, hdone⟩ := pb_chain hpb
  have e1 : t1 = t := by
    rcases hrep with ⟨-, e⟩ | ⟨e, -⟩
    · exact e
    · simp at e
  have e2 : t2 = t1 := by
    rcases hreq with ⟨-, e⟩ | ⟨e, -⟩
    · exact e
    · simp at e
  subst e1 e2
  have hd' : DoneOK (endOf st1.phase b) t2 s' := hdone
  have hmA : msgAfter s1 b false = s1.message := by simp [msgAfter]
  rw [hmA] at ht
  have ha := hv1
  simp only [view, View.mk.injEq] at ha
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := ha
  have hb := ht
  simp only [view, View.mk.injEq] at hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
  have hmt : MsgEq s t2 := ⟨by rw [b1, a1], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4], by rw [b5, a5],
    by rw [b6, a6], by rw [b7, a7], by rw [b11, a11]⟩
  have htf : t2.frame = TlsWebSocketFrame.stateBytes S' := by rw [b8, a8]
  have htu : t2.upgraded = true := by rw [b9, a9]; exact hs.up
  obtain ⟨f1, f2, f3⟩ := doneOK_frame hd'
  have hst : st1.phase ≠ .dead := by
    obtain ⟨S, -, hfs⟩ := hs.frame
    intro e; have := hfs.phase; rw [e] at this; exact this
  have hnd : (Stream.step ob st1 b n).2.phase ≠ .dead := by
    intro e; have := hfs'.phase; rw [e] at this; exact this
  obtain ⟨-, hne, hmsg⟩ := stream_nodata ob st1 b n hd hst hnd
  refine ⟨by simp [Stream.stepF, hne], by rw [f2]; exact htu, by rw [f3, ← hmt.openBody]; exact hs.openBody,
    ⟨S', by rw [f1]; exact htf, by simpa [Stream.stepF] using hfs'⟩, ?_,
    by simpa [Stream.stepF] using fits_finish hfs' htf ho hd'⟩
  simp only [Stream.stepF, Bool.false_eq_true, if_false]
  rw [hmsg]
  cases he : endOf st1.phase b
  · rw [he] at hd'
    rcases hd' with ⟨-, e⟩ | ⟨e, -⟩
    · exact msgSim_congr (⟨hmt.message.trans (vMessage e).symm, hmt.request.trans (vRequest e).symm,
        hmt.bodySkipped.trans (vBodySkipped e).symm, hmt.skip.trans (vSkip e).symm,
        hmt.inner.trans (vInner e).symm, hmt.reply.trans (vReply e).symm,
        hmt.replySkipped.trans (vReplySkipped e).symm, hmt.openBody.trans (vOpenBody e).symm⟩) hs.msg
    · cases e
  · rw [he] at hd'
    obtain ⟨hm0, hc0⟩ := doneOK_clean hd'
    exact MsgSim.empty hm0 hc0

/-! ### A data payload byte's class -/

/-- A data payload byte's class is not `error` if the message's classes up to it are not, the bytes
after it in the message being `W` (with `complete`: as many as the frame has left). -/
theorem payloadClass_ne (ob cpl : Bool) (msg : List Byte) (b : Byte) (k : Nat) (W : List Byte)
    (hW : cpl = true → W.length = k - 1)
    (hne : ∀ x ∈ (ReceiveSpec.message ob cpl (msg ++ b :: W)).take (msg.length + 1), x ≠ .error) :
    Stream.payloadClass ob cpl msg b k ≠ .error := by
  unfold Stream.payloadClass
  have hlen : ∀ (c : Bool) (X : List Byte), msg.length < (ReceiveSpec.message ob c (msg ++ b :: X)).length := by
    intro c X; rw [ReceiveStream.message_len]; simp
  cases cpl
  · simp only [Bool.false_eq_true, if_false, List.replicate_zero]
    have hp := ReceiveStream.message_prefix ob (msg ++ [b]) W
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_singleton]
      at hp
    rw [List.getElem?_eq_getElem (hlen false [])]
    simp only [Option.getD_some]
    intro e
    apply hne _ _ e
    rw [hp]
    exact List.getElem_mem _
  · have hW' := hW rfl
    simp only [if_true]
    have e1 : (ReceiveSpec.message ob true (msg ++ b :: List.replicate (k - 1) 0))[msg.length]? =
        (ReceiveSpec.message ob true (msg ++ b :: W))[msg.length]? := by
      have c1 := ReceiveStream.message_causal ob true (msg ++ [b]) (List.replicate (k - 1) 0) W
        (fun _ => by simp [hW'])
      have := congrArg (fun l => l[msg.length]?) c1
      simp only [List.getElem?_take, List.length_append, List.length_singleton,
        show msg.length < msg.length + 1 by omega, if_true, List.append_assoc, List.cons_append,
        List.nil_append] at this
      exact this
    rw [e1, List.getElem?_eq_getElem (hlen true W)]
    simp only [Option.getD_some]
    intro e
    apply hne _ _ e
    rw [List.mem_iff_getElem]
    exact ⟨msg.length, by have := hlen true W; simp; omega, by simp⟩

theorem noerr_take_le {L : List ReceiveSpec.Class} {m n : Nat} (hn : n ≤ m) (h : ∀ x ∈ L.take m, x ≠ .error) :
    ∀ x ∈ L.take n, x ≠ .error := by
  intro x hx
  apply h x
  rw [show n = min n m by omega, ← List.take_take] at hx
  exact List.mem_of_mem_take hx

/-- The bytes after the byte, for its class: what is left of the frame (with `complete`), or any `n`. -/
def padOf (cpl : Bool) (k n : Nat) : List Byte := if cpl then List.replicate (k - 1) 0 else List.replicate n 0

theorem padOf_len (cpl : Bool) (k n : Nat) (h : cpl = true) : (padOf cpl k n).length = k - 1 := by
  subst h; simp [padOf]

/-! ### A response's byte -/

theorem data_reply {ob : Bool} {s s' t t1 : State} {P : List Byte} {b : Byte} {cpl done : Bool} {k : Nat}
    (hR : ReplyIn s P) (hreq0 : s.request = []) (hbs0 : s.bodySkipped = false) (hin0 : s.inner = none)
    (hob : s.openBody = ob) (hsk : s.skip = 0) (ht : MsgEq s t) (hrep : RepStep t b t1)
    (hd : DoneOK done t1 s') (hfit2 : cpl = true → pendingField t1 ≤ k - 1) :
    MsgSim s' (if done = true then [] else 8 :: 2 :: (P ++ [b])) ∧
      Stream.payloadClass ob cpl (8 :: 2 :: P) b k ≠ .error := by
  have hsh0 := hR.shape [] (by simp [hsk])
  rw [List.append_nil, hob] at hsh0
  have hne := rshape_ne hsh0
  have hrep_eq : repAfter t b = s.reply ++ [b] := by
    unfold repAfter; rw [← ht.reply, hne]; rfl
  cases hrep with
  | more hm hv =>
    rw [hrep_eq, ← ht.replySkipped, ← ht.openBody, hob] at hm
    have hsh' := rshape_more hsh0 b hm
    have hv' := hv
    simp only [view, View.mk.injEq] at hv'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, -, -, c11⟩ := hv'
    rw [hrep_eq] at c6
    -- t1's fields
    have m1 : t1.message = [8, 2] := by rw [c1, ← ht.message, hR.message]
    have k1 : t1.skip = 0 := by rw [c4, ← ht.skip, hsk]
    have pend : pendingField t1 = replyMissing (s.reply ++ [b]) ob := by
      unfold pendingField; rw [m1, k1, c6, c11, ← ht.openBody, hob]; rfl
    refine ⟨?_, ?_⟩
    · cases done
      · rcases hd with ⟨-, e⟩ | ⟨e, -⟩
        · have q := msgEq_of_view e
          simp only [Bool.false_eq_true, if_false]
          refine MsgSim.reply ⟨by rw [q.message, m1], fun B hB => ?_⟩ ?_ ?_ ?_ ?_
          · rw [q.skip, k1] at hB
            rw [List.eq_nil_of_length_eq_zero hB, List.append_nil, q.reply, q.replySkipped, q.openBody, c6, c7, c11,
              ← ht.replySkipped, ← ht.openBody, hob]
            exact hsh'
          · rw [q.request, c2, ← ht.request, hreq0]
          · rw [q.bodySkipped, c3, ← ht.bodySkipped, hbs0]
          · rw [q.inner, c5, ← ht.inner, hin0]
          · intro hp; rw [q.skip, k1] at hp; omega
        · cases e
      · obtain ⟨hm0, hc0⟩ := doneOK_clean hd
        simpa using MsgSim.empty hm0 hc0
    · have hfit : cpl = true → replyMissing (s.reply ++ [b]) ob ≤ (padOf cpl k 0).length := by
        intro e; rw [padOf_len cpl k 0 e, ← pend]; exact hfit2 e
      have hn := rshape_noerr_c (c := cpl) hsh' (padOf cpl k 0) hfit
      apply payloadClass_ne ob cpl (8 :: 2 :: P) b k (padOf cpl k 0) (padOf_len cpl k 0)
      have e1 : (8 :: 2 :: ((P ++ [b]) ++ padOf cpl k 0) : List Byte) = (8 :: 2 :: P) ++ b :: padOf cpl k 0 := by
        simp
      have e2 : 2 + (P ++ [b]).length = (8 :: 2 :: P : List Byte).length + 1 := by simp; omega
      rw [e1, e2] at hn
      exact hn
  | @skip n hm hv =>
    rw [hrep_eq, ← ht.replySkipped, ← ht.openBody, hob] at hm
    have hmiss := rshape_skip_missing hsh0 b hm
    have hv' := hv
    simp only [view, View.mk.injEq] at hv'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, -, -, c11⟩ := hv'
    rw [hrep_eq] at c6
    have m1 : t1.message = [8, 2] := by rw [c1, ← ht.message, hR.message]
    have pend : n ≤ pendingField t1 := by
      unfold pendingField; rw [m1, c4]
      simp only [show (([8, 2] : List Byte) == [8, 1]) = false by decide, Bool.false_eq_true, if_false,
        beq_self_eq_true, if_true]
      split <;> omega
    refine ⟨?_, ?_⟩
    · cases done
      · rcases hd with ⟨-, e⟩ | ⟨e, -⟩
        · have q := msgEq_of_view e
          simp only [Bool.false_eq_true, if_false]
          refine MsgSim.reply ⟨by rw [q.message, m1], fun B hB => ?_⟩ ?_ ?_ ?_ ?_
          · rw [q.skip, c4] at hB
            rw [q.reply, q.replySkipped, q.openBody, c6, c7, c11, ← ht.openBody, hob, List.append_assoc,
              List.singleton_append]
            exact rshape_skip hsh0 b hm B hB
          · rw [q.request, c2, ← ht.request, hreq0]
          · rw [q.bodySkipped, c3, ← ht.bodySkipped, hbs0]
          · rw [q.inner, c5, ← ht.inner, hin0]
          · intro _; rw [q.reply, q.openBody, c6, c11, ← ht.openBody, hob]; exact hmiss
        · cases e
      · obtain ⟨hm0, hc0⟩ := doneOK_clean hd
        simpa using MsgSim.empty hm0 hc0
    · -- the body's `n` bytes, then the rest
      have hW : n ≤ (padOf cpl k n).length := by
        unfold padOf; cases cpl
        · simp
        · have := hfit2 rfl; simp; omega
      have hshB := rshape_skip hsh0 b hm ((padOf cpl k n).take n) (by simp; omega)
      have hn := rshape_noerr_c (c := cpl) hshB ((padOf cpl k n).drop n)
        (fun _ => by rw [hmiss]; exact Nat.zero_le _)
      apply payloadClass_ne ob cpl (8 :: 2 :: P) b k (padOf cpl k n) (padOf_len cpl k n)
      have hn' := noerr_take_le (n := (8 :: 2 :: P).length + 1)
        (by simp; omega) hn
      have e1 : (8 :: 2 :: ((P ++ b :: (padOf cpl k n).take n) ++ (padOf cpl k n).drop n) : List Byte) =
          (8 :: 2 :: P) ++ b :: padOf cpl k n := by
        simp [List.take_append_drop]
      rw [e1] at hn'
      exact hn'

/-! ### A server request's byte -/

theorem take_noerr_of_eq {C L : List ReceiveSpec.Class} {m : Nat} (hm : m = C.length) (hC : NoErr C)
    {R : List ReceiveSpec.Class} (h : L = C ++ R) : ∀ x ∈ L.take m, x ≠ .error := by
  rw [h, hm, List.take_left]; exact hC

theorem data_request {ob : Bool} {s s' t t1 : State} {P : List Byte} {b : Byte} {cpl done : Bool} {k : Nat}
    (hQ : QIn s P) (hrep0 : s.reply = []) (hrs0 : s.replySkipped = false)
    (hsk : s.skip = 0) (ht : MsgEq s t) (hreq : ReqStep t b t1)
    (hd : DoneOK done t1 s') (hfit2 : cpl = true → pendingField t1 ≤ k - 1) :
    MsgSim s' (if done = true then [] else 8 :: 1 :: (P ++ [b])) ∧
      Stream.payloadClass ob cpl (8 :: 1 :: P) b k ≠ .error := by
  have hsh0 := hQ.shape [] (by simp [hsk])
  rw [List.append_nil] at hsh0
  have hne := qshape_ne hsh0
  have hreq_eq : reqAfter t b = s.request ++ [b] := by
    unfold reqAfter; rw [← ht.request, hne]; rfl
  have hbs : t.bodySkipped = s.bodySkipped := ht.bodySkipped.symm
  cases hreq with
  | more hm hv =>
    rw [hreq_eq, hbs] at hm
    have hsh' := qshape_more hsh0 b hm
    have hv' := hv
    simp only [view, View.mk.injEq] at hv'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, -, -, c11⟩ := hv'
    rw [hreq_eq] at c2
    have m1 : t1.message = [8, 1] := by rw [c1, ← ht.message, hQ.message]
    have k1 : t1.skip = 0 := by rw [c4, ← ht.skip, hsk]
    have i1 : t1.inner = none := by rw [c5, ← ht.inner, hQ.inner]
    have pend : pendingField t1 = fieldMissing (s.request ++ [b]) := by
      unfold pendingField; rw [m1, i1, k1, c2]; rfl
    refine ⟨?_, ?_⟩
    · cases done
      · rcases hd with ⟨-, e⟩ | ⟨e, -⟩
        · have q := msgEq_of_view e
          simp only [Bool.false_eq_true, if_false]
          refine MsgSim.request ⟨by rw [q.message, m1], by rw [q.inner, i1], fun B hB => ?_⟩ ?_ ?_ ?_
          · rw [q.skip, k1] at hB
            rw [List.eq_nil_of_length_eq_zero hB, List.append_nil, q.request, q.bodySkipped, c2, c3, hbs]
            exact hsh'
          · rw [q.reply, c6, ← ht.reply, hrep0]
          · rw [q.replySkipped, c7, ← ht.replySkipped, hrs0]
          · intro hp; rw [q.skip, k1] at hp; omega
        · cases e
      · obtain ⟨hm0, hc0⟩ := doneOK_clean hd
        simpa using MsgSim.empty hm0 hc0
    · have hfit : cpl = true → fieldMissing (s.request ++ [b]) ≤ (padOf cpl k 0).length := by
        intro e; rw [padOf_len cpl k 0 e, ← pend]; exact hfit2 e
      have hn := qshape_noerr_c hsh' ob cpl (padOf cpl k 0) hfit
      apply payloadClass_ne ob cpl (8 :: 1 :: P) b k (padOf cpl k 0) (padOf_len cpl k 0)
      have e1 : (8 :: 1 :: ((P ++ [b]) ++ padOf cpl k 0) : List Byte) = (8 :: 1 :: P) ++ b :: padOf cpl k 0 := by
        simp
      have e2 : 2 + (P ++ [b]).length = (8 :: 1 :: P : List Byte).length + 1 := by simp; omega
      rw [e1, e2] at hn
      exact hn
  | @skip n f hm hpath hv =>
    rw [hreq_eq, hbs] at hm
    have hmf : (scan (s.request ++ [b]) s.bodySkipped).1 = .skip n := by rw [hm]
    obtain ⟨npos, hmiss⟩ := scan_skip_missing _ _ hm
    have hp' : (scan (s.request ++ [b]) s.bodySkipped).2.path ≠ ReceiveSpec.messagePath := by
      rw [hm]; exact (messagePath_beq f.path).mp hpath
    have hv' := hv
    simp only [view, View.mk.injEq] at hv'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, -, -, c11⟩ := hv'
    rw [hreq_eq] at c2
    have m1 : t1.message = [8, 1] := by rw [c1, ← ht.message, hQ.message]
    have i1 : t1.inner = none := by rw [c5, ← ht.inner, hQ.inner]
    have pend : pendingField t1 = n := by
      unfold pendingField; rw [m1, i1, c4]
      simp only [beq_self_eq_true, if_true]
      rw [if_pos npos]
    refine ⟨?_, ?_⟩
    · cases done
      · rcases hd with ⟨-, e⟩ | ⟨e, -⟩
        · have q := msgEq_of_view e
          simp only [Bool.false_eq_true, if_false]
          refine MsgSim.request ⟨by rw [q.message, m1], by rw [q.inner, i1], fun B hB => ?_⟩ ?_ ?_ ?_
          · rw [q.skip, c4] at hB
            rw [q.request, q.bodySkipped, c2, c3, List.append_assoc, List.singleton_append]
            exact qshape_skip hsh0 b hmf B hB (requestBody_noErr hp' B)
          · rw [q.reply, c6, ← ht.reply, hrep0]
          · rw [q.replySkipped, c7, ← ht.replySkipped, hrs0]
          · intro _; rw [q.request, c2]; exact hmiss
        · cases e
      · obtain ⟨hm0, hc0⟩ := doneOK_clean hd
        simpa using MsgSim.empty hm0 hc0
    · have hW : cpl = true → n ≤ (padOf cpl k n).length := by
        intro e; rw [padOf_len cpl k n e, ← pend]; exact hfit2 e
      obtain ⟨C, hCe, hCl, hCn⟩ := qshape_body_c hsh0 b hmf ob cpl (padOf cpl k n) hW
      apply payloadClass_ne ob cpl (8 :: 1 :: P) b k (padOf cpl k n) (padOf_len cpl k n)
      have e1 : (8 :: 1 :: P : List Byte) ++ b :: padOf cpl k n = 8 :: 1 :: (P ++ b :: padOf cpl k n) := by simp
      rw [e1]
      exact take_noerr_of_eq (by rw [hCl]; simp; omega) hCn hCe
  | @env n f hm hpath hadv =>
    rw [hreq_eq, hbs] at hm
    have hmf : (scan (s.request ++ [b]) s.bodySkipped).1 = .skip n := by rw [hm]
    obtain ⟨npos, hmiss⟩ := scan_skip_missing _ _ hm
    obtain ⟨⟨am, areq⟩, hcase⟩ := envelopeAdvance_ok hadv
    have hq0 : (envelopeScan [] 0).1 = .more true := by rw [envelopeScan_eq]; rfl
    have hav := envelopeAdvance_view hadv
    have hv' := hav
    simp only [view, View.mk.injEq] at hv'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, -, -, c11⟩ := hv'
    rcases hcase with ⟨bd, -, s2skip, -, hnz⟩ | ⟨n', cf, hq', -⟩
    case inr => rw [hq0] at hq'; cases hq'
    have hi2 : t1.inner = some ([], 0, n) := hnz (by omega)
    have m1 : t1.message = [8, 1] := by rw [am, ← ht.message, hQ.message]
    have k1 : t1.skip = 0 := by rw [s2skip, ← ht.skip, hsk]
    have r1 : t1.request = s.request ++ [b] := by rw [← hreq_eq]; exact areq
    have pend : pendingField t1 = n := by unfold pendingField; rw [m1, hi2]; rfl
    refine ⟨?_, ?_⟩
    · cases done
      · rcases hd with ⟨-, e⟩ | ⟨e, -⟩
        · have q := msgEq_of_view e
          simp only [Bool.false_eq_true, if_false]
          refine MsgSim.env ⟨P, b, [], s.request, s.bodySkipped, n, [], 0, 0, n, [], by simp, ?_⟩ ?_ ?_
          · refine ⟨hsh0, by rw [q.request, r1], by rw [q.bodySkipped, c3], hmf,
              by rw [hm]; exact beq_iff_eq.mp hpath, ⟨by rw [q.message, m1], by rw [q.inner, hi2],
              by rw [q.skip, k1], Nat.zero_le _, by rw [q.request, r1]; exact hmiss⟩, npos, by simp,
              fun X => by simp, rfl⟩
          · rw [q.reply, c6, ← ht.reply, hrep0]
          · rw [q.replySkipped, c7, ← ht.replySkipped, hrs0]
        · cases e
      · rcases hd with ⟨e, -⟩ | ⟨-, -, hin, -⟩
        · cases e
        · rw [hi2] at hin; cases hin
    · have hW : cpl = true → n ≤ (padOf cpl k n).length := by
        intro e; rw [padOf_len cpl k n e, ← pend]; exact hfit2 e
      obtain ⟨C, hCe, hCl, hCn⟩ := qshape_body_c hsh0 b hmf ob cpl (padOf cpl k n) hW
      apply payloadClass_ne ob cpl (8 :: 1 :: P) b k (padOf cpl k n) (padOf_len cpl k n)
      have e1 : (8 :: 1 :: P : List Byte) ++ b :: padOf cpl k n = 8 :: 1 :: (P ++ b :: padOf cpl k n) := by simp
      rw [e1]
      exact take_noerr_of_eq (by rw [hCl]; simp; omega) hCn hCe

/-! ### A delivered envelope's revealed byte -/

theorem mem_take_getElem? {α : Type} {l : List α} {m : Nat} {x : α} (h : x ∈ l.take m) :
    ∃ i, i < m ∧ l[i]? = some x := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  rw [List.getElem?_take] at hi
  split at hi
  · exact ⟨i, by assumption, hi⟩
  · cases hi

/-- The classes of a delivered envelope up to the next revealed byte have no `error` (the walk covers
them). -/
theorem env_class_noerr (E0 : List Byte) (b : Byte) (W : List Byte) (L : List Bool) (hd : List Byte) (p k : Nat)
    (hw : ∀ X, envWalk [] 0 0 (E0 ++ X) = L ++ envWalk hd p k X) (hL : L.length = E0.length) :
    ∀ x ∈ (ReceiveSpec.envelope ((E0 ++ b :: W).length + 1) (E0 ++ b :: W)).take (E0.length + 1), x ≠ .error := by
  have hcov := ReceiveEnvDone.envWalk_noErr (E0 ++ b :: W)
  rw [hw (b :: W)] at hcov
  have hl : E0.length + 1 ≤ (L ++ envWalk hd p k (b :: W)).length := by
    rw [List.length_append, hL]
    have h1 := ReceiveEnvDone.envWalk_ne_nil hd p k b W
    have : (envWalk hd p k (b :: W)).length ≠ 0 := fun e => h1 (List.eq_nil_of_length_eq_zero e)
    omega
  intro x hx hxe
  subst hxe
  obtain ⟨i, hi, hix⟩ := mem_take_getElem? hx
  exact hcov i (by omega) hix

/-- The class of the envelope byte at index `E0.length` is public (the walk reveals it). -/
theorem env_class_public (E0 : List Byte) (b : Byte) (W : List Byte) (L : List Bool) (hd : List Byte) (p : Nat)
    (hw : ∀ X, envWalk [] 0 0 (E0 ++ X) = L ++ envWalk hd p 0 X) (hL : L.length = E0.length) :
    ∃ x, (ReceiveSpec.envelope ((E0 ++ b :: W).length + 1) (E0 ++ b :: W))[E0.length]? = some x ∧
      x.secret = false := by
  have hs := envelope_payload_unrevealed (E0 ++ b :: W)
  apply hs E0.length
  rw [hw (b :: W), List.getElem?_append_right (by omega), hL, Nat.sub_self]
  obtain ⟨rest, e⟩ := envWalk_reveal_head hd p b W
  rw [e]; rfl

theorem data_env {ob : Bool} {s s' t t1 : State} {P : List Byte} {b : Byte} {cpl done : Bool} {k : Nat}
    (hE : EnvSim s P) (hrep0 : s.reply = []) (hrs0 : s.replySkipped = false)
    (hsk : s.skip = 0) (hfitS : cpl = true → pendingField s ≤ k) (ht : MsgEq s t)
    (hadv : ∃ hd p r, t.inner = some (hd, p, r) ∧ 0 < r ∧ envelopeAdvance t (hd ++ [b]) p (r - 1) = .ok t1)
    (hd : DoneOK done t1 s') :
    MsgSim s' (if done = true then [] else 8 :: 1 :: (P ++ [b])) ∧
      Stream.payloadClass ob cpl (8 :: 1 :: P) b k ≠ .error := by
  obtain ⟨Pre, y, E0, H0, bs, n, hd0, p0, k0, r0, L, rfl, hA⟩ := hE
  have hk0 : k0 = 0 := hA.at_.skip.symm.trans hsk
  subst hk0
  obtain ⟨hd1, p1, r1, hi1, hr1, hadv1⟩ := hadv
  rw [← ht.inner, hA.at_.inner] at hi1
  cases hi1
  obtain ⟨⟨am, areq⟩, hcase⟩ := envelopeAdvance_ok hadv1
  have hav := envelopeAdvance_view hadv1
  have hv' := hav
  simp only [view, View.mk.injEq] at hv'
  obtain ⟨-, -, c3, -, -, c6, c7, -, -, -, -⟩ := hv'
  have m1 : t1.message = [8, 1] := by rw [am, ← ht.message, hA.at_.message]
  have rq1 : t1.request = H0 ++ [y] := by rw [areq, ← ht.request, hA.request]
  have bs1 : t1.bodySkipped = true := by rw [c3, ← ht.bodySkipped, hA.bodySkipped]
  have rp1 : t1.reply = [] := by rw [c6, ← ht.reply, hrep0]
  have rs1 : t1.replySkipped = false := by rw [c7, ← ht.replySkipped, hrs0]
  have miss : fieldMissing (H0 ++ [y]) = 0 := by rw [← hA.request]; exact hA.at_.missing
  -- the class of the revealed byte
  have hcls : Stream.payloadClass ob cpl (8 :: 1 :: (Pre ++ y :: E0)) b k ≠ .error := by
    have pend : pendingField s = r0 := by unfold pendingField; rw [hA.at_.message, hA.at_.inner]; rfl
    have hW : cpl = true → n ≤ (E0 ++ b :: padOf cpl k n).length := by
      intro e; have := hfitS e; rw [pend] at this; rw [List.length_append, List.length_cons, padOf_len cpl k n e]
      have := hA.len; omega
    obtain ⟨C, hCe, hCl, hCn⟩ := qshape_body_c hA.shape y hA.scanSkip ob cpl (E0 ++ b :: padOf cpl k n) hW
    rw [hA.path] at hCe
    apply payloadClass_ne ob cpl _ b k (padOf cpl k n) (padOf_len cpl k n)
    have e1 : (8 :: 1 :: (Pre ++ y :: E0) : List Byte) ++ b :: padOf cpl k n =
        8 :: 1 :: (Pre ++ y :: (E0 ++ b :: padOf cpl k n)) := by simp
    rw [e1, hCe]
    have hn1 : E0.length + 1 ≤ n := by have := hA.len; have := hA.rpos; omega
    have etake : (E0 ++ b :: padOf cpl k n).take n = E0 ++ b :: (padOf cpl k n).take (n - E0.length - 1) := by
      rw [List.take_append, List.take_of_length_le (by omega), show n - E0.length = (n - E0.length - 1) + 1 by omega]
      rfl
    rw [etake]
    unfold ReceiveSpec.requestBody
    rw [if_pos rfl]
    have hlenA := ReceiveStream.envelope_len ((E0 ++ b :: (padOf cpl k n).take (n - E0.length - 1)).length + 1)
      (E0 ++ b :: (padOf cpl k n).take (n - E0.length - 1))
    rw [show (8 :: 1 :: (Pre ++ y :: E0) : List Byte).length + 1 = C.length + (E0.length + 1) by
      rw [hCl]; simp; omega]
    apply noerr_take_append hCn
    rw [List.take_append_of_le_length (by rw [hlenA]; simp)]
    have hw0 : ∀ X, envWalk [] 0 0 (E0 ++ X) = L ++ envWalk hd0 p0 0 X := hA.walk
    exact env_class_noerr E0 b _ L hd0 p0 0 hw0 hA.walkLen
  refine ⟨?_, hcls⟩
  have hwalk := hA.walk
  rcases hcase with ⟨bd, hq, s2skip, hz, hnz⟩ | ⟨n', cf, hq, npos, nle, s2skip, s2inner⟩
  · -- the scanner asks for more
    have k1 : t1.skip = 0 := by rw [s2skip, ← ht.skip, hsk]
    have hw1 : ∀ X, envWalk hd0 p0 0 (b :: X) = true :: envWalk (hd0 ++ [b]) p0 0 X := fun X => walk_more1 hq
    by_cases hr : r0 - 1 = 0
    · have i1 := hz hr
      cases done
      · rcases hd with ⟨-, e⟩ | ⟨e, -⟩
        · have q := msgEq_of_view e
          simp only [Bool.false_eq_true, if_false]
          have hE1 : (E0 ++ [b]).length = n := by have := hA.len; simp; omega
          have hL1 : (L ++ [true]).length = (E0 ++ [b]).length := by simp [hA.walkLen]
          have hne := ReceiveEnvDone.envelope_noErr (E0 ++ [b]) (L ++ [true]) (hd0 ++ [b]) p0 0 hL1
            (by rw [List.append_assoc, List.singleton_append, hwalk, hw1, List.append_assoc]; rfl)
          have hneB : NoErr (ReceiveSpec.requestBody (scan (H0 ++ [y]) bs).2.path (E0 ++ [b])) := by
            rw [hA.path]; unfold ReceiveSpec.requestBody; rw [if_pos rfl, hE1]
            have := hne; rw [hE1] at this; exact this
          refine MsgSim.request ⟨by rw [q.message, m1], by rw [q.inner, i1], fun B hB => ?_⟩
            (by rw [q.reply, rp1]) (by rw [q.replySkipped, rs1]) (fun hp => by rw [q.skip, k1] at hp; omega)
          rw [q.skip, k1] at hB
          rw [List.eq_nil_of_length_eq_zero hB, List.append_nil, q.request, q.bodySkipped, rq1, bs1,
            List.append_assoc, List.cons_append]
          exact qshape_skip hA.shape y hA.scanSkip (E0 ++ [b]) hE1 hneB
        · cases e
      · obtain ⟨hm0, hc0⟩ := doneOK_clean hd
        simpa using MsgSim.empty hm0 hc0
    · have i1 := hnz hr
      cases done
      · rcases hd with ⟨-, e⟩ | ⟨e, -⟩
        · have q := msgEq_of_view e
          simp only [Bool.false_eq_true, if_false]
          refine MsgSim.env ⟨Pre, y, E0 ++ [b], H0, bs, n, hd0 ++ [b], p0, 0, r0 - 1, L ++ [true], by simp,
            hA.shape, by rw [q.request, rq1], by rw [q.bodySkipped, bs1], hA.scanSkip, hA.path,
            ⟨by rw [q.message, m1], by rw [q.inner, i1], by rw [q.skip, k1], Nat.zero_le _,
              by rw [q.request, rq1]; exact miss⟩, by omega, by have := hA.len; simp; omega,
            fun X => by rw [List.append_assoc, List.singleton_append, hwalk, hw1, List.append_assoc]; rfl,
            by simp [hA.walkLen]⟩ (by rw [q.reply, rp1]) (by rw [q.replySkipped, rs1])
        · cases e
      · rcases hd with ⟨e, -⟩ | ⟨-, -, hin, -⟩
        · cases e
        · rw [i1] at hin; cases hin
  · -- the scanner asks to pass over a payload
    have hw1 : ∀ X, envWalk hd0 p0 0 (b :: X) = true :: envWalk (hd0 ++ [b]) p0 n' X := fun X => walk_pass hq
    cases done
    · rcases hd with ⟨-, e⟩ | ⟨e, -⟩
      · have q := msgEq_of_view e
        simp only [Bool.false_eq_true, if_false]
        refine MsgSim.env ⟨Pre, y, E0 ++ [b], H0, bs, n, hd0 ++ [b], p0, n', r0 - 1, L ++ [true], by simp,
          hA.shape, by rw [q.request, rq1], by rw [q.bodySkipped, bs1], hA.scanSkip, hA.path,
          ⟨by rw [q.message, m1], by rw [q.inner, s2inner], by rw [q.skip, s2skip], nle,
            by rw [q.request, rq1]; exact miss⟩, by omega, by have := hA.len; simp; omega,
          fun X => by rw [List.append_assoc, List.singleton_append, hwalk, hw1, List.append_assoc]; rfl,
          by simp [hA.walkLen]⟩ (by rw [q.reply, rp1]) (by rw [q.replySkipped, rs1])
      · cases e
    · rcases hd with ⟨e, -⟩ | ⟨-, -, hin, -⟩
      · cases e
      · rw [s2inner] at hin; cases hin

/-! ### Every accepted byte keeps `Sim` -/

/-- The response's and request's steps keep the frame state, `upgraded` and `openBody`. -/
theorem chain_keep {t t1 t2 : State} {b : Byte} {m : List Byte} {data : Bool}
    (hrep : ((data && m == [8, 2]) = false ∧ t1 = t) ∨ ((data && m == [8, 2]) = true ∧ RepStep t b t1))
    (hreq : ((data && m == [8, 1]) = false ∧ t2 = t1) ∨
       ((data && m == [8, 1]) = true ∧
        ((∃ hd p r, t1.inner = some (hd, p, r) ∧ 0 < r ∧ envelopeAdvance t1 (hd ++ [b]) p (r - 1) = .ok t2) ∨
         (t1.inner = none ∧ ReqStep t1 b t2)))) :
    t2.frame = t.frame ∧ t2.upgraded = t.upgraded ∧ t2.openBody = t.openBody := by
  have h1 : t1.frame = t.frame ∧ t1.upgraded = t.upgraded ∧ t1.openBody = t.openBody := by
    rcases hrep with ⟨-, rfl⟩ | ⟨-, hr⟩
    · exact ⟨rfl, rfl, rfl⟩
    · cases hr with
      | more _ hv => exact ⟨vFrame hv, vUpgraded hv, vOpenBody hv⟩
      | skip _ hv => exact ⟨vFrame hv, vUpgraded hv, vOpenBody hv⟩
  have h2 : t2.frame = t1.frame ∧ t2.upgraded = t1.upgraded ∧ t2.openBody = t1.openBody := by
    rcases hreq with ⟨-, rfl⟩ | ⟨-, ⟨hd, p, r, -, -, ha⟩ | ⟨-, hq⟩⟩
    · exact ⟨rfl, rfl, rfl⟩
    · have hv := envelopeAdvance_view ha
      exact ⟨vFrame hv, vUpgraded hv, vOpenBody hv⟩
    · cases hq with
      | more _ hv => exact ⟨vFrame hv, vUpgraded hv, vOpenBody hv⟩
      | skip _ _ hv => exact ⟨vFrame hv, vUpgraded hv, vOpenBody hv⟩
      | env _ _ ha =>
        have hv := envelopeAdvance_view ha
        exact ⟨vFrame hv, vUpgraded hv, vOpenBody hv⟩
  exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Assembling `Sim` after a byte. -/
theorem sim_finish {ob : Bool} {s' t2 : State} {S' : FState} {st' : Stream.St} {n : Nat} {done : Bool}
    (cls : ReceiveSpec.Class) (hcls : cls ≠ .error) (hfs' : FrameSim S' st' n)
    (hframe : t2.frame = TlsWebSocketFrame.stateBytes S') (hup : t2.upgraded = true) (hob : t2.openBody = ob)
    (ho : overrun t2 = false) (hd : DoneOK done t2 s') (hmsg : MsgSim s' st'.msg) :
    Sim ob s' (st', decide (cls = .error)) n := by
  obtain ⟨f1, f2, f3⟩ := doneOK_frame hd
  exact ⟨by simp [hcls], by rw [f2, hup], by rw [f3, hob], ⟨S', by rw [f1, hframe], hfs'⟩, hmsg,
    fits_finish hfs' hframe ho hd⟩

/-- **A data frame's payload byte keeps `Sim`.** -/
theorem sim_step_data {ob : Bool} {s s' : State} {st1 : Stream.St} {n : Nat} {b : Byte} {c : Bool}
    {f cpl : Bool} {k : Nat} (hs : Sim ob s (st1, false) (n + 1)) (h : step s b = .ok (s', c))
    (hp : st1.phase = .payload false f cpl k) : Sim ob s' (Stream.stepF ob (st1, false) b n).2 n := by
  obtain ⟨S', s1, flags, hfs', hv1, hk, hpb⟩ := step_frame hs h
  rw [hp] at hpb
  simp only [dataOf, endOf, Bool.not_false, Bool.true_and] at hpb
  obtain ⟨hkind, hfd, t, t1, t2, ht, hrep, hreq, ho, hdone⟩ := pb_chain hpb
  obtain ⟨S, -, hfs⟩ := hs.frame
  have hph := hfs.phase
  rw [hp] at hph
  obtain ⟨-, -, hk1, -, -, -, -, hcpl, -⟩ := hph
  have ha := hv1
  simp only [view, View.mk.injEq] at ha
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := ha
  have hb := ht
  simp only [view, View.mk.injEq] at hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
  have hmA : msgAfter s1 b true = (if s.message.length < 2 then s.message ++ [b] else s.message) := by
    unfold msgAfter; rw [a1]; simp
  obtain ⟨k2f, k2u, k2o⟩ := chain_keep hrep hreq
  have hframe : t2.frame = TlsWebSocketFrame.stateBytes S' := by rw [k2f, b8, a8]
  have hup : t2.upgraded = true := by rw [k2u, b9, a9]; exact hs.up
  have hob : t2.openBody = ob := by rw [k2o, b11, a11]; exact hs.openBody
  -- what is left of the frame after the byte, with `complete`
  have hfit2 : cpl = true → pendingField t2 ≤ k - 1 := by
    intro e
    by_cases hk2 : k ≤ 1
    · have hk1' : k = 1 := by omega
      subst hk1'
      have hf : f = true := by
        rw [e] at hcpl; cases f
        · simp at hcpl
        · rfl
      subst hf
      rcases hdone with ⟨e', -⟩ | ⟨-, -, -, hp0, -⟩
      · cases e'
      · omega
    · have hph' : (Stream.step ob st1 b n).2.phase = .payload false f true (k - 1) := by
        obtain ⟨phase, msg, fr⟩ := st1
        simp only at hp; subst hp; subst e
        simp [Stream.step, hk2]
      exact fits_of_overrun hfs' hph' hframe ho
  -- the reference's side
  obtain ⟨phase, M, fr⟩ := st1
  simp only at hp
  subst hp
  obtain ⟨hcl, hmsg⟩ := stream_data ob M fr f cpl k b n hk1
  have hd' : DoneOK (f && k == 1) t2 s' := hdone
  have hfitS : cpl = true → pendingField s ≤ k := by
    intro e; have := hs.fits; simp only [Fits] at this; rw [e] at this; exact this
  -- the message side, case by case
  have hM := hs.msg
  simp only at hM
  have key : MsgSim s' (if (f && k == 1) = true then [] else M ++ [b]) ∧
      Stream.payloadClass ob cpl M b k ≠ .error := by
    cases hM with
    | empty hm0 hc =>
      rw [hm0] at hmA
      simp only [List.length_nil, Nat.zero_lt_two, if_true, List.nil_append] at hmA
      rw [hm0] at hfd
      have hdn : (f && k == 1) = false := by simpa using hfd
      rw [hmA] at hrep hreq b1
      have e1 : t1 = t := by
        rcases hrep with ⟨-, e⟩ | ⟨e, -⟩
        · exact e
        · simp at e
      have e2 : t2 = t1 := by
        rcases hreq with ⟨-, e⟩ | ⟨e, -⟩
        · exact e
        · simp at e
      subst e1 e2
      rw [hdn] at hd' ⊢
      rcases hd' with ⟨-, e⟩ | ⟨e, -⟩
      · have q := msgEq_of_view e
        refine ⟨?_, ?_⟩
        · simp only [Bool.false_eq_true, if_false, List.nil_append]
          refine MsgSim.one (by rw [q.message, b1]) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [q.skip, b4, a4, hc.skip]
          · rw [q.inner, b5, a5, hc.inner]
          · rw [q.reply, b6, a6, hc.reply]
          · rw [q.replySkipped, b7, a7, hc.replySkipped]
          · rw [q.request, b2, a2, hc.request]
          · rw [q.bodySkipped, b3, a3, hc.bodySkipped]
        · apply payloadClass_ne ob cpl [] b k (padOf cpl k 0) (padOf_len cpl k 0)
          intro x hx
          rw [List.length_nil, Nat.zero_add, List.nil_append, ReceiveStream.message_take1] at hx
          simp at hx; rw [hx]; decide
      · cases e
    | @one a hm0 hc =>
      rw [hm0] at hmA
      simp only [List.length_singleton, Nat.one_lt_two, if_true, List.singleton_append] at hmA
      rw [hmA] at hkind hrep hreq b1
      have hab : (a = 8 ∧ b = 2) ∨ (a = 8 ∧ b = 1) := by
        unfold kindOK at hkind
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_irrefl, decide_false,
          Bool.false_or, Bool.or_eq_true, beq_iff_eq, List.cons.injEq, and_true] at hkind
        rcases hkind with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
      have hcls : Stream.payloadClass ob cpl [a] b k ≠ .error := by
        apply payloadClass_ne ob cpl [a] b k (padOf cpl k 0) (padOf_len cpl k 0)
        intro x hx
        rw [List.singleton_append] at hx
        rw [ReceiveStream.message_eq] at hx
        simp only [List.length_singleton, Nat.reduceAdd, List.take_succ_cons, List.take_zero] at hx
        split at hx <;> (try split at hx) <;>
          (simp at hx; rcases hx with rfl | rfl <;> decide)
      refine ⟨?_, hcls⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- a response begins
        have e2 : t2 = t1 := by
          rcases hreq with ⟨-, e⟩ | ⟨e, -⟩
          · exact e
          · simp at e
        subst e2
        rcases hrep with ⟨e, -⟩ | ⟨-, hr⟩
        · simp at e
        have hrA : repAfter t 2 = [8, 2] := by
          unfold repAfter; rw [b6, a6, hc.reply]; rfl
        cases hr with
        | skip hm hv =>
          rw [hrA] at hm
          have : (replyScan [8, 2] t.replySkipped t.openBody).1 = .more := by rw [replyScan_eq]; rfl
          rw [this] at hm; cases hm
        | more hm hv =>
          have hv' := hv
          simp only [view, View.mk.injEq] at hv'
          obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, -, -, c11⟩ := hv'
          cases hdk : (f && k == 1)
          · rw [hdk] at hd'
            rcases hd' with ⟨-, e⟩ | ⟨e, -⟩
            · have q := msgEq_of_view e
              simp only [Bool.false_eq_true, if_false, List.singleton_append]
              refine MsgSim.reply ⟨by rw [q.message, c1, b1], fun B hB => ?_⟩ ?_ ?_ ?_ ?_
              · rw [q.skip, c4, b4, a4, hc.skip] at hB
                rw [List.eq_nil_of_length_eq_zero hB, q.reply, q.replySkipped, q.openBody, c6, hrA, c7, b7, a7,
                  hc.replySkipped, c11, b11, a11]
                exact RShape.kind
              · rw [q.request, c2, b2, a2, hc.request]
              · rw [q.bodySkipped, c3, b3, a3, hc.bodySkipped]
              · rw [q.inner, c5, b5, a5, hc.inner]
              · intro hp; rw [q.skip, c4, b4, a4, hc.skip] at hp; omega
            · cases e
          · rw [hdk] at hd'
            obtain ⟨hm0', hc0⟩ := doneOK_clean hd'
            simpa using MsgSim.empty hm0' hc0
      · -- a server request begins
        have e1 : t1 = t := by
          rcases hrep with ⟨-, e⟩ | ⟨e, -⟩
          · exact e
          · simp at e
        subst e1
        rcases hreq with ⟨e, -⟩ | ⟨-, ⟨hd, p, r, hi, -⟩ | ⟨hi, hq⟩⟩
        · simp at e
        · rw [b5, a5, hc.inner] at hi; cases hi
        have hqA : reqAfter t1 1 = [8, 1] := by
          unfold reqAfter; rw [b2, a2, hc.request]; rfl
        have hsc : scan [8, 1] t1.bodySkipped = (.more, {}) := by rw [scan_eq]; rfl
        cases hq with
        | skip hm _ _ => rw [hqA, hsc] at hm; cases hm
        | env hm _ _ => rw [hqA, hsc] at hm; cases hm
        | more hm hv =>
          have hv' := hv
          simp only [view, View.mk.injEq] at hv'
          obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, -, -, c11⟩ := hv'
          cases hdk : (f && k == 1)
          · rw [hdk] at hd'
            rcases hd' with ⟨-, e⟩ | ⟨e, -⟩
            · have q := msgEq_of_view e
              simp only [Bool.false_eq_true, if_false, List.singleton_append]
              refine MsgSim.request ⟨by rw [q.message, c1, b1], by rw [q.inner, c5, b5, a5, hc.inner],
                fun B hB => ?_⟩ ?_ ?_ ?_
              · rw [q.skip, c4, b4, a4, hc.skip] at hB
                rw [List.eq_nil_of_length_eq_zero hB, q.request, q.bodySkipped, c2, hqA, c3, b3, a3,
                  hc.bodySkipped]
                exact QShape.kind
              · rw [q.reply, c6, b6, a6, hc.reply]
              · rw [q.replySkipped, c7, b7, a7, hc.replySkipped]
              · intro hp; rw [q.skip, c4, b4, a4, hc.skip] at hp; omega
            · cases e
          · rw [hdk] at hd'
            obtain ⟨hm0', hc0⟩ := doneOK_clean hd'
            simpa using MsgSim.empty hm0' hc0
    | @reply P hR hreq0 hbs0 hin0 _ =>
      have hm8 : s.message = [8, 2] := hR.message
      rw [hm8] at hmA
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_irrefl, if_false] at hmA
      rw [hmA] at hrep hreq
      have e2 : t2 = t1 := by
        rcases hreq with ⟨-, e⟩ | ⟨e, -⟩
        · exact e
        · simp at e
      subst e2
      rcases hrep with ⟨e, -⟩ | ⟨-, hr⟩
      · simp at e
      have hmt : MsgEq s t := ⟨by rw [b1, hmA, hm8], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4],
        by rw [b5, a5], by rw [b6, a6], by rw [b7, a7], by rw [b11, a11]⟩
      have := data_reply (ob := ob) (cpl := cpl) (k := k) hR hreq0 hbs0 hin0 hs.openBody hk hmt hr hd' hfit2
      simpa using this
    | @request P hQ hrep0 hrs0 _ =>
      have hm8 : s.message = [8, 1] := hQ.message
      rw [hm8] at hmA
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_irrefl, if_false] at hmA
      rw [hmA] at hrep hreq
      have e1 : t1 = t := by
        rcases hrep with ⟨-, e⟩ | ⟨e, -⟩
        · exact e
        · simp at e
      subst e1
      have hmt : MsgEq s t1 := ⟨by rw [b1, hmA, hm8], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4],
        by rw [b5, a5], by rw [b6, a6], by rw [b7, a7], by rw [b11, a11]⟩
      rcases hreq with ⟨e, -⟩ | ⟨-, ⟨hd, p, r, hi, -⟩ | ⟨-, hq⟩⟩
      · simp at e
      · rw [← hmt.inner, hQ.inner] at hi; cases hi
      have := data_request (ob := ob) (cpl := cpl) (k := k) hQ hrep0 hrs0 hk hmt hq hd' hfit2
      simpa using this
    | @env P hE hrep0 hrs0 =>
      obtain ⟨Pre, y, E0, H0, bs, n0, hd0, p0, k0, r0, L, hP, hA⟩ := hE
      have hm8 : s.message = [8, 1] := hA.at_.message
      rw [hm8] at hmA
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_irrefl, if_false] at hmA
      rw [hmA] at hrep hreq
      have e1 : t1 = t := by
        rcases hrep with ⟨-, e⟩ | ⟨e, -⟩
        · exact e
        · simp at e
      subst e1
      have hmt : MsgEq s t1 := ⟨by rw [b1, hmA, hm8], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4],
        by rw [b5, a5], by rw [b6, a6], by rw [b7, a7], by rw [b11, a11]⟩
      rcases hreq with ⟨e, -⟩ | ⟨-, hadv | ⟨hi, -⟩⟩
      · simp at e
      · have := data_env (ob := ob) (cpl := cpl) (k := k) ⟨Pre, y, E0, H0, bs, n0, hd0, p0, k0, r0, L, hP, hA⟩
          hrep0 hrs0 hk hfitS hmt hadv hd'
        simpa using this
      · rw [← hmt.inner, hA.at_.inner] at hi; cases hi
  obtain ⟨hmsg', hcls'⟩ := key
  have := sim_finish (Stream.step ob ⟨.payload false f cpl k, M, fr⟩ b n).1 (by rw [hcl]; exact hcls') hfs' hframe hup hob
    ho hd' (by rw [hmsg]; exact hmsg')
  simpa [Stream.stepF] using this

/-- **Every byte the controller accepts keeps `Sim`** (`step` succeeding). -/
theorem sim_step {ob : Bool} {s s' : State} {st1 : Stream.St} {n : Nat} {b : Byte} {c : Bool}
    (hs : Sim ob s (st1, false) (n + 1)) (h : step s b = .ok (s', c)) :
    Sim ob s' (Stream.stepF ob (st1, false) b n).2 n := by
  cases hd : dataOf st1.phase
  · exact sim_step_nodata hs h hd
  · obtain ⟨phase, msg, fr⟩ := st1
    cases phase with
    | payload c0 f cpl k =>
      cases c0
      · exact sim_step_data hs h rfl
      · simp [dataOf] at hd
    | _ => simp [dataOf] at hd

/-! ### Every byte the controller passes over keeps `Sim` -/

/-- The frame side of a passed-over byte: it is a data frame's payload byte (the parser ran on a zero
in its place, which the reference's position does not depend on). -/
theorem pass_frame {ob : Bool} {s : State} {st1 : Stream.St} {n : Nat} (hs : Sim ob s (st1, false) (n + 1))
    (h0 : PublicReceive.get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 0 = on)
    (h1 : PublicReceive.get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 1 = on) (b : Byte) :
    ∃ S' f cpl k, st1.phase = .payload false f cpl k ∧ FrameSim S' (Stream.step ob st1 b n).2 n ∧
      (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])).drop 8 = TlsWebSocketFrame.stateBytes S' ∧
      (PublicReceive.get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0])) 5 == on) = (f && k == 1) := by
  obtain ⟨S, hS, hfs⟩ := hs.frame
  have hrun : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) =
      eventBytes (TlsWebSocketFrame.step fast capacity S 0) ++
        TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.step fast capacity S 0).state := by
    rw [hS]; exact runByte_active capacity S hfs.shaped 0
  rw [hrun] at h0 h1 ⊢
  have hlen := TlsMpc.KernelSpecs.ParseWebSocketFrame.eventBytes_length (TlsWebSocketFrame.step fast capacity S 0)
  rw [get_app_left _ _ 0 (by omega), get_eventBytes0] at h0
  rw [get_app_left _ _ 1 (by omega), get_eventBytes1, h0, and_on'] at h1
  obtain ⟨hfs0, hd, hdn⟩ := frame_sim_step ob hfs h0
  rw [hd] at h1
  have hdat : dataOf st1.phase = true := by rw [← mb_beq_on (dataOf st1.phase), h1]; rfl
  obtain ⟨phase, msg, fr⟩ := st1
  cases phase with
  | payload c0 f cpl k =>
    cases c0
    · obtain ⟨e1, e2⟩ := step_payload_indep ob (st := ⟨.payload false f cpl k, msg, fr⟩) rfl 0 b n
      refine ⟨_, f, cpl, k, rfl, frameSim_congr hfs0 e1.symm e2.symm, List.drop_left' hlen, ?_⟩
      rw [get_app_left _ _ 5 (by omega), get_eventBytes5, h0, and_on', hdn, mb_beq_on]
      simp [endOf]
    · simp [dataOf] at hdat
  | _ => simp [dataOf] at hdat

/-- The class of a passed-over body byte, inside a response. -/
theorem pass_reply_class {ob cpl : Bool} {s : State} {P : List Byte} {b : Byte} {k : Nat}
    (hR : ReplyIn s P) (hob : s.openBody = ob) (hk : 0 < s.skip) (hmiss0 : replyMissing s.reply s.openBody = 0)
    (hfitS : cpl = true → s.skip ≤ k) : Stream.payloadClass ob cpl (8 :: 2 :: P) b k ≠ .error := by
  have hW : s.skip - 1 ≤ (padOf cpl k (s.skip - 1)).length := by
    unfold padOf; cases cpl
    · simp
    · have := hfitS rfl; simp; omega
  have hsh := hR.shape (b :: (padOf cpl k (s.skip - 1)).take (s.skip - 1)) (by simp; omega)
  rw [hob] at hsh hmiss0
  have hn := rshape_noerr_c (c := cpl) hsh ((padOf cpl k (s.skip - 1)).drop (s.skip - 1))
    (fun _ => by rw [hmiss0]; exact Nat.zero_le _)
  apply payloadClass_ne ob cpl (8 :: 2 :: P) b k (padOf cpl k (s.skip - 1)) (padOf_len cpl k _)
  have hn' := noerr_take_le (n := (8 :: 2 :: P).length + 1) (by simp; omega) hn
  have e1 : (8 :: 2 :: ((P ++ b :: (padOf cpl k (s.skip - 1)).take (s.skip - 1)) ++
      (padOf cpl k (s.skip - 1)).drop (s.skip - 1)) : List Byte) = (8 :: 2 :: P) ++ b :: padOf cpl k (s.skip - 1) := by
    simp [List.take_append_drop]
  rw [e1] at hn'
  exact hn'

/-- The class of a passed-over body byte, inside a server request (no envelope). -/
theorem pass_request_class {ob cpl : Bool} {s : State} {P : List Byte} {b : Byte} {k : Nat}
    (hQ : QIn s P) (hk : 0 < s.skip) (hmiss0 : fieldMissing s.request = 0)
    (hfitS : cpl = true → s.skip ≤ k) : Stream.payloadClass ob cpl (8 :: 1 :: P) b k ≠ .error := by
  have hW : s.skip - 1 ≤ (padOf cpl k (s.skip - 1)).length := by
    unfold padOf; cases cpl
    · simp
    · have := hfitS rfl; simp; omega
  have hsh := hQ.shape (b :: (padOf cpl k (s.skip - 1)).take (s.skip - 1)) (by simp; omega)
  have hn := qshape_noerr_c hsh ob cpl ((padOf cpl k (s.skip - 1)).drop (s.skip - 1))
    (fun _ => by rw [hmiss0]; exact Nat.zero_le _)
  apply payloadClass_ne ob cpl (8 :: 1 :: P) b k (padOf cpl k (s.skip - 1)) (padOf_len cpl k _)
  have hn' := noerr_take_le (n := (8 :: 1 :: P).length + 1) (by simp; omega) hn
  have e1 : (8 :: 1 :: ((P ++ b :: (padOf cpl k (s.skip - 1)).take (s.skip - 1)) ++
      (padOf cpl k (s.skip - 1)).drop (s.skip - 1)) : List Byte) = (8 :: 1 :: P) ++ b :: padOf cpl k (s.skip - 1) := by
    simp [List.take_append_drop]
  rw [e1] at hn'
  exact hn'

/-- The class of a passed-over byte of a delivered envelope. -/
theorem pass_env_class {ob cpl : Bool} {s : State} {Pre E0 H0 : List Byte} {y b : Byte} {bs : Bool}
    {n0 : Nat} {hd0 : List Byte} {p0 k0 r0 : Nat} {L : List Bool} {k : Nat}
    (hA : EnvAtP s Pre y E0 H0 bs n0 hd0 p0 k0 r0 L) (hfitS : cpl = true → r0 ≤ k) :
    Stream.payloadClass ob cpl (8 :: 1 :: (Pre ++ y :: E0)) b k ≠ .error := by
  have hW : cpl = true → n0 ≤ (E0 ++ b :: padOf cpl k n0).length := by
    intro e; have := hfitS e; rw [List.length_append, List.length_cons, padOf_len cpl k n0 e]
    have := hA.len; omega
  obtain ⟨C, hCe, hCl, hCn⟩ := qshape_body_c hA.shape y hA.scanSkip ob cpl (E0 ++ b :: padOf cpl k n0) hW
  rw [hA.path] at hCe
  apply payloadClass_ne ob cpl _ b k (padOf cpl k n0) (padOf_len cpl k n0)
  have e1 : (8 :: 1 :: (Pre ++ y :: E0) : List Byte) ++ b :: padOf cpl k n0 =
      8 :: 1 :: (Pre ++ y :: (E0 ++ b :: padOf cpl k n0)) := by simp
  rw [e1, hCe]
  have hn1 : E0.length + 1 ≤ n0 := by have := hA.len; have := hA.rpos; omega
  have etake : (E0 ++ b :: padOf cpl k n0).take n0 = E0 ++ b :: (padOf cpl k n0).take (n0 - E0.length - 1) := by
    rw [List.take_append, List.take_of_length_le (by omega), show n0 - E0.length = (n0 - E0.length - 1) + 1 by omega]
    rfl
  rw [etake]
  unfold ReceiveSpec.requestBody
  rw [if_pos rfl]
  have hlenA := ReceiveStream.envelope_len ((E0 ++ b :: (padOf cpl k n0).take (n0 - E0.length - 1)).length + 1)
    (E0 ++ b :: (padOf cpl k n0).take (n0 - E0.length - 1))
  rw [show (8 :: 1 :: (Pre ++ y :: E0) : List Byte).length + 1 = C.length + (E0.length + 1) by
    rw [hCl]; simp; omega]
  apply noerr_take_append hCn
  rw [List.take_append_of_le_length (by rw [hlenA]; simp)]
  exact env_class_noerr E0 b _ L hd0 p0 k0 hA.walk hA.walkLen

/-- Assembling `Sim` after a passed-over byte. -/
theorem pass_finish {ob : Bool} {s' : State} {S' : FState} {f cpl : Bool} {k : Nat} {M : List Byte} {fr : Bool}
    {n : Nat} {b : Byte} (hcls : Stream.payloadClass ob cpl M b k ≠ .error) (hk1 : 1 ≤ k)
    (hfs' : FrameSim S' (Stream.step ob ⟨.payload false f cpl k, M, fr⟩ b n).2 n)
    (hframe : s'.frame = TlsWebSocketFrame.stateBytes S') (hup : s'.upgraded = true) (hob : s'.openBody = ob)
    (hmsg : MsgSim s' (if (f && k == 1) = true then [] else M ++ [b]))
    (hfit : cpl = true → 2 ≤ k → pendingField s' ≤ k - 1) :
    Sim ob s' (Stream.stepF ob (⟨.payload false f cpl k, M, fr⟩, false) b n).2 n := by
  obtain ⟨hcl, hm⟩ := stream_data ob M fr f cpl k b n hk1
  simp only [Stream.stepF, Bool.false_eq_true, if_false]
  refine ⟨by simp [hcl, hcls], hup, hob, ⟨S', hframe, hfs'⟩, by rw [hm]; exact hmsg, ?_⟩
  simp only [Stream.step, Bool.false_eq_true, if_false]
  by_cases hk : k ≤ 1
  · rw [if_pos hk]; unfold Stream.endFrame
    cases f <;> simp [Fits]
  · rw [if_neg hk]
    simp only [Fits]
    cases cpl
    · trivial
    · exact hfit rfl (by omega)

theorem pending_reset {s' : State} (h : s'.message = []) : pendingField s' = 0 := by
  unfold pendingField; rw [h]; rfl

/-- **Every byte the controller passes over keeps `Sim`** (`passOne` succeeding). -/
theorem sim_pass {ob : Bool} {s s' : State} {st1 : Stream.St} {n : Nat} {b : Byte} {d : Bool}
    (hs : Sim ob s (st1, false) (n + 1)) (h : passOne s = .ok (s', d)) :
    Sim ob s' (Stream.stepF ob (st1, false) b n).2 n := by
  obtain ⟨phase, M, fr⟩ := st1
  have hfits := hs.fits
  have hM := hs.msg
  obtain ⟨S, -, hfs⟩ := hs.frame
  have hob : s.openBody = ob := hs.openBody
  simp only at hfits hM hfs
  unfold passOne at h
  by_cases hm2 : s.message = [8, 2]
  · rw [if_pos (by rw [hm2]; rfl)] at h
    obtain ⟨hu, hpos, -, F0, F1, hcase⟩ := stepPassed_view h
    obtain ⟨S', f, cpl, k, hp, hfs', hF8, hF5⟩ := pass_frame hs F0 F1 b
    simp only at hp
    subst hp
    obtain ⟨-, -, hk1, -⟩ := hfs.phase
    have hfitS : cpl = true → s.skip ≤ k := by
      intro e; simp only [Fits, e] at hfits
      unfold pendingField at hfits; rw [hm2] at hfits
      simp only [show (([8, 2] : List Byte) == [8, 1]) = false by decide, Bool.false_eq_true, if_false,
        beq_self_eq_true, if_true, if_pos hpos] at hfits
      exact hfits
    cases hM with
    | empty a _ => rw [a] at hm2; cases hm2
    | one a _ => rw [a] at hm2; cases hm2
    | request hQ _ _ _ => rw [hQ.message] at hm2; cases hm2
    | env hE _ _ =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hA⟩ := hE
      rw [hA.at_.message] at hm2; cases hm2
    | @reply P hR hreq0 hbs0 hin0 hmiss0 =>
      have hcls := pass_reply_class (cpl := cpl) (b := b) hR hob hpos (hmiss0 hpos) hfitS
      rcases hcase with ⟨e5, e⟩ | ⟨e5, hz, e⟩
      · rw [hF5] at e5
        simp only [view, View.mk.injEq] at e
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, -, g11⟩ := e
        apply pass_finish hcls hk1 hfs' (by rw [g8, hF8]) (by rw [g9]; exact hu) (by rw [g11]; exact hob)
        · rw [e5]
          simp only [Bool.false_eq_true, if_false, List.cons_append]
          refine MsgSim.reply ⟨by rw [g1, hm2], fun B hB => ?_⟩ (by rw [g2, hreq0]) (by rw [g3, hbs0])
            (by rw [g5, hin0]) (fun _ => by rw [g6, g11]; exact hmiss0 hpos)
          rw [g4] at hB
          rw [g6, g7, g11, List.append_assoc, List.singleton_append]
          exact hR.shape (b :: B) (by simp; omega)
        · intro e1 _
          have h1 := hfitS e1
          unfold pendingField; rw [g1, hm2, g4]
          simp only [show (([8, 2] : List Byte) == [8, 1]) = false by decide, Bool.false_eq_true, if_false,
            beq_self_eq_true, if_true]
          split
          · omega
          · rw [g6, g11, hmiss0 hpos]; exact Nat.zero_le _
      · rw [hF5] at e5
        simp only [view, View.mk.injEq] at e
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, -, g11⟩ := e
        apply pass_finish hcls hk1 hfs' (by rw [g8, hF8]) (by rw [g9]; exact hu) (by rw [g11]; exact hob)
        · rw [e5]
          simp only [if_true]
          exact MsgSim.empty g1 ⟨g4, by rw [g5, hin0], g6, g7, by rw [g2, hreq0], by rw [g3, hbs0]⟩
        · intro _ _; rw [pending_reset g1]; exact Nat.zero_le _
  · rw [if_neg (by simpa using hm2)] at h
    obtain ⟨s2, h2, h3⟩ := bind_ok h
    cases h3
    cases hM with
    | empty a hc =>
      have := (stepSkipped_none hc.inner h2).2.2.1
      rw [a] at this; cases this
    | one a hc =>
      have := (stepSkipped_none hc.inner h2).2.2.1
      rw [a] at this; cases this
    | reply hR _ _ _ _ => exact absurd hR.message hm2
    | @request P hQ hrep0 hrs0 hmiss0 =>
      obtain ⟨hu, hpos, hm1, F0, F1, hcase⟩ := stepSkipped_none hQ.inner h2
      obtain ⟨S', f, cpl, k, hp, hfs', hF8, hF5⟩ := pass_frame hs F0 F1 b
      simp only at hp
      subst hp
      obtain ⟨-, -, hk1, -⟩ := hfs.phase
      have hfitS : cpl = true → s.skip ≤ k := by
        intro e; simp only [Fits, e] at hfits
        unfold pendingField at hfits; rw [hm1, hQ.inner] at hfits
        simp only [beq_self_eq_true, if_true, if_pos hpos] at hfits
        exact hfits
      have hcls := pass_request_class (ob := ob) (cpl := cpl) (b := b) hQ hpos (hmiss0 hpos) hfitS
      rcases hcase with ⟨e5, e⟩ | ⟨e5, hz, e⟩
      · rw [hF5] at e5
        simp only [view, View.mk.injEq] at e
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, -, g11⟩ := e
        apply pass_finish hcls hk1 hfs' (by rw [g8, hF8]) (by rw [g9]; exact hu) (by rw [g11]; exact hob)
        · rw [e5]
          simp only [Bool.false_eq_true, if_false, List.cons_append]
          refine MsgSim.request ⟨by rw [g1, hm1], by rw [g5, hQ.inner], fun B hB => ?_⟩ (by rw [g6, hrep0])
            (by rw [g7, hrs0]) (fun _ => by rw [g2]; exact hmiss0 hpos)
          rw [g4] at hB
          rw [g2, g3, List.append_assoc, List.singleton_append]
          exact hQ.shape (b :: B) (by simp; omega)
        · intro e1 _
          have h1 := hfitS e1
          unfold pendingField; rw [g1, hm1, g5, hQ.inner, g4]
          simp only [beq_self_eq_true, if_true]
          split
          · omega
          · rw [g2, hmiss0 hpos]; exact Nat.zero_le _
      · rw [hF5] at e5
        simp only [view, View.mk.injEq] at e
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, -, g11⟩ := e
        apply pass_finish hcls hk1 hfs' (by rw [g8, hF8]) (by rw [g9]; exact hu) (by rw [g11]; exact hob)
        · rw [e5]
          simp only [if_true]
          exact MsgSim.empty g1 ⟨g4, by rw [g5, hQ.inner], by rw [g6, hrep0], by rw [g7, hrs0], g2, g3⟩
        · intro _ _; rw [pending_reset g1]; exact Nat.zero_le _
    | @env P hE hrep0 hrs0 =>
      obtain ⟨Pre, y, E0, H0, bs, n0, hd0, p0, k0, r0, L, hP, hA⟩ := hE
      subst hP
      obtain ⟨hu, hpos, hm1, hr, F0, F1, t2, ht2, hcase⟩ := stepSkipped_some hA.at_.inner h2
      obtain ⟨S', f, cpl, k, hp, hfs', hF8, hF5⟩ := pass_frame hs F0 F1 b
      simp only at hp
      subst hp
      obtain ⟨-, -, hk1, -⟩ := hfs.phase
      have pend : pendingField s = r0 := by unfold pendingField; rw [hA.at_.message, hA.at_.inner]; rfl
      have hfitS : cpl = true → r0 ≤ k := by
        intro e; simp only [Fits, e] at hfits; rw [pend] at hfits; exact hfits
      have hcls := pass_env_class (ob := ob) (b := b) hA hfitS
      have hk0 : k0 = (k0 - 1) + 1 := by have := hA.at_.skip; omega
      have hAt : EnvAt s hd0 p0 ((k0 - 1) + 1) r0 := by rw [← hk0]; exact hA.at_
      -- t2: the frame, the request and its flags kept
      have ht2v : t2.frame = TlsWebSocketFrame.stateBytes S' ∧ t2.upgraded = s.upgraded ∧
          t2.openBody = s.openBody ∧ t2.message = s.message ∧ t2.request = s.request ∧
          t2.bodySkipped = s.bodySkipped ∧ t2.reply = s.reply ∧ t2.replySkipped = s.replySkipped := by
        rcases ht2 with ⟨-, e⟩ | ⟨-, t, et, ea⟩
        · simp only [view, View.mk.injEq] at e
          obtain ⟨g1, g2, g3, -, -, g6, g7, g8, g9, -, g11⟩ := e
          exact ⟨by rw [g8, hF8], g9, g11, g1, g2, g3, g6, g7⟩
        · have e2 := envelopeAdvance_view ea
          simp only [view, View.mk.injEq] at e2 et
          obtain ⟨g1, g2, g3, -, -, g6, g7, g8, g9, -, g11⟩ := e2
          obtain ⟨h1, h2', h3, -, -, h6, h7, h8, h9, -, h11⟩ := et
          exact ⟨by rw [g8, h8, hF8], by rw [g9, h9], by rw [g11, h11], by rw [g1, h1], by rw [g2, h2'],
            by rw [g3, h3], by rw [g6, h6], by rw [g7, h7]⟩
      obtain ⟨f2f, f2u, f2o, f2m, f2r, f2b, f2p, f2q⟩ := ht2v
      rcases hcase with ⟨e5, e⟩ | ⟨e5, hz2, hin2, e⟩
      · -- the message goes on
        rw [hF5] at e5
        have eq := e
        simp only [view, View.mk.injEq] at eq
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, -, g11⟩ := eq
        apply pass_finish hcls hk1 hfs' (by rw [g8, f2f]) (by rw [g9, f2u]; exact hu) (by rw [g11, f2o]; exact hob)
        · rw [e5]
          simp only [Bool.false_eq_true, if_false, List.cons_append]
          by_cases hr1 : r0 - 1 = 0
          · -- the envelope ends at this byte
            obtain ⟨h'', p'', k'', hw0, hdone, -⟩ := env_pass hAt h2 b [0]
            obtain ⟨hin', hsk'⟩ := hdone hr1
            have hE1 : (E0 ++ [b]).length = n0 := by have := hA.len; simp; omega
            have hL1 : (L ++ [false]).length = (E0 ++ [b]).length := by simp [hA.walkLen]
            have hne := ReceiveEnvDone.envelope_noErr (E0 ++ [b]) (L ++ [false]) h'' p'' k'' hL1
              (by rw [List.append_assoc, List.singleton_append, hA.walk, hk0, hw0, List.append_assoc]; rfl)
            have hneB : NoErr (ReceiveSpec.requestBody (scan (H0 ++ [y]) bs).2.path (E0 ++ [b])) := by
              rw [hA.path]; unfold ReceiveSpec.requestBody; rw [if_pos rfl, hE1]
              have := hne; rw [hE1] at this; exact this
            refine MsgSim.request ⟨by rw [g1, f2m, hm1], hin', fun B hB => ?_⟩
              (by rw [g6, f2p, hrep0]) (by rw [g7, f2q, hrs0]) (fun hp => by rw [hsk'] at hp; omega)
            rw [hsk'] at hB
            rw [List.eq_nil_of_length_eq_zero hB, List.append_nil, g2, g3, f2r, f2b, hA.request, hA.bodySkipped,
              List.append_assoc, List.cons_append]
            exact qshape_skip hA.shape y hA.scanSkip (E0 ++ [b]) hE1 hneB
          · -- the walk goes on
            obtain ⟨h1, p1, k1, -, -, hat⟩ := env_pass hAt h2 b []
            have hat' := hat hr1
            refine MsgSim.env ⟨Pre, y, E0 ++ [b], H0, bs, n0, h1, p1, k1, r0 - 1, L ++ [false], by simp,
              hA.shape, by rw [g2, f2r, hA.request], by rw [g3, f2b, hA.bodySkipped], hA.scanSkip, hA.path,
              hat', by omega, by have := hA.len; simp; omega, fun X => ?_, by simp [hA.walkLen]⟩
              (by rw [g6, f2p, hrep0]) (by rw [g7, f2q, hrs0])
            obtain ⟨h2', p2', k2', hw2, -, hat2⟩ := env_pass hAt h2 b X
            have hat2' := hat2 hr1
            have e1 : some (h2', p2', r0 - 1) = some (h1, p1, r0 - 1) := by rw [← hat2'.inner, hat'.inner]
            simp only [Option.some.injEq, Prod.mk.injEq] at e1
            obtain ⟨rfl, rfl, -⟩ := e1
            have e2 : k2' = k1 := by rw [← hat2'.skip, hat'.skip]
            subst e2
            rw [List.append_assoc, List.singleton_append, hA.walk, hk0, hw2, List.append_assoc]; rfl
        · intro e1 _
          have hrk := hfitS e1
          unfold pendingField; rw [g1, f2m, hm1]
          simp only [beq_self_eq_true, if_true]
          by_cases hr1 : r0 - 1 = 0
          · obtain ⟨h1, p1, k1, -, hdone, -⟩ := env_pass hAt h2 b []
            obtain ⟨hin', hsk'⟩ := hdone hr1
            rw [hin', hsk']
            simp only [Nat.lt_irrefl, if_false, gt_iff_lt]
            rw [g2, f2r, hA.at_.missing]; exact Nat.zero_le _
          · obtain ⟨h1, p1, k1, -, -, hat⟩ := env_pass hAt h2 b []
            rw [(hat hr1).inner]; show r0 - 1 ≤ k - 1; omega
      · -- the message ends at this byte
        rw [hF5] at e5
        have eq := e
        simp only [view, View.mk.injEq] at eq
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, -, g11⟩ := eq
        apply pass_finish hcls hk1 hfs' (by rw [g8, f2f]) (by rw [g9, f2u]; exact hu) (by rw [g11, f2o]; exact hob)
        · rw [e5]
          simp only [if_true]
          exact MsgSim.empty g1 ⟨by rw [g4, hz2], by rw [g5, hin2], by rw [g6, f2p, hrep0],
            by rw [g7, f2q, hrs0], g2, g3⟩
        · intro _ _; rw [pending_reset g1]; exact Nat.zero_le _

end ReceiveSim

