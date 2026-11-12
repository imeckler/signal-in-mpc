import TlsMpc.KernelSpecs.ParseWebSocketAccept
import TlsMpc.KernelSpecs.ParseWebSocketControl

/-!
# From a control frame's bytes to the control queue's reply (RFC 6455 sections 5.5, 5.2)

New file; it changes no definition and no emitter imports it.

The controller feeds the control queue (`TlsWebSocketControl.run`) the frame parser's
`controlData`, `controlDone`, `controlKind` bytes (output bytes 2, 6, 7 of `runByte`, which for a
valid event are the event's fields: `ParseWebSocketFrame.controller_run`) and the byte itself.
`ParseWebSocketControl.control_frame*` took those inputs as given; here they are computed from the
frame's bytes, using the acceptance lemmas of `ParseWebSocketAccept`.

* `controlFrame o p`: RFC 6455 section 5.2's unmasked final frame with opcode `o` and a payload `p`
  of at most 125 bytes (the only encoding `Header.wellFormed` allows a control frame);
  `controlFrame_parse`, `controlFrame_accepts`: the reference reads and accepts it.
* `control_inputs` / `control_inputs_empty`: from a frame boundary, the queue's inputs over the
  frame are: nothing for the two header bytes, control data for every payload byte, and at the last
  byte control data, control done and the opcode.
* **`control_queue`** (Ping, Close with payload), **`control_queue_pong`**, **`control_queue_empty`**
  (Ping, Close without payload): from an idle queue, the frame's bytes leave the queue with exactly
  `reply`'s answer appended (`ParseWebSocketControl.reply`: Pong for a Ping, Close echoing a Close),
  and nothing for a Pong.

What `replies` then sends for the queued answer is `ParseWebSocketReplies` (kept apart: `replies`
may change).
-/

open TlsMpc TlsMpc.Signal
open PublicReceive (fast)
open TlsMpc.KernelSpecs.ParseWebSocketFrame
open TlsMpc.KernelSpecs.ParseWebSocketAccept
open TlsMpc.KernelSpecs.ParseWebSocketControl (runC Idle idleIn collectIn control_frame control_frame_pong
  control_frame_empty kindOf reply kindOf_reply blockSet)
open TlsWebSocketUpgrade (initial)
open TlsWebSocketFrame (State Event step wordValue)

set_option linter.unusedSimpArgs false

namespace TlsMpc.KernelSpecs.ParseWebSocketControlFrame

/-- RFC 6455 section 5.2: a final (`FIN`), unmasked frame with opcode `o` and a 7-bit length. -/
def controlFrame (o : Nat) (p : List Byte) : List Byte :=
  [BitVec.ofNat 8 (128 + o), BitVec.ofNat 8 p.length] ++ p

theorem controlFrame_parse (o : Nat) (ho : o < 16) (p : List Byte) (hp : p.length ≤ 125) :
    parseHeader (controlFrame o p) = some ⟨true, 0, o, false, p.length, 2, 7⟩ := by
  have h1 : (BitVec.ofNat 8 (128 + o)).toNat = 128 + o := by simp; omega
  have h2 : (BitVec.ofNat 8 p.length).toNat = p.length := by simp; omega
  simp only [controlFrame, List.cons_append, List.nil_append, parseHeader, h1, h2]
  have e1 : decide (128 ≤ 128 + o) = true := by simp
  have e2 : (128 + o) / 16 % 8 = 0 := by omega
  have e3 : (128 + o) % 16 = o := by omega
  have e4 : decide (128 ≤ p.length) = false := by simp; omega
  have e5 : p.length % 128 = p.length := by omega
  simp only [e1, e2, e3, e4, e5, if_pos hp]
  rfl

theorem controlFrame_accepts (cap : Nat) (c : Ctx) (o : Nat) (ho : o = 8 ∨ o = 9 ∨ o = 10) (p : List Byte)
    (hp : p.length ≤ 125) (hc : p.length ≤ cap) (hclose : o = 8 → CloseBody p) :
    Accepts cap c ⟨true, 0, o, false, p.length, 2, 7⟩ ((controlFrame o p).drop 2) := by
  refine ⟨⟨rfl, ?_, rfl, fun h => by simp at h, fun h => by simp at h, fun _ => ⟨rfl, hp⟩⟩,
    ?_, hc, ?_, ?_, ?_⟩
  · show o ∈ [0, 1, 2, 8, 9, 10]
    rcases ho with rfl | rfl | rfl <;> simp
  · show o ≠ 1; omega
  · intro h; exact absurd (show o = 0 from h) (by omega)
  · intro h; exact absurd (show o = 2 from h) (by omega)
  · intro h
    have e : (controlFrame o p).drop 2 = p := by simp [controlFrame]
    rw [e]; exact hclose h

theorem first_true (o : Nat) : firstByte true o = BitVec.ofNat 8 (128 + o) := rfl

/-- The queue's inputs over a control frame with a payload `q ++ [b]` (1 to 125 bytes), from a
frame boundary: the header bytes give nothing, every payload byte control data, the last also
control done and the opcode. -/
theorem control_inputs (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx) (hS : Boundary S c false)
    (o : Nat) (ho : o = 8 ∨ o = 9 ∨ o = 10) (q : List Byte) (b : Byte) (hp : (q ++ [b]).length ≤ 125)
    (hc : (q ++ [b]).length ≤ cap) (hclose : o = 8 → CloseBody (q ++ [b])) :
    List.zipWith cin (events cap S (controlFrame o (q ++ [b]))) (controlFrame o (q ++ [b])) =
      [idleIn (BitVec.ofNat 8 (128 + o)), idleIn (BitVec.ofNat 8 (q ++ [b]).length)] ++ q.map collectIn ++
        [(255#8, 255#8, BitVec.ofNat 8 o, b)] := by
  obtain ⟨ph, v, cl, op, fn, fr, hi0, lo0, mh, ml, pf, ps, ch, cv, u⟩ := S
  obtain ⟨hph, hv, hcl, hfr, hm, hu⟩ := hS
  simp only at hph hv hcl hfr hm hu
  subst hph hv hcl hfr
  have hfirst : FirstOk c.fragmented true o := Or.inr (Or.inr ⟨ho, rfl⟩)
  have hk : Op o := by rcases ho with e | e | e <;> simp [Op, e]
  have hql : (q ++ [b]).length = q.length + 1 := by simp
  have hlen : (BitVec.ofNat 8 (q ++ [b]).length).toNat = (q ++ [b]).length := by simp; omega
  simp only [controlFrame, List.cons_append, List.nil_append, events, mb_false]
  rw [← first_true, acc_first cap op fn c.fragmented hi0 lo0 mh ml pf ps ch cv u hu true o hfirst]
  simp only [events]
  rw [acc_short cap hcap o hk (mb true) (mb c.fragmented) hi0 lo0 _ _ pf ps ch cv u hu _ (by rw [hlen]; omega)
    (by rw [hlen]; omega) (by rw [hlen, hql]; omega) (by rw [hlen]; omega)
    (by
      intro e8 e1
      rw [hlen, hql] at e1
      rcases hclose e8 with e | ⟨c1, c2, r, e, -, -⟩
      · simp at e
      · have := congrArg List.length e
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega)]
  have hw : wordValue 0#8 (fast.and (BitVec.ofNat 8 (q ++ [b]).length) 127#8) = q.length + 1 := by
    rw [word_short, hlen, hql]; omega
  simp only [List.zipWith_cons_cons, cin]
  rcases ho with rfl | rfl | rfl
  · -- Close
    rcases hclose rfl with e | ⟨c1, c2, r, e, hcode, hr⟩
    · simp at e
    · have hlr := congrArg List.length e
      simp only [List.length_append, List.length_cons, List.length_nil] at hlr
      rw [e]
      rw [close_run_inputs cap c1 c2 r hcode hr _ _ _ _ _ _ ?hn q b e.symm]
      · rfl
      · first | (rw [hw]; omega) | (rw [← e, hw]; omega)
  · obtain ⟨-, -, hin⟩ := ping_run cap 9 (Or.inl rfl) q b (mb true) (mb c.fragmented) _ _ _ _ 255#8 0#8 0#8 0#8
      (initial fast 7) rfl hw
    rw [hin]; rfl
  · obtain ⟨-, -, hin⟩ := ping_run cap 10 (Or.inr rfl) q b (mb true) (mb c.fragmented) _ _ _ _ 255#8 0#8 0#8 0#8
      (initial fast 7) rfl hw
    rw [hin]; rfl

/-- The queue's inputs over a control frame with no payload. -/
theorem control_inputs_empty (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx)
    (hS : Boundary S c false) (o : Nat) (ho : o = 8 ∨ o = 9 ∨ o = 10) :
    List.zipWith cin (events cap S (controlFrame o [])) (controlFrame o []) =
      [idleIn (BitVec.ofNat 8 (128 + o)), (0#8, 255#8, BitVec.ofNat 8 o, 0#8)] := by
  obtain ⟨ph, v, cl, op, fn, fr, hi0, lo0, mh, ml, pf, ps, ch, cv, u⟩ := S
  obtain ⟨hph, hv, hcl, hfr, hm, hu⟩ := hS
  simp only at hph hv hcl hfr hm hu
  subst hph hv hcl hfr
  have hfirst : FirstOk c.fragmented true o := Or.inr (Or.inr ⟨ho, rfl⟩)
  simp only [controlFrame, List.cons_append, List.nil_append, events, mb_false, List.length_nil]
  rw [← first_true, acc_first cap op fn c.fragmented hi0 lo0 mh ml pf ps ch cv u hu true o hfirst]
  simp only [events]
  rw [show (BitVec.ofNat 8 0 : Byte) = 0#8 from rfl,
    acc_empty_control cap hcap o ho (mb true) (mb c.fragmented) hi0 lo0 _ _ pf ps ch cv u hu]
  rfl

/-- **`control_queue`.** A Ping (9) or a Close (8) with a payload `q ++ [b]` (1 to 125 bytes; for
a Close a valid code and UTF-8 reason), its bytes run through the frame parser from a frame
boundary and the queue fed the parser's outputs from an idle queue: the queue is idle again with
`reply`'s answer appended in slot `Q.queued` (kind: Pong for a Ping, Close for a Close; the length;
the payload, zero-padded). -/
theorem control_queue (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx) (hS : Boundary S c false)
    (Q : TlsWebSocketControl.State Byte) (hQ : Idle Q) (o : Nat) (ho : o = 8 ∨ o = 9) (q : List Byte) (b : Byte)
    (hp : (q ++ [b]).length ≤ 125) (hc : (q ++ [b]).length ≤ cap) (hclose : o = 8 → CloseBody (q ++ [b])) :
    runC Q (List.zipWith cin (events cap S (controlFrame o (q ++ [b]))) (controlFrame o (q ++ [b]))) =
      { valid := Q.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (Q.queued.toNat + 1),
        kinds := Q.kinds.set Q.queued.toNat (kindOf (BitVec.ofNat 8 o)),
        lengths := Q.lengths.set Q.queued.toNat (BitVec.ofNat 8 (q ++ [b]).length),
        payloads := blockSet Q.payloads Q.queued.toNat
          ((q ++ [b]) ++ List.replicate (125 - (q ++ [b]).length) 0#8) } ∧
    reply o (q ++ [b]) = some ((kindOf (BitVec.ofNat 8 o)).toNat, q ++ [b]) := by
  rw [control_inputs cap hcap S c hS o (by omega) q b hp hc hclose]
  have hs : [idleIn (BitVec.ofNat 8 (128 + o)), idleIn (BitVec.ofNat 8 (q ++ [b]).length)] =
      [BitVec.ofNat 8 (128 + o), BitVec.ofNat 8 (q ++ [b]).length].map idleIn := rfl
  have ho' : BitVec.ofNat 8 o = 8#8 ∨ BitVec.ofNat 8 o = 9#8 := by rcases ho with rfl | rfl <;> simp
  rw [hs, control_frame Q hQ _ q b _ ho' (by simp at hp ⊢; omega)]
  refine ⟨by simp, ?_⟩
  have := kindOf_reply (BitVec.ofNat 8 o) ho' (q ++ [b])
  rcases ho with rfl | rfl <;> exact this

/-- **`control_queue_pong`.** A Pong leaves an idle queue as it is: no answer is owed. -/
theorem control_queue_pong (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx) (hS : Boundary S c false)
    (Q : TlsWebSocketControl.State Byte) (hQ : Idle Q) (q : List Byte) (b : Byte)
    (hp : (q ++ [b]).length ≤ 125) (hc : (q ++ [b]).length ≤ cap) :
    runC Q (List.zipWith cin (events cap S (controlFrame 10 (q ++ [b]))) (controlFrame 10 (q ++ [b]))) = Q ∧
    reply 10 (q ++ [b]) = none := by
  rw [control_inputs cap hcap S c hS 10 (by omega) q b hp hc (by omega)]
  have hs : [idleIn (BitVec.ofNat 8 (128 + 10)), idleIn (BitVec.ofNat 8 (q ++ [b]).length)] =
      [BitVec.ofNat 8 (128 + 10), BitVec.ofNat 8 (q ++ [b]).length].map idleIn := rfl
  rw [hs]
  exact ⟨control_frame_pong Q hQ _ q b (by simp at hp ⊢; omega), rfl⟩

/-- **`control_queue_empty`.** A Ping or Close with no payload: the answer is queued with length 0. -/
theorem control_queue_empty (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx) (hS : Boundary S c false)
    (Q : TlsWebSocketControl.State Byte) (hQ : Idle Q) (o : Nat) (ho : o = 8 ∨ o = 9) :
    runC Q (List.zipWith cin (events cap S (controlFrame o [])) (controlFrame o [])) =
      { valid := Q.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (Q.queued.toNat + 1),
        kinds := Q.kinds.set Q.queued.toNat (kindOf (BitVec.ofNat 8 o)),
        lengths := Q.lengths.set Q.queued.toNat 0#8,
        payloads := blockSet Q.payloads Q.queued.toNat (List.replicate 125 0#8) } ∧
    reply o [] = some ((kindOf (BitVec.ofNat 8 o)).toNat, []) := by
  rw [control_inputs_empty cap hcap S c hS o (by omega)]
  have ho' : BitVec.ofNat 8 o = 8#8 ∨ BitVec.ofNat 8 o = 9#8 := by rcases ho with rfl | rfl <;> simp
  have hs : [idleIn (BitVec.ofNat 8 (128 + o)), (0#8, 255#8, BitVec.ofNat 8 o, 0#8)] =
      [BitVec.ofNat 8 (128 + o)].map idleIn ++ [(0#8, 255#8, BitVec.ofNat 8 o, 0#8)] := rfl
  rw [hs, control_frame_empty Q hQ _ 0#8 _ ho']
  refine ⟨rfl, ?_⟩
  have := kindOf_reply (BitVec.ofNat 8 o) ho' []
  rcases ho with rfl | rfl <;> exact this

end TlsMpc.KernelSpecs.ParseWebSocketControlFrame
