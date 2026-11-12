import TlsMpc.Node.Policy.ReceiveStream
import TlsMpc.Node.Policy.ReceiveInvariant

/-!
# The frame layer against the reference's errors (proof track P1, item 3, part)

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

The byte-by-byte reference (`ReceiveStream.Stream.step`) makes every byte after a malformed header
byte `error` (`Phase.dead`): a first header byte that does not fit (`headerFits`: a reserved bit, an
opcode outside 0, 2, 8, 9, 10, a continuation with no message in progress, a new message inside a
fragmented one, a control frame without FIN), a bad second header byte (`secondBad`: MASK set, the
64-bit length code, a control frame with the 16-bit code), a 16-bit length below 126. Here: at each of
those bytes the controller's frame parser (`TlsWebSocketFrame.step`, which `frameByte` runs:
`frameByte_frame`) clears its validity byte (`first_reject`, `second_reject`, `extLo_reject`, from the
`reject_*` lemmas of `TlsMpc/KernelSpecs/ParseWebSocketFrame.lean`), so `frameByte` refuses that very
byte (`frameByte_reject`): nothing after it is revealed by a later run. (The run that contains it may
reveal the byte after it: the first header byte and the second are one run; that byte is the
reference's first `error`, T1's one-byte allowance.)

The hypotheses relating the parser's state to the reference's position (its phase is `P 0` at a
frame's first byte, `P 1` at the second, `P 3` at a 16-bit length's low byte; its `fragmented` byte is
the reference's flag; its opcode is the first byte's) are the frame-position simulation, which is not
proved here (see `ReceiveProofs`' header, "What is not proved here").
-/

open TlsMpc

namespace ReceiveFrame

open PublicReceive ReceiveProofs
open TlsMpc.KernelSpecs.ParseWebSocketFrame (P mb Shaped eventBytes runByte_active)
open TlsWebSocketFrame (State step)

theorem mb_true' : mb true = 255#8 := rfl
theorem mb_false' : mb false = 0#8 := rfl

/-- **A first header byte the reference rejects is rejected by the frame parser.** -/
theorem first_reject (cap : Nat) (S : State Byte) (h : S.phases = P 0) (fr : Bool) (hfr : S.fragmented = mb fr)
    (b0 : Byte) (hb : ¬ ReceiveStream.Stream.headerFits b0 fr) : (step fast cap S b0).state.valid = 0#8 := by
  unfold ReceiveStream.Stream.headerFits ReceiveStream.Stream.isControl ReceiveStream.Stream.finOf at hb
  by_cases hr : b0.toNat / 16 % 8 = 0
  case neg => exact TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_rsv cap S b0 h hr
  by_cases h2 : b0.toNat % 16 = 2
  · cases fr
    · exfalso; exact hb ⟨hr, Or.inl ⟨h2, rfl⟩⟩
    · exact TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_interleaved cap S b0 h (by rw [hfr]; rfl) h2
  by_cases h0 : b0.toNat % 16 = 0
  · cases fr
    · exact TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_continuation cap S b0 h (by rw [hfr]; rfl) h0
    · exfalso; exact hb ⟨hr, Or.inr (Or.inl ⟨h0, rfl⟩)⟩
  by_cases hc : b0.toNat % 16 = 8 ∨ b0.toNat % 16 = 9 ∨ b0.toNat % 16 = 10
  · by_cases hf : 128 ≤ b0.toNat
    · exfalso; exact hb ⟨hr, Or.inr (Or.inr ⟨by simp [hc], by simp [hf]⟩)⟩
    · exact TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_control_fragment cap S b0 h hc (by omega)
  · exact TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_opcode cap S b0 h
      ⟨h0, h2, fun e => hc (Or.inl e), fun e => hc (Or.inr (Or.inl e)), fun e => hc (Or.inr (Or.inr e))⟩

/-- **A second header byte the reference rejects is rejected by the frame parser** (the parser's opcode
being the first byte's). -/
theorem second_reject (cap : Nat) (S : State Byte) (h : S.phases = P 1) (b0 b1 : Byte)
    (hop : S.opcode = BitVec.ofNat 8 (b0.toNat % 16)) (hb : ReceiveStream.Stream.secondBad b0 b1) :
    (step fast cap S b1).state.valid = 0#8 := by
  unfold ReceiveStream.Stream.secondBad ReceiveStream.Stream.isControl at hb
  rcases hb with hb | hb | ⟨hc, he⟩
  · exact TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_second cap S b1 h (Or.inl hb)
  · exact TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_second cap S b1 h (Or.inr hb)
  · simp only [decide_eq_true_eq] at hc
    apply TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_control_extended cap S b1 h _ he
    rw [hop]
    rcases hc with e | e | e <;> rw [e] <;> simp

/-- **A non-canonical 16-bit length is rejected by the frame parser** (its high byte being the one it
recorded). -/
theorem extLo_reject (cap : Nat) (S : State Byte) (h : S.phases = P 3) (hi lo : Byte) (hh : S.high = hi)
    (hw : ReceiveSpec.word hi lo < 126) : (step fast cap S lo).state.valid = 0#8 := by
  unfold ReceiveSpec.word at hw
  have hi0 : hi = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  exact TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_noncanonical cap S lo h (by rw [hh, hi0]) (by omega)

/-- **A byte the frame parser rejects is refused by `frameByte`** (once upgraded, the controller's
frame state being the parser's): nothing after it is revealed. -/
theorem frameByte_reject {s : State} {b : Byte} {S : TlsWebSocketFrame.State Byte} (hu : s.upgraded = true)
    (hf : s.frame = TlsWebSocketFrame.stateBytes S) (hS : Shaped S)
    (hv : (step fast capacity S b).state.valid = 0#8) : ∀ r, frameByte s b ≠ .ok r := by
  intro r h
  obtain ⟨s1, ev⟩ := r
  rw [frameByte_split, frameUpgrade_eq, bind_ok_iff] at h
  obtain ⟨⟨a, s0⟩, h1, h2⟩ := h
  unfold upgradePart at h1
  rw [if_pos hu] at h1
  cases h1
  have hrun : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b]) =
      eventBytes (step fast capacity S b) ++ TlsWebSocketFrame.stateBytes (step fast capacity S b).state := by
    rw [hf]; exact runByte_active capacity S hS b
  have hget : PublicReceive.get (TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b])) 0 = 0#8 := by
    rw [hrun]; unfold eventBytes; simp only [List.cons_append]; rw [hv]; rfl
  unfold frameRest at h2
  by_cases g1 : (s.skip == 0) = true
  case neg => simp only [g1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h2
  simp only [g1, ↓reduceIte, pure_bind] at h2
  by_cases g2 : (s.pending && s.message.isEmpty && PublicReceive.get s.frame 0 == on) = true
  · simp only [g2, ↓reduceIte] at h2
    rw [hget] at h2
    simp only [show ((0#8 : Byte) == on) = false by decide, Bool.false_eq_true, ↓reduceIte, throw_bind_ex,
      throw_ok_iff] at h2
  · simp only [g2, Bool.false_eq_true, ↓reduceIte] at h2
    rw [hget] at h2
    simp only [show ((0#8 : Byte) == on) = false by decide, Bool.false_eq_true, ↓reduceIte, throw_bind_ex,
      throw_ok_iff] at h2

end ReceiveFrame
