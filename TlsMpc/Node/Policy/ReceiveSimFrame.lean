import TlsMpc.Node.Policy.ReceiveFrame

/-!
# T1, item 1 (frame side): the frame parser against the byte-by-byte reference

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`ReceiveStream.Stream.step` reads the frames one byte at a time (`Phase`: which header byte comes
next, or how many payload bytes are left, and whether the message is complete). The controller's
frame parser (`TlsWebSocketFrame.step`, which `frameByte`, `stepPassed` and `stepSkipped` run on the
serialised state: `runByte_active`) keeps the same position in its one-hot `phases`, its opcode, FIN,
`fragmented` and 16-bit length bytes. `FrameSim S st n` says the parser's state `S` is at the
reference's position `st` (`n` stream bytes not yet read, for the reference's `complete` flag).

* `frame_sim_step`: on every byte the parser accepts (its validity byte stays 255), the relation is
  kept, and the byte's `data` and `messageDone` events are the reference's (`dataOf`, `endOf`): a
  data frame's payload byte; the last byte of a data frame with FIN (its last payload byte, or the
  second header byte of an empty one). At every byte where the reference enters its error state
  (`Phase.dead`), the parser's validity byte is 0 (`ReceiveFrame.first_reject`, `second_reject`,
  `extLo_reject`): `frameByte` refuses it (`ReceiveFrame.frameByte_reject`).
* `frame_step_aux_*`: what `TlsWebSocketFrame.step` does to FIN, `fragmented` and the
  `messageDone` event in each phase (the `step_*` lemmas of `ParseWebSocketFrame` give the rest).
-/

open TlsMpc

namespace ReceiveSimFrame

open PublicReceive ReceiveProofs ReceiveStream
open TlsMpc.KernelSpecs.ParseWebSocketFrame (P mb dat ctl Shaped eventBytes core core_eq Flags step_first
  step_second_short step_second_empty step_second_extended step_high step_low step_payload step_payload_last
  bit7 len_eq len_eq7 len_eq0 zero_word one_word word_short and_mb step_shaped)
open PublicReceive.PassOver (hiOf loOf wordValue_of wordValue_lt)
open TlsWebSocketFrame (step wordValue)

abbrev FState := TlsWebSocketFrame.State Byte

/-! ### What one step does to FIN, `fragmented` and `messageDone` -/

theorem aux_first (cap : Nat) (S : FState) (x : Byte) (h : S.phases = P 0) :
    (step fast cap S x).state.fin = mb (decide (128 ≤ x.toNat)) ∧
    (step fast cap S x).state.fragmented = S.fragmented ∧
    (step fast cap S x).messageDone = 0#8 := by
  refine ⟨?_, ?_, ?_⟩ <;> valid_simp [h, bit7 x]

theorem aux_second_ext (cap : Nat) (S : FState) (x : Byte) (h : S.phases = P 1) (hm : x.toNat < 128)
    (he : x.toNat % 128 = 126) :
    (step fast cap S x).state.fin = S.fin ∧
    (step fast cap S x).state.fragmented = S.fragmented ∧
    (step fast cap S x).messageDone = 0#8 := by
  have h126 : (x.toNat % 128 == 126) = true := by simp; omega
  have h127 : (x.toNat % 128 == 127) = false := by simp; omega
  have h0 : (x.toNat % 128 == 0) = false := by simp; omega
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  refine ⟨?_, ?_, ?_⟩ <;> valid_simp [h, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7]

theorem aux_second_short (cap : Nat) (S : FState) (x : Byte) (h : S.phases = P 1) (hm : x.toNat < 128)
    (hl : x.toNat % 128 ≤ 125) (hz : x.toNat % 128 ≠ 0) :
    (step fast cap S x).state.fin = S.fin ∧
    (step fast cap S x).state.fragmented = S.fragmented ∧
    (step fast cap S x).messageDone = 0#8 := by
  have h126 : (x.toNat % 128 == 126) = false := by simp; omega
  have h127 : (x.toNat % 128 == 127) = false := by simp; omega
  have h0 : (x.toNat % 128 == 0) = false := by simp; omega
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  refine ⟨?_, ?_, ?_⟩ <;> valid_simp [h, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7]

theorem aux_second_empty (cap : Nat) (S : FState) (x : Byte) (h : S.phases = P 1) (hm : x.toNat < 128)
    (hz : x.toNat % 128 = 0) (f fr : Bool) (hf : S.fin = mb f) (hfr : S.fragmented = mb fr) :
    (step fast cap S x).state.fragmented = mb (if dat S.opcode then !f else fr) ∧
    (step fast cap S x).messageDone = fast.and (step fast cap S x).state.valid (mb (dat S.opcode && f)) := by
  have h126 : (x.toNat % 128 == 126) = false := by simp; omega
  have h127 : (x.toNat % 128 == 127) = false := by simp; omega
  have h0 : (x.toNat % 128 == 0) = true := by simp; omega
  have h7 : decide (128 ≤ x.toNat) = false := by simp; omega
  refine ⟨?_, ?_⟩
  · valid_simp [h, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7, hf, hfr, dat]
    cases f <;> cases fr <;> simp <;>
      (by_cases h1 : S.opcode = 0#8 <;> by_cases h2 : S.opcode = 2#8 <;> simp [h1, h2, mb])
  · valid_simp [h, len_eq x, len_eq7 x, len_eq0 x, bit7 x, h126, h127, h0, h7, hf, hfr, dat]

theorem aux_high (cap : Nat) (S : FState) (x : Byte) (h : S.phases = P 2) :
    (step fast cap S x).state.fin = S.fin ∧
    (step fast cap S x).state.fragmented = S.fragmented ∧
    (step fast cap S x).messageDone = 0#8 := by
  refine ⟨?_, ?_, ?_⟩ <;> valid_simp [h]

theorem aux_low (cap : Nat) (S : FState) (x : Byte) (h : S.phases = P 3) (hw : wordValue S.high x ≠ 0) :
    (step fast cap S x).state.fin = S.fin ∧
    (step fast cap S x).state.fragmented = S.fragmented ∧
    (step fast cap S x).messageDone = 0#8 := by
  have hz : (S.high == 0#8 && x == 0#8) = false := by rw [zero_word]; simpa using hw
  refine ⟨?_, ?_, ?_⟩ <;> valid_simp [h, hz]

theorem aux_payload (cap : Nat) (S : FState) (x : Byte) (h : S.phases = P 4) (hw : 2 ≤ wordValue S.high S.low) :
    (step fast cap S x).state.fin = S.fin ∧
    (step fast cap S x).state.fragmented = S.fragmented ∧
    (step fast cap S x).messageDone = 0#8 := by
  have hz : (S.high == 0#8 && S.low == 1#8) = false := by rw [one_word]; simp; omega
  refine ⟨?_, ?_, ?_⟩ <;> valid_simp [h, hz]

theorem aux_payload_last (cap : Nat) (S : FState) (x : Byte) (h : S.phases = P 4)
    (hw : wordValue S.high S.low = 1) (f fr : Bool) (hf : S.fin = mb f) (hfr : S.fragmented = mb fr) :
    (step fast cap S x).state.fragmented = mb (if dat S.opcode then !f else fr) ∧
    (step fast cap S x).messageDone = fast.and (step fast cap S x).state.valid (mb (dat S.opcode && f)) := by
  have hz : (S.high == 0#8 && S.low == 1#8) = true := by rw [one_word]; simp; omega
  refine ⟨?_, ?_⟩
  · valid_simp [h, hz, hf, hfr, dat]
    cases f <;> cases fr <;> simp <;>
      (by_cases h1 : S.opcode = 0#8 <;> by_cases h2 : S.opcode = 2#8 <;> simp [h1, h2, mb])
  · valid_simp [h, hz, hf, hfr, dat]

/-! ### Opcodes -/

theorem op_ofNat : ∀ b0 : Byte, fast.and b0 15#8 = BitVec.ofNat 8 (b0.toNat % 16) := by decide +kernel

theorem op_dat : ∀ b0 : Byte, dat (fast.and b0 15#8) = (b0.toNat % 16 == 0 || b0.toNat % 16 == 2) := by
  decide +kernel

theorem op_ctl : ∀ b0 : Byte, ctl (fast.and b0 15#8) =
    (b0.toNat % 16 == 8 || (b0.toNat % 16 == 9 || b0.toNat % 16 == 10)) := by
  decide +kernel

theorem op_lt8 : ∀ b0 : Byte, (fast.and b0 15#8).toNat = b0.toNat % 16 := by decide +kernel

/-- A first header byte the reference accepts is a data opcode (0, 2) or a control one (8, 9, 10). -/
theorem fits_kind {b0 : Byte} {fr : Bool} (h : Stream.headerFits b0 fr) :
    ctl (fast.and b0 15#8) = Stream.isControl b0 ∧ dat (fast.and b0 15#8) = !Stream.isControl b0 ∧
    ((fast.and b0 15#8).toNat < 8 ↔ Stream.isControl b0 = false) ∧
    (Stream.isControl b0 = true → Stream.finOf b0 = true) := by
  unfold Stream.headerFits at h
  obtain ⟨-, h⟩ := h
  rw [op_ctl, op_dat, op_lt8]
  unfold Stream.isControl
  rcases h with ⟨h2, -⟩ | ⟨h0, -⟩ | ⟨hc, hf⟩
  · simp [h2]
  · simp [h0]
  · simp only [Stream.isControl, decide_eq_true_eq] at hc
    refine ⟨?_, ?_, ?_, fun _ => hf⟩
    · rcases hc with e | e | e <;> simp [e]
    · rcases hc with e | e | e <;> simp [e]
    · rcases hc with e | e | e <;> simp [e]

/-! ### The relation -/

/-- The parser's phase against the reference's (`fr`: the reference's `fragmented`; `n`: stream bytes
not yet read). -/
def PhaseSim (S : FState) (fr : Bool) (n : Nat) : Stream.Phase → Prop
  | .first => S.phases = P 0
  | .second b0 => S.phases = P 1 ∧ S.opcode = fast.and b0 15#8 ∧ S.fin = mb (Stream.finOf b0) ∧
      Stream.headerFits b0 fr
  | .extHi b0 => S.phases = P 2 ∧ S.opcode = fast.and b0 15#8 ∧ S.fin = mb (Stream.finOf b0) ∧
      Stream.headerFits b0 fr ∧ Stream.isControl b0 = false
  | .extLo b0 hi => S.phases = P 3 ∧ S.high = hi ∧ S.opcode = fast.and b0 15#8 ∧
      S.fin = mb (Stream.finOf b0) ∧ Stream.headerFits b0 fr ∧ Stream.isControl b0 = false
  | .payload c f cpl k => S.phases = P 4 ∧ wordValue S.high S.low = k ∧ 1 ≤ k ∧ ctl S.opcode = c ∧
      dat S.opcode = !c ∧ (S.opcode.toNat < 8 ↔ c = false) ∧ S.fin = mb f ∧
      cpl = (f && decide (k ≤ n)) ∧ (c = true → f = true)
  | .dead => False

/-- **The frame parser's state `S` is at the reference's position `st`**, `n` stream bytes not yet
read. -/
structure FrameSim (S : FState) (st : Stream.St) (n : Nat) : Prop where
  shaped : Shaped S
  frag : S.fragmented = mb st.fragmented
  phase : PhaseSim S st.fragmented n st.phase

/-- The reference's answer to "is this byte a data frame's payload byte". -/
def dataOf : Stream.Phase → Bool
  | .payload c _ _ _ => !c
  | _ => false

/-- The reference's answer to "does this byte end a binary message" (the last byte of a data frame with
FIN). -/
def endOf : Stream.Phase → Byte → Bool
  | .payload c f _ k, _ => !c && f && k == 1
  | .second b0, b => b.toNat % 128 == 0 && !Stream.isControl b0 && Stream.finOf b0
  | _, _ => false

theorem and_on (x : Byte) : fast.and 255#8 x = x := TlsMpc.KernelSpecs.ParseWebSocketFrame.and_ones_l x

theorem mb_inj {a b : Bool} (h : mb a = mb b) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

/-- **One accepted byte keeps the frame relation**, and its `data` and `messageDone` events are the
reference's. -/
theorem frame_sim_step (ob : Bool) {S : FState} {st : Stream.St} {n : Nat} {b : Byte}
    (hfs : FrameSim S st (n + 1)) (hv : (step fast capacity S b).state.valid = 255#8) :
    FrameSim (step fast capacity S b).state (Stream.step ob st b n).2 n ∧
    (step fast capacity S b).data = mb (dataOf st.phase) ∧
    (step fast capacity S b).messageDone = mb (endOf st.phase b) := by
  obtain ⟨hsh, hfr, hph⟩ := hfs
  have hsh' := step_shaped capacity S b hsh
  obtain ⟨phase, msg, fr⟩ := st
  simp only at hfr hph
  cases phase with
  | dead => exact absurd hph id
  | first =>
    obtain ⟨c0, f0⟩ := step_first capacity S b hph
    obtain ⟨p1, -, -, o1⟩ := core_eq c0
    obtain ⟨a1, a2, a3⟩ := aux_first capacity S b hph
    by_cases hf : Stream.headerFits b fr
    · simp only [Stream.step, if_pos hf]
      refine ⟨⟨hsh', by rw [a2, hfr], p1, o1, by rw [a1]; rfl, hf⟩, ?_, ?_⟩
      · rw [f0.1, hv, and_on]; rfl
      · rw [a3]; rfl
    · exfalso
      have := ReceiveFrame.first_reject capacity S hph fr hfr b hf
      rw [hv] at this; exact absurd this (by decide)
  | second b0 =>
    obtain ⟨hp, ho, hfin, hfits⟩ := hph
    obtain ⟨hctl, hdat, hlt, hcf⟩ := fits_kind hfits
    by_cases hbad : Stream.secondBad b0 b
    · exfalso
      have := ReceiveFrame.second_reject capacity S hp b0 b (by rw [ho, op_ofNat]) hbad
      rw [hv] at this; exact absurd this (by decide)
    have hm : b.toNat < 128 := by unfold Stream.secondBad at hbad; omega
    have h127 : b.toNat % 128 ≠ 127 := by unfold Stream.secondBad at hbad; omega
    by_cases h126 : b.toNat % 128 = 126
    · have hnc : Stream.isControl b0 = false := by
        unfold Stream.secondBad at hbad
        cases e : Stream.isControl b0
        · rfl
        · exfalso; exact hbad (Or.inr (Or.inr ⟨e, h126⟩))
      obtain ⟨c1, f1⟩ := step_second_extended capacity S b hp hm h126
      obtain ⟨p2, -, -, o2⟩ := core_eq c1
      obtain ⟨a1, a2, a3⟩ := aux_second_ext capacity S b hp hm h126
      simp only [Stream.step, if_neg hbad, if_pos h126]
      refine ⟨⟨hsh', by rw [a2, hfr], p2, by rw [o2, ho], by rw [a1, hfin], hfits, hnc⟩, ?_, ?_⟩
      · rw [f1.1, hv, and_on]; rfl
      · rw [a3]; simp [endOf, h126]
    · have hl : b.toNat % 128 ≤ 125 := by omega
      by_cases hz : b.toNat % 128 = 0
      · obtain ⟨c1, f1⟩ := step_second_empty capacity S b hp hm hz
        obtain ⟨p2, -, -, -⟩ := core_eq c1
        obtain ⟨a2, a3⟩ := aux_second_empty capacity S b hp hm hz (Stream.finOf b0) fr hfin hfr
        simp only [Stream.step, if_neg hbad, if_neg h126, Stream.startPayload, if_pos hz]
        rw [ho, hdat] at a2 a3
        refine ⟨⟨hsh', ?_, ?_⟩, ?_, ?_⟩
        · rw [a2]; unfold Stream.endFrame
          cases hc : Stream.isControl b0 <;> cases hfn : Stream.finOf b0 <;> simp
        · unfold Stream.endFrame; split <;> (try split) <;> exact p2
        · rw [f1.1, hv, and_on]; rfl
        · rw [a3, hv, and_on]
          simp only [endOf, hz]
          cases Stream.isControl b0 <;> cases Stream.finOf b0 <;> rfl
      · obtain ⟨c1, f1⟩ := step_second_short capacity S b hp hm hl hz
        obtain ⟨p2, h2, l2, o2⟩ := core_eq c1
        obtain ⟨a1, a2, a3⟩ := aux_second_short capacity S b hp hm hl hz
        simp only [Stream.step, if_neg hbad, if_neg h126, Stream.startPayload, if_neg hz]
        refine ⟨⟨hsh', by rw [a2, hfr], p2, by rw [h2, l2, word_short], by omega, by rw [o2, ho, hctl],
          by rw [o2, ho, hdat], by rw [o2, ho]; exact hlt, by rw [a1, hfin], by simp, hcf⟩, ?_, ?_⟩
        · rw [f1.1, hv, and_on]; rfl
        · have hz' : (b.toNat % 128 == 0) = false := by simp [hz]
          rw [a3]; simp [endOf, hz']
  | extHi b0 =>
    obtain ⟨hp, ho, hfin, hfits, hnc⟩ := hph
    obtain ⟨c1, f1⟩ := step_high capacity S b hp
    obtain ⟨p3, h3, -, o3⟩ := core_eq c1
    obtain ⟨a1, a2, a3⟩ := aux_high capacity S b hp
    simp only [Stream.step]
    refine ⟨⟨hsh', by rw [a2, hfr], p3, h3, by rw [o3, ho], by rw [a1, hfin], hfits, hnc⟩, ?_, ?_⟩
    · rw [f1.1, hv, and_on]; rfl
    · rw [a3]; rfl
  | extLo b0 hi =>
    obtain ⟨hp, hh, ho, hfin, hfits, hnc⟩ := hph
    obtain ⟨hctl, hdat, hlt, hcf⟩ := fits_kind hfits
    by_cases hw : ReceiveSpec.word hi b < 126
    · exfalso
      have := ReceiveFrame.extLo_reject capacity S hp hi b hh hw
      rw [hv] at this; exact absurd this (by decide)
    have hwv : wordValue S.high b = ReceiveSpec.word hi b := by
      rw [hh]; unfold wordValue ReceiveSpec.word; omega
    obtain ⟨c1, f1⟩ := step_low capacity S b hp (by omega)
    obtain ⟨p4, h4, l4, o4⟩ := core_eq c1
    obtain ⟨a1, a2, a3⟩ := aux_low capacity S b hp (by omega)
    simp only [Stream.step, if_neg hw, Stream.startPayload, if_neg (show ¬ ReceiveSpec.word hi b = 0 by omega)]
    refine ⟨⟨hsh', by rw [a2, hfr], p4, by rw [h4, l4, hwv], by omega, by rw [o4, ho, hctl],
      by rw [o4, ho, hdat], by rw [o4, ho]; exact hlt, by rw [a1, hfin], by simp, hcf⟩, ?_, ?_⟩
    · rw [f1.1, hv, and_on]; rfl
    · rw [a3]; rfl
  | payload c f cpl k =>
    obtain ⟨hp, hk, hk1, hctl, hdat, hlt, hfin, hcpl, hcf⟩ := hph
    have hlt' := wordValue_lt S.high S.low
    by_cases h1 : k = 1
    · subst h1
      obtain ⟨c1, f1⟩ := step_payload_last capacity S b hp hk
      obtain ⟨p0, -, -, -⟩ := core_eq c1
      obtain ⟨a2, a3⟩ := aux_payload_last capacity S b hp hk f fr hfin hfr
      rw [hdat] at a2 a3
      simp only [Stream.step, Nat.le_refl, if_true]
      refine ⟨⟨hsh', ?_, ?_⟩, ?_, ?_⟩
      · rw [a2]; unfold Stream.endFrame
        cases c <;> cases f <;> simp
      · unfold Stream.endFrame; split <;> (try split) <;> exact p0
      · rw [f1.1, hv, and_on, hdat]; rfl
      · rw [a3, hv, and_on]; simp [endOf]
    · have h2 : 2 ≤ wordValue S.high S.low := by omega
      obtain ⟨c1, f1⟩ := step_payload capacity S b hp h2
      obtain ⟨p4, h4, l4, o4⟩ := core_eq c1
      obtain ⟨a1, a2, a3⟩ := aux_payload capacity S b hp h2
      simp only [Stream.step, if_neg (show ¬ k ≤ 1 by omega)]
      refine ⟨⟨hsh', by rw [a2, hfr], p4, by rw [h4, l4, wordValue_of _ (by omega), hk], by omega,
        by rw [o4, hctl], by rw [o4, hdat], by rw [o4]; exact hlt, by rw [a1, hfin], ?_, hcf⟩, ?_, ?_⟩
      · rw [hcpl]; congr 1; simp only [decide_eq_decide]; omega
      · rw [f1.1, hv, and_on, hdat]; rfl
      · have h1' : (k == 1) = false := by simp [h1]
        rw [a3]; simp [endOf, h1']

/-- In a payload, the reference's next position does not depend on the byte (what `stepPassed` and
`stepSkipped` rely on: they run the parser on a zero in place of the unrevealed byte). -/
theorem step_payload_indep (ob : Bool) {st : Stream.St} {c f cpl : Bool} {k : Nat}
    (hp : st.phase = .payload c f cpl k) (b b' : Byte) (n : Nat) :
    (Stream.step ob st b n).2.phase = (Stream.step ob st b' n).2.phase ∧
    (Stream.step ob st b n).2.fragmented = (Stream.step ob st b' n).2.fragmented := by
  obtain ⟨phase, msg, fr⟩ := st
  simp only at hp
  subst hp
  simp only [Stream.step]
  by_cases hk : k ≤ 1
  · simp only [hk, if_true, Stream.endFrame]
    cases c <;> cases f <;> simp
  · simp only [hk, if_false]
    exact ⟨trivial, trivial⟩

/-- `FrameSim` depends on the reference's state only through its phase and `fragmented`. -/
theorem frameSim_congr {S : FState} {st st' : Stream.St} {n : Nat} (h : FrameSim S st n)
    (hp : st'.phase = st.phase) (hf : st'.fragmented = st.fragmented) : FrameSim S st' n :=
  ⟨h.shaped, by rw [hf]; exact h.frag, by rw [hp, hf]; exact h.phase⟩

end ReceiveSimFrame
