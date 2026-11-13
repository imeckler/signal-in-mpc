import TlsMpc.Node.Flows.Registry

/-!
# The ceremony scripts against the reveal list and the pipe (S16, ops 80, 81)

* `s16_flows_reveal`: ops 80 and 81 declare their kinds on every branch (registered:
  `Registry.declared_registered` covers the entries `Ceremony.secrets`, `Ceremony.register`).
* `secretsScript_bounded`, `registerScript_bounded`: the Lean sender emits only `Wire.Bounded`
  instructions for them (ids below 2^64); `registerName_lt` and `registerCtr_bounded`: the record
  seal of the registration request (`Send.requestCtrScript` with `ceremony-register-ctr …`) too, for
  the arguments `registerOk` admits.
-/

namespace TlsMpc.Node.Flows.Registry

open TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts
open TlsMpc.Node (RevealKind)

/-- **Every S16 ceremony script declares its kinds** (on every branch, for every argument). -/
theorem s16_flows_reveal :
    (∀ n a b c, Reveals Ceremony.secretsKinds (Ceremony.secretsScript n a b c)) ∧
    (∀ st n a b c, Reveals Ceremony.secretsKinds (Ceremony.secretsStep st n a b c)) ∧
    (∀ n p r t, Reveals [] (Ceremony.registerScript n p r t)) ∧
    (∀ st n t, Reveals [] (Ceremony.registerStep st n t)) :=
  ⟨Ceremony.secrets_reveals, Ceremony.secretsStep_reveals, Ceremony.register_reveals, Ceremony.registerStep_reveals⟩

/-- The ceremony's kinds are registered (`Label.kinds`). -/
theorem s16_kinds_registered : ∀ k ∈ Ceremony.secretsKinds, k ∈ Label.kinds := by decide

theorem length_secretsName : Ceremony.secretsName.length = 16 := by
  simp only [Ceremony.secretsName, length_ascii]
  decide

/-- **Op 80's wires fit the pipe.** -/
theorem secretsScript_bounded (n a b c : Nat) (hn : n + 11 < B64) :
    Every Instr.Bounded (Ceremony.secretsScript n a b c) := by
  have hB := big_lt_B64
  have hname := length_secretsName
  unfold Ceremony.secretsScript
  refine every_seqs (every_openThen ?_ (fun out => ?_)) _ ?_
  · simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Label.maskedPassword, Label.ofKind]
    omega
  · unfold Ceremony.afterMasked
    refine every_seqs ?_ _ ?_
    · split
      · exact Every.done _
      · exact Every.abort _
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
      omega
  · intro i hi
    simp only [Ceremony.inputBlock, Ceremony.kernelBlock, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, Ceremony.seedBytes,
        Ceremony.passwordBytes, Ceremony.recoveryBytes, Ceremony.outputBytes] <;> omega

/-- **Op 81's engine part's wires fit the pipe.** -/
theorem registerScript_bounded (n : Nat) (password recovery : BoolH) (tail : B8) (hn : n + 2 < B64)
    (hp : password.id < B64) (hr : recovery.id < B64) :
    Every Instr.Bounded (Ceremony.registerScript n password recovery tail) := by
  have hB := big_lt_B64
  unfold Ceremony.registerScript
  split
  · next htl =>
    refine every_seqs (Every.done _) _ ?_
    intro i hi
    unfold Ceremony.registerBlock at hi
    split at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank] <;>
        omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank] <;> omega
  · exact Every.abort _

/-- The register kernel's name is short. -/
theorem registerName_length (size payloadAt authAt tail recoveryAt : Nat) :
    (Ceremony.registerName size payloadAt authAt tail recoveryAt).length ≤
      size + payloadAt + authAt + tail + recoveryAt + 31 := by
  have h1 := length_toString size
  have h2 := length_toString payloadAt
  have h3 := length_toString authAt
  have h4 := length_toString tail
  have h5 := length_toString recoveryAt
  have e1 : "ceremony-register-ctr ".length = 22 := by decide
  have e2 : " ".length = 1 := by decide
  simp only [Ceremony.registerName, length_ascii, String.length_append]
  omega

theorem registerName_lt (size payloadAt authAt tail recoveryAt : Nat) (h : size ≤ 16384) (hp : payloadAt ≤ 16384)
    (ha : authAt ≤ 16384) (ht : tail ≤ 2) (hr : recoveryAt ≤ 16384) :
    (Ceremony.registerName size payloadAt authAt tail recoveryAt).length < B64 := by
  have := registerName_length size payloadAt authAt tail recoveryAt
  have hB := big_lt_B64
  omega

/-- **The registration request's record phase fits the pipe** (S13's `requestCtrScript_bounded`
with the register kernel's name). -/
theorem registerCtr_bounded (n : Nat) (traffic conv : BoolH) (seq frame mask : B8)
    (payloadAt authAt recoveryAt tail : Nat) (hn : n + 6 < B64) (ht : traffic.id < B64) (hc : conv.id < B64)
    (hs : seq.length = 8) (hm : mask.length = 4) (hf : frame.length ≤ 16384) (hp : payloadAt ≤ 16384)
    (ha : authAt ≤ 16384) (htl : tail ≤ 2) (hr : recoveryAt ≤ 16384) :
    Every Instr.Bounded (Send.requestCtrScript n traffic conv seq frame mask
      (Ceremony.registerName frame.length payloadAt authAt tail recoveryAt)) :=
  requestCtrScript_bounded n traffic conv seq frame mask _ hn ht hc hs hm (by omega)
    (registerName_lt _ _ _ _ _ hf hp ha htl hr)

end TlsMpc.Node.Flows.Registry
