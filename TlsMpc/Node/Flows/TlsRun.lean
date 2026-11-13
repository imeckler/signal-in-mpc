import TlsMpc.Node.Flows.RunAgree
import TlsMpc.Node.Flows.TlsWF

/-!
# T4-TLS through `jointRun`: the seal (gap F13, part (a))

REORGANIZATION_PLAN.md stage S12, T4-TLS lifted from the function level (`Tls.seal_is_record`) to
whole runs of the scripts in the ideal model (`Engine/Model.lean` `jointRun`: two honest parties in
lockstep). The kernels' circuits computing their Lean definitions (`TlsBase.circuitOf`) is T2's
trust, as `Contacts.Loaded` / `Ghash.GhashLoaded` state it.

  * Generic: reading the engines' ideal state after `setBool` / `dropBool` (`bools_set_self`,
    `bools_set_ne`, `bools_drop_ne`), one local instruction's effect (`localStep_public`,
    `localStep_concat`, `localStep_run`, `localStep_slice`, `localStep_free`), `runLocal_step`;
    bytes as wire bits under slicing (`bitsOf_take`, `bitsOf_drop`, `slice_bitsOf`); a kernel's
    model circuit on a byte bundle (`circuitOf_eval`).
  * `sealCtr_honest`: two honest parties run `sealCtrScript`; both return header ‖ ciphertext (the
    first `5 + L` bytes of `tls-seal-ctr`'s output on traffic ‖ sequence ‖ content) and the pad's
    handle, which holds the pad (the next 16 bytes); the stores are untouched and every handle below
    the block keeps its value.
  * `tag_honest`: then both run `tagScript` with their halves in their store slots; both return
    `gcm-tag`'s output on pad ‖ A's half ‖ B's half.
  * **`seal_honest` (T4-TLS for the seal, through `jointRun`)**: the two phases in sequence, the halves
    computed between them by each party from ITS OWN shares (`Local.Ghash.half a` for A, `half b` for
    B, over the opened header and ciphertext: what `TlsBackend.sealPhases` stashes), the shares
    sharing H¹ … Hⁿ of the traffic block's GHASH key with `n` covering the record (P-GHASH (a)): the
    record header ‖ ciphertext ‖ tag the parties jointly produce is EXACTLY
    `TlsRecord.sealCore` of the block's key and IV, the sequence, the content, the kind and the
    padding (`Tls.seal_is_record`, i.e. `sealCtr_with_tag_is_seal` with `halves` discharged).

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.Tls

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Node.Flows.Run

/-! ## The engines' ideal state -/

theorem bools_set_self (I : Ideal) (n : Nat) (v : Bits) : (I.setBool ⟨n⟩ v).bools n = some v := by
  simp [Ideal.setBool]

theorem bools_set_ne (I : Ideal) (h : BoolH) (v : Bits) (j : Nat) (hj : j ≠ h.id) :
    (I.setBool h v).bools j = I.bools j := by
  simp [Ideal.setBool, hj]

theorem bools_drop_ne (I : Ideal) (h : BoolH) (j : Nat) (hj : j ≠ h.id) : (I.dropBool h).bools j = I.bools j := by
  simp [Ideal.dropBool, hj]

/-- A handle's value after sets and drops of other ids. -/
macro "ival_tac" : tactic => `(tactic|
  (simp (disch := ne_tac) only [bools_set_self, bools_set_ne, bools_drop_ne] <;> first | rfl | assumption))

/-! ## One local instruction -/

theorem localStep_public (E : Env) (out : BoolH) (bits : Bits) (I : Ideal) :
    localStep E (.boolPublic out bits) I = some (I.setBool out bits) := by
  simp [localStep, idealStep, blankWire, InstrP.map]

theorem localStep_concat (E : Env) (out : BoolH) (parts : List BoolH) (I : Ideal) (vs : List Bits)
    (hv : parts.mapM (fun g => I.bools g.id) = some vs) :
    localStep E (.concat out parts) I = some (I.setBool out vs.flatten) := by
  simp [localStep, idealStep, blankWire, InstrP.map, hv]

theorem localStep_run (E : Env) (out : BoolH) (name : Bytes) (copies : Nat) (input : BoolH) (I : Ideal)
    (c : Engine.Circuit) (v : Bits) (hc : E.circuits name = some c) (hv : I.bools input.id = some v)
    (hl : v.length = copies * c.inWidth) :
    localStep E (.run out name copies input) I = some (I.setBool out (runCopies c copies v)) := by
  simp [localStep, idealStep, blankWire, InstrP.map, hc, hv, hl]

theorem localStep_slice (E : Env) (out h : BoolH) (lo hi : Nat) (I : Ideal) (v w : Bits)
    (hv : I.bools h.id = some v) (hb : lo ≤ hi ∧ hi ≤ v.length) (hw : (v.drop lo).take (hi - lo) = w) :
    localStep E (.slice out h lo hi) I = some (I.setBool out w) := by
  simp [localStep, idealStep, blankWire, InstrP.map, hv, hb, hw]

theorem localStep_free (E : Env) (h : BoolH) (I : Ideal) : localStep E (.freeBool h) I = some (I.dropBool h) := by
  simp [localStep, idealStep, blankWire, InstrP.map]

theorem runLocal_step (E : Env) (i : Instr) (is : List Instr) (I I1 : Ideal) (h : localStep E i I = some I1) :
    runLocal E (i :: is) I = runLocal E is I1 := by
  simp [runLocal, h]

theorem runLocal_nil (E : Env) (I : Ideal) : runLocal E [] I = some I := rfl

/-! ## Bytes as wire bits -/

theorem bitsOf_drop : ∀ (l : B8) (k : Nat), (bitsOf l).drop (8 * k) = bitsOf (l.drop k)
  | [], k => by simp
  | b :: l, 0 => by simp
  | b :: l, k + 1 => by
    rw [bitsOf_cons, show 8 * (k + 1) = 8 + 8 * k by omega, ← List.drop_drop,
      List.drop_left' (length_bitsOfByte b), bitsOf_drop l k, List.drop_succ_cons]

theorem bitsOf_take : ∀ (l : B8) (k : Nat), (bitsOf l).take (8 * k) = bitsOf (l.take k)
  | [], k => by simp
  | b :: l, 0 => by simp
  | b :: l, k + 1 => by
    rw [bitsOf_cons, show 8 * (k + 1) = (bitsOfByte b).length + 8 * k by simp; omega, List.take_length_add_append,
      bitsOf_take l k, List.take_succ_cons, bitsOf_cons]

theorem slice_bitsOf (l : B8) (a b : Nat) :
    ((bitsOf l).drop (8 * a)).take (8 * b - 8 * a) = bitsOf ((l.drop a).take (b - a)) := by
  rw [bitsOf_drop, ← Nat.mul_sub, bitsOf_take]

theorem circuitOf_eval (K : HybridKernel.Kernel) (x : B8) :
    (circuitOf K).eval (bitsOf x) = bitsOf (kernelOut K x) := by
  show bitsOf (kernelOut K (bytesOf (bitsOf x))) = _
  rw [bytesOf_bitsOf]

theorem runCopies_circuitOf (K : HybridKernel.Kernel) (x : B8) (h : 8 * x.length = (circuitOf K).inWidth) :
    runCopies (circuitOf K) 1 (bitsOf x) = bitsOf (kernelOut K x) := by
  rw [runCopies_one' _ _ (by rw [length_bitsOf]; exact h), circuitOf_eval]

theorem flatten3 (a b c : B8) : [bitsOf a, bitsOf b, bitsOf c].flatten = bitsOf (a ++ (b ++ c)) := by
  simp

theorem sealCtr_inBytes (kind size padding : Nat) :
    (circuitOf (HybridKernel.tlsSealCtr kind size padding)).inWidth = 8 * (68 + size) := by
  simp [circuitOf, kernelCircuit, kernelInBytes, HybridKernel.tlsSealCtr, HybridKernel.Shape.variables]
  omega

theorem gcmTag_inBytes : (circuitOf HybridKernel.gcmTag).inWidth = 8 * 48 := by
  simp [circuitOf, kernelCircuit, kernelInBytes, HybridKernel.gcmTag, HybridKernel.Shape.variables]

/-! ## The seal through `jointRun` -/

/-- **The seal's first phase, two honest parties** (`sealCtrScript`). -/
theorem sealCtr_honest (E : Env) (kind size padding : Nat)
    (hE : E.circuits (sealCtrName kind size padding) = some (circuitOf (HybridKernel.tlsSealCtr kind size padding)))
    (n : Nat) (traffic content : BoolH) (K seqB C : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hC : C.length = size) (htn : traffic.id < n) (hcn : content.id < n) (σA σB : Store) (I : Ideal)
    (hIt : I.bools traffic.id = some (bitsOf K)) (hIc : I.bools content.id = some (bitsOf C)) :
    let out := kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))
    ∃ J, JRet (jointRun E (sealCtrScript n traffic content seqB kind size padding)
        (sealCtrScript n traffic content seqB kind size padding) σA σB I)
      (out.take (5 + innerLength size padding), ⟨n + 3⟩) (out.take (5 + innerLength size padding), ⟨n + 3⟩)
        J σA σB ∧
      J.bools (n + 3) = some (bitsOf ((out.drop (5 + innerLength size padding)).take 16)) ∧
      ∀ j, j < n → J.bools j = I.bools j := by
  intro out
  have hdef : kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C)) = out := rfl
  have hlen : out.length = 5 + innerLength size padding + 16 := by
    obtain ⟨hout, -⟩ := sealCtr_kernelOut kind size padding K seqB C hK hs hC
    have hH := header_length (innerLength size padding + 16)
    have hCT : (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding)).length =
        innerLength size padding := by
      rw [HybridKernel.ctrOf_length _ _ _ hK, inner_length, hC]
    have hP := padOf_length K seqB hK
    rw [← hdef, hout]
    simp only [List.length_append, hH, hCT, hP]
  clear_value out
  -- the engines' states, step by step
  have hw : 8 * (K ++ (seqB ++ C)).length = (circuitOf (HybridKernel.tlsSealCtr kind size padding)).inWidth := by
    rw [sealCtr_inBytes]
    simp only [List.length_append, hK, hs, hC]
    omega
  have s1 := localStep_public E ⟨n⟩ (bitsOf seqB) I
  have s2 := localStep_concat E ⟨n + 1⟩ [traffic, ⟨n⟩, content] (I.setBool ⟨n⟩ (bitsOf seqB))
    [bitsOf K, bitsOf seqB, bitsOf C] (by
      simp only [List.mapM_cons, List.mapM_nil]
      rw [show (I.setBool ⟨n⟩ (bitsOf seqB)).bools traffic.id = some (bitsOf K) by ival_tac,
        show (I.setBool ⟨n⟩ (bitsOf seqB)).bools (⟨n⟩ : BoolH).id = some (bitsOf seqB) by ival_tac,
        show (I.setBool ⟨n⟩ (bitsOf seqB)).bools content.id = some (bitsOf C) by ival_tac]
      rfl)
  rw [flatten3] at s2
  have s3 := localStep_run E ⟨n + 2⟩ (sealCtrName kind size padding) 1 ⟨n + 1⟩
    ((I.setBool ⟨n⟩ (bitsOf seqB)).setBool ⟨n + 1⟩ (bitsOf (K ++ (seqB ++ C)))) _ _ hE
    (by ival_tac) (by rw [length_bitsOf, Nat.one_mul]; exact hw)
  rw [runCopies_circuitOf _ _ hw, hdef] at s3
  have s4 := localStep_slice E ⟨n + 3⟩ ⟨n + 2⟩ (8 * (5 + innerLength size padding))
    (8 * (5 + innerLength size padding + 16))
    (((I.setBool ⟨n⟩ (bitsOf seqB)).setBool ⟨n + 1⟩ (bitsOf (K ++ (seqB ++ C)))).setBool ⟨n + 2⟩ (bitsOf out))
    (bitsOf out) _ (by ival_tac) (by rw [length_bitsOf, hlen]; omega) (slice_bitsOf out _ _)
  rw [show 5 + innerLength size padding + 16 - (5 + innerLength size padding) = 16 by omega] at s4
  have s5 := localStep_slice E ⟨n + 4⟩ ⟨n + 2⟩ 0 (8 * (5 + innerLength size padding))
    ((((I.setBool ⟨n⟩ (bitsOf seqB)).setBool ⟨n + 1⟩ (bitsOf (K ++ (seqB ++ C)))).setBool ⟨n + 2⟩ (bitsOf out)).setBool
      ⟨n + 3⟩ (bitsOf ((out.drop (5 + innerLength size padding)).take 16)))
    (bitsOf out) (bitsOf (out.take (5 + innerLength size padding)))
    (by ival_tac) (by rw [length_bitsOf, hlen]; omega)
    (by rw [show (0 : Nat) = 8 * 0 from rfl, slice_bitsOf, List.drop_zero, Nat.sub_zero])
  refine ⟨((((((((I.setBool ⟨n⟩ (bitsOf seqB)).setBool ⟨n + 1⟩ (bitsOf (K ++ (seqB ++ C)))).setBool ⟨n + 2⟩
    (bitsOf out)).setBool ⟨n + 3⟩ (bitsOf ((out.drop (5 + innerLength size padding)).take 16))).setBool ⟨n + 4⟩
      (bitsOf (out.take (5 + innerLength size padding)))).dropBool ⟨n⟩).dropBool ⟨n + 1⟩).dropBool ⟨n + 2⟩).dropBool
        ⟨n + 4⟩, ?_, ?_, ?_⟩
  · unfold sealCtrScript
    apply jret_locals E _ _ σA σB _ _ _ σA σB _ (by simp [isLocal]) I
    · rw [runLocal_step E _ _ _ _ s1, runLocal_step E _ _ _ _ s2, runLocal_step E _ _ _ _ s3,
        runLocal_step E _ _ _ _ s4, runLocal_step E _ _ _ _ s5, runLocal_step E _ _ _ _ (localStep_free E _ _),
        runLocal_step E _ _ _ _ (localStep_free E _ _), runLocal_step E _ _ _ _ (localStep_free E _ _),
        runLocal_nil]
    · refine jret_openThen E _ _ _ _ σA σB _ (bitsOf (out.take (5 + innerLength size padding))) _ _ _ σA σB
        (by ival_tac) ?_
      rw [bytesOf_bitsOf]
      apply jret_locals E _ _ σA σB _ _ _ σA σB [.freeBool ⟨n + 4⟩] (by simp [isLocal])
      · rw [runLocal_step E _ _ _ _ (localStep_free E _ _), runLocal_nil]
      · exact jret_done E _ _ σA σB _
  · ival_tac
  · intro j hj
    ival_tac

theorem bothBools_a (I : Ideal) (oa ob : BoolH) (mine peer : Bits) :
    bothBools .a I oa ob mine peer = (I.setBool oa mine).setBool ob peer := by
  simp [bothBools]

/-- **The seal's last phase, two honest parties** (`tagScript`): with this party's half in its own
store slot (A: `xa`, B: `xb`) and the pad's handle holding the pad, both return `gcm-tag`'s output on
pad ‖ A's half ‖ B's half. -/
theorem tag_honest (E : Env) (hE : E.circuits tagName = some (circuitOf HybridKernel.gcmTag))
    (m : Nat) (pad : BoolH) (halfSlot : Nat) (padB : B8) (hp : padB.length = 16) (hpm : pad.id < m)
    (σA σB : Store) (I : Ideal) (hIp : I.bools pad.id = some (bitsOf padB)) (xa xb : W)
    (hA : σA.bits halfSlot = bitsOfW xa) (hB : σB.bits halfSlot = bitsOfW xb) :
    ∃ J, JRet (jointRun E (tagScript m pad halfSlot) (tagScript m pad halfSlot) σA σB I)
      (kernelOut HybridKernel.gcmTag (padB ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb)))
      (kernelOut HybridKernel.gcmTag (padB ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb))) J σA σB := by
  have hw : 8 * (padB ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb)).length =
      (circuitOf HybridKernel.gcmTag).inWidth := by
    rw [gcmTag_inBytes]
    simp only [List.length_append, hp, Local.Ghash.toBytes_length]
  have s1 := localStep_concat E ⟨m + 2⟩ [pad, ⟨m⟩, ⟨m + 1⟩]
    ((I.setBool ⟨m⟩ (bitsOfW xa)).setBool ⟨m + 1⟩ (bitsOfW xb)) [bitsOf padB, bitsOfW xa, bitsOfW xb] (by
      simp only [List.mapM_cons, List.mapM_nil]
      rw [show ((I.setBool ⟨m⟩ (bitsOfW xa)).setBool ⟨m + 1⟩ (bitsOfW xb)).bools pad.id = some (bitsOf padB) by ival_tac,
        show ((I.setBool ⟨m⟩ (bitsOfW xa)).setBool ⟨m + 1⟩ (bitsOfW xb)).bools (⟨m⟩ : BoolH).id = some (bitsOfW xa) by
          ival_tac,
        show ((I.setBool ⟨m⟩ (bitsOfW xa)).setBool ⟨m + 1⟩ (bitsOfW xb)).bools (⟨m + 1⟩ : BoolH).id = some (bitsOfW xb) by
          ival_tac]
      rfl)
  have hf : [bitsOf padB, bitsOfW xa, bitsOfW xb].flatten =
      bitsOf (padB ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb)) := by
    simp [bitsOfW]
  rw [hf] at s1
  have s2 := localStep_run E ⟨m + 3⟩ tagName 1 ⟨m + 2⟩
    (((I.setBool ⟨m⟩ (bitsOfW xa)).setBool ⟨m + 1⟩ (bitsOfW xb)).setBool ⟨m + 2⟩
      (bitsOf (padB ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb)))) _ _ hE
    (by ival_tac) (by rw [length_bitsOf, Nat.one_mul]; exact hw)
  rw [runCopies_circuitOf _ _ hw] at s2
  refine ⟨(((((I.setBool ⟨m⟩ (bitsOfW xa)).setBool ⟨m + 1⟩ (bitsOfW xb)).setBool ⟨m + 2⟩
      (bitsOf (padB ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb)))).setBool ⟨m + 3⟩
      (bitsOf (kernelOut HybridKernel.gcmTag (padB ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb))))).dropBool
      pad).dropBool ⟨m + 3⟩, ?_⟩
  unfold tagScript
  rw [seqs_cons]
  apply jret_boolInputBoth E ⟨m⟩ ⟨m + 1⟩ 128 true false halfSlot halfSlot _ _ σA σB I _ _ _ σA σB
    (by rw [hA, length_bitsOfW]) (by rw [hB, length_bitsOfW])
  rw [bothBools_a, hA, hB]
  apply jret_locals E _ _ σA σB _ _ _ σA σB _ (by simp [isLocal])
  · rw [runLocal_step E _ _ _ _ s1, runLocal_step E _ _ _ _ s2, runLocal_step E _ _ _ _ (localStep_free E _ _),
      runLocal_nil]
  · refine jret_openThen E _ _ _ _ σA σB _
      (bitsOf (kernelOut HybridKernel.gcmTag (padB ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb))))
      _ _ _ σA σB (by ival_tac) ?_
    rw [bytesOf_bitsOf]
    apply jret_locals E _ _ σA σB _ _ _ σA σB [.freeBool ⟨m + 3⟩] (by simp [isLocal])
    · rw [runLocal_step E _ _ _ _ (localStep_free E _ _), runLocal_nil]
    · exact jret_done E _ _ σA σB _

/-- **T4-TLS for the seal, through `jointRun`** (gap F13 (a)). Two honest parties run the seal's first
phase on the client traffic block `K` and the content `C`; both return header ‖ ciphertext `hc` and
the pad's handle. Each then computes ITS OWN half over the opened header and ciphertext from its own
shares (`Local.Ghash.half a` for A, `half b` for B; the backend stashes it, `TlsBackend.sealPhases`);
whatever else the stores hold, the second phase returns, to both, a tag such that `hc ‖ tag` is
`TlsRecord.sealCore` of the block's key and IV, the sequence, the content, the kind and the padding,
provided `a` and `b` share H¹ … Hⁿ of the block's GHASH key with `n` covering the record
(P-GHASH (a); `ensure`). -/
theorem seal_honest (E : Env) (kind size padding : Nat)
    (hctr : E.circuits (sealCtrName kind size padding) = some (circuitOf (HybridKernel.tlsSealCtr kind size padding)))
    (htag : E.circuits tagName = some (circuitOf HybridKernel.gcmTag))
    (n m : Nat) (hm : n + 3 < m) (traffic content : BoolH) (K seqB C : B8) (hK : K.length = 60)
    (hs : seqB.length = 8) (hC : C.length = size) (htn : traffic.id < n) (hcn : content.id < n)
    (σA σB : Store) (I : Ideal) (hIt : I.bools traffic.id = some (bitsOf K)) (hIc : I.bools content.id = some (bitsOf C))
    (halfSlot : Nat) (a b : List W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (innerLength size padding) ≤ nPow) :
    let hc := (kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))).take
      (5 + innerLength size padding)
    ∃ J, JRet (jointRun E (sealCtrScript n traffic content seqB kind size padding)
        (sealCtrScript n traffic content seqB kind size padding) σA σB I) (hc, ⟨n + 3⟩) (hc, ⟨n + 3⟩) J σA σB ∧
      ∀ σA' σB' : Store,
        σA'.bits halfSlot = bitsOfW (Local.Ghash.half a (hc.take 5) (hc.drop 5)) →
        σB'.bits halfSlot = bitsOfW (Local.Ghash.half b (hc.take 5) (hc.drop 5)) →
        ∃ J' tag, JRet (jointRun E (tagScript m ⟨n + 3⟩ halfSlot) (tagScript m ⟨n + 3⟩ halfSlot) σA' σB' J)
            tag tag J' σA' σB' ∧
          hc ++ tag = TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB C kind padding := by
  intro hc
  obtain ⟨J, hJ, hpad, -⟩ := sealCtr_honest E kind size padding hctr n traffic content K seqB C hK hs hC htn hcn
    σA σB I hIt hIc
  refine ⟨J, hJ, fun σA' σB' hA hB => ?_⟩
  have hlen : (kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))).length =
      5 + innerLength size padding + 16 := by
    obtain ⟨hout, -⟩ := sealCtr_kernelOut kind size padding K seqB C hK hs hC
    have hH := header_length (innerLength size padding + 16)
    have hCT : (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding)).length =
        innerLength size padding := by
      rw [HybridKernel.ctrOf_length _ _ _ hK, inner_length, hC]
    rw [hout]
    simp only [List.length_append, hH, hCT, padOf_length K seqB hK]
  obtain ⟨J', hJ'⟩ := tag_honest E htag m ⟨n + 3⟩ halfSlot _ (by simp only [List.length_take, List.length_drop, hlen]; omega)
    (show n + 3 < m from hm) σA' σB' J hpad _ _ hA hB
  exact ⟨J', _, hJ', seal_is_record kind size padding K seqB C hK hs hC a b nPow hsh hn⟩

end TlsMpc.Node.Flows.Tls
