import TlsMpc.Node.Flows.TlsGhashRun

/-!
# Value-level T3 for a whole seal and a whole open, against ANY adversary

REORGANIZATION_PLAN.md stage S12, T3 at the level of values (plan 8.1): for the honest party A and
ANY adversary playing B (`Engine/Model.lean` `withAdv`: any function of its view so far), the
adversary's view of a run is at most the releases the script declares (`Tls.sealKinds`,
`Tls.openKinds`), each with its value characterised by the kernel theorems.

  * `sealCtr_disclosure` (the seal's first phase, any honest party): at most ONE release,
    `sealedRecord`, the header ‖ ciphertext of `tls-seal-ctr` on the traffic block, the sequence and
    the content (`sealCtr_kernelOut`: the record header and the CTR ciphertext; the pad stays
    private); the adversary contributes nothing.
  * `tag_disclosure_A` (the seal's last phase): at most ONE release, `sealedRecord`, the tag
    `pad ⊕ halfA ⊕ halfB'` for the 16 bytes `halfB'` the adversary input (`tag_out`); with B's honest
    half it is GCM's tag (`seal_is_record`).
  * `open_disclosure_A` (the open): at most TWO releases: `recordKindBit`, the typed kernel's bit, which
    is 0 or 255, and `recordEvent`, which is EXACTLY the event of the single class kernel
    `tls-open-application-class CAP` on the record, the keys, the parser state and the tag check's
    output (`classSpec`, `open_event_class`), whichever branch ran, for the 16 bytes the adversary
    input as its half; when that check output is 0 (the record is refused), the two releases are the
    constants `[0]` and `[0, 0]` (`open_disclosure_rejected`, `tlsOpenTyped_gated`), whatever the
    record and the keys.

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.Tls

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Node.Flows.Run
open TlsMpc.TypedOpenKernel
open TlsMpc.HybridKernel (lookup lookupFrom inputValue)
open Std.Tactic.BVDecide

/-- One local instruction against an adversary: nothing released, the run goes on from its state. -/
theorem viewD_local1 {α : Type} (E : Env) (me : Party) (adv : Adversary) (i : Instr) (hi : isLocal i = true)
    (s : Script α) (σ : Store) (I I1 : Ideal) (vD L : List Release) (h : localStep E i I = some I1)
    (hk : (withAdv E me adv s σ I1 vD).viewD <+: L) : (withAdv E me adv (seq i s) σ I vD).viewD <+: L :=
  viewD_locals E me adv s σ L [i] (by simp [hi]) I vD (fun I' hI' => by
    rw [runLocal_step E _ _ _ _ h, runLocal_nil, Option.some.injEq] at hI'
    subst hI'
    exact hk)

/-- `viewD_local1` under an existential bound. -/
theorem viewD_local1_ex {α β : Type} (E : Env) (me : Party) (adv : Adversary) (i : Instr) (hi : isLocal i = true)
    (s : Script α) (σ : Store) (I I1 : Ideal) (vD : List Release) (h : localStep E i I = some I1)
    (P : β → Prop) (L : β → List Release)
    (hk : ∃ b, P b ∧ (withAdv E me adv s σ I1 vD).viewD <+: L b) :
    ∃ b, P b ∧ (withAdv E me adv (seq i s) σ I vD).viewD <+: L b := by
  obtain ⟨b, hb, hv⟩ := hk
  exact ⟨b, hb, viewD_local1 E me adv i hi s σ I I1 vD (L b) h hv⟩

theorem localStep_concat3 (E : Env) (out a b c : BoolH) (I : Ideal) (va vb vc w : Bits)
    (ha : I.bools a.id = some va) (hb : I.bools b.id = some vb) (hc : I.bools c.id = some vc)
    (hw : va ++ (vb ++ vc) = w) :
    localStep E (.concat out [a, b, c]) I = some (I.setBool out w) := by
  rw [localStep_concat E out _ I [va, vb, vc] (by simp [List.mapM_cons, ha, hb, hc])]
  simp [hw]

/-! ## The seal -/

/-- **T3, the seal's first phase** (any honest party, any adversary). -/
theorem sealCtr_disclosure (E : Env) (me : Party) (adv : Adversary) (kind size padding : Nat)
    (hE : E.circuits (sealCtrName kind size padding) = some (circuitOf (HybridKernel.tlsSealCtr kind size padding)))
    (n : Nat) (traffic content : BoolH) (K seqB C : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hC : C.length = size) (htn : traffic.id < n) (hcn : content.id < n) (σ : Store) (I : Ideal) (vD : List Release)
    (hIt : I.bools traffic.id = some (bitsOf K)) (hIc : I.bools content.id = some (bitsOf C)) :
    (withAdv E me adv (sealCtrScript n traffic content seqB kind size padding) σ I vD).viewD <+:
      [⟨Label.sealedRecord, .bits (bitsOf ((kernelOut (HybridKernel.tlsSealCtr kind size padding)
        (K ++ (seqB ++ C))).take (5 + innerLength size padding)))⟩] := by
  have hlen : (kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))).length =
      5 + innerLength size padding + 16 := by
    obtain ⟨hout, -⟩ := sealCtr_kernelOut kind size padding K seqB C hK hs hC
    have hH := header_length (innerLength size padding + 16)
    have hCT : (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding)).length =
        innerLength size padding := by
      rw [HybridKernel.ctrOf_length _ _ _ hK, inner_length, hC]
    rw [hout]
    simp only [List.length_append, hH, hCT, padOf_length K seqB hK]
  generalize hout : kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C)) = out at hlen ⊢
  have hw : 8 * (K ++ (seqB ++ C)).length = (circuitOf (HybridKernel.tlsSealCtr kind size padding)).inWidth := by
    rw [sealCtr_inBytes]
    simp only [List.length_append, hK, hs, hC]
    omega
  have hb : (bitsOf out).length = 8 * (5 + innerLength size padding + 16) := by rw [length_bitsOf, hlen]
  unfold sealCtrScript
  simp only [seqs_cons, seqs_nil]
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_public E ⟨n⟩ (bitsOf seqB) I) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_concat3 E ⟨n + 1⟩ traffic ⟨n⟩ content _
    (bitsOf K) (bitsOf seqB) (bitsOf C) (bitsOf (K ++ (seqB ++ C))) (by ival_tac) (by ival_tac) (by ival_tac)
    (by simp)) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_runK E ⟨n + 2⟩ _ ⟨n + 1⟩ _ _ _ _ hE (by ival_tac)
    hw hout) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 3⟩ ⟨n + 2⟩ _ _ _ (bitsOf out)
    (bitsOf ((out.drop (5 + innerLength size padding)).take 16)) (by ival_tac) (by rw [hb]; omega)
    (by rw [slice_bitsOf' out (5 + innerLength size padding) (5 + innerLength size padding + 16) _ _ rfl rfl,
      show 5 + innerLength size padding + 16 - (5 + innerLength size padding) = 16 by omega])) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 4⟩ ⟨n + 2⟩ 0 _ _ (bitsOf out)
    (bitsOf (out.take (5 + innerLength size padding))) (by ival_tac) (by rw [hb]; omega)
    (by rw [slice_bitsOf' out 0 (5 + innerLength size padding) _ _ rfl rfl, List.drop_zero, Nat.sub_zero])) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_openThen E me adv _ _ _ σ _ vD _ [] (by ival_tac) ?_
  exact silent_prefix E me adv _ (Silent.seq rfl (Silent.done _)) _ _ _ _

theorem bytesOf_128 (pb : Bits) (h : pb.length = 128) : (bytesOf pb).length = 16 ∧ bitsOf (bytesOf pb) = pb := by
  have e := Ghash.bitsOf_bytesOf pb (by omega)
  refine ⟨?_, e⟩
  have := congrArg List.length e
  rw [length_bitsOf, h] at this
  omega

/-- **T3, the seal's last phase, A honest** (any adversary B): at most one release, the tag
`gcm-tag` computes from the pad, A's half and the 16 bytes B input. -/
theorem tag_disclosure_A (E : Env) (adv : Adversary) (hE : E.circuits tagName = some (circuitOf HybridKernel.gcmTag))
    (m : Nat) (pad : BoolH) (halfSlot : Nat) (padB : B8) (hp : padB.length = 16) (hpm : pad.id < m)
    (σ : Store) (I : Ideal) (vD : List Release) (hIp : I.bools pad.id = some (bitsOf padB)) (xa : W)
    (hA : σ.bits halfSlot = bitsOfW xa) :
    ∃ hb : B8, hb.length = 16 ∧ (withAdv E .a adv (tagScript m pad halfSlot) σ I vD).viewD <+:
      [⟨Label.sealedRecord, .bits (bitsOf (kernelOut HybridKernel.gcmTag (padB ++ (Local.Ghash.toBytes xa ++ hb))))⟩] := by
  unfold tagScript
  rw [seqs_cons]
  rcases Ghash.viewD_both E adv ⟨m⟩ ⟨m + 1⟩ 128 true false halfSlot _ σ I vD (by rw [hA, length_bitsOfW])
    with h1 | ⟨pb, hpb, h1⟩
  · exact ⟨List.replicate 16 0, by simp, by rw [h1]; exact List.nil_prefix⟩
  obtain ⟨hbl, hbb⟩ := bytesOf_128 pb hpb
  refine ⟨bytesOf pb, hbl, ?_⟩
  rw [h1, hA]
  have hw : 8 * (padB ++ (Local.Ghash.toBytes xa ++ bytesOf pb)).length = (circuitOf HybridKernel.gcmTag).inWidth := by
    rw [gcmTag_inBytes]
    simp only [List.length_append, hp, Local.Ghash.toBytes_length, hbl]
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_concat3 E ⟨m + 2⟩ pad ⟨m⟩ ⟨m + 1⟩ _
    (bitsOf padB) (bitsOfW xa) pb (bitsOf (padB ++ (Local.Ghash.toBytes xa ++ bytesOf pb)))
    (by ival_tac) (by ival_tac) (by ival_tac) (by rw [bitsOf_append, bitsOf_append, hbb]; rfl)) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_runK E ⟨m + 3⟩ _ ⟨m + 2⟩ _ _ _ _ hE (by ival_tac)
    hw rfl) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_openThen E .a adv _ _ _ σ _ vD _ [] (by ival_tac) ?_
  exact silent_prefix E .a adv _ (Silent.seq rfl (Silent.done _)) _ _ _ _

/-! ## The open -/

/-- The event the open releases is the class kernel's, in both branches. -/
theorem open_event_class (cap : Nat) (hcap : 21 ≤ cap) (tin P : B8) (hP : P.length = 11)
    (bP : (lookup (typedInputs cap) "parser").map (BVExpr.eval (assignOf tin)) = P) :
    ((kernelOut (tlsOpenTyped cap) tin).take 1 = [0] →
      ((kernelOut (tlsOpenTyped cap) tin).drop 1).take 2 = (classSpec cap (assignOf tin)).take 2) ∧
    ((kernelOut (tlsOpenTyped cap) tin).take 1 = [255] →
      (kernelOut (tlsFrame cap) (P ++ parsedOf cap (kernelOut (tlsOpenTyped cap) tin))).take 2 =
        (classSpec cap (assignOf tin)).take 2) := by
  have hCS := classSpec_length cap hcap (assignOf tin)
  have hpv := parsed_length cap hcap (assignOf tin)
  have hpo := typedOut_parsed cap hcap tin
  have hbit := typedOut_bit (cap := cap) tin
  refine ⟨fun h0 => ?_, fun _ => ?_⟩
  · have hb0 : BVExpr.eval (assignOf tin) (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed cap)) = 0 := by
      rw [hbit] at h0
      simpa using h0
    have hfv := typed_fields cap _ hb0
    have hout : kernelOut (tlsOpenTyped cap) tin = [0] ++ (classSpec cap (assignOf tin) ++
        (typedParsed cap).map (BVExpr.eval (assignOf tin))) := by
      show (fieldValues (tlsOpenTyped cap) _).flatten = _
      rw [hfv]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append]
      rw [flatten_fields _ (by omega)]
      simp
    rw [hout]
    simp only [List.singleton_append, List.drop_one, List.tail_cons]
    rw [List.take_append_of_le_length (by omega)]
  · have hfi1 : (lookup (frameInputs cap) "parser").map (BVExpr.eval (assignOf (P ++ parsedOf cap
        (kernelOut (tlsOpenTyped cap) tin)))) = P := by
      have : lookup (frameInputs cap) "parser" = ByteCircuit.inputBytes 0 11 := by simp [lookup, lookupFrom, frameInputs]
      rw [this]
      show inputValue _ 0 11 = _
      rw [iv _ _ _ (by simp; omega), List.drop_zero, List.take_left' hP]
    have hfi2 : (lookup (frameInputs cap) "parsed").map (BVExpr.eval (assignOf (P ++ parsedOf cap
        (kernelOut (tlsOpenTyped cap) tin)))) = parsedOf cap (kernelOut (tlsOpenTyped cap) tin) := by
      have : lookup (frameInputs cap) "parsed" = ByteCircuit.inputBytes 11 (cap - 17) := by
        simp [lookup, lookupFrom, frameInputs, HybridKernel.Shape.variables]
      rw [this]
      show inputValue _ 11 (cap - 17) = _
      rw [iv _ _ _ (by simp; rw [hpo, hpv]; omega), List.drop_left' hP,
        List.take_of_length_le (Nat.le_of_eq (by rw [hpo, hpv]))]
    rw [frameOut_eq cap hcap, hfi1, hfi2, hpo, classSpec, bP]

theorem viewD_direct (E : Env) (me : Party) (adv : Adversary) (n cap : Nat) (tout : B8)
    (htl : tout.length = 16 + (cap - 21) + (cap - 17)) (σ : Store) (I : Ideal) (vD : List Release)
    (h8 : I.bools (n + 8) = some (bitsOf tout)) :
    (withAdv E me adv (directRest n cap) σ I vD).viewD <+:
      [⟨Label.recordEvent, .bits (bitsOf ((tout.drop 1).take 2))⟩] := by
  have hb : (bitsOf tout).length = 8 * (16 + (cap - 21) + (cap - 17)) := by rw [length_bitsOf, htl]
  unfold directRest
  simp only [seqs_cons, seqs_nil]
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 10⟩ ⟨n + 8⟩ 8 24 I _
    (bitsOf ((tout.drop 1).take 2)) h8 (by rw [hb]; omega) (by rw [slice_bitsOf' tout 1 3 8 24 rfl rfl])) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 11⟩ ⟨n + 8⟩ 24 112 _ (bitsOf tout) _
    (by ival_tac) (by rw [hb]; omega) (slice_bitsOf' tout 3 14 24 112 rfl rfl)) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 12⟩ ⟨n + 8⟩ 112 128 _ (bitsOf tout) _
    (by ival_tac) (by rw [hb]; omega) (slice_bitsOf' tout 14 16 112 128 rfl rfl)) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 13⟩ ⟨n + 8⟩ 128 (128 + 8 * (cap - 21)) _
    (bitsOf tout) _ (by ival_tac) (by rw [hb]; omega)
    (slice_bitsOf' tout 16 (16 + (cap - 21)) _ _ rfl (by omega))) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_openThen E me adv _ _ _ σ _ vD _ [] (by ival_tac) ?_
  exact silent_prefix E me adv _ (Silent.seq rfl (Silent.done _)) _ _ _ _

theorem viewD_frame (E : Env) (me : Party) (adv : Adversary) (cap : Nat)
    (hE : E.circuits (frameName cap) = some (circuitOf (tlsFrame cap))) (n : Nat) (hcap : 21 ≤ cap)
    (parser : BoolH) (hpn : parser.id < n) (P tout : B8) (hP : P.length = 11)
    (htl : tout.length = 16 + (cap - 21) + (cap - 17)) (σ : Store) (I : Ideal) (vD : List Release)
    (h8 : I.bools (n + 8) = some (bitsOf tout)) (hp : I.bools parser.id = some (bitsOf P)) :
    (withAdv E me adv (frameRest n parser cap) σ I vD).viewD <+:
      [⟨Label.recordEvent, .bits (bitsOf ((kernelOut (tlsFrame cap) (P ++ parsedOf cap tout)).take 2))⟩] := by
  have hb : (bitsOf tout).length = 8 * (16 + (cap - 21) + (cap - 17)) := by rw [length_bitsOf, htl]
  have hpl : (parsedOf cap tout).length = cap - 17 := by
    simp only [parsedOf, List.length_take, List.length_drop, htl]
    omega
  have hw : 8 * (P ++ parsedOf cap tout).length = (circuitOf (tlsFrame cap)).inWidth := by
    rw [frame_inWidth, List.length_append, hP, hpl]
  have hfl := frameOut_length cap hcap (P ++ parsedOf cap tout)
  generalize hfo : kernelOut (tlsFrame cap) (P ++ parsedOf cap tout) = fout at hfl ⊢
  have hfb : (bitsOf fout).length = 8 * (15 + (cap - 21)) := by rw [length_bitsOf, hfl]
  unfold frameRest
  simp only [seqs_cons, seqs_nil]
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 10⟩ ⟨n + 8⟩ (128 + 8 * (cap - 21))
    (128 + 8 * (cap - 21) + 8 * (cap - 17)) I _ (bitsOf (parsedOf cap tout)) h8 (by rw [hb]; omega)
    (by rw [slice_bitsOf' tout (16 + (cap - 21)) (16 + (cap - 21) + (cap - 17)) _ _ (by omega) (by omega),
          Nat.add_sub_cancel_left]; rfl)) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_concat2 E ⟨n + 11⟩ parser ⟨n + 10⟩ _ (bitsOf P)
    (bitsOf (parsedOf cap tout)) (bitsOf (P ++ parsedOf cap tout)) (by ival_tac) (by ival_tac)
    (by rw [bitsOf_append])) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_runK E ⟨n + 12⟩ _ ⟨n + 11⟩ _ _ _ _ hE (by ival_tac)
    hw hfo) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 13⟩ ⟨n + 12⟩ 0 16 _ (bitsOf fout)
    (bitsOf (fout.take 2)) (by ival_tac) (by rw [hfb]; omega)
    (by rw [slice_bitsOf' fout 0 2 0 16 rfl rfl]; simp)) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 14⟩ ⟨n + 12⟩ 16 104 _ (bitsOf fout) _
    (by ival_tac) (by rw [hfb]; omega) (slice_bitsOf' fout 2 13 16 104 rfl rfl)) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 15⟩ ⟨n + 12⟩ 104 120 _ (bitsOf fout) _
    (by ival_tac) (by rw [hfb]; omega) (slice_bitsOf' fout 13 15 104 120 rfl rfl)) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 16⟩ ⟨n + 12⟩ 120 (120 + 8 * (cap - 21)) _
    (bitsOf fout) _ (by ival_tac) (by rw [hfb]; omega)
    (slice_bitsOf' fout 15 (15 + (cap - 21)) _ _ rfl (by omega))) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E me adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_openThen E me adv _ _ _ σ _ vD _ [] (by ival_tac) ?_
  exact silent_prefix E me adv _ (Silent.seq rfl (Silent.done _)) _ _ _ _

/-- **T3 for the open, A honest** (any adversary B): for the 16 bytes `hb` the adversary input as its
half, the adversary's view of `openScript` is a prefix of TWO releases: `recordKindBit`, the typed
kernel's bit, which is 0 or 255; and `recordEvent`, EXACTLY the first two bytes of the single class
kernel's output (`classSpec`) on the parser state, the record, the keys and the tag check's output
on A's half and `hb`, whichever branch ran. -/
theorem open_disclosure_A (E : Env) (adv : Adversary) (cap : Nat)
    (hcE : E.circuits checkName = some (circuitOf HybridKernel.gcmCheck))
    (htE : E.circuits (typedName cap) = some (circuitOf (tlsOpenTyped cap)))
    (hfE : E.circuits (frameName cap) = some (circuitOf (tlsFrame cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser traffic : BoolH) (hpn : parser.id < n) (htn : traffic.id < n)
    (P K seqB tag recordPadded size : B8) (hP : P.length = 11) (hK : K.length = 60) (hs : seqB.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2) (halfSlot : Nat)
    (σ : Store) (I : Ideal) (vD : List Release) (hIp : I.bools parser.id = some (bitsOf P))
    (hIt : I.bools traffic.id = some (bitsOf K)) (xa : W) (hA : σ.bits halfSlot = bitsOfW xa) :
    ∃ hb : B8, (hb.length = 16 ∧
      ((kernelOut (tlsOpenTyped cap) (typedInput P K seqB recordPadded size (kernelOut HybridKernel.gcmCheck
        (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag))))))).take 1 = [0] ∨
       (kernelOut (tlsOpenTyped cap) (typedInput P K seqB recordPadded size (kernelOut HybridKernel.gcmCheck
        (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag))))))).take 1 = [255])) ∧
      (withAdv E .a adv (openScript n parser traffic seqB tag recordPadded size cap halfSlot) σ I vD).viewD <+:
        [⟨Label.recordKindBit, .bits (bitsOf ((kernelOut (tlsOpenTyped cap) (typedInput P K seqB recordPadded size
            (kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag))))))).take 1))⟩,
         ⟨Label.recordEvent, .bits (bitsOf ((classSpec cap (assignOf (typedInput P K seqB recordPadded size
            (kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag)))))))).take 2))⟩] := by
  unfold openScript checkBlock typedBlock
  simp only [List.cons_append, List.nil_append, seqs_cons, seqs_nil]
  refine viewD_local1_ex E .a adv _ rfl _ σ I _ vD (localStep_public E ⟨n⟩ (bitsOf seqB) I) _ _ ?_
  rcases Ghash.viewD_both E adv ⟨n + 1⟩ ⟨n + 2⟩ 128 true false halfSlot _ σ _ vD (by rw [hA, length_bitsOfW])
    with h1 | ⟨pb, hpb, h1⟩
  · exact ⟨List.replicate 16 0, ⟨by simp, typedOut_bit_cases cap _⟩, by rw [h1]; exact List.nil_prefix⟩
  obtain ⟨hbl, hbb⟩ := bytesOf_128 pb hpb
  refine ⟨bytesOf pb, ⟨hbl, typedOut_bit_cases cap _⟩, ?_⟩
  rw [h1, hA]
  have hcl := checkOut_length (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (bytesOf pb ++ tag))))
  have hcw : 8 * (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (bytesOf pb ++ tag)))).length =
      (circuitOf HybridKernel.gcmCheck).inWidth := by
    rw [check_inWidth]
    simp only [List.length_append, hK, hs, htag, Local.Ghash.toBytes_length, hbl]
  generalize hacc : kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (bytesOf pb ++ tag)))) =
    acc at hcl ⊢
  have bP := (open_binding cap P K seqB recordPadded size acc hP hK hs hr hz hcl).1
  have htw : 8 * (typedInput P K seqB recordPadded size acc).length = (circuitOf (tlsOpenTyped cap)).inWidth := by
    rw [typed_inWidth, typedInput_length, hP, hK, hs, hr, hz, hcl]
    omega
  have hev := open_event_class cap hcap (typedInput P K seqB recordPadded size acc) P hP bP
  have htl := typedOut_length cap hcap (typedInput P K seqB recordPadded size acc)
  have hbits := typedOut_bit_cases cap (typedInput P K seqB recordPadded size acc)
  generalize hto : kernelOut (tlsOpenTyped cap) (typedInput P K seqB recordPadded size acc) = tout at htl hev hbits ⊢
  have hob : (bitsOf tout).length = 8 * (16 + (cap - 21) + (cap - 17)) := by rw [length_bitsOf, htl]
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_public E ⟨n + 3⟩ (bitsOf tag) _) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_concat5 E ⟨n + 4⟩ traffic ⟨n⟩ ⟨n + 1⟩ ⟨n + 2⟩ ⟨n + 3⟩ _
    (bitsOf K) (bitsOf seqB) (bitsOfW xa) pb (bitsOf tag)
    (bitsOf (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (bytesOf pb ++ tag)))))
    (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac)
    (by simp only [bitsOf_append, hbb, bitsOfW])) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_runK E ⟨n + 5⟩ _ ⟨n + 4⟩ _ _ _ _ hcE (by ival_tac)
    hcw hacc) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_public E ⟨n + 6⟩ (bitsOf recordPadded ++ bitsOf size) _) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_concat5 E ⟨n + 7⟩ parser traffic ⟨n⟩ ⟨n + 6⟩ ⟨n + 5⟩ _
    (bitsOf P) (bitsOf K) (bitsOf seqB) (bitsOf recordPadded ++ bitsOf size) (bitsOf acc)
    (bitsOf (typedInput P K seqB recordPadded size acc))
    (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) (by simp [typedInput])) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_runK E ⟨n + 8⟩ _ ⟨n + 7⟩ _ _ _ _ htE (by ival_tac)
    htw hto) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_slice E ⟨n + 9⟩ ⟨n + 8⟩ 0 8 _ (bitsOf tout)
    (bitsOf (tout.take 1)) (by ival_tac) (by rw [hob]; omega)
    (by rw [slice_bitsOf' tout 0 1 0 8 rfl rfl]; simp)) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_local1 E .a adv _ rfl _ σ _ _ vD _ (localStep_free E _ _) ?_
  refine viewD_openThen E .a adv _ _ _ σ _ vD _ _ (by ival_tac) ?_
  rcases hbits with h0 | h255
  · rw [h0]
    unfold afterBit
    rw [if_pos rfl, ← hev.1 h0]
    exact viewD_direct E .a adv n cap tout htl σ _ _ (by ival_tac)
  · rw [h255]
    unfold afterBit
    rw [if_neg (by decide), if_pos rfl, ← hev.2 h255]
    exact viewD_frame E .a adv cap hfE n hcap parser hpn P tout hP htl σ _ _ (by ival_tac) (by ival_tac)

/-- **A refused record releases constants**: when the tag check's output bound to the typed kernel is
0, the bit is 0 and the class kernel's event is `[0, 0]`, whatever the record, the keys and the
parser state (`rejected_parse`, `frame_unauthenticated`). With `open_disclosure_A`: the adversary's
view of a refused open is a prefix of `[bit 0, event [0, 0]]`. -/
theorem rejected_values (cap : Nat) (P K seqB recordPadded size : B8) (hP : P.length = 11) (hK : K.length = 60)
    (hs : seqB.length = 8) (hr : recordPadded.length = cap) (hz : size.length = 2) :
    (kernelOut (tlsOpenTyped cap) (typedInput P K seqB recordPadded size [0])).take 1 = [0] ∧
    (classSpec cap (assignOf (typedInput P K seqB recordPadded size [0]))).take 2 = [0, 0] := by
  have hacc := (open_binding cap P K seqB recordPadded size [0] hP hK hs hr hz rfl).2.2.2.2.2
  generalize hAdef : assignOf (typedInput P K seqB recordPadded size [0]) = A at hacc
  have l6 : lookup (typedInputs cap) "accepted" = ByteCircuit.inputBytes (79 + cap + 2) 1 := by
    simp [lookup, lookupFrom, typedInputs, HybridKernel.Shape.variables]
    all_goals omega
  have h0 : BVExpr.eval A (HybridService.at' (lookup (typedInputs cap) "accepted") 0) = 0 := by
    rw [l6] at hacc ⊢
    simp only [ByteCircuit.inputBytes, List.range_one, List.map_cons, List.map_nil, List.cons.injEq,
      and_true] at hacc
    simp only [ByteCircuit.inputBytes, List.range_one, List.map_cons, List.map_nil, HybridService.at',
      List.getD_cons_zero]
    exact hacc
  have hzero : ∃ k, (typedParsed cap).map (BVExpr.eval A) = List.replicate k 0 := by
    simp only [typedParsed, RecordClass.openParsed_refines, h0]
    exact ⟨_, TypedOpen.rejected_parse _ _ _ _ _⟩
  obtain ⟨k, hk⟩ := hzero
  refine ⟨?_, ?_⟩
  · rw [typedOut_bit, hAdef, TypedOpen.handshakeBit_map (ByteAuth.evaluationHom A), hk, TypedOpen.handshakeBit_zeros]
  · rw [classSpec, hk]
    exact TypedOpen.frame_unauthenticated _ _

theorem open_disclosure_rejected (E : Env) (adv : Adversary) (cap : Nat)
    (hcE : E.circuits checkName = some (circuitOf HybridKernel.gcmCheck))
    (htE : E.circuits (typedName cap) = some (circuitOf (tlsOpenTyped cap)))
    (hfE : E.circuits (frameName cap) = some (circuitOf (tlsFrame cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser traffic : BoolH) (hpn : parser.id < n) (htn : traffic.id < n)
    (P K seqB tag recordPadded size : B8) (hP : P.length = 11) (hK : K.length = 60) (hs : seqB.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2) (halfSlot : Nat)
    (σ : Store) (I : Ideal) (vD : List Release) (hIp : I.bools parser.id = some (bitsOf P))
    (hIt : I.bools traffic.id = some (bitsOf K)) (xa : W) (hA : σ.bits halfSlot = bitsOfW xa) :
    ∃ hb : B8, hb.length = 16 ∧
      ((kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag))))) = [0] →
      (withAdv E .a adv (openScript n parser traffic seqB tag recordPadded size cap halfSlot) σ I vD).viewD <+:
        [⟨Label.recordKindBit, .bits (bitsOf [0])⟩, ⟨Label.recordEvent, .bits (bitsOf [0, 0])⟩]) := by
  obtain ⟨hb, ⟨hl, -⟩, hv⟩ := open_disclosure_A E adv cap hcE htE hfE n hcap parser traffic hpn htn P K seqB tag
    recordPadded size hP hK hs htag hr hz halfSlot σ I vD hIp hIt xa hA
  refine ⟨hb, hl, fun hacc => ?_⟩
  rw [hacc] at hv
  obtain ⟨r1, r2⟩ := rejected_values cap P K seqB recordPadded size hP hK hs hr hz
  rw [r1, r2] at hv
  exact hv

end TlsMpc.Node.Flows.Tls
