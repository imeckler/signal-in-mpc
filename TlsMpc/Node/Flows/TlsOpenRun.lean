import TlsMpc.Node.Flows.TlsRun

/-!
# T4-TLS through `jointRun`: the open (gap F13, part (b))

REORGANIZATION_PLAN.md stage S12. `openScript` run by two honest parties in the ideal model, the
kernels' circuits computing their Lean definitions (T2's trust, as for the seal).

  * The output lengths of the two parser kernels (`finish_length`, `direct_length`, `core_length`,
    `parsed_length`): the parse is `CAP − 17` bytes, the parser's output `11 +` the parse; so
    `tls-open-typed CAP` outputs `16 + (CAP − 21) + (CAP − 17)` bytes and `tls-frame CAP`
    `15 + (CAP − 21)`, the layouts `openScript` cuts (and `typedMarks` / `frameMarks` of the WF
    statement).
  * **The binding the vectors only tested** (`open_binding`): the byte `openScript` puts in
    `tls-open-typed`'s `accepted` input IS `gcm-check`'s output on the traffic block, the sequence,
    the two parties' halves and the received tag (the concat order of the script, read through the
    kernel's input layout `typedInputs`). With honest halves of shared key powers it is 255 exactly
    when the received tag is GCM's tag (`check_accepts`), else 0 (`open_binding_honest`).
  * `parser_honest`: `parserScript` returns a handle holding 11 zero bytes.
  * `open_prefix`, `open_direct`, `open_frame`: the joint run up to the bit (tag check, typed kernel),
    then (bit 0) the typed kernel's event opened and its parser state, length and content kept, or
    (bit 255) `tls-frame`'s on the same parser state and the typed kernel's private parse; the bit is
    0 or 255 (`typedOut_bit_cases`), so the abort branch is never taken.
  * **`open_class` (T4-TLS for the open, through `jointRun`)**: whichever bit, the event both
    parties receive and the values behind the three handles they keep are EXACTLY the four fields of
    the single class kernel `tls-open-application-class CAP` on the same inputs
    (`fields (classSpec …)`: the post-handshake parser on the record's parse), by
    `typed_pair_refines` / `class_fields` (the function-level `open_event_refines`).
  * `open_rejected_run`: with honest halves and a tag that is not GCM's tag (a forged or corrupted
    record), the run returns the event `[0, 0]` (`tlsOpenTyped_gated` through the binding).

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

/-! ## Output lengths of the parser kernels -/

theorem finish_length {B W : Type} (o : Signal.Word64.Ops B W) (a : ByteAuth.Ops B)
    (s : TlsPostHandshake.State B W) (parsed : List B) (after : TlsPostHandshake.Scan B W)
    (hp : 4 ≤ parsed.length) :
    (TlsPostHandshake.finish o a s parsed after).length = 11 + parsed.length := by
  simp only [TlsPostHandshake.finish, TlsPostHandshake.encodeState, ByteAuth.release, List.length_append,
    List.length_cons, List.length_nil, List.length_map, List.length_take, List.length_drop,
    Signal.Word64.bytes_length]
  omega

theorem direct_length {B W : Type} (o : Signal.Word64.Ops B W) (a : ByteAuth.Ops B) (st p : List B)
    (hp : 4 ≤ p.length) : (TypedOpen.direct o a st p).length = 11 + p.length := by
  have hf := finish_length o a (TlsPostHandshake.decodeState o a st) p
    ⟨TlsPostHandshake.decodeState o a st, a.const 0, a.const 0⟩ hp
  simp only [TypedOpen.direct, ByteAuth.release, List.length_append, List.length_map, List.length_take,
    List.length_drop, hf]
  omega

theorem core_length {B W : Type} (o : Signal.Word64.Ops B W) (a : ByteAuth.Ops B) (st p : List B)
    (hp : 4 ≤ p.length) : (TlsPostHandshake.core o a st p).length = 11 + p.length := by
  simp only [TlsPostHandshake.core, TlsPostHandshake.process]
  exact finish_length _ _ _ _ _ hp

theorem inputBytes_eval_length (A : BVExpr.Assignment) (s c : Nat) :
    ((ByteCircuit.inputBytes s c).map (BVExpr.eval A)).length = c := by
  simp [ByteCircuit.inputBytes]

/-- **The parse is `CAP − 17` bytes** (under every assignment of `tls-open-typed`'s inputs). -/
theorem parsed_length (cap : Nat) (hcap : 21 ≤ cap) (A : BVExpr.Assignment) :
    ((typedParsed cap).map (BVExpr.eval A)).length = cap - 17 := by
  have hblock : lookup (typedInputs cap) "serverApplication" = ByteCircuit.inputBytes 11 60 := by
    simp [lookup, lookupFrom, typedInputs, HybridKernel.Shape.variables]
  have hrec : lookup (typedInputs cap) "record" = ByteCircuit.inputBytes 79 cap := by
    simp [lookup, lookupFrom, typedInputs, HybridKernel.Shape.variables]
  have he : ((HybridKernel.gcmExpanded (lookup (typedInputs cap) "serverApplication")).map (BVExpr.eval A)).length =
      176 := by
    rw [HybridKernel.gcmExpanded_eval, HybridKernel.expandedOf_length]
    rw [hblock, inputBytes_eval_length]
  have hw : ((lookup (typedInputs cap) "record").map (BVExpr.eval A)).length = cap := by
    rw [hrec, inputBytes_eval_length]
  simp only [typedParsed, RecordClass.openParsed_refines]
  generalize (HybridKernel.gcmExpanded (lookup (typedInputs cap) "serverApplication")).map (BVExpr.eval A) = ex at he
  generalize (lookup (typedInputs cap) "record").map (BVExpr.eval A) = w at hw
  have hm := TlsWebSocketActivity.activity_length ByteAuth.concrete
  have hc := TlsReceive.ciphertext_length w
  simp only [RecordClass.openParsed, RecordClass.openPlaintext, RecordClass.within, TlsReceive.releaseOpened,
    ByteAuth.release, List.length_map, TlsInnerParallel.decode_length]
  rw [TypedOpen.maskBytes_length _ _ _ (by rw [hm, Gcm.ctr_length _ _ _ _ he]), Gcm.ctr_length _ _ _ _ he, hc, hw]
  omega

/-- The parser's output on the evaluated inputs (`classSpec`) is `11 +` the parse. -/
theorem classSpec_length (cap : Nat) (hcap : 21 ≤ cap) (A : BVExpr.Assignment) :
    (classSpec cap A).length = 11 + (cap - 17) := by
  unfold classSpec
  rw [core_length _ _ _ _ (by rw [parsed_length cap hcap]; omega), parsed_length cap hcap]

/-- **`tls-open-typed CAP`'s output is `16 + (CAP − 21) + (CAP − 17)` bytes.** -/
theorem typedOut_length (cap : Nat) (hcap : 21 ≤ cap) (x : B8) :
    (kernelOut (tlsOpenTyped cap) x).length = 16 + (cap - 21) + (cap - 17) := by
  have h1 := parsed_length cap hcap (assignOf x)
  have h2 : ((TypedOpen.direct Signal.Word64.symbolicMux ByteAuth.symbolic (lookup (typedInputs cap) "parser")
      (typedParsed cap)).map (BVExpr.eval (assignOf x))).length = 11 + (cap - 17) := by
    rw [TypedOpen.direct_refines, direct_length _ _ _ _ (by rw [h1]; omega), h1]
  rw [List.length_map] at h1 h2
  simp only [kernelOut, tlsOpenTyped, HybridKernel.pub, HybridKernel.priv, HybridKernel.sl, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append, List.length_map,
    List.length_take, List.length_drop, List.length_cons, List.length_nil, h1, h2]
  omega

/-- The four parser fields, concatenated, are the parser's output (when it has at least 15 bytes). -/
theorem flatten_fields (C : B8) (h : 15 ≤ C.length) : (fields C).flatten = C := by
  simp only [fields, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_zero]
  apply List.ext_getElem
  · simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    simp only [List.length_append, List.length_take, List.length_drop] at h1
    by_cases a : i < 2
    · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
    · rw [List.getElem_append_right (by simp; omega)]
      by_cases b : i - 2 < 11
      · rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem_drop]
        congr 1
        simp only [List.length_take]
        omega
      · rw [List.getElem_append_right (by simp; omega)]
        by_cases d : i - 2 - 11 < 2
        · rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem_drop]
          congr 1
          simp only [List.length_take, List.length_drop]
          omega
        · rw [List.getElem_append_right (by simp; omega), List.getElem_drop]
          congr 1
          simp only [List.length_take, List.length_drop]
          omega

/-- **`tls-frame CAP`'s output is the parser's output on its inputs** (`15 + (CAP − 21)` bytes). -/
theorem frameOut_eq (cap : Nat) (hcap : 21 ≤ cap) (y : B8) :
    kernelOut (tlsFrame cap) y = TlsPostHandshake.core Signal.Word64.concrete ByteAuth.concrete
      ((lookup (frameInputs cap) "parser").map (BVExpr.eval (assignOf y)))
      ((lookup (frameInputs cap) "parsed").map (BVExpr.eval (assignOf y))) := by
  have hp : lookup (frameInputs cap) "parsed" = ByteCircuit.inputBytes 11 (cap - 17) := by
    simp [lookup, lookupFrom, frameInputs, HybridKernel.Shape.variables]
  have hl : ((lookup (frameInputs cap) "parsed").map (BVExpr.eval (assignOf y))).length = cap - 17 := by
    rw [hp, inputBytes_eval_length]
  show (fieldValues (tlsFrame cap) (assignOf y)).flatten = _
  rw [frame_fields, flatten_fields _ (by rw [core_length _ _ _ _ (by omega), hl]; omega)]

theorem frameOut_length (cap : Nat) (hcap : 21 ≤ cap) (y : B8) :
    (kernelOut (tlsFrame cap) y).length = 15 + (cap - 21) := by
  have hp : lookup (frameInputs cap) "parsed" = ByteCircuit.inputBytes 11 (cap - 17) := by
    simp [lookup, lookupFrom, frameInputs, HybridKernel.Shape.variables]
  have hl : ((lookup (frameInputs cap) "parsed").map (BVExpr.eval (assignOf y))).length = cap - 17 := by
    rw [hp, inputBytes_eval_length]
  rw [frameOut_eq cap hcap, core_length _ _ _ _ (by omega), hl]
  omega

/-! ## The binding of the tag check to the typed open -/

/-- The bytes `openScript` feeds `gcm-check`: traffic ‖ sequence ‖ A's half ‖ B's half ‖ tag. -/
def checkInput (K seqB : B8) (xa xb : W) (tag : B8) : B8 :=
  K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (Local.Ghash.toBytes xb ++ tag)))

/-- The bytes `openScript` feeds `tls-open-typed CAP`: parser ‖ traffic ‖ sequence ‖ record ‖ length
field ‖ the check's output. -/
def typedInput (P K seqB recordPadded size acc : B8) : B8 :=
  P ++ (K ++ (seqB ++ (recordPadded ++ (size ++ acc))))

theorem typedInput_length (P K seqB recordPadded size acc : B8) :
    (typedInput P K seqB recordPadded size acc).length =
      P.length + K.length + seqB.length + recordPadded.length + size.length + acc.length := by
  simp only [typedInput, List.length_append]
  omega

theorem checkOut_length (x : B8) : (kernelOut HybridKernel.gcmCheck x).length = 1 := by
  obtain ⟨o, ho⟩ : ∃ o, HybridKernel.gcmCheck.outputs = [o] := ⟨_, rfl⟩
  have hk := TlsMpc.Node.Flows.Ghash.outputs_one _ o ho x
  rw [HybridKernel.gcmCheck_spec] at hk
  simp only [List.cons.injEq, and_true] at hk
  rw [← hk]
  rfl

/-- **The binding** (what the stand-in vectors only tested): under the assignment of the bytes
`openScript` concatenates for `tls-open-typed CAP`, the kernel's inputs `parser`, `serverApplication`,
`sequence`, `record`, `size` and `accepted` read exactly the parser state, the traffic block, the
sequence, the padded record, its length field and `gcm-check`'s output. -/
theorem open_binding (cap : Nat) (P K seqB recordPadded size acc : B8) (hP : P.length = 11) (hK : K.length = 60)
    (hs : seqB.length = 8) (hr : recordPadded.length = cap) (hz : size.length = 2) (ha : acc.length = 1) :
    let A := assignOf (typedInput P K seqB recordPadded size acc)
    (lookup (typedInputs cap) "parser").map (BVExpr.eval A) = P ∧
    (lookup (typedInputs cap) "serverApplication").map (BVExpr.eval A) = K ∧
    (lookup (typedInputs cap) "sequence").map (BVExpr.eval A) = seqB ∧
    (lookup (typedInputs cap) "record").map (BVExpr.eval A) = recordPadded ∧
    (lookup (typedInputs cap) "size").map (BVExpr.eval A) = size ∧
    (lookup (typedInputs cap) "accepted").map (BVExpr.eval A) = acc := by
  intro A
  have hl := typedInput_length P K seqB recordPadded size acc
  have l1 : lookup (typedInputs cap) "parser" = ByteCircuit.inputBytes 0 11 := by
    simp [lookup, lookupFrom, typedInputs]
  have l2 : lookup (typedInputs cap) "serverApplication" = ByteCircuit.inputBytes 11 60 := by
    simp [lookup, lookupFrom, typedInputs, HybridKernel.Shape.variables]
  have l3 : lookup (typedInputs cap) "sequence" = ByteCircuit.inputBytes 71 8 := by
    simp [lookup, lookupFrom, typedInputs, HybridKernel.Shape.variables]
  have l4 : lookup (typedInputs cap) "record" = ByteCircuit.inputBytes 79 cap := by
    simp [lookup, lookupFrom, typedInputs, HybridKernel.Shape.variables]
  have l5 : lookup (typedInputs cap) "size" = ByteCircuit.inputBytes (79 + cap) 2 := by
    simp [lookup, lookupFrom, typedInputs, HybridKernel.Shape.variables]
  have l6 : lookup (typedInputs cap) "accepted" = ByteCircuit.inputBytes (79 + cap + 2) 1 := by
    simp [lookup, lookupFrom, typedInputs, HybridKernel.Shape.variables]
    all_goals omega
  rw [l1, l2, l3, l4, l5, l6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [show ∀ s c, (ByteCircuit.inputBytes s c).map (BVExpr.eval A) = inputValue A s c from fun _ _ => rfl,
      iv _ _ _ (by omega)])
  · have := TlsMpc.Node.Flows.Ghash.drop_take_mid [] P (K ++ (seqB ++ (recordPadded ++ (size ++ acc)))) 0 rfl
    rw [hP] at this
    simpa [typedInput] using this
  · have := TlsMpc.Node.Flows.Ghash.drop_take_mid P K (seqB ++ (recordPadded ++ (size ++ acc))) 11 hP
    rw [hK] at this
    simpa [typedInput] using this
  · have := TlsMpc.Node.Flows.Ghash.drop_take_mid (P ++ K) seqB (recordPadded ++ (size ++ acc)) 71
      (by simp; omega)
    rw [hs] at this
    simpa [typedInput, List.append_assoc] using this
  · have := TlsMpc.Node.Flows.Ghash.drop_take_mid (P ++ K ++ seqB) recordPadded (size ++ acc) 79
      (by simp; omega)
    rw [hr] at this
    simpa [typedInput, List.append_assoc] using this
  · have := TlsMpc.Node.Flows.Ghash.drop_take_mid (P ++ K ++ seqB ++ recordPadded) size acc (79 + cap)
      (by simp; omega)
    rw [hz] at this
    simpa [typedInput, List.append_assoc] using this
  · have := TlsMpc.Node.Flows.Ghash.drop_take_mid (P ++ K ++ seqB ++ recordPadded ++ size) acc [] (79 + cap + 2)
      (by simp; omega)
    rw [ha] at this
    simpa [typedInput, List.append_assoc] using this

/-- **The binding with honest halves**: the byte in `tls-open-typed`'s `accepted` input is 255 exactly
when the received tag is GCM's tag of the received header and ciphertext under the server key, and 0
otherwise (`check_accepts`, P-GHASH (c)). -/
theorem open_binding_honest (cap : Nat) (P K seqB recordPadded size hdr ct tag : B8) (hP : P.length = 11)
    (hK : K.length = 60) (hs : seqB.length = 8) (hr : recordPadded.length = cap) (hz : size.length = 2)
    (ht : tag.length = 16) (a b : List W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow) :
    (lookup (typedInputs cap) "accepted").map (BVExpr.eval (assignOf (typedInput P K seqB recordPadded size
      (kernelOut HybridKernel.gcmCheck (checkInput K seqB (Local.Ghash.half a hdr ct) (Local.Ghash.half b hdr ct) tag))))) =
      [if Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB) = tag
        then 255 else 0] := by
  rw [(open_binding cap P K seqB recordPadded size _ hP hK hs hr hz (checkOut_length _)).2.2.2.2.2]
  exact check_accepts K seqB hdr ct tag hK hs ht a b nPow hsh hn

/-! ## Building a returning joint run, step by step, with a property of the final state -/

section Ex

variable (E : Env) {α β : Type}

theorem ex_local (i : Instr) (hi : isLocal i = true) (tA : Script α) (tB : Script β) (σA σB : Store)
    (I I1 : Ideal) (a : α) (b : β) (sA sB : Store) (Q : Ideal → Prop) (h : localStep E i I = some I1)
    (hk : ∃ J, JRet (jointRun E tA tB σA σB I1) a b J sA sB ∧ Q J) :
    ∃ J, JRet (jointRun E (seq i tA) (seq i tB) σA σB I) a b J sA sB ∧ Q J := by
  obtain ⟨J, hJ, hQ⟩ := hk
  exact ⟨J, jret_locals E tA tB σA σB a b J sA sB [i] (by simp [hi]) I I1
    (by rw [runLocal_step E _ _ _ _ h, runLocal_nil]) hJ, hQ⟩

theorem ex_openThen (h : BoolH) (l : Label) (kA : Bits → Script α) (kB : Bits → Script β) (σA σB : Store)
    (I : Ideal) (v : Bits) (a : α) (b : β) (sA sB : Store) (Q : Ideal → Prop) (hv : I.bools h.id = some v)
    (hk : ∃ J, JRet (jointRun E (kA v) (kB v) σA σB I) a b J sA sB ∧ Q J) :
    ∃ J, JRet (jointRun E (openThen h l kA) (openThen h l kB) σA σB I) a b J sA sB ∧ Q J := by
  obtain ⟨J, hJ, hQ⟩ := hk
  exact ⟨J, jret_openThen E h l kA kB σA σB I v a b J sA sB hv hJ, hQ⟩

theorem ex_done (a : α) (b : β) (σA σB : Store) (I : Ideal) (Q : Ideal → Prop) (hQ : Q I) :
    ∃ J, JRet (jointRun E (.done a) (.done b) σA σB I) a b J σA σB ∧ Q J :=
  ⟨I, jret_done E a b σA σB I, hQ⟩

theorem ex_both (oa ob : BoolH) (w : Nat) (once rev : Bool) (slotA slotB : Nat) (tA : Script α) (tB : Script β)
    (σA σB : Store) (I : Ideal) (a : α) (b : β) (sA sB : Store) (Q : Ideal → Prop)
    (hlA : (σA.bits slotA).length = w) (hlB : (σB.bits slotB).length = w)
    (hk : ∃ J, JRet (jointRun E tA tB σA σB ((I.setBool oa (σA.bits slotA)).setBool ob (σB.bits slotB))) a b J sA sB ∧
      Q J) :
    ∃ J, JRet (jointRun E (seq (.boolInputBoth oa ob w once rev slotA) tA) (seq (.boolInputBoth oa ob w once rev slotB) tB)
      σA σB I) a b J sA sB ∧ Q J := by
  obtain ⟨J, hJ, hQ⟩ := hk
  refine ⟨J, jret_boolInputBoth E oa ob w once rev slotA slotB tA tB σA σB I a b J sA sB hlA hlB ?_, hQ⟩
  rw [bothBools_a]
  exact hJ

end Ex

theorem localStep_concat2 (E : Env) (out a b : BoolH) (I : Ideal) (x y w : Bits)
    (ha : I.bools a.id = some x) (hb : I.bools b.id = some y) (hw : x ++ y = w) :
    localStep E (.concat out [a, b]) I = some (I.setBool out w) := by
  rw [localStep_concat E out [a, b] I [x, y] (by simp [List.mapM_cons, ha, hb])]
  simp [hw]

theorem localStep_runK (E : Env) (out : BoolH) (name : Bytes) (input : BoolH) (I : Ideal)
    (K : HybridKernel.Kernel) (x y : B8) (hc : E.circuits name = some (circuitOf K))
    (hv : I.bools input.id = some (bitsOf x)) (hw : 8 * x.length = (circuitOf K).inWidth) (ho : kernelOut K x = y) :
    localStep E (.run out name 1 input) I = some (I.setBool out (bitsOf y)) := by
  rw [localStep_run E out name 1 input I _ _ hc hv (by rw [length_bitsOf, Nat.one_mul]; exact hw),
    runCopies_circuitOf _ _ hw, ho]

theorem slice_bitsOf' (l : B8) (a b lo hi : Nat) (h1 : lo = 8 * a) (h2 : hi = 8 * b) :
    ((bitsOf l).drop lo).take (hi - lo) = bitsOf ((l.drop a).take (b - a)) := by
  subst h1 h2
  exact slice_bitsOf l a b

theorem check_inWidth : (circuitOf HybridKernel.gcmCheck).inWidth = 8 * 116 := by
  simp [circuitOf, kernelCircuit, kernelInBytes, HybridKernel.gcmCheck, HybridKernel.Shape.variables]

theorem typed_inWidth (cap : Nat) : (circuitOf (tlsOpenTyped cap)).inWidth = 8 * (82 + cap) := by
  simp [circuitOf, kernelCircuit, kernelInBytes, tlsOpenTyped, typedInputs, HybridKernel.Shape.variables]
  omega

theorem frame_inWidth (cap : Nat) : (circuitOf (tlsFrame cap)).inWidth = 8 * (11 + (cap - 17)) := by
  simp [circuitOf, kernelCircuit, kernelInBytes, tlsFrame, frameInputs, HybridKernel.Shape.variables]

/-- The typed kernel's output on the bytes `openScript` feeds it. -/
def openOut (cap : Nat) (P K seqB tag recordPadded size : B8) (xa xb : W) : B8 :=
  kernelOut (tlsOpenTyped cap) (typedInput P K seqB recordPadded size
    (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))

/-- The private parse, as the typed kernel outputs it (its last field). -/
def parsedOf (cap : Nat) (tout : B8) : B8 := (tout.drop (16 + (cap - 21))).take (cap - 17)

/-! ## The two branches after the handshake bit -/

/-- Bit 0: the typed kernel's event, opened; its parser state, length and content kept. -/
theorem open_direct (E : Env) (n cap : Nat) (hcap : 21 ≤ cap) (tout : B8)
    (htl : tout.length = 16 + (cap - 21) + (cap - 17)) (σA σB : Store) (I : Ideal)
    (h8 : I.bools (n + 8) = some (bitsOf tout)) :
    ∃ J, JRet (jointRun E (directRest n cap) (directRest n cap) σA σB I)
        ⟨(tout.drop 1).take 2, ⟨n + 11⟩, ⟨n + 12⟩, ⟨n + 13⟩⟩ ⟨(tout.drop 1).take 2, ⟨n + 11⟩, ⟨n + 12⟩, ⟨n + 13⟩⟩
        J σA σB ∧
      J.bools (n + 11) = some (bitsOf ((tout.drop 3).take 11)) ∧
      J.bools (n + 12) = some (bitsOf ((tout.drop 14).take 2)) ∧
      J.bools (n + 13) = some (bitsOf ((tout.drop 16).take (cap - 21))) := by
  have hb : (bitsOf tout).length = 8 * (16 + (cap - 21) + (cap - 17)) := by rw [length_bitsOf, htl]
  unfold directRest
  simp only [seqs_cons, seqs_nil]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 10⟩ ⟨n + 8⟩ 8 24 I _ _ h8
    (by rw [hb]; omega) (slice_bitsOf' tout 1 3 8 24 rfl rfl)) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 11⟩ ⟨n + 8⟩ 24 112 _ (bitsOf tout) _
    (by ival_tac) (by rw [hb]; omega) (slice_bitsOf' tout 3 14 24 112 rfl rfl)) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 12⟩ ⟨n + 8⟩ 112 128 _ (bitsOf tout) _
    (by ival_tac) (by rw [hb]; omega) (slice_bitsOf' tout 14 16 112 128 rfl rfl)) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 13⟩ ⟨n + 8⟩ 128 (128 + 8 * (cap - 21)) _
    (bitsOf tout) _ (by ival_tac) (by rw [hb]; omega)
    (slice_bitsOf' tout 16 (16 + (cap - 21)) _ _ rfl (by omega))) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_openThen E _ _ _ _ σA σB _ (bitsOf ((tout.drop 1).take (3 - 1))) _ _ σA σB _ (by ival_tac) ?_
  simp only [bytesOf_bitsOf, show (3 : Nat) - 1 = 2 from rfl, show 16 + (cap - 21) - 16 = cap - 21 by omega]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_done E _ _ σA σB _ _ ⟨?_, ?_, ?_⟩ <;> ival_tac

/-- Bit 255: `tls-frame` on the old parser state and the typed kernel's private parse; its event
opened, its parser state, length and content kept. -/
theorem open_frame (E : Env) (hE : E.circuits (frameName cap) = some (circuitOf (tlsFrame cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser : BoolH) (hpn : parser.id < n) (P tout : B8) (hP : P.length = 11)
    (htl : tout.length = 16 + (cap - 21) + (cap - 17)) (σA σB : Store) (I : Ideal)
    (h8 : I.bools (n + 8) = some (bitsOf tout)) (hp : I.bools parser.id = some (bitsOf P)) :
    ∃ J, JRet (jointRun E (frameRest n parser cap) (frameRest n parser cap) σA σB I)
        ⟨(kernelOut (tlsFrame cap) (P ++ parsedOf cap tout)).take 2, ⟨n + 14⟩, ⟨n + 15⟩, ⟨n + 16⟩⟩
        ⟨(kernelOut (tlsFrame cap) (P ++ parsedOf cap tout)).take 2, ⟨n + 14⟩, ⟨n + 15⟩, ⟨n + 16⟩⟩ J σA σB ∧
      J.bools (n + 14) = some (bitsOf (((kernelOut (tlsFrame cap) (P ++ parsedOf cap tout)).drop 2).take 11)) ∧
      J.bools (n + 15) = some (bitsOf (((kernelOut (tlsFrame cap) (P ++ parsedOf cap tout)).drop 13).take 2)) ∧
      J.bools (n + 16) = some (bitsOf (((kernelOut (tlsFrame cap) (P ++ parsedOf cap tout)).drop 15).take (cap - 21))) := by
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
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 10⟩ ⟨n + 8⟩ (128 + 8 * (cap - 21))
    (128 + 8 * (cap - 21) + 8 * (cap - 17)) I _ (bitsOf (parsedOf cap tout)) h8 (by rw [hb]; omega)
    (by rw [slice_bitsOf' tout (16 + (cap - 21)) (16 + (cap - 21) + (cap - 17)) _ _ (by omega) (by omega),
          Nat.add_sub_cancel_left]; rfl)) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_concat2 E ⟨n + 11⟩ parser ⟨n + 10⟩ _ (bitsOf P)
    (bitsOf (parsedOf cap tout)) (bitsOf (P ++ parsedOf cap tout)) (by ival_tac) (by ival_tac)
    (by rw [bitsOf_append])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_runK E ⟨n + 12⟩ _ ⟨n + 11⟩ _ _ _ _ hE (by ival_tac)
    hw hfo) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 13⟩ ⟨n + 12⟩ 0 16 _ (bitsOf fout)
    (bitsOf (fout.take 2)) (by ival_tac) (by rw [hfb]; omega)
    (by rw [slice_bitsOf' fout 0 2 0 16 rfl rfl]; simp)) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 14⟩ ⟨n + 12⟩ 16 104 _ (bitsOf fout)
    (bitsOf ((fout.drop 2).take 11)) (by ival_tac) (by rw [hfb]; omega)
    (by rw [slice_bitsOf' fout 2 13 16 104 rfl rfl])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 15⟩ ⟨n + 12⟩ 104 120 _ (bitsOf fout)
    (bitsOf ((fout.drop 13).take 2)) (by ival_tac) (by rw [hfb]; omega)
    (by rw [slice_bitsOf' fout 13 15 104 120 rfl rfl])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 16⟩ ⟨n + 12⟩ 120 (120 + 8 * (cap - 21)) _
    (bitsOf fout) (bitsOf ((fout.drop 15).take (cap - 21))) (by ival_tac) (by rw [hfb]; omega)
    (by rw [slice_bitsOf' fout 15 (15 + (cap - 21)) _ _ rfl (by omega), Nat.add_sub_cancel_left])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_openThen E _ _ _ _ σA σB _ (bitsOf (fout.take 2)) _ _ σA σB _ (by ival_tac) ?_
  simp only [bytesOf_bitsOf]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_done E _ _ σA σB _ _ ⟨?_, ?_, ?_⟩ <;> ival_tac

/-! ## The common part: the tag check, the typed kernel, the bit -/

theorem localStep_concat5 (E : Env) (out a b c d e : BoolH) (I : Ideal) (va vb vc vd ve w : Bits)
    (ha : I.bools a.id = some va) (hb : I.bools b.id = some vb) (hc : I.bools c.id = some vc)
    (hd : I.bools d.id = some vd) (he : I.bools e.id = some ve) (hw : va ++ (vb ++ (vc ++ (vd ++ ve))) = w) :
    localStep E (.concat out [a, b, c, d, e]) I = some (I.setBool out w) := by
  rw [localStep_concat E out _ I [va, vb, vc, vd, ve] (by simp [List.mapM_cons, ha, hb, hc, hd, he])]
  simp [hw]

/-- Up to the handshake bit: both parties run the tag check on their halves and the typed kernel on
parser ‖ traffic ‖ sequence ‖ record ‖ length field ‖ the check's output, and open the bit; the rest
continues from a state holding the typed kernel's output and the parser state. -/
theorem open_prefix (E : Env) (cap : Nat)
    (hcE : E.circuits checkName = some (circuitOf HybridKernel.gcmCheck))
    (htE : E.circuits (typedName cap) = some (circuitOf (tlsOpenTyped cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser traffic : BoolH) (hpn : parser.id < n) (htn : traffic.id < n)
    (P K seqB tag recordPadded size : B8) (hP : P.length = 11) (hK : K.length = 60) (hs : seqB.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2) (halfSlot : Nat)
    (σA σB : Store) (I : Ideal) (hIp : I.bools parser.id = some (bitsOf P)) (hIt : I.bools traffic.id = some (bitsOf K))
    (xa xb : W) (hA : σA.bits halfSlot = bitsOfW xa) (hB : σB.bits halfSlot = bitsOfW xb) (o : Opened)
    (Q : Ideal → Prop)
    (hk : ∀ I' : Ideal, I'.bools (n + 8) = some (bitsOf (openOut cap P K seqB tag recordPadded size xa xb)) →
      I'.bools parser.id = some (bitsOf P) →
      ∃ J, JRet (jointRun E (afterBit n parser cap (bitsOf ((openOut cap P K seqB tag recordPadded size xa xb).take 1)))
        (afterBit n parser cap (bitsOf ((openOut cap P K seqB tag recordPadded size xa xb).take 1))) σA σB I') o o J
        σA σB ∧ Q J) :
    ∃ J, JRet (jointRun E (openScript n parser traffic seqB tag recordPadded size cap halfSlot)
      (openScript n parser traffic seqB tag recordPadded size cap halfSlot) σA σB I) o o J σA σB ∧ Q J := by
  have hcl := checkOut_length (checkInput K seqB xa xb tag)
  have hcw : 8 * (checkInput K seqB xa xb tag).length = (circuitOf HybridKernel.gcmCheck).inWidth := by
    rw [check_inWidth]
    simp only [checkInput, List.length_append, hK, hs, htag, Local.Ghash.toBytes_length]
  have htw : 8 * (typedInput P K seqB recordPadded size
      (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag))).length = (circuitOf (tlsOpenTyped cap)).inWidth := by
    rw [typed_inWidth, typedInput_length, hP, hK, hs, hr, hz, hcl]
    omega
  have hol := typedOut_length cap hcap (typedInput P K seqB recordPadded size
      (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))
  have hob : (bitsOf (openOut cap P K seqB tag recordPadded size xa xb)).length =
      8 * (16 + (cap - 21) + (cap - 17)) := by
    rw [length_bitsOf]
    unfold openOut
    rw [hol]
  revert hk
  generalize hacc : kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag) = acc at hcl htw hol
  generalize hout : openOut cap P K seqB tag recordPadded size xa xb = tout at hob
  have hto : kernelOut (tlsOpenTyped cap) (typedInput P K seqB recordPadded size acc) = tout := by
    rw [← hout, ← hacc]
    rfl
  intro hk
  unfold openScript checkBlock typedBlock
  simp only [List.cons_append, List.nil_append, seqs_cons, seqs_nil]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_public E ⟨n⟩ (bitsOf seqB) I) ?_
  refine ex_both E ⟨n + 1⟩ ⟨n + 2⟩ 128 true false halfSlot halfSlot _ _ σA σB _ _ _ σA σB _
    (by rw [hA, length_bitsOfW]) (by rw [hB, length_bitsOfW]) ?_
  rw [hA, hB]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_public E ⟨n + 3⟩ (bitsOf tag) _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_concat5 E ⟨n + 4⟩ traffic ⟨n⟩ ⟨n + 1⟩ ⟨n + 2⟩ ⟨n + 3⟩ _
    (bitsOf K) (bitsOf seqB) (bitsOfW xa) (bitsOfW xb) (bitsOf tag) (bitsOf (checkInput K seqB xa xb tag))
    (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac)
    (by simp [checkInput, bitsOfW])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_runK E ⟨n + 5⟩ _ ⟨n + 4⟩ _ _ _ _ hcE (by ival_tac)
    hcw hacc) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_public E ⟨n + 6⟩
    (bitsOf recordPadded ++ bitsOf size) _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_concat5 E ⟨n + 7⟩ parser traffic ⟨n⟩ ⟨n + 6⟩ ⟨n + 5⟩ _
    (bitsOf P) (bitsOf K) (bitsOf seqB) (bitsOf recordPadded ++ bitsOf size) (bitsOf acc)
    (bitsOf (typedInput P K seqB recordPadded size acc))
    (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac)
    (by simp [typedInput])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_runK E ⟨n + 8⟩ _ ⟨n + 7⟩ _ _ _ _ htE (by ival_tac)
    htw hto) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_slice E ⟨n + 9⟩ ⟨n + 8⟩ 0 8 _ (bitsOf tout)
    (bitsOf (tout.take 1)) (by ival_tac) (by rw [hob]; omega)
    (by rw [slice_bitsOf' tout 0 1 0 8 rfl rfl]; simp)) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  refine ex_openThen E _ _ _ _ σA σB _ (bitsOf (tout.take 1)) _ _ σA σB _ (by ival_tac) ?_
  exact hk _ (by ival_tac) (by ival_tac)

/-! ## The typed kernel's output, field by field -/

/-- The typed kernel's output: the bit, the four parser fields of `direct`, the parse. -/
theorem typedOut_eq (cap : Nat) (x : B8) :
    kernelOut (tlsOpenTyped cap) x =
      [BVExpr.eval (assignOf x) (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed cap))] ++
      ((((TypedOpen.direct Signal.Word64.symbolicMux ByteAuth.symbolic (lookup (typedInputs cap) "parser")
          (typedParsed cap)).map (BVExpr.eval (assignOf x))).take 2 ++
        ((((TypedOpen.direct Signal.Word64.symbolicMux ByteAuth.symbolic (lookup (typedInputs cap) "parser")
          (typedParsed cap)).map (BVExpr.eval (assignOf x))).drop 2).take 11 ++
        ((((TypedOpen.direct Signal.Word64.symbolicMux ByteAuth.symbolic (lookup (typedInputs cap) "parser")
          (typedParsed cap)).map (BVExpr.eval (assignOf x))).drop 13).take 2 ++
        ((TypedOpen.direct Signal.Word64.symbolicMux ByteAuth.symbolic (lookup (typedInputs cap) "parser")
          (typedParsed cap)).map (BVExpr.eval (assignOf x))).drop 15)))) ++
      (typedParsed cap).map (BVExpr.eval (assignOf x)) := by
  simp only [kernelOut, tlsOpenTyped, HybridKernel.pub, HybridKernel.priv, HybridKernel.sl, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.map_take, List.map_drop,
    List.drop_zero, List.singleton_append, List.cons_append, List.append_assoc]

theorem typedOut_bit (cap : Nat) (x : B8) :
    (kernelOut (tlsOpenTyped cap) x).take 1 =
      [BVExpr.eval (assignOf x) (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed cap))] := by
  rw [typedOut_eq]
  simp

/-- The last field of the typed kernel's output, as `frameRest` cuts it, is the private parse. -/
theorem typedOut_parsed (cap : Nat) (hcap : 21 ≤ cap) (x : B8) :
    parsedOf cap (kernelOut (tlsOpenTyped cap) x) = (typedParsed cap).map (BVExpr.eval (assignOf x)) := by
  have h1 := parsed_length cap hcap (assignOf x)
  have h2 : ((TypedOpen.direct Signal.Word64.symbolicMux ByteAuth.symbolic (lookup (typedInputs cap) "parser")
      (typedParsed cap)).map (BVExpr.eval (assignOf x))).length = 11 + (cap - 17) := by
    rw [TypedOpen.direct_refines, direct_length _ _ _ _ (by rw [h1]; omega), h1]
  rw [typedOut_eq, parsedOf]
  generalize (TypedOpen.direct Signal.Word64.symbolicMux ByteAuth.symbolic (lookup (typedInputs cap) "parser")
      (typedParsed cap)).map (BVExpr.eval (assignOf x)) = D at h2
  generalize (typedParsed cap).map (BVExpr.eval (assignOf x)) = pv at h1
  rw [List.drop_left' (by simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
    List.length_nil, h2]; omega), List.take_of_length_le (by omega)]

/-- The opened bit is 0 or 255 (`typed_pair_refines`). -/
theorem typedOut_bit_cases (cap : Nat) (x : B8) :
    (kernelOut (tlsOpenTyped cap) x).take 1 = [0] ∨ (kernelOut (tlsOpenTyped cap) x).take 1 = [255] := by
  rw [typedOut_bit]
  rcases (typed_pair_refines cap (assignOf x) (assignOf x)).1 with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

theorem take_drop_cons_append (x : BitVec 8) (C p : B8) (a b : Nat) (h : a + b ≤ C.length) :
    ((x :: (C ++ p)).drop (a + 1)).take b = (C.drop a).take b := by
  rw [List.drop_succ_cons, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

theorem fields_eq (C : B8) : fields C = [C.take 2, (C.drop 2).take 11, (C.drop 13).take 2, C.drop 15] := by
  simp [fields]

/-- **T4-TLS for the open, through `jointRun`** (gap F13 (b)). Two honest parties run `openScript` on
a received record (padded to its class `CAP ≥ 21`), the parser state `P` and the server traffic
block `K` behind their handles, each with its own half (A: `xa`, B: `xb`) in its store slot. The run
RETURNS to both the same opening `o`, and whichever handshake bit the typed kernel opened, the event
both receive and the values behind the three handles they keep (parser state, payload length,
payload content) are EXACTLY the four fields of the single class kernel `tls-open-application-class
CAP` on the same inputs (`classSpec`: the post-handshake parser on the record's parse), where the
inputs are bound as the script concatenates them: the typed kernel's `accepted` byte is `gcm-check`'s
output on the two halves (`open_binding`; with honest halves, 255 exactly when the tag is right:
`open_binding_honest`). -/
theorem open_class (E : Env) (cap : Nat)
    (hcE : E.circuits checkName = some (circuitOf HybridKernel.gcmCheck))
    (htE : E.circuits (typedName cap) = some (circuitOf (tlsOpenTyped cap)))
    (hfE : E.circuits (frameName cap) = some (circuitOf (tlsFrame cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser traffic : BoolH) (hpn : parser.id < n) (htn : traffic.id < n)
    (P K seqB tag recordPadded size : B8) (hP : P.length = 11) (hK : K.length = 60) (hs : seqB.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2) (halfSlot : Nat)
    (σA σB : Store) (I : Ideal) (hIp : I.bools parser.id = some (bitsOf P)) (hIt : I.bools traffic.id = some (bitsOf K))
    (xa xb : W) (hA : σA.bits halfSlot = bitsOfW xa) (hB : σB.bits halfSlot = bitsOfW xb) :
    ∃ o J, JRet (jointRun E (openScript n parser traffic seqB tag recordPadded size cap halfSlot)
        (openScript n parser traffic seqB tag recordPadded size cap halfSlot) σA σB I) o o J σA σB ∧
      ∃ vp vl vc, J.bools o.parser.id = some (bitsOf vp) ∧ J.bools o.length.id = some (bitsOf vl) ∧
        J.bools o.content.id = some (bitsOf vc) ∧
        [o.event, vp, vl, vc] = fields (classSpec cap (assignOf (typedInput P K seqB recordPadded size
          (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag))))) := by
  have hcl := checkOut_length (checkInput K seqB xa xb tag)
  obtain ⟨bP, -, -, -, -, -⟩ := open_binding cap P K seqB recordPadded size _ hP hK hs hr hz hcl
  have hCS := classSpec_length cap hcap (assignOf (typedInput P K seqB recordPadded size
    (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag))))
  have hpv := parsed_length cap hcap (assignOf (typedInput P K seqB recordPadded size
    (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag))))
  have htl := typedOut_length cap hcap (typedInput P K seqB recordPadded size
    (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))
  have hpo := typedOut_parsed cap hcap (typedInput P K seqB recordPadded size
    (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))
  have hbit := typedOut_bit (cap := cap) (typedInput P K seqB recordPadded size
    (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))
  have hfeq := frameOut_eq cap hcap (P ++ parsedOf cap (openOut cap P K seqB tag recordPadded size xa xb))
  have hty := fun h => (typed_pair_refines cap (assignOf (typedInput P K seqB recordPadded size
    (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))) (assignOf (P ++ parsedOf cap
      (openOut cap P K seqB tag recordPadded size xa xb)))).2.1 h
  rcases typedOut_bit_cases cap (typedInput P K seqB recordPadded size
      (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag))) with h0 | h255
  · -- bit 0: the typed kernel's own fields
    have hb0 : BVExpr.eval (assignOf (typedInput P K seqB recordPadded size
        (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag))))
        (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed cap)) = 0 := by
      rw [hbit] at h0
      simpa using h0
    have hfv := typed_fields cap _ hb0
    have hout : openOut cap P K seqB tag recordPadded size xa xb = [0] ++ (classSpec cap (assignOf (typedInput P K seqB
        recordPadded size (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))) ++
        (typedParsed cap).map (BVExpr.eval (assignOf (typedInput P K seqB recordPadded size
          (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))))) := by
      show (fieldValues (tlsOpenTyped cap) _).flatten = _
      rw [hfv]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append]
      rw [flatten_fields _ (by omega)]
      simp
    have h0' : (openOut cap P K seqB tag recordPadded size xa xb).take 1 = [0] := h0
    obtain ⟨J, hJ, h11, h12, h13⟩ := open_prefix E cap hcE htE n hcap parser traffic hpn htn P K seqB tag recordPadded
      size hP hK hs htag hr hz halfSlot σA σB I hIp hIt xa xb hA hB
      ⟨((openOut cap P K seqB tag recordPadded size xa xb).drop 1).take 2, ⟨n + 11⟩, ⟨n + 12⟩, ⟨n + 13⟩⟩
      (fun J => J.bools (n + 11) = some (bitsOf (((openOut cap P K seqB tag recordPadded size xa xb).drop 3).take 11)) ∧
        J.bools (n + 12) = some (bitsOf (((openOut cap P K seqB tag recordPadded size xa xb).drop 14).take 2)) ∧
        J.bools (n + 13) = some (bitsOf (((openOut cap P K seqB tag recordPadded size xa xb).drop 16).take (cap - 21))))
      (fun I' h8 _ => by
        rw [h0']
        unfold afterBit
        rw [if_pos rfl]
        exact open_direct E n cap hcap _ htl σA σB I' h8)
    refine ⟨_, J, hJ, _, _, _, h11, h12, h13, ?_⟩
    rw [hout, fields_eq]
    generalize classSpec cap _ = CS at hCS ⊢
    generalize (typedParsed cap).map _ = pv at hpv ⊢
    have e1 := take_drop_cons_append 0 CS pv 0 2 (by omega)
    have e2 := take_drop_cons_append 0 CS pv 2 11 (by omega)
    have e3 := take_drop_cons_append 0 CS pv 13 2 (by omega)
    have e4 := take_drop_cons_append 0 CS pv 15 (cap - 21) (by omega)
    simp only [Nat.reduceAdd, List.drop_zero] at e1 e2 e3 e4
    rw [List.take_of_length_le (l := CS.drop 15) (by simp; omega)] at e4
    simp only [List.singleton_append]
    rw [e1, e2, e3, e4]
  · -- bit 255: `tls-frame` on the old parser state and the private parse
    have h255' : (openOut cap P K seqB tag recordPadded size xa xb).take 1 = [255] := h255
    obtain ⟨J, hJ, h14, h15, h16⟩ := open_prefix E cap hcE htE n hcap parser traffic hpn htn P K seqB tag recordPadded
      size hP hK hs htag hr hz halfSlot σA σB I hIp hIt xa xb hA hB
      ⟨(kernelOut (tlsFrame cap) (P ++ parsedOf cap (openOut cap P K seqB tag recordPadded size xa xb))).take 2,
        ⟨n + 14⟩, ⟨n + 15⟩, ⟨n + 16⟩⟩
      (fun J => J.bools (n + 14) = some (bitsOf (((kernelOut (tlsFrame cap)
            (P ++ parsedOf cap (openOut cap P K seqB tag recordPadded size xa xb))).drop 2).take 11)) ∧
          J.bools (n + 15) = some (bitsOf (((kernelOut (tlsFrame cap)
            (P ++ parsedOf cap (openOut cap P K seqB tag recordPadded size xa xb))).drop 13).take 2)) ∧
          J.bools (n + 16) = some (bitsOf (((kernelOut (tlsFrame cap)
            (P ++ parsedOf cap (openOut cap P K seqB tag recordPadded size xa xb))).drop 15).take (cap - 21))))
      (fun I' h8 hp => by
        rw [h255']
        unfold afterBit
        rw [if_neg (by decide), if_pos rfl]
        exact open_frame E hfE n hcap parser hpn P _ hP htl σA σB I' h8 hp)
    refine ⟨_, J, hJ, _, _, _, h14, h15, h16, ?_⟩
    -- the frame's output is the class kernel's
    have hpo' : parsedOf cap (openOut cap P K seqB tag recordPadded size xa xb) =
        (typedParsed cap).map (BVExpr.eval (assignOf (typedInput P K seqB recordPadded size
          (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag))))) := hpo
    have hfi1 : (lookup (frameInputs cap) "parser").map (BVExpr.eval (assignOf (P ++ parsedOf cap
        (openOut cap P K seqB tag recordPadded size xa xb)))) = P := by
      have : lookup (frameInputs cap) "parser" = ByteCircuit.inputBytes 0 11 := by simp [lookup, lookupFrom, frameInputs]
      rw [this]
      show inputValue _ 0 11 = _
      rw [iv _ _ _ (by simp; omega), List.drop_zero, List.take_left' hP]
    have hfi2 : (lookup (frameInputs cap) "parsed").map (BVExpr.eval (assignOf (P ++ parsedOf cap
        (openOut cap P K seqB tag recordPadded size xa xb)))) = parsedOf cap (openOut cap P K seqB tag recordPadded size xa xb) := by
      have : lookup (frameInputs cap) "parsed" = ByteCircuit.inputBytes 11 (cap - 17) := by
        simp [lookup, lookupFrom, frameInputs, HybridKernel.Shape.variables]
      rw [this]
      show inputValue _ 11 (cap - 17) = _
      rw [iv _ _ _ (by simp; rw [hpo', hpv]; omega), List.drop_left' hP,
        List.take_of_length_le (Nat.le_of_eq (by rw [hpo', hpv]))]
    have hfo : kernelOut (tlsFrame cap) (P ++ parsedOf cap (openOut cap P K seqB tag recordPadded size xa xb)) =
        classSpec cap (assignOf (typedInput P K seqB recordPadded size
          (kernelOut HybridKernel.gcmCheck (checkInput K seqB xa xb tag)))) := by
      rw [hfeq, hfi1, hfi2, hpo', classSpec, bP]
    simp only [hfo]
    rw [fields_eq]
    generalize classSpec cap _ = CS at hCS ⊢
    rw [List.take_of_length_le (l := CS.drop 15) (by simp; omega)]

theorem parserInitial_out (x : B8) : kernelOut HybridKernel.tlsParserInitial x = List.replicate 11 0 := by
  simp [kernelOut, HybridKernel.tlsParserInitial, HybridKernel.priv, HybridKernel.zeros, HybridKernel.const]

/-- **The initial parser state, two honest parties** (`parserScript`): both return the handle
`n + 1`, which holds `tls-parser-initial`'s output, 11 zero bytes (the post-handshake parser's
initial state). -/
theorem parser_honest (E : Env) (hE : E.circuits parserName = some (circuitOf HybridKernel.tlsParserInitial))
    (n : Nat) (σA σB : Store) (I : Ideal) :
    ∃ J, JRet (jointRun E (parserScript n) (parserScript n) σA σB I) ⟨n + 1⟩ ⟨n + 1⟩ J σA σB ∧
      J.bools (n + 1) = some (bitsOf (List.replicate 11 0)) := by
  have hw : 8 * ([0] : B8).length = (circuitOf HybridKernel.tlsParserInitial).inWidth := by
    simp [circuitOf, kernelCircuit, kernelInBytes, HybridKernel.tlsParserInitial, HybridKernel.Shape.variables]
  unfold parserScript
  simp only [seqs_cons, seqs_nil]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_public E ⟨n⟩ (bitsOf [0]) I) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_runK E ⟨n + 1⟩ _ ⟨n⟩ _ _ _ _ hE (by ival_tac)
    hw (parserInitial_out _)) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ σA σB _ (localStep_free E _ _) ?_
  exact ex_done E _ _ σA σB _ _ (by ival_tac)

/-- **A forged record opens nothing but the rejection** (through `jointRun`): with honest halves of
shared key powers (P-GHASH (a)) and a received tag that is NOT GCM's tag of the received header and
ciphertext under the server key, the two parties' run returns the event `[0, 0]`, and the bit they
opened is 0 (`tlsOpenTyped_gated` / `rejected_parse` through the binding): the only releases of
`openScript` (`open_reveals`) carry these two constant values, whatever the record. -/
theorem open_rejected_run (E : Env) (cap : Nat)
    (hcE : E.circuits checkName = some (circuitOf HybridKernel.gcmCheck))
    (htE : E.circuits (typedName cap) = some (circuitOf (tlsOpenTyped cap)))
    (hfE : E.circuits (frameName cap) = some (circuitOf (tlsFrame cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser traffic : BoolH) (hpn : parser.id < n) (htn : traffic.id < n)
    (P K seqB tag recordPadded size : B8) (hP : P.length = 11) (hK : K.length = 60) (hs : seqB.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2) (halfSlot : Nat)
    (σA σB : Store) (I : Ideal) (hIp : I.bools parser.id = some (bitsOf P)) (hIt : I.bools traffic.id = some (bitsOf K))
    (hdr ct : B8) (a b : List W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow)
    (hA : σA.bits halfSlot = bitsOfW (Local.Ghash.half a hdr ct))
    (hB : σB.bits halfSlot = bitsOfW (Local.Ghash.half b hdr ct))
    (hforged : Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB) ≠ tag) :
    ∃ o J, JRet (jointRun E (openScript n parser traffic seqB tag recordPadded size cap halfSlot)
        (openScript n parser traffic seqB tag recordPadded size cap halfSlot) σA σB I) o o J σA σB ∧
      o.event = [0, 0] ∧
      (openOut cap P K seqB tag recordPadded size (Local.Ghash.half a hdr ct) (Local.Ghash.half b hdr ct)).take 1 = [0] := by
  obtain ⟨o, J, hJ, vp, vl, vc, -, -, -, hf⟩ := open_class E cap hcE htE hfE n hcap parser traffic hpn htn P K seqB
    tag recordPadded size hP hK hs htag hr hz halfSlot σA σB I hIp hIt _ _ hA hB
  have hacc := open_binding_honest cap P K seqB recordPadded size hdr ct tag hP hK hs hr hz htag a b nPow hsh hn
  rw [if_neg hforged] at hacc
  generalize hAdef : assignOf (typedInput P K seqB recordPadded size (kernelOut HybridKernel.gcmCheck
    (checkInput K seqB (Local.Ghash.half a hdr ct) (Local.Ghash.half b hdr ct) tag))) = A at hacc hf
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
  refine ⟨o, J, hJ, ?_, ?_⟩
  · rw [fields_eq] at hf
    simp only [List.cons.injEq] at hf
    rw [hf.1, classSpec, hk]
    exact TypedOpen.frame_unauthenticated _ _
  · show (kernelOut (tlsOpenTyped cap) _).take 1 = [0]
    rw [typedOut_bit, hAdef, TypedOpen.handshakeBit_map (ByteAuth.evaluationHom A), hk,
      TypedOpen.handshakeBit_zeros]

end TlsMpc.Node.Flows.Tls
