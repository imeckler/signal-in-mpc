import TlsMpc.FlatLowering
import TlsMpc.FlatKernelLayout
import TlsMpc.ByteCircuit
import TlsMpc.BoolDag
import TlsMpc.FieldDag
import TlsMpc.FieldDagMulti
import TlsMpc.FieldProgramsV3
import TlsMpc.HybridKernelsProofs
import TlsMpc.SealCtrProofs
import TlsMpc.GcmShareKernelsProofs
import TlsMpc.ContactKernelsProofs
import TlsMpc.RecordClassProofs
import TlsMpc.TypedOpenProofs
import TlsMpc.MlKemFastProofs
import TlsMpc.ReceiveProofs
import TlsMpc.EstablishProofs
import TlsMpc.BundleProofs
import TlsMpc.BundleItemKernels
import TlsMpc.CeremonyProofs
import TlsMpc.Aes
import TlsMpc.AesSbox
import TlsMpc.Sha256
import TlsMpc.TlsKdfPrepared
import TlsMpc.Gcm
import TlsMpc.TlsRecord
import TlsMpc.TlsReceive
import TlsMpc.TlsHandshake
import TlsMpc.TlsPostHandshake
import TlsMpc.TlsPublicHandshake
import TlsMpc.TlsProviderGate
import TlsMpc.TlsClient
import TlsMpc.TlsApplicationPolicy
import TlsMpc.TlsWebSocketActivity
import TlsMpc.TlsPrivateSeal
import TlsMpc.EstablishField
import TlsMpc.EdwardsHinted
import TlsMpc.EdwardsAffine
import TlsMpc.EdwardsShare
import TlsMpc.ReceiveField
import TlsMpc.WordMask
import TlsMpc.FieldBits
import TlsMpc.X25519
import TlsMpc.X25519Fast
import TlsMpc.X25519SwapBits
import TlsMpc.GhashShares
import TlsMpc.MaskedAgreement
import TlsMpc.OffsetAgreement
import TlsMpc.Signal.Pqxdh
import TlsMpc.Signal.Symmetric
import TlsMpc.Signal.DhRatchet
import TlsMpc.Signal.SpqrChain
import TlsMpc.Signal.Establish
import TlsMpc.Signal.XEdDsaScalar
import TlsMpc.Signal.XEdDsa
import TlsMpc.Signal.MessageMac
import TlsMpc.Signal.RelayUpgrade
import TlsMpc.Signal.ChainSend
import TlsMpc.Signal.SpqrSend
import TlsMpc.Signal.Send
import TlsMpc.Signal.OpenResult
import TlsMpc.Signal.PreKeyValidation
import TlsMpc.Signal.Word64Fast
import TlsMpc.Signal.VarintDecode.Spqr
import TlsMpc.Signal.PrivateTextNotification
import TlsMpc.KernelSpecs.RequestCtr
import TlsMpc.KernelSpecs.SealFixed
import TlsMpc.KernelSpecs.TlsHandshakeKernels
import TlsMpc.KernelSpecs.RevealMasked
import TlsMpc.KernelSpecs.SignalKernels
import TlsMpc.KernelSpecs.PointsAndItem
import TlsMpc.KernelSpecs.RequestFrame
import TlsMpc.KernelSpecs.BundleItemWhole
import TlsMpc.KernelSpecs.WidthFlags
import TlsMpc.KernelSpecs.SlotEncoders
import TlsMpc.KernelSpecs.SlotBase64
import TlsMpc.KernelSpecs.SlotDecimal
import TlsMpc.KernelSpecs.SealFrame
import TlsMpc.KernelSpecs.BundleSlotWhole
import TlsMpc.KernelSpecs.ReceiveAcceptAccessKey
import TlsMpc.KernelSpecs.EstablishRequest
import TlsMpc.Node.Policy.Receive
import TlsMpc.Node.Policy.Clock
import TlsMpc.Node.Local.WebSocketAccept
import TlsMpc.KernelSpecs.ParseWebSocketFrame
import TlsMpc.KernelSpecs.ParseWebSocketControl
import TlsMpc.KernelSpecs.ParseTlsRecord
import TlsMpc.Node.Policy.RequestProofs
import TlsMpc.Node.Policy.CloseProofs
import TlsMpc.KernelSpecs.KemCompose
import TlsMpc.Node.Engine.Model
import TlsMpc.Node.Flows.Random
import TlsMpc.Node.Flows.Upgrade
import TlsMpc.Node.Flows.Contacts
import TlsMpc.Node.Flows.ContactsTable
import TlsMpc.Node.Flows.Account
import TlsMpc.Node.Flows.ContactsWrite
import TlsMpc.Node.Engine.Labels
import TlsMpc.Node.Engine.Reveal
import TlsMpc.Node.Flows.MasksRun
import TlsMpc.Node.Flows.ConvertRun
import TlsMpc.Node.Flows.ConvertWF
import TlsMpc.Node.Flows.MasksWF
import TlsMpc.Node.Flows.MasksModel
import TlsMpc.Node.Flows.MasksHonest
import TlsMpc.Node.Flows.MasksHides
import TlsMpc.Node.Flows.Registry
import TlsMpc.Node.Flows.TlsProofs
import TlsMpc.Node.Flows.SendProofs
import TlsMpc.Node.Flows.ReceiveFlowProofs
import TlsMpc.Node.Flows.RefreshFirstProofs
import TlsMpc.Node.Flows.RefreshWF
import TlsMpc.Node.Flows.CurveWF
import TlsMpc.Node.Flows.CurveLive
import TlsMpc.Node.Flows.CurveCommit
import TlsMpc.Node.Flows.CurveHonest
import TlsMpc.Node.Flows.Join
import TlsMpc.Node.Flows.JoinBackend
import TlsMpc.Node.Flows.JoinOnce
import TlsMpc.Node.Flows.Runner
import TlsMpc.Node.Flows.Select
import TlsMpc.Node.Flows.JoinIdentity
import TlsMpc.Node.Flows.CurveRunI
import TlsMpc.Node.Flows.CurveRunJ
import TlsMpc.Node.Flows.CurveRunK
import TlsMpc.Node.Flows.CurveLocalLive
import TlsMpc.Node.Flows.TlsBounded
import TlsMpc.Node.Flows.TlsClassSeal
import TlsMpc.Node.Flows.TlsDerive
import TlsMpc.Node.Flows.TlsT3
import TlsMpc.Node.Flows.SendRecordRun
import TlsMpc.Node.Flows.SendDevicesBounded
import TlsMpc.Node.Messages
import TlsMpc.KernelSpecs.ParseWebSocketAccept
import TlsMpc.KernelSpecs.ParseWebSocketControlFrame
import TlsMpc.KernelSpecs.ParseWebSocketReplies
import TlsMpc.KernelSpecs.ParseChatResponse
import TlsMpc.Node.Policy.ReceiveProofs
import TlsMpc.Node.Policy.ReceiveEnvelope
import TlsMpc.Node.Policy.ReceiveInvariant
import TlsMpc.Node.Types
import TlsMpc.Node.Policy.ReceiveSession
import TlsMpc.Node.Policy.ReceiveHead
import TlsMpc.Node.Policy.ReceiveStart
import TlsMpc.Node.Policy.ReceiveFrame
import TlsMpc.Node.Session.ServeProofs
import TlsMpc.Node.Policy.Rotation
import TlsMpc.Node.Stock.Use
import Lean.Elab.Command

/-!
# Security theorems, version 1 (REORGANIZATION_PLAN.md stage S1)

The one-file answer to "where are the important theorems". Every entry below restates a theorem
that already exists elsewhere in the repository, word for word, and is proved by **direct
reference** to it (`theorem X : <statement> := Original.name`). So renaming, deleting or weakening
the original breaks this file. Nothing here is a new proof. `#print axioms` for every entry is at
the end; `scripts/check_axioms.py` runs this file and records the output in `SECURITY_AXIOMS.txt`.

The order follows the catalogue of REORGANIZATION_PLAN.md section 8.2:
1. lowering and artifacts;
2. kernels compute their specification;
3. gating and what each opening reveals;
4. the controller: parsers, the reveal policy, templates, results;
5. state and ordering;
6. conversions and helper protocols;
7. flows and channels;
8. NOT YET PROVED (comments only, each pointing at the stage or proof track that delivers it);
9. machine checks (`#print axioms`, and which entries depend on `bv_decide`).

## Status of each entry (SECURITY_MAP.md section C)

* **K** — about a term that is lowered into a kernel or field program that a deployment loads
  (`real_signal/deployment-production.json`, `local_signal_server/deployment-compact.json`).
* **K-fn** — about a *function* that a deployed kernel is built from, stated for the function on
  its own (usually "the symbolic circuit evaluates to the concrete function"). No theorem
  composes it with the rest of the kernel unless the entry says so.
* **C** — about a function the Lean controller (`public_service_controller`) executes, directly or
  through a variant proved equal to it.
* **M** — a model, or code that no deployment runs. Kept because it states an intended property
  that later stages must discharge for the running code.
* **switch** — used only when the worker runs with `TLS_WORKER_HINTED=1` (the constant-depth curve
  programs). Only the local harness (`--hinted`) and `deployment/vm_pair_test` set it; neither
  deployment file does.
* **ceremony** — used only by the registration ceremony (`ceremony=1`), a separate run; no
  standing deployment lists the ceremony kernels.
* **C-gen** — about a monad-generic definition that the controller executes (the deployed
  function IS that definition at `SessionM` and the deployed operations record), proved at a pure
  model monad for every operations record satisfying the entry's assumptions. Carried to the
  running code by the free theorem of the definition's type (one text, two monads; Lean does not
  state free theorems: trusted with the compiler, PROOF_GAPS.md A8) and by the entry's
  assumptions on the real operations (`Session/Events.lean` header; `ReceiveSession.Faithful`).

## What every entry silently relies on (trusted, not proved)

* The field-program printers (`EmitWordMask.render`/`renderField`), the choice of which flat
  outputs form which named field (`selection`), and that the engines' loaders parse the files as
  `parseFlat`/`parseLayout` do (SECURITY_MAP C.1). Since the emitter batch the flat circuit
  printer and the layout text with its open/private marks are proved (section 1b: what they
  print parses back to the gate list and to the kernel's declared fields and marks).
* `ShareCommon.shareCommon'` (used by the translation validators), the Lean compiler and runtime.
* The engines (emp-ag2pc, the MP-SPDZ-based field engine) compute ideally; the C++ worker's
  sequencing (SECURITY_MAP D.5, D.6). None of the C++ is modelled here except where an entry says
  "models `…h`", and then only as a model (**M**).

## Assumptions that stay hypotheses (REORGANIZATION_PLAN R7)

* **H-GROUP**: **now a theorem for the Edwards formulas** (2026-11-12) in `proofs/` (index
  `SecurityMathlib.lean` section 7): `edwards_complete`, `edwards_add_assoc`, `edwards_group_laws`,
  `pointAddValue_is_group_add`, `extAddValue_is_group_add`, `curveCheck_zero_iff`,
  `sumTreeValue_is_group_sum`, `extSumValue_is_group_sum`, `recipient_on_curve`,
  `xeddsa_recover_on_curve`, `base_order_nsmul`, `base_addOrderOf`, `curve_subgroup_card`,
  `x25519_spec_scalar_mult`, `x25519_spec_scalar_mult_all` (also `u = 0`), `x25519_on_curve`,
  `x25519_clampedScalar_rfc`, `window_table`, `bitTable_entries`, `recode_offset`,
  `offsetSum_scalar_mult`, `bitSum_is_x25519`, `prepareHinted_initial_point`,
  `xeddsa_doubleScalar`, `montgomery_map_onCurve`, `montQ_square_iff`, `liftPoint_valid_point`
  (proofs/ sections 7c–7e). Still assumed: `#E = 8ℓ` (point counting); the recipient point
  nonzero and killed by ℓ; X25519 on the quadratic twist; that the C++ `step` / `Local/Edwards`
  implement `recode` / the Lean programs.
* **H-QR**: 2 is a non-square mod p (used by the hinted lift; no entry here needs it yet).
  **Now a theorem** (2026-11-12) in the Mathlib-backed package `proofs/`, which no executable
  and nothing in this package imports: `prime_modulus`, `two_not_square`, `euler_criterion`,
  `euler_nonsquare` (index: `proofs/TlsMpcProofs/SecurityMathlib.lean`, sections 1–2).
* **idealCommit**: SHA-256 commitments are hiding and binding (commit-then-open; no entry here
  states it yet — the commit-then-open exchanges are C++ today).
* The pad `E = AES_K(J0)` is a fresh pseudorandom value (GHASH share entries).
-/

namespace TlsMpc.Security

/-! ## 1. Lowering and artifacts (SECURITY_MAP C.1)

How a Lean circuit term becomes the gate list the worker loads, and why the gate list computes the
term. Since the emitter batch the printers that turn the gate list and the kernel's fields into
text are covered too (section 1b): parsing the printed text gives back what was printed. The V3
field-program printer (`EmitWordMask`) is not (stage S9/S10). -/

open TlsMpc.FlatLowering Std.Sat Std.Tactic.BVDecide in
open scoped Std.Sat.AIG in
/-- **The lowering is sound.** If `lower` accepts an AIG and returns a flat gate list, the list
is well formed, has the stated number of inputs and outputs, and every output wire evaluates to
the AIG node it was made from, for every input. Hypotheses: the AIG is a DAG; the flat inputs
agree with the AIG's variable assignment. **K** (generic: every flat kernel goes through it).
SECURITY_MAP C.1. -/
theorem lower_sound {decls : Decls} {widths : Array Nat} {outs : Array (Nat × Bool)} {flat : Flat}
    (dag : AIG.IsDAG BVBit decls) (h : lower decls widths outs = .ok flat)
    (inp : Nat → Bool) (asg : BVBit → Bool) (hin : InputsAgree widths (offsets widths) inp asg) :
    flat.wellFormed = true ∧ flat.inputs = totalBits widths ∧ flat.outputs.size = outs.size ∧
      ∀ (k w : Nat) (o : Nat × Bool), flat.outputs[k]? = some w → outs[k]? = some o →
        flat.eval inp w = (nodeVal decls asg o.1 ^^ o.2) :=
  TlsMpc.FlatLowering.lower_sound dag h inp asg hin

open TlsMpc.FlatLowering Std.Sat Std.Tactic.BVDecide in
open scoped Std.Sat.AIG in
/-- **The lowering agrees with `AIG.denote`.** Output `k` of the flat list evaluates to the
denotation of the `k`-th AIG reference. Hypothesis: inputs agree with the assignment. **K**
(generic). SECURITY_MAP C.1. -/
theorem lower_correct (aig : AIG BVBit) {widths : Array Nat} (refs : Array (AIG.Ref aig)) {flat : Flat}
    (h : lower aig.decls widths (refs.map fun r => (r.gate, r.invert)) = .ok flat)
    (inp : Nat → Bool) (asg : BVBit → Bool) (hin : InputsAgree widths (offsets widths) inp asg) :
    flat.outputs.size = refs.size ∧
      ∀ (k w : Nat) (hk : k < refs.size), flat.outputs[k]? = some w →
        flat.eval inp w = ⟦aig, refs[k], asg⟧ :=
  TlsMpc.FlatLowering.lower_correct aig refs h inp asg hin

open TlsMpc.FlatLowering Std.Sat Std.Tactic.BVDecide in
/-- **A kernel expression lowers to a flat list that computes it.** Flat output `k` equals bit
`sel[k]` of the expression's value, when the flat input wires carry the assignment's bits at the
offsets of `widths`. `EmitFlatKernel` and `EmitCeremonyKernel` call exactly
`lowerExpr (joinExpr bytes)`. **K** (generic). SECURITY_MAP C.1. -/
theorem lowerExpr_correct (expr : BVExpr w) (widths : Array Nat) (sel : Array (Fin w)) (flat : Flat)
    (h : lowerExpr expr widths sel = .ok flat) (assign : BVExpr.Assignment) (inp : Nat → Bool)
    (hin : ∀ (v off b : Nat) (width : Nat), widths[v]? = some width → (offsets widths)[v]? = some off →
      b < width → inp (off + b) = (assign.get v).bv.getLsbD b) :
    flat.outputs.size = sel.size ∧
      ∀ (k out : Nat) (hk : k < sel.size), flat.outputs[k]? = some out →
        flat.eval inp out = (expr.eval assign).getLsbD sel[k].val :=
  TlsMpc.FlatLowering.lowerExpr_correct expr widths sel flat h assign inp hin

open TlsMpc.FlatLowering in
/-- **The loader's one-pass evaluation equals the reference evaluation** of a well-formed flat
list, for every wire. **K** (generic; the C++ loader's own evaluation is not modelled).
SECURITY_MAP C.1. -/
theorem flat_run_eq_eval (f : Flat) (inp : Nat → Bool) (hwf : f.wellFormed = true) (w : Nat)
    (hw : w < f.inputs + f.opa.size) : (f.run inp)[w]? = some (f.eval inp w) :=
  TlsMpc.FlatLowering.Flat.run_eq_eval f inp hwf w hw

/-! ### 1b. Printers and marks (T2, proof track P3; emitter batch)

The circuit text and the layout file the four kernel emitters write. The printers print what they
always printed (`layoutText_eq_before`; `Flat.print` uses the same `++` chains); the theorems
below say what they print. -/

open TlsMpc.FlatLowering in
/-- **What the circuit printer writes is `Flat.render`** (run with a `write` that appends; the
emitters run the same `printWith` in `IO`). **K** (generic). -/
theorem flat_printWith_render (f : Flat) : ((f.printWith appendOut).run "").2 = f.render :=
  TlsMpc.FlatLowering.printWith_render f

open TlsMpc.FlatLowering in
/-- **A loader's parse of the printed text gives back the gate list**, for every well-formed one
(every `lower` result). **K** (generic). Trusted: the engines' loaders parse as `parseFlat`. -/
theorem flat_parse_render (f : Flat) (hwf : f.wellFormed = true) : parseFlat f.render.toList = some f :=
  TlsMpc.FlatLowering.parseFlat_render f hwf

open TlsMpc.FlatLowering Std.Tactic.BVDecide in
/-- **The text the engines load denotes the lowered expression**: it parses back to the gate list,
and output `k` of that list is bit `sel[k]` of the expression's value. **K** (generic). -/
theorem flat_lowerExpr_loaded (expr : BVExpr w) (widths : Array Nat) (sel : Array (Fin w)) (flat : Flat)
    (h : lowerExpr expr widths sel = .ok flat) :
    parseFlat ((flat.printWith appendOut).run "").2.toList = some flat ∧ flat.outputs.size = sel.size ∧
      ∀ (assign : BVExpr.Assignment) (inp : Nat → Bool),
        (∀ (v off b : Nat) (width : Nat), widths[v]? = some width → (offsets widths)[v]? = some off →
          b < width → inp (off + b) = (assign.get v).bv.getLsbD b) →
        ∀ (k out : Nat) (hk : k < sel.size), flat.outputs[k]? = some out →
          flat.eval inp out = (expr.eval assign).getLsbD sel[k].val :=
  TlsMpc.FlatLowering.lowerExpr_loaded expr widths sel flat h

open TlsMpc.FlatKernelLayout in
/-- **The layout file is byte for byte what the emitters wrote before the batch.** -/
theorem layoutText_unchanged (k : HybridKernel.Kernel) : layoutText k = layoutTextBefore k :=
  TlsMpc.FlatKernelLayout.layoutText_eq_before k

open TlsMpc.FlatKernelLayout in
/-- **The layout file lists exactly the kernel's declared fields and open marks** (alphanumeric
names, which `lowerKernel` checks). **K** (generic). -/
theorem layout_parse (k : HybridKernel.Kernel) (hin : ∀ f ∈ k.inputs, ValidName f.1)
    (hout : ∀ o ∈ k.outputs, ValidName o.name) :
    parseLayout (layoutText k).toList = some (inputFields k, outputFields k) :=
  TlsMpc.FlatKernelLayout.parseLayout_layoutText k hin hout

open TlsMpc.FlatKernelLayout in
/-- **The open mark says who may see an output**: 2 / 3 exactly for party 1 / 2 only, 1 exactly
for an `opened` output with no single audience, 0 for a private one. -/
theorem layout_openCode (o : HybridKernel.Output) :
    (openCode o = 2 ↔ o.audience = 1) ∧ (openCode o = 3 ↔ o.audience = 2) ∧
      (openCode o = 1 ↔ o.opened = true ∧ o.audience ≠ 1 ∧ o.audience ≠ 2) ∧
      (openCode o = 0 ↔ o.opened = false ∧ o.audience ≠ 1 ∧ o.audience ≠ 2) :=
  TlsMpc.FlatKernelLayout.openCode_spec o

open TlsMpc.FlatKernelLayout in
/-- **What the engines load for a kernel is that kernel (T2 for every kernel the four kernel
emitters lower).** If `lowerKernel k` returns `flat`: the circuit text parses back to `flat`, the
layout file to the kernel's fields and marks, and `flat` is `lowerExpr` of the kernel's joined
outputs (so `flat_lowerExpr_loaded` and `joinExpr_correct` give each output wire's value). Not
covered: `selection` (which named output bit is which bit of the joined value). -/
theorem kernel_loaded (k : HybridKernel.Kernel) (flat : TlsMpc.FlatLowering.Flat) (h : lowerKernel k = .ok flat) :
    TlsMpc.FlatLowering.parseFlat ((flat.printWith TlsMpc.FlatLowering.appendOut).run "").2.toList = some flat ∧
      parseLayout (layoutText k).toList = some (inputFields k, outputFields k) ∧
      ∃ chosen, TlsMpc.FlatLowering.lowerExpr (ByteCircuit.joinExpr (k.outputs.flatMap (·.value)))
        (inputWidths k) chosen = .ok flat :=
  TlsMpc.FlatKernelLayout.lowerKernel_loaded k flat h

open TlsMpc.ByteCircuit Std.Tactic.BVDecide in
/-- **Joining a kernel's byte outputs into one bit vector is faithful:** the joined expression
evaluates to the join of the evaluated bytes. Glue used by every kernel. **K** (generic).
SECURITY_MAP C.1. -/
theorem joinExpr_correct (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (joinExpr bytes).eval assign =
      (joinValue (bytes.map (BVExpr.eval assign))).cast (by simp) :=
  TlsMpc.ByteCircuit.joinExpr_correct bytes assign

open TlsMpc.HybridKernel Std.Tactic.BVDecide in
/-- **Every exported AIG output bit of a kernel equals the Lean definition** of that kernel,
evaluated on the same input. Per-family copies with an extra (unused) lookup hypothesis:
`ReceiveKernel`, `EstablishKernel`, `BundleKernel`, `CeremonyKernel`, `MlKemFastKernel`
`.compiled_correct`. **K** (the AIG export path). Not composed with `lowerExpr_correct` and a
kernel `_spec` into "the loaded file computes the spec" (SECURITY_MAP C.1, last paragraph). -/
theorem kernel_compiled_correct (k : Kernel) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * k.bytes.length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr k.bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr k.bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (k.bytes.map (BVExpr.eval assign))).getLsbD index :=
  TlsMpc.HybridKernel.compiled_correct k assign index hi

open TlsMpc.BoolDag in
/-- **An accepted Boolean DAG compilation evaluates to its expressions** (translation validation
of the word-mask circuits: `modadd`, `into-field`, `finalize-*`, `swap-bits`, …). **K**:
`EmitWordMask` calls it. SECURITY_MAP C.1. -/
theorem boolDag_compile_correct (es : List Expr) (a : Artifact) (compiled : compile es = some a)
    (input : Nat → Bool) :
    a.outputs.map (result (concrete input) a.nodes) = es.map (Expr.eval input) :=
  TlsMpc.BoolDag.compile_correct es a compiled input

open TlsMpc.FieldDag in
/-- **An accepted field-program compilation (one output) evaluates to its expression.** **K**:
`EmitWordMask.renderField`. The `D` (division) nodes are evaluated by the C++ evaluator with its
own masking, which is not modelled. SECURITY_MAP C.1. -/
theorem fieldDag_compile_correct (e : Expr) (a : Artifact) (compiled : compile e = some a)
    (input : Nat → F) :
    result (concrete input) a.nodes a.output = e.eval input :=
  TlsMpc.FieldDag.compile_correct e a compiled input

open TlsMpc.FieldDag in
/-- **An accepted field-program compilation (several outputs) evaluates to its expressions.**
**K**: `EmitWordMask.renderFieldAll` (x25519-fast, edwards-*, xeddsa-*, receive-torsion, …).
SECURITY_MAP C.1. -/
theorem fieldDag_compileAll_correct (es : List Expr) (a : MultiArtifact) (compiled : compileAll es = some a)
    (input : Nat → F) :
    a.outputs.map (result (concrete input) a.nodes) = es.map (Expr.eval input) :=
  TlsMpc.FieldDag.compileAll_correct es a compiled input

/-! ### 1a. Field programs, format V3 (`TlsMpc/FieldDagV3.lean`, plan 5.5)

**Trust:** the evaluator (`node_worker/src/program.rs`) and the engines are outside the theorems;
`FieldInverse` (Fermat for p) is a named hypothesis, true because p is prime. -/

open TlsMpc.FieldDag.V3 in
/-- **V3 round trip**: a valid program's text parses back to it. -/
theorem fieldDagV3_parse_render (p : Program) (hp : p.valid = true) : parse (render p) = some p :=
  TlsMpc.FieldDag.V3.parse_render p hp

open TlsMpc.FieldDag.V3 in
/-- **One text per program**: the parser accepts only rendered texts (so a pin names a program). -/
theorem fieldDagV3_render_parse (s : String) (p : Program) (h : parse s = some p) : render p = s :=
  TlsMpc.FieldDag.V3.render_parse s p h

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 in
/-- **V3 evaluation agrees with FieldDag**: a translated artifact that does not abort outputs the
FieldDag results, so every theorem about a compiled field program carries over to its V3 file. -/
theorem fieldDagV3_eval_ofArtifact (hinv : FieldInverse) (inputs : Nat) (a : MultiArtifact)
    (marks : Nat → OMark) (input mask : Nat → F) (outs opened : List F)
    (h : V3.eval (ofArtifact inputs a marks) input mask = some (outs, opened)) :
    outs = a.outputs.map (result (concrete input) a.nodes) :=
  TlsMpc.FieldDag.V3.eval_ofArtifact hinv inputs a marks input mask outs opened h

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 in
/-- With nonzero masks, a translated artifact aborts only on a zero FieldDag denominator. -/
theorem fieldDagV3_eval_ofArtifact_some (hinv : FieldInverse) (inputs : Nat) (a : MultiArtifact)
    (marks : Nat → OMark) (input mask : Nat → F) (hm : ∀ j, mask j ≠ 0)
    (hd : DivisorsNonzero input #[] a.nodes) :
    (V3.eval (ofArtifact inputs a marks) input mask).isSome :=
  TlsMpc.FieldDag.V3.eval_ofArtifact_some hinv inputs a marks input mask hm hd

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 in
/-- The V3 program of `compileAll es` outputs the source expressions' values. -/
theorem fieldDagV3_eval_compileAll (hinv : FieldInverse) (inputs : Nat) (es : List Expr)
    (a : MultiArtifact) (hc : compileAll es = some a) (marks : Nat → OMark)
    (input mask : Nat → F) (outs opened : List F)
    (h : V3.eval (ofArtifact inputs a marks) input mask = some (outs, opened)) :
    outs = es.map (Expr.eval input) :=
  TlsMpc.FieldDag.V3.eval_compileAll hinv inputs es a hc marks input mask outs opened h

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 in
/-- **P-INV (d)** for every translated program: each mask feeds exactly one `D` row. -/
theorem fieldDagV3_ofArtifact_masksOk (inputs : Nat) (a : MultiArtifact) (marks : Nat → OMark) :
    (ofArtifact inputs a marks).masksOk = true :=
  TlsMpc.FieldDag.V3.ofArtifact_masksOk inputs a marks

open TlsMpc.FieldDag.V3 in
/-- **P-INV (d)** for every loaded program (the parser checks it). -/
theorem fieldDagV3_parse_masksOk (s : String) (p : Program) (h : parse s = some p) : p.masksOk = true :=
  TlsMpc.FieldDag.V3.parse_masksOk s p h

open TlsMpc.FieldDag.V3 in
/-- What `masksOk` means: mask `j` is named by exactly one `D`/`Z` row iff `j < masks`. -/
theorem fieldDagV3_masksOk_once (p : Program) (h : p.masksOk = true) (j : Nat) :
    p.maskUses.count j = if j < p.masks then 1 else 0 :=
  TlsMpc.FieldDag.V3.masksOk_once p h j

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 in
/-- **P-INV (a)**: a nonzero opening gives the true quotient. -/
theorem fieldDagV3_masked_div (hinv : FieldInverse) (a b m : F) (h : b * m ≠ 0) :
    a * m * inverse (b * m) = a * inverse b :=
  TlsMpc.FieldDag.V3.masked_div hinv a b m h

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 in
/-- **P-INV (b)**: the opening is 0 iff the denominator or the mask is. -/
theorem fieldDagV3_opening_zero_iff (hinv : FieldInverse) (b m : F) : b * m = 0 ↔ b = 0 ∨ m = 0 :=
  TlsMpc.FieldDag.V3.opening_zero_iff hinv b m

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 in
/-- **P-INV (c)**: for `b ≠ 0`, `m ↦ b·m` is a bijection (the opening is uniform for a uniform mask). -/
theorem fieldDagV3_opening_bijective (hinv : FieldInverse) (b : F) (hb : b ≠ 0) :
    (∀ m m' : F, b * m = b * m' → m = m') ∧ (∀ o : F, b * (inverse b * o) = o) :=
  TlsMpc.FieldDag.V3.opening_bijective hinv b hb

open TlsMpc.FieldDag.V3 in
/-- **P-FIELDPROG** for every translated program: its public outputs are its declared checks. -/
theorem fieldDagV3_ofArtifact_declares (inputs : Nat) (a : TlsMpc.FieldDag.MultiArtifact) (roles : List Role)
    (hl : a.outputs.length = roles.length) (hf : Role.flag ∉ roles) :
    (ofArtifact inputs a (marksOf roles)).declares roles = true :=
  TlsMpc.FieldDag.V3.ofArtifact_declares inputs a roles hl hf

open TlsMpc.FieldDag.V3 in
/-- **P-INV (d) and P-FIELDPROG for the quotient program** (`decide` on its rows). -/
theorem fieldDagV3_quotient_checks :
    quotient.masksOk = true ∧ quotient.declares [.secret, .flag] = true ∧ quotient.publicOutputs = [1] :=
  ⟨TlsMpc.FieldDag.V3.quotient_masksOk, TlsMpc.FieldDag.V3.quotient_declares⟩

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 in
/-- The quotient program computes `x·z⁻¹` and the zero flag of `z`, opening only `z·m`. -/
theorem fieldDagV3_quotient_spec (hinv : FieldInverse) (input mask : Nat → F) (hm : mask 0 ≠ 0) :
    V3.eval quotient input mask =
      some ([input 0 * inverse (input 1), if input 1 = 0 then ofNat 1 else ofNat 0], [input 1 * mask 0]) :=
  TlsMpc.FieldDag.V3.quotient_spec hinv input mask hm

open TlsMpc.FieldDag.V3 TlsMpc.FieldProgramsV3 in
/-- **P-INV (d) and P-FIELDPROG for every exported declaration** (`TlsMpc/FieldProgramsV3.lean`):
masks used once, public outputs exactly the declared checks. -/
theorem fieldProgramsV3_decl_checks (d : Decl) (hd : d.ok = true) (p : Program) (hp : d.program = some p) :
    p.masksOk = true ∧ p.declares d.roles = true ∧
      p.publicOutputs = publicPositions (d.roles.map Role.mark) :=
  TlsMpc.FieldProgramsV3.Decl.checks d hd p hp

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 TlsMpc.FieldProgramsV3 in
/-- **P-FIELDPROG (values)**: an exported program's outputs are its source expressions' values. -/
theorem fieldProgramsV3_decl_values (hinv : FieldInverse) (d : Decl) (p : Program) (hp : d.program = some p)
    (input mask : Nat → F) (outs opened : List F) (h : V3.eval p input mask = some (outs, opened)) :
    outs = d.exprs.map (Expr.eval input) :=
  TlsMpc.FieldProgramsV3.Decl.values hinv d p hp input mask outs opened h

open TlsMpc.FieldDag TlsMpc.FieldDag.V3 TlsMpc.FieldProgramsV3 in
/-- `field-bit-check` in V3: one public output, `b·(b − 1)`, zero on bits. -/
theorem fieldProgramsV3_bitCheck (hinv : FieldInverse) (p : Program) (hp : bitCheck.program = some p) :
    p.masksOk = true ∧ p.declares [.check] = true ∧ p.publicOutputs = [0] ∧
      ∀ input mask outs opened, V3.eval p input mask = some (outs, opened) →
        outs = [input 0 * (input 0 - ofNat 1)] ∧
        ∀ b : Bool, input 0 = X25519.bitValue b → outs = [0] :=
  TlsMpc.FieldProgramsV3.bitCheck_fieldprog hinv p hp

/-! ## 2. Kernels compute their specification (SECURITY_MAP C.2)

"Specification" here is usually the repository's own concrete transcription of the standard,
not an independent statement; no theorem checks a spec against official test vectors. -/

/-! ### 2a. Primitives (function level) -/

open TlsMpc.Aes Std.Tactic.BVDecide in
/-- **The AES circuit computes AES** (the concrete transcription), bit for bit, for any key and
block expressions. **K-fn**: AES is inside every TLS record kernel. SECURITY_MAP C.2. -/
theorem aes_encryptCore_compiled (nk rounds : Nat) (key block : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (encryptCore symbolic nk rounds key block).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (encryptCore symbolic nk rounds key block))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (encryptCore symbolic nk rounds key block))).vec.get index hi)) =
    (ByteCircuit.joinValue (encryptCore concrete nk rounds (key.map (BVExpr.eval assign))
      (block.map (BVExpr.eval assign)))).getLsbD index :=
  TlsMpc.Aes.compiled_encryptCore_correct nk rounds key block assign index hi

open TlsMpc.AesSbox in
/-- **The packed S-box circuit outputs the AES S-box table** (checked by `decide +kernel`, no
extra axiom). **K-fn**. SECURITY_MAP C.2. -/
theorem aesSbox_packed_correct : circuit packedOps packedInputs = packedOutputs :=
  TlsMpc.AesSbox.packed_correct

open TlsMpc.Sha256 Std.Tactic.BVDecide in
/-- **The SHA-256 circuit evaluates to concrete SHA-256.** **K-fn** (key schedule, contact key,
Signal kernels). SECURITY_MAP C.2. -/
theorem sha256_hash_refines (message : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (hash symbolic message).map (BVExpr.eval assign) =
      hash concrete (message.map (BVExpr.eval assign)) :=
  TlsMpc.Sha256.hash_refines message assign

open TlsMpc.Sha256 Std.Tactic.BVDecide in
/-- **The HMAC-SHA-256 circuit evaluates to concrete HMAC.** **K-fn**. SECURITY_MAP C.2. -/
theorem sha256_hmac_refines (key message : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (hmac symbolic key message).map (BVExpr.eval assign) =
      hmac concrete (key.map (BVExpr.eval assign)) (message.map (BVExpr.eval assign)) :=
  TlsMpc.Sha256.hmac_refines key message assign

open TlsMpc.TlsKdf in
/-- **The prepared (fast) TLS 1.3 handshake key schedule equals the textbook one**, for any
SHA-256 operations. **K-fn** (`tls-derive` has no kernel-level spec). SECURITY_MAP C.2. -/
theorem tls_handshakeSecretsFast_correct {B W : Type} (o : Sha256.Ops B W) (ecdhe helloHash : List B) :
    handshakeSecretsFast o ecdhe helloHash = handshakeSecrets o ecdhe helloHash :=
  TlsMpc.TlsKdf.handshakeSecretsFast_correct o ecdhe helloHash

open TlsMpc.TlsKdf in
/-- **The prepared TLS 1.3 application-traffic key schedule equals the textbook one.** **K-fn**.
SECURITY_MAP C.2. -/
theorem tls_applicationSecretsFast_correct {B W : Type} (o : Sha256.Ops B W) (secret transcript : List B) :
    applicationSecretsFast o secret transcript = applicationSecrets o secret transcript :=
  TlsMpc.TlsKdf.applicationSecretsFast_correct o secret transcript

open TlsMpc.TlsKdf in
/-- **The prepared HKDF-Expand-Label equals the textbook one.** **K-fn**. SECURITY_MAP C.2. -/
theorem tls_expandLabelFast_correct {B W : Type} (o : Sha256.Ops B W) (secret : List B) (label : String)
    (context : List B) (length : Nat) :
    expandLabelFast o secret label context length = expandLabelCore o secret label context length :=
  TlsMpc.TlsKdf.expandLabelFast_correct o secret label context length

open TlsMpc.Gcm Std.Tactic.BVDecide in
/-- **The AES-GCM seal circuit computes concrete AES-GCM.** **K-fn**: reached by `tls-finish`
through `TlsRecord.sealCore`. The deployed record sealing (`tls-seal-ctr` + `gcm-tag`) does
not use it; see section 6 for the share-based tag. SECURITY_MAP C.2. -/
theorem gcm_sealCore_compiled (key nonce aad content : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (sealCore symbolic key nonce aad content).bytes.length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (sealCore symbolic key nonce aad content).bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (sealCore symbolic key nonce aad content).bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (sealCore concrete (key.map (BVExpr.eval assign))
      (nonce.map (BVExpr.eval assign)) (aad.map (BVExpr.eval assign))
      (content.map (BVExpr.eval assign))).bytes).getLsbD index :=
  TlsMpc.Gcm.compiled_sealCore_correct key nonce aad content assign index hi

open TlsMpc.TlsRecord Std.Tactic.BVDecide in
/-- **The TLS 1.3 record-seal circuit computes the concrete record seal** (header, AES-GCM of
content‖type‖padding). **K-fn**: `tls-finish` seals the client Finished with it. SECURITY_MAP
C.2. -/
theorem tlsRecord_sealCore_compiled (key iv sequence content : List (BVExpr 8)) (kind padding : Nat)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (sealCore Gcm.symbolic key iv sequence content kind padding).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (sealCore Gcm.symbolic key iv sequence content kind padding))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (sealCore Gcm.symbolic key iv sequence content kind padding))).vec.get index hi)) =
    (ByteCircuit.joinValue (sealCore Gcm.concrete (key.map (BVExpr.eval assign))
      (iv.map (BVExpr.eval assign)) (sequence.map (BVExpr.eval assign))
      (content.map (BVExpr.eval assign)) kind padding)).getLsbD index :=
  TlsMpc.TlsRecord.compiled_sealCore_correct key iv sequence content kind padding assign index hi

open TlsMpc.TlsReceive Std.Tactic.BVDecide in
/-- **The exact-size record open equals its specification** (16-byte key). **M**: `openCore`
is used by the exact-size `tls-open-application`, which no deployment loads; the deployed
class kernels use `RecordClass.openParsed` (section 3). SECURITY_MAP C.2, C.3. -/
theorem tlsReceive_openCore_correct (key iv sequence wire : List (BitVec 8)) (hk : key.length = 16) :
    openCore Gcm.concrete ByteAuth.concrete key iv sequence wire = spec key iv sequence wire :=
  TlsMpc.TlsReceive.openCore_correct key iv sequence wire hk

open TlsMpc.TlsHandshake Std.Tactic.BVDecide in
/-- **The Finished check outputs 255 exactly when the received Finished message is the one
computed from the secret and transcript hash, else 0** (accept direction included). **K-fn**
(`tls-verify-finished` has no kernel-level spec). SECURITY_MAP C.2, C.3. -/
theorem tls_verifyHash_value (secret transcriptHash receivedMessage : List (BitVec 8)) :
    verifyHash Sha256.concrete ByteAuth.concrete secret transcriptHash receivedMessage =
      if finishedMessage Sha256.concrete secret transcriptHash = receivedMessage then 255 else 0 :=
  TlsMpc.TlsHandshake.verifyHash_value secret transcriptHash receivedMessage

open TlsMpc.EstablishField TlsMpc.FieldDag in
/-- **The `xeddsa-recover` field program computes `XEdDsaField.run`.** **K**. Formulas only:
not proved to be the group law (H-GROUP: the group law is proved in `proofs/`, `SecurityMathlib.lean` section 7). SECURITY_MAP C.2. -/
theorem xeddsa_recover_correct (artifact : MultiArtifact) (compiled : compileAll recover = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) =
      TlsMpc.Signal.XEdDsaField.run TlsMpc.X25519.concrete true input :=
  TlsMpc.EstablishField.recover_correct artifact compiled input

open TlsMpc.EstablishField TlsMpc.FieldDag in
/-- **The `xeddsa-check` field program computes `XEdDsaField.signedRun`.** **K**. Formulas
only (H-GROUP: the group law is proved in `proofs/`, `SecurityMathlib.lean` section 7). SECURITY_MAP C.2. -/
theorem xeddsa_check_correct (artifact : MultiArtifact) (compiled : compileAll check = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) =
      TlsMpc.Signal.XEdDsaField.signedRun TlsMpc.X25519.concrete input :=
  TlsMpc.EstablishField.check_correct artifact compiled input

open TlsMpc.ReceiveField TlsMpc.FieldDag in
/-- **The `receive-torsion` field program computes `torsionRun`.** **K**. Formulas only
(H-GROUP: the group law is proved in `proofs/`, `SecurityMathlib.lean` section 7). Not listed in SECURITY_MAP C.2; found while building this file. -/
theorem receive_torsion_correct (artifact : MultiArtifact) (compiled : compileAll torsion = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) = torsionRun TlsMpc.X25519.concrete input :=
  TlsMpc.ReceiveField.torsion_correct artifact compiled input

open TlsMpc.FieldDag in
/-- **The `x25519-fast` program outputs (x, z) with RFC 7748's X25519 result = x·z⁻¹**, for any
scalar bits and u (bits supplied as swap bits). **K**: the worker loads `x25519-fast`. The
division x·z⁻¹ happens in C++ (`x25519_fast.h`, masked inversion), which is not modelled.
SECURITY_MAP C.2. -/
theorem x25519Fast_compiled_correct (bits : Nat → Bool) (u : F) (artifact : FieldDag.MultiArtifact)
    (compiled : FieldDag.compileAll X25519Fast.exprs = some artifact) :
    ∃ x z, artifact.outputs.map
        (FieldDag.result (FieldDag.concrete (X25519Fast.assignment bits u)) artifact.nodes) = [x, z] ∧
      X25519.spec bits u = x * X25519.inverse X25519.concrete z :=
  TlsMpc.X25519Fast.compiled_correct bits u artifact compiled

open TlsMpc.FieldDag TlsMpc.X25519 in
/-- **The full X25519 field program computes RFC 7748's X25519.** **M**: only the `emit_mpc`
executable compiles `X25519.expr`; the worker loads `x25519-fast` instead (previously believed
to be on the running path). SECURITY_MAP C.2. -/
theorem x25519_compiled_compute_correct (bits : Nat → Bool) (u : F) (artifact : FieldDag.Artifact)
    (compiled : FieldDag.compile expr = some artifact) :
    FieldDag.result (FieldDag.concrete (assignment bits u)) artifact.nodes artifact.output = spec bits u :=
  TlsMpc.X25519.compiled_compute_correct bits u artifact compiled

open TlsMpc.FieldDag TlsMpc.EdwardsAffine in
/-- **The `edwards-offset-sum` program computes the Montgomery u of the sum** of the initial
point and the signed table entries (one per window). **K** (the non-hinted sealed-sender offset
agreement, `edwards_points.h`). Formulas only (H-GROUP: the group law is proved in `proofs/`, `SecurityMathlib.lean` section 7). Not listed in SECURITY_MAP C.2; found
while building this file. No theorem covers `edwards-prepare`. -/
theorem edwards_offsetSum_eval (input : Nat → F) :
    offsetSum.map (Expr.eval input) =
      (let sum := sumTreeValue ((input 0, input 1) :: (List.range windows).map
          (fun w => (input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1))))
       [(ofNat 1 + sum.2) * inverse (ofNat 1 - sum.2)]) :=
  TlsMpc.EdwardsAffine.offsetSum_eval input

open TlsMpc.FieldDag TlsMpc.EdwardsAffine TlsMpc.EdwardsHinted in
/-- **Hinted window tables are sound:** whatever hints a party supplies, if every link check
holds (`LinkedFrom`), the table entries equal the honest chain from the base. **switch**
(constant-depth programs only). SECURITY_MAP C.2. -/
theorem edwardsHinted_entries_sound (ev : Point → Value) (evE : ε → β)
    (step : Point → List ε × Point) (stepV : Value → List β × Value)
    (hstep : ∀ b, (step b).1.map evE = (stepV (ev b)).1 ∧ ev (step b).2 = (stepV (ev b)).2)
    (b : Point) (rest : List Point) (h : LinkedFrom ev step b rest) :
    (entries step (b :: rest)).map evE = chain stepV (ev b) (rest.length + 1) :=
  TlsMpc.EdwardsHinted.entries_sound ev evE step stepV hstep b rest h

open TlsMpc.FieldDag TlsMpc.EdwardsAffine TlsMpc.EdwardsHinted in
/-- **Each accepted hinted program evaluates to its expressions.** **switch**. SECURITY_MAP
C.2. -/
theorem edwardsHinted_compiled_correct (program : List Expr) (artifact : MultiArtifact)
    (compiled : compileAll program = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) = program.map (Expr.eval input) :=
  TlsMpc.EdwardsHinted.compiled_correct program artifact compiled input

open TlsMpc.Signal TlsMpc.Signal.Pqxdh Std.Tactic.BVDecide in
/-- **PQXDH key derivation equals its specification** (the repository's transcription of the
Signal PQXDH KDF). **K-fn** (Signal session establishment). SECURITY_MAP C.2. -/
theorem pqxdh_deriveCore_specification (dh1 dh2 dh3 oneTime kem : List (BitVec 8)) :
    deriveCore Sha256.concrete dh1 dh2 dh3 oneTime kem = specification dh1 dh2 dh3 oneTime kem :=
  TlsMpc.Signal.Pqxdh.deriveCore_specification dh1 dh2 dh3 oneTime kem

open TlsMpc.Signal TlsMpc.Signal.Symmetric in
/-- **The fast symmetric-ratchet derivation equals the textbook one** for any SHA-256
operations. **K-fn**. SECURITY_MAP C.2. -/
theorem symmetric_deriveFast_correct {B W : Type} (o : Sha256.Ops B W) (chainKey salt : List B) :
    deriveFast o chainKey salt = derive o chainKey salt :=
  TlsMpc.Signal.Symmetric.deriveFast_correct o chainKey salt

open TlsMpc.Signal TlsMpc.Signal.DhRatchet in
/-- **The fast DH-ratchet key material equals the textbook one.** **K-fn**. SECURITY_MAP C.2. -/
theorem dhRatchet_materialFast_correct {B W : Type} (s : Sha256.Ops B W) (root agreement : List B) :
    materialFast s root agreement = material s root agreement :=
  TlsMpc.Signal.DhRatchet.materialFast_correct s root agreement

open TlsMpc.Signal TlsMpc.Signal.SpqrChain in
/-- **The fast SPQR chain key material equals the textbook one.** **K-fn**. SECURITY_MAP C.2. -/
theorem spqrChain_materialFast_correct {B W : Type} (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (key counter : List B) : materialFast s a key counter = material s a key counter :=
  TlsMpc.Signal.SpqrChain.materialFast_correct s a key counter

open TlsMpc.Signal TlsMpc.Signal.Establish Std.Tactic.BVDecide in
/-- **Session-establishment keys equal the independent key formula** `keysSpecification`.
**K-fn** (`establish-session`, `bundle-seal`). SECURITY_MAP C.2. -/
theorem establish_keys_specification (dh1 dh2 dh3 oneTime kem ratchetAgreement : List (BitVec 8)) :
    keys Sha256.concrete dh1 dh2 dh3 oneTime kem ratchetAgreement =
      keysSpecification dh1 dh2 dh3 oneTime kem ratchetAgreement :=
  TlsMpc.Signal.Establish.keys_specification dh1 dh2 dh3 oneTime kem ratchetAgreement

open TlsMpc.Signal TlsMpc.Signal.XEdDsaScalar Std.Tactic.BVDecide in
/-- **The scalar reduction circuit reduces a 64-byte little-endian value mod the group order.**
**K-fn** (XEdDSA). SECURITY_MAP C.2. -/
theorem xeddsa_reduce_bytes_spec (bytes : List (BitVec 8)) (hlen : bytes.length = 64) :
    (reduce concrete bytes).map BitVec.toNat =
      (List.range 32).map (fun i => (decodeLE bytes % order / 2^(i*8)) % 256) :=
  TlsMpc.Signal.XEdDsaScalar.reduce_bytes_spec bytes hlen

open TlsMpc.Signal TlsMpc.Signal.MessageMac Std.Tactic.BVDecide in
/-- **The Signal message MAC check outputs 255 exactly when the received tag equals the
computed tag, else 0** (accept direction included). **K-fn**; composed with `receive-session`'s
status in section 3a (`receiveAccept_session_status_iff`). SECURITY_MAP C.2, C.3. -/
theorem messageMac_verifyMask_value (macKey sender receiver wire : List (BitVec 8)) :
    verifyMask Sha256.concrete ByteAuth.concrete macKey sender receiver wire =
      if tag Sha256.concrete macKey sender receiver (content wire) = receivedTag wire then 255 else 0 :=
  TlsMpc.Signal.MessageMac.verifyMask_value macKey sender receiver wire

open TlsMpc.Signal TlsMpc.Signal.XEdDsa Std.Tactic.BVDecide in
/-- **The XEdDSA scalar-range mask is 255 exactly on canonical top bytes.** **K-fn**.
SECURITY_MAP C.2. -/
theorem xeddsa_scalarMask_spec (last : BitVec 8) :
    scalarMask ByteAuth.concrete last = if (last &&& 127).toNat < 32 then 255 else 0 :=
  TlsMpc.Signal.XEdDsa.scalarMask_spec last

open TlsMpc.Signal TlsMpc.Signal.RelayUpgrade TlsMpc.Signal.RelayEncoding Std.Tactic.BVDecide in
/-- **The authenticated WebSocket upgrade request circuit computes the concrete request.**
**K-fn** (`signal-upgrade(-shared)` has no kernel-level spec). The controller's
`anonymousRequest` has no theorem. SECURITY_MAP C.2. -/
theorem relayUpgrade_request_compiled (passwordBytes : Nat) (raw : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat) (hi : index<8*(request ByteAuth.symbolic passwordBytes raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (request ByteAuth.symbolic passwordBytes raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (request ByteAuth.symbolic passwordBytes raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (request ByteAuth.concrete passwordBytes (raw.map (BVExpr.eval assign)))).getLsbD index :=
  TlsMpc.Signal.RelayUpgrade.compiled_request_correct passwordBytes raw assign index hi

/-! ### 2b. Kernel level: the kernel's outputs under every assignment equal the spec -/

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`tls-update` computes the TLS 1.3 key update**: the next traffic secret and its key and
IV, from the current one. **K**. (`tls-derive`, `tls-verify-finished`, `tls-open-handshake`,
`tls-finish`: section 2c.) SECURITY_MAP C.2. -/
theorem tlsUpdate_spec (assign : BVExpr.Assignment) :
    let block := (ByteCircuit.inputBytes 0 60).map (BVExpr.eval assign)
    let next := TlsKdf.updateTraffic Sha256.concrete (secretOf block)
    tlsUpdate.bytes.map (BVExpr.eval assign) =
      next ++ (TlsKdf.trafficKeys Sha256.concrete next).1 ++ (TlsKdf.trafficKeys Sha256.concrete next).2 :=
  TlsMpc.HybridKernel.tlsUpdate_spec assign

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`tls-seal-ctr` outputs the record header, the AES-CTR ciphertext of the inner plaintext,
and the GCM pad** `E = AES_K(J0)`, for any size and padding. **K** (KeyUpdate, close). The tag
comes from `gcm-tag` (section 6). SECURITY_MAP C.2. -/
theorem tlsSealCtr_spec (kind size padding : Nat) (assign : BVExpr.Assignment) :
    (tlsSealCtr kind size padding).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [TlsRecord.header Gcm.concrete ((TlsRecord.inner Gcm.concrete (inputValue assign 68 size) kind padding).length + 16),
        ctrOf (inputValue assign 0 60) (inputValue assign 60 8)
          (TlsRecord.inner Gcm.concrete (inputValue assign 68 size) kind padding),
        padOf (inputValue assign 0 60) (inputValue assign 60 8)] :=
  TlsMpc.HybridKernel.tlsSealCtr_spec kind size padding assign

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`gcm-tag` outputs pad ⊕ halfA ⊕ halfB.** **K**. SECURITY_MAP C.2. -/
theorem gcmTag_spec (assign : BVExpr.Assignment) :
    gcmTag.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [Aes.addRoundKey Gcm.concrete.aes
        (Aes.addRoundKey Gcm.concrete.aes (inputValue assign 0 16) (inputValue assign 16 16))
        (inputValue assign 32 16)] :=
  TlsMpc.HybridKernel.gcmTag_spec assign

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`gcm-check` outputs 255 iff pad ⊕ halfA ⊕ halfB equals the received tag, else 0**
(accept direction included). **K**. SECURITY_MAP C.2, C.3. -/
theorem gcmCheck_spec (assign : BVExpr.Assignment) :
    gcmCheck.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[if Aes.addRoundKey Gcm.concrete.aes
            (Aes.addRoundKey Gcm.concrete.aes (padOf (inputValue assign 0 60) (inputValue assign 60 8))
              (inputValue assign 68 16))
            (inputValue assign 84 16) = inputValue assign 100 16 then 255 else 0]] :=
  TlsMpc.HybridKernel.gcmCheck_spec assign

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`gcm-key-share` outputs the GHASH key H = AES_K(0¹²⁸) masked by A's 16-byte input.**
**K**. SECURITY_MAP C.2. -/
theorem gcmKeyShare_spec (assign : BVExpr.Assignment) :
    gcmKeyShare.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [Aes.addRoundKey Gcm.concrete.aes
        (Aes.encryptExpanded Gcm.concrete.aes 10 (expandedOf (inputValue assign 0 60)) (Gcm.zeros Gcm.concrete 16))
        (inputValue assign 60 16)] :=
  TlsMpc.HybridKernel.gcmKeyShare_spec assign

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`gcm-multiply` outputs the GF(2¹²⁸) product of two XOR-shared values, masked by A's
input.** **K**. SECURITY_MAP C.2. -/
theorem gcmMultiply_spec (assign : BVExpr.Assignment) :
    gcmMultiply.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [Aes.addRoundKey Gcm.concrete.aes
        (Gcm.concrete.unpack (Ghash.multiply Gcm.concrete.field
          (Gcm.concrete.pack (Aes.addRoundKey Gcm.concrete.aes (inputValue assign 0 16) (inputValue assign 16 16)))
          (Gcm.concrete.pack (Aes.addRoundKey Gcm.concrete.aes (inputValue assign 32 16) (inputValue assign 48 16)))))
        (inputValue assign 64 16)] :=
  TlsMpc.HybridKernel.gcmMultiply_spec assign

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`contact-key` derives the contact's state key from the sum of the two additive shares:**
32 zero bytes, then the first 28 bytes of SHA-256(label ‖ (a + b mod 2²⁵⁵−19)).
Hypotheses: **both shares are below 2²⁵⁵ − 19** (nothing in the kernel checks this). **K**.
SECURITY_MAP C.2. -/
theorem contactKey_spec (assign : BVExpr.Assignment)
    (aBound : ModAdd.leValue (inputValue assign 0 32) < shareModulus)
    (bBound : ModAdd.leValue (inputValue assign 32 32) < shareModulus) :
    contactKey.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [List.replicate 32 0 ++
        (Sha256.hash Sha256.concrete (contactLabel ++ ModAdd.leBytes 32
          ((ModAdd.leValue (inputValue assign 0 32) + ModAdd.leValue (inputValue assign 32 32)) % shareModulus))).take 28] :=
  TlsMpc.HybridKernel.contactKey_spec assign aBound bBound

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`contact-seal` outputs the AES-CTR encryption of the stored contact state under the
contact key and version, and the key's check value.** **K**. Nonce uniqueness is not proved
(T10, section 8). SECURITY_MAP C.2. -/
theorem contactSeal_spec (size : Nat) (assign : BVExpr.Assignment) :
    (contactSeal size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [ctrOf (inputValue assign 0 60) (inputValue assign 60 8) (inputValue assign 68 size),
        checkOf (inputValue assign 0 60)] :=
  TlsMpc.HybridKernel.contactSeal_spec size assign

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`contact-open` outputs the check flag and the decrypted state released only under the
flag.** **K**. SECURITY_MAP C.2. -/
theorem contactOpen_spec (size : Nat) (assign : BVExpr.Assignment) :
    (contactOpen size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[contactMask (inputValue assign 0 60) (inputValue assign (68 + size) 16)],
        ByteAuth.release ByteAuth.concrete (contactMask (inputValue assign 0 60) (inputValue assign (68 + size) 16))
          (ctrOf (inputValue assign 0 60) (inputValue assign 60 8) (inputValue assign 68 size))] :=
  TlsMpc.HybridKernel.contactOpen_spec size assign

open TlsMpc.RecordClass Std.Tactic.BVDecide in
/-- **Opening a size-class record padded with zeros equals opening the exact record, followed
by zeros.** Hypotheses: an expanded AES key (176 bytes), a record of at least 22 bytes, total
below 65536, and the header length field matches. **K** (the class kernels). Depends on
`bv_decide` through `within_value` (section 9). SECURITY_MAP C.2. -/
theorem recordClass_open_padded (state expanded nonce wire : List (BitVec 8)) (high low accepted : BitVec 8) (k : Nat)
    (he : expanded.length = 176) (hn : 22 ≤ wire.length) (hb : wire.length + k < 65536)
    (hs : TlsPrivateSeal.lengthValue high low = wire.length - 5) :
    TlsPostHandshake.core TlsMpc.Signal.Word64.concrete ByteAuth.concrete state
        (openParsed Gcm.concrete ByteAuth.concrete expanded nonce (wire ++ List.replicate k 0) high low accepted) =
      TlsPostHandshake.core TlsMpc.Signal.Word64.concrete ByteAuth.concrete state (exactParsed expanded nonce wire accepted) ++
        List.replicate k 0 :=
  TlsMpc.RecordClass.open_padded state expanded nonce wire high low accepted k he hn hb hs

open TlsMpc.RecordClass Std.Tactic.BVDecide in
/-- **Sealing in a size class encrypts exactly the content (as an application-data record) and
outputs zeros for the class padding.** Hypotheses: expanded key, size bound, length field
matches. **K** (`tls-seal-class`). Depends on `bv_decide` through `within_value` (section 9).
SECURITY_MAP C.2. -/
theorem recordClass_sealCiphertext_padded (expanded nonce content rest : List (BitVec 8)) (high low : BitVec 8)
    (he : expanded.length = 176) (hb : content.length + rest.length + 17 < 65536)
    (hs : TlsPrivateSeal.lengthValue high low = content.length + 17) :
    sealCiphertext Gcm.concrete ByteAuth.concrete expanded nonce (content ++ rest) high low =
      (255, Gcm.ctr Gcm.concrete expanded nonce (TlsRecord.inner Gcm.concrete content 23 0) ++
        List.replicate rest.length 0) :=
  TlsMpc.RecordClass.sealCiphertext_padded expanded nonce content rest high low he hb hs

open TlsMpc.TypedOpenKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`tls-open-application-class` computes its class specification field by field.** **K**.
SECURITY_MAP C.2. -/
theorem typedOpen_class_fields (capacity : Nat) (assign : BVExpr.Assignment) :
    fieldValues (RecordClassKernel.tlsOpenApplicationClass capacity) assign = fields (classSpec capacity assign) :=
  TlsMpc.TypedOpenKernel.class_fields capacity assign

open TlsMpc.TypedOpenKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel Shape lookup lookupFrom pub priv sl) in
/-- **`tls-frame` computes the post-handshake parser core on its inputs.** **K**. SECURITY_MAP
C.2. -/
theorem typedOpen_frame_fields (capacity : Nat) (assign : BVExpr.Assignment) :
    fieldValues (tlsFrame capacity) assign =
      fields (TlsPostHandshake.core Word64.concrete ByteAuth.concrete
        ((lookup (frameInputs capacity) "parser").map (BVExpr.eval assign))
        ((lookup (frameInputs capacity) "parsed").map (BVExpr.eval assign))) :=
  TlsMpc.TypedOpenKernel.frame_fields capacity assign

open TlsMpc.TypedOpenKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel Shape lookup lookupFrom pub priv sl) in
/-- **The pair `tls-open-typed` + `tls-frame` refines the single class kernel:** the handshake
bit is 0 or 255; when it is 0 the typed kernel's fields are the class kernel's plus the parsed
record; and `tls-frame`, run on the same parser and parsed bytes, gives the class kernel's
fields. **K**. SECURITY_MAP C.2. -/
theorem typedOpen_typed_pair_refines (capacity : Nat) (assign frame : BVExpr.Assignment) :
    let bit := BVExpr.eval assign (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed capacity))
    let existing := fieldValues (RecordClassKernel.tlsOpenApplicationClass capacity) assign
    (bit = 0 ∨ bit = 255) ∧
    (bit = 0 → fieldValues (tlsOpenTyped capacity) assign =
      [[0]] ++ existing ++ [(typedParsed capacity).map (BVExpr.eval assign)]) ∧
    ((lookup (frameInputs capacity) "parser").map (BVExpr.eval frame) =
        (lookup (typedInputs capacity) "parser").map (BVExpr.eval assign) →
      (lookup (frameInputs capacity) "parsed").map (BVExpr.eval frame) =
        (typedParsed capacity).map (BVExpr.eval assign) →
      fieldValues (tlsFrame capacity) frame = existing) :=
  TlsMpc.TypedOpenKernel.typed_pair_refines capacity assign frame

open TlsMpc.MlKemFastKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.EstablishKernel (Kernel.values getD_map) in
/-- **`kem-hash` computes the ML-KEM hash stage.** **K**. The kernels' composition into
`MlKem.encapsulate` is NOT proved (MlKemFastProofs header). SECURITY_MAP C.2. -/
theorem kemHash_spec (kyber : Bool) (assign : BVExpr.Assignment) :
    let value := fun name => (lookup hashInputs name).map (BVExpr.eval assign)
    Kernel.values (kemHash kyber) assign =
      MlKemFast.hashStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete kyber
        (value "kyberPrekey") (value "entropyA") (value "entropyB") :=
  TlsMpc.MlKemFastKernel.kemHash_spec kyber assign

open TlsMpc.MlKemFastKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.EstablishKernel (Kernel.values getD_map) in
/-- **`kem-ntt` computes the ML-KEM NTT stage.** **K**. SECURITY_MAP C.2. -/
theorem kemNtt_spec (assign : BVExpr.Assignment) :
    Kernel.values (kemNtt ()) assign =
      [MlKemFast.nttStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete
        ((lookup nttInputs "coins").map (BVExpr.eval assign))] :=
  TlsMpc.MlKemFastKernel.kemNtt_spec assign

open TlsMpc.MlKemFastKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.EstablishKernel (Kernel.values getD_map) in
/-- **`kem-matrix r` computes row r of the ML-KEM matrix stage.** **K**. SECURITY_MAP C.2. -/
theorem kemMatrix_spec (row : Nat) (assign : BVExpr.Assignment) :
    Kernel.values (kemMatrix row) assign =
      MlKemFast.matrixStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete row
        ((lookup matrixInputs "kyberPrekey").map (BVExpr.eval assign)) :=
  TlsMpc.MlKemFastKernel.kemMatrix_spec row assign

open TlsMpc.MlKemFastKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.EstablishKernel (Kernel.values getD_map) in
/-- **`kem-u r` computes row r of the ML-KEM u stage.** **K**. SECURITY_MAP C.2. -/
theorem kemU_spec (row : Nat) (assign : BVExpr.Assignment) :
    let value := fun name => (lookup (uInputs row) name).map (BVExpr.eval assign)
    Kernel.values (kemU row) assign =
      [MlKemFast.uStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete row
        (value s!"row{row}") (value "rhat") (value "coins")] :=
  TlsMpc.MlKemFastKernel.kemU_spec row assign

open TlsMpc.MlKemFastKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.EstablishKernel (Kernel.values getD_map) in
/-- **`kem-v` computes the ML-KEM v stage.** **K**. SECURITY_MAP C.2. -/
theorem kemV_spec (assign : BVExpr.Assignment) :
    let value := fun name => (lookup vInputs name).map (BVExpr.eval assign)
    Kernel.values (kemV ()) assign =
      [MlKemFast.vStage MlKemFast.concrete ByteAuth.concrete Keccak.concrete
        (value "kyberPrekey") (value "rhat") (value "coins") (value "message")] :=
  TlsMpc.MlKemFastKernel.kemV_spec assign

open TlsMpc.MlKemFastKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.EstablishKernel (Kernel.values getD_map) in
/-- **`kem-finish` computes the ML-KEM finish stage** (status, ciphertext, shared secret).
**K**. SECURITY_MAP C.2. -/
theorem kemFinish_spec (kyber : Bool) (assign : BVExpr.Assignment) :
    let get := lookup finishInputs
    let e := BVExpr.eval assign
    Kernel.values (kemFinish kyber) assign =
      MlKemFast.finishStage ByteAuth.concrete Keccak.concrete kyber
        ((get "u0" ++ get "u1" ++ get "u2" ++ get "u3" ++ get "v").map e) ((get "kbar").map e)
        ((get "ok0" ++ get "ok1" ++ get "ok2" ++ get "ok3" ++ get "keyValid").map e) :=
  TlsMpc.MlKemFastKernel.kemFinish_spec kyber assign

open TlsMpc.MlKemFastKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.EstablishKernel (Kernel.values getD_map) in
/-- **`kem-sample` computes the ML-KEM sampling stage.** **M**: `kem-sample` is in no
deployment. SECURITY_MAP C.2. -/
theorem kemSample_spec (assign : BVExpr.Assignment) :
    Kernel.values (kemSample ()) assign =
      MlKemFast.sampleStage MlKemFast.concrete ((lookup sampleInputs "stream").map (BVExpr.eval assign)) :=
  TlsMpc.MlKemFastKernel.kemSample_spec assign

/-! The 13 `receive-*` kernels. Their "spec" is the same `ReceiveFirst` definition on concrete
operations (ReceiveProofs.lean header: "Nothing here is a security statement"). They say the
lowered term is that definition, nothing about what the definition achieves; the one independent
formula is `receive_keys_specification`. All **K**. SECURITY_MAP C.2. -/

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-envelope-point`** = `Establish.part` of the envelope (bytes 4..36). **K**. -/
theorem receive_envelopePoint_spec (size : Nat) (assign : BVExpr.Assignment) :
    values (envelopePoint size) assign =
      [Establish.part ((lookup (envelopeInputs size) "envelope").map (BVExpr.eval assign)) 4 32] :=
  TlsMpc.ReceiveKernel.envelopePoint_spec size assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-unseal-static`** = `ReceiveFirst.unsealStatic` (outputs rearranged). **K**. -/
theorem receive_unsealStatic_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (staticInputs size)
    let e := BVExpr.eval assign
    let out := ReceiveFirst.unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size
      ((get "ourIdentity").map e) ((get "envelope").map e) ((get "agreement").map e)
    values (unsealStatic size) assign = [out.getD 0 [], out.getD 1 [], out.getD 1 [], out.getD 2 []] :=
  TlsMpc.ReceiveKernel.unsealStatic_spec size assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-unseal-message`** = `ReceiveFirst.unsealMessage`. **K**. -/
theorem receive_unsealMessage_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (messageInputs size)
    let e := BVExpr.eval assign
    values (unsealMessage size) assign =
      ReceiveFirst.unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size ((get "envelope").map e)
        ((get "staticValid").map e) ((get "chain").map e) ((get "agreement").map e) :=
  TlsMpc.ReceiveKernel.unsealMessage_spec size assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-content-shape`** = `ReceiveFirst.contentShape`. **K**. -/
theorem receive_contentShape_spec (size cert : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (contentInputs size)
    let e := BVExpr.eval assign
    values (contentShape size cert) assign =
      ReceiveFirst.contentShape ByteAuth.concrete size cert ((get "content").map e) ((get "valid").map e) :=
  TlsMpc.ReceiveKernel.contentShape_spec size cert assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-content`** = `ReceiveFirst.contentParts`. **K**. -/
theorem receive_content_spec (size cert : Nat) (hint : Bool) (assign : BVExpr.Assignment) :
    let get := lookup (contentInputs size)
    let e := BVExpr.eval assign
    values (content size cert hint) assign =
      ReceiveFirst.contentParts ByteAuth.concrete size cert hint ((get "content").map e) ((get "valid").map e) :=
  TlsMpc.ReceiveKernel.content_spec size cert hint assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-certificate`** = `ReceiveFirst.certificate` (outputs rearranged). **K**. -/
theorem receive_certificate_spec (cert : Nat) (c : ReceiveFirst.CertShape) (assign : BVExpr.Assignment) :
    let get := lookup (certificateInputs cert c)
    let e := BVExpr.eval assign
    let out := ReceiveFirst.certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete cert c
      ((get "certificate").map e) ((get "valid").map e) ((get "senderIdentity").map e) ((get "signer").map e)
      ((get "now").map e) ((get "serverX").map e) ((get "serverY").map e)
    values (certificate cert c) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [],
        (out.getD 3 []).drop 32] :=
  TlsMpc.ReceiveKernel.certificate_spec cert c assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-certificate-verified`** = `ReceiveFirst.certificateVerified`. **K**. What status
255 implies: `receiveAccept_certificateVerified_iff` (section 3a). -/
theorem receive_certificateVerified_spec (assign : BVExpr.Assignment) :
    let get := lookup verifiedInputs
    let e := BVExpr.eval assign
    values (certificateVerified ()) assign =
      ReceiveFirst.certificateVerified ByteAuth.concrete ((get "certificateValid").map e) ((get "signature").map e)
        ((get "serverValid").map e) ((get "rx").map e) ((get "ry").map e) :=
  TlsMpc.ReceiveKernel.certificateVerified_spec assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-prekey-shape`** = `ReceiveFirst.prekeyShape`. **K**. -/
theorem receive_prekeyShape_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (shapeInputs size)
    let e := BVExpr.eval assign
    values (prekeyShape size) assign =
      ReceiveFirst.prekeyShape ByteAuth.concrete size ((get "message").map e) ((get "valid").map e) :=
  TlsMpc.ReceiveKernel.prekeyShape_spec size assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-prekey-open`** = `ReceiveFirst.prekeyOpen`. **K**. -/
theorem receive_prekeyOpen_spec (size : Nat) (p : ReceiveFirst.PreKeyShape) (assign : BVExpr.Assignment) :
    let get := lookup (openInputs size)
    let e := BVExpr.eval assign
    values (prekeyOpen size p) assign =
      ReceiveFirst.prekeyOpen ByteAuth.concrete p size ((get "message").map e) ((get "valid").map e)
        ((get "messageType").map e) ((get "senderIdentity").map e) :=
  TlsMpc.ReceiveKernel.prekeyOpen_spec size p assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-signal-shape`** = `ReceiveFirst.signalShape`. **K**. -/
theorem receive_signalShape_spec (size : Nat) (p : ReceiveFirst.PreKeyShape) (assign : BVExpr.Assignment) :
    let get := lookup (shapeInputs size)
    let e := BVExpr.eval assign
    values (signalShape size p) assign =
      ReceiveFirst.signalShape ByteAuth.concrete p size ((get "message").map e) ((get "valid").map e) :=
  TlsMpc.ReceiveKernel.signalShape_spec size p assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-session`** = `ReceiveFirst.session` (first four outputs). **K**. Status 255
iff the message MAC verified and the other checks passed: `receiveAccept_session_status_iff`
(section 3a). -/
theorem receive_session_spec (cert size : Nat) (p : ReceiveFirst.PreKeyShape) (q : ReceiveFirst.SignalShape) (jump : Nat)
    (assign : BVExpr.Assignment) :
    let get := lookup (sessionInputs cert size (p.oneTime != 0))
    let e := BVExpr.eval assign
    let out := ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump
        ((get "message").map e)
        ((get "prekeyValid").map e ++ (get "verified").map e) ((get "senderIdentity").map e) ((get "ourIdentity").map e)
        ((get "localAddress").map e) ((get "uuid").map e) ((get "deviceId").map e) ((get "dh1").map e)
        ((get "dh2").map e) ((get "dh3").map e) ((get "dh4").map e) ((get "kemSecret").map e)
        ((get "receiveAgreement").map e) ((get "sendAgreement").map e) ((get "ratchetPublic").map e)
        ((get "baseValid").map e) ((get "torsionX").map e) ((get "torsionY").map e) ((get "certificate").map e)
        ((get "accessKey").map e) ((get "requestId").map e)
    values (session cert size p q jump) assign = [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 []] :=
  TlsMpc.ReceiveKernel.session_spec cert size p q jump assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-text`** = `ReceiveFirst.text`. **K**. Its `_rejects` lemma and what it opens:
`receiveAcceptText_text_*` (section 3a). -/
theorem receive_text_spec (ciphertext capacity : Nat) (assign : BVExpr.Assignment) :
    let out := ReceiveFirst.text ByteAuth.concrete capacity
        ((lookup (textInputs ciphertext) "plaintext").map (BVExpr.eval assign))
    values (text ciphertext capacity) assign = [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 []] :=
  TlsMpc.ReceiveKernel.text_spec ciphertext capacity assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
/-- **`receive-access-key`** = `ReceiveFirst.withAccessKey`. **K**. -/
theorem receive_accessKey_spec (cert ciphertext offset : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (accessKeyInputs cert ciphertext)
    let e := BVExpr.eval assign
    let out := ReceiveFirst.withAccessKey Aes.concrete ByteAuth.concrete cert offset ((get "conversation").map e)
        ((get "plaintext").map e)
    values (accessKey cert ciphertext offset) assign = [out.getD 0 [], out.getD 1 []] :=
  TlsMpc.ReceiveKernel.accessKey_spec cert ciphertext offset assign

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **The receive key derivation equals the independent PQXDH + ratchet key formula.** **K-fn**
(inside `receive-session`). SECURITY_MAP C.2. -/
theorem receive_keys_specification (dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement : List (BitVec 8)) :
    ReceiveFirst.keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement =
      keysSpecification dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement :=
  TlsMpc.ReceiveKernel.keys_specification dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement

open TlsMpc.EstablishKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
/-- **`establish-challenges`** computes the two XEdDSA challenges (signed prekey, Kyber prekey).
**K**. SECURITY_MAP C.2. -/
theorem establishChallenges_spec (assign : BVExpr.Assignment) :
    let value := fun name => (lookup challengeInputs name).map (BVExpr.eval assign)
    let run := fun (tag : Nat) (signature key : String) =>
      Establish.challenge ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete tag
        (value signature) (value "identityX") (value "identityY") (value key)
    Kernel.values establishChallenges assign =
      [(run 5 "signedPrekeySignature" "signedPrekey").take 1, (run 5 "signedPrekeySignature" "signedPrekey").drop 1,
        (value "signedPrekeySignature").drop 32,
        (run 8 "kyberPrekeySignature" "kyberPrekey").take 1, (run 8 "kyberPrekeySignature" "kyberPrekey").drop 1,
        (value "kyberPrekeySignature").drop 32] :=
  TlsMpc.EstablishKernel.establishChallenges_spec assign

open TlsMpc.EstablishKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
/-- **`establish-verified`** = `Establish.verified` of the signature checks. **K**. -/
theorem establishVerified_spec (assign : BVExpr.Assignment) :
    let value := fun name => (lookup verifiedInputs name).map (BVExpr.eval assign)
    Kernel.values establishVerified assign =
      [[Establish.verified ByteAuth.concrete (value "signedPrekeySignature") (value "kyberPrekeySignature")
        (value "identityValid") (value "ecRx") (value "ecRy") (value "pqRx") (value "pqRy")]] :=
  TlsMpc.EstablishKernel.establishVerified_spec assign

open TlsMpc.EstablishKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
/-- **`establish-session`** = `Establish.establish`. **K**. SECURITY_MAP C.2. -/
theorem establishSession_spec (cert : Nat) (withOneTime : Bool) (assign : BVExpr.Assignment) :
    let get := lookup (sessionInputs cert withOneTime)
    let e := BVExpr.eval assign
    Kernel.values (establishSession cert withOneTime) assign =
      Establish.establish Sha256.concrete ByteAuth.concrete 80 ((get "verified" ++ get "kemStatus").map e)
        ((get "dh1").map e) ((get "dh2").map e) ((get "dh3").map e) ((get "dh4").map e) ((get "kemSecret").map e)
        ((get "ratchetAgreement").map e) ((get "basePublic").map e) ((get "ratchetPublic").map e)
        ((get "senderPublic").map e) ((get "identityKey").map e) ((get "signedPrekey").map e)
        ((get "certificate").map e) ((get "uuid").map e) ((get "accessKey").map e) ((get "requestId").map e)
        ((get "deviceId").map e) ((get "registrationId").map e) ((get "localRegistrationId").map e)
        ((if withOneTime then get "oneTimePrekeyId" else HybridKernel.zeros 4).map e)
        ((get "signedPrekeyId").map e) ((get "kyberPrekeyId").map e) ((get "kemCiphertext").map e) :=
  TlsMpc.EstablishKernel.establishSession_spec cert withOneTime assign

open TlsMpc.EstablishKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
/-- **`establish-seal`** = `Establish.sealMessage` (rearranged). **M**: `establish-seal` is in
no deployment (replaced by `bundle-seal`). SECURITY_MAP C.2. -/
theorem establishSeal_spec (cert : Nat) (withOneTime : Bool) (counterWidth previousWidth epochWidth indexWidth : Nat)
    (assign : BVExpr.Assignment) :
    let get := lookup (sealInputs cert)
    let e := BVExpr.eval assign
    let record := get "conversation"
    let text := PrivateTextNotification.build Sha256.symbolic Varint64.symbolic ByteAuth.symbolic (get "text")
    let out := Establish.sealMessage Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete withOneTime
      ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩ 80 ((sl record cert 262).map e)
      ((sl record (cert + 262) 57).map e) ((get "pending").map e) ((sl record 0 cert).map e)
      ((get "localAddress").map e) (text.map e) ((get "ephemeralPublic").map e) ((get "senderPublic").map e)
      ((get "ephemeralAgreement").map e) ((get "staticAgreement").map e)
    Kernel.values (establishSeal cert withOneTime counterWidth previousWidth epochWidth indexWidth) assign =
      [out.getD 0 [], (sl record 0 cert).map e ++ out.getD 1 [] ++ (sl record (cert + 262) 57).map e,
        (sl text 82 8).map e, out.getD 2 []] :=
  TlsMpc.EstablishKernel.establishSeal_spec cert withOneTime counterWidth previousWidth epochWidth indexWidth assign

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-shape`** = `BundleResponse.shape` of the response body. **K**. -/
theorem bundleShape_spec (size : Nat) (assign : BVExpr.Assignment) :
    values (bundleShape size) assign =
      BundleResponse.shape ByteAuth.concrete ((lookup (shapeInputs size) "body").map (BVExpr.eval assign)) :=
  TlsMpc.BundleKernel.bundleShape_spec size assign

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-rebind`** = `BundleResponse.rebind`. **K**. -/
theorem bundleRebind_spec (assign : BVExpr.Assignment) :
    let get := lookup bindInputs
    let e := BVExpr.eval assign
    values (bundleRebind ()) assign =
      BundleResponse.rebind ByteAuth.concrete ((get "record").map e) ((get "valid").map e) ((get "verified").map e)
        ((get "identityKey").map e) :=
  TlsMpc.BundleKernel.bundleRebind_spec assign

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-seal`** = `Establish.sealMessage` (rearranged). **K**. The value of
`Establish.sealMessage` and of the kernel: `establishSeal_sealMessage_value`,
`establishSeal_bundleSeal_value` (section 2c). -/
theorem bundleSeal_spec (cert : Nat) (withOneTime : Bool)
    (content counterWidth previousWidth epochWidth indexWidth : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (sealInputs cert content)
    let e := BVExpr.eval assign
    let record := get "conversation"
    let out := Establish.sealMessage Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete withOneTime
      ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩ content ((sl record cert 262).map e)
      ((sl record (cert + 262) 57).map e) ((get "pending").map e) ((sl record 0 cert).map e)
      ((get "localAddress").map e) ((get "text").map e) ((get "ephemeralPublic").map e) ((get "senderPublic").map e)
      ((get "ephemeralAgreement").map e) ((get "staticAgreement").map e)
    values (bundleSeal cert withOneTime content counterWidth previousWidth epochWidth indexWidth) assign =
      [out.getD 0 [], (sl record 0 cert).map e ++ (out.getD 1 []).take 262 ++ (sl record (cert + 262) 57).map e,
        (sl (get "text") (2 + content) 8).map e, out.getD 2 []] :=
  TlsMpc.BundleKernel.bundleSeal_spec cert withOneTime content counterWidth previousWidth epochWidth indexWidth assign

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-device`** = `BundleResponse.device`. **M**: `bundle-device` was replaced by
`bundle-item`, which has no kernel-level spec. SECURITY_MAP C.2. -/
theorem bundleDevice_spec (size start : Nat) (w : BundleResponse.Widths) (assign : BVExpr.Assignment) :
    let out := BundleResponse.device ByteAuth.concrete size start w
      ((lookup (shapeInputs size) "body").map (BVExpr.eval assign))
    values (bundleDevice size start w) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) :=
  TlsMpc.BundleKernel.bundleDevice_spec size start w assign

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup sl) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-bind`** = `BundleResponse.bind`. **M**: replaced by `bundle-rebind`. -/
theorem bundleBind_spec (assign : BVExpr.Assignment) :
    let get := lookup bindInputs
    let e := BVExpr.eval assign
    values (bundleBind ()) assign =
      BundleResponse.bind ByteAuth.concrete ((get "record").map e) ((get "valid").map e) ((get "verified").map e)
        ((get "identityKey").map e) :=
  TlsMpc.BundleKernel.bundleBind_spec assign

open TlsMpc.CeremonyKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`ceremony-secrets`** = `Ceremony.secrets` (password and recovery secrets from both
parties' seeds, masked per party). **ceremony**. SECURITY_MAP C.2. -/
theorem ceremonySecrets_spec (assign : BVExpr.Assignment) :
    let get := lookup secretsInputs
    let e := BVExpr.eval assign
    values (ceremonySecrets ()) assign =
      Ceremony.secrets ByteAuth.concrete ((get "seedA").map e) ((get "seedB").map e) ((get "maskA").map e)
        ((get "maskB").map e) ((get "recoveryA").map e) ((get "recoveryB").map e) :=
  TlsMpc.CeremonyKernel.ceremonySecrets_spec assign

open TlsMpc.CeremonyKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`ceremony-register-ctr`'s plaintext** = the register frame with the secrets filled into
their slots and masked. Plaintext only (the encryption is not covered). **ceremony**.
SECURITY_MAP C.2. -/
theorem registerPlaintext_spec (size payloadAt authAt tail recoveryAt : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (registerInputs size tail)
    let e := BVExpr.eval assign
    (registerPlaintext size payloadAt authAt tail recoveryAt).map e =
      Ceremony.fill ByteAuth.concrete ((get "frame").map e) ((get "mask").map e) payloadAt
        (Ceremony.registerSlots ByteAuth.concrete ((get "secrets").map e) tail authAt recoveryAt) :=
  TlsMpc.CeremonyKernel.registerPlaintext_spec size payloadAt authAt tail recoveryAt assign

open TlsMpc.Signal TlsMpc.Signal.ChainSend Std.Tactic.BVDecide in
/-- **The chain-key send core equals its specification** (16+4-byte key/counter lengths). **M**:
about `ChainSend.sealCore`, a sibling that `signal-seal-official`/`-built` never call; those
kernels recompose `acceptedMask`, `prepare`, `boundSeal`, `selectState` (SECURITY_MAP C.2). -/
theorem chainSend_sealCore_concrete_correct (shape : Serialization.Shape) (version present : BitVec 8)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List (BitVec 8))
    (hkey : chainKey.length = 32) (hcounter : counter.length = 4) :
    sealCore Aes.concrete Sha256.concrete ByteAuth.concrete shape version present
      counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses =
      spec shape version present counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses :=
  TlsMpc.Signal.ChainSend.sealCore_concrete_correct shape version present counter previous ratchet chainKey pqKey
    sender receiver plaintext pq addresses hkey hcounter

open TlsMpc.Signal TlsMpc.Signal.SpqrSend Std.Tactic.BVDecide in
/-- **The SPQR send core equals its specification.** **M**: sibling `sealCore`, not called by the
deployed seal kernels (SECURITY_MAP C.2). -/
theorem spqrSend_sealCore_concrete_correct (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (i : Input (BitVec 8))
    (hkey : i.chainKey.length = 32) (hcounter : i.counter.length = 4)
    (hpkey : i.pqChainKey.length = 32) (hpcounter : i.pqCounter.length = 4) :
    sealCore Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete shape pqShape i = spec shape pqShape i :=
  TlsMpc.Signal.SpqrSend.sealCore_concrete_correct shape pqShape i hkey hcounter hpkey hpcounter

/-! ### 2c. Kernel level, the kernels that had no spec (TlsMpc/KernelSpecs/*.lean)

Same form as 2b: on every input assignment the kernel's outputs equal the reference function on
the values of its input fields. Unless an entry says otherwise the reference is the kernel's own
composition on concrete operations (as for the `receive-*` kernels), not an independent standard.
All **K**. -/

open TlsMpc.KernelSpecs Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-request-ctr` seals the public frame with the contact's UUID, base64 access key and
space-padded device and registration ids inserted (XORed with the WebSocket mask) at their
slots**: outputs `[valid]`, the record header, the CTR ciphertext released under `valid`, and the
pad. **K** (wire). SECURITY_MAP C.2, T7(a). -/
theorem signalRequestCtr_spec (cert size uuidAt keyAt deviceAt registrationAt : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (signalRequestInputs cert size) name).map (BVExpr.eval assign)
    let slots := signalRequestSlots cert uuidAt keyAt deviceAt registrationAt (get "conversation")
    (HybridKernel.signalRequestCtr cert size uuidAt keyAt deviceAt registrationAt).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (insertSlots ByteAuth.concrete 0 (get "frame") (get "mask") 8 slots.2) slots.1 :=
  TlsMpc.KernelSpecs.signalRequestCtr_spec cert size uuidAt keyAt deviceAt registrationAt assign

open TlsMpc.KernelSpecs Std.Tactic.BVDecide TlsMpc.Signal in
/-- **A refused `signal-request-ctr` opens an all-zero ciphertext.** **K**. -/
theorem signalRequestCtr_rejects (cert size uuidAt keyAt deviceAt registrationAt : Nat) (assign : BVExpr.Assignment)
    (refused : ((HybridKernel.signalRequestCtr cert size uuidAt keyAt deviceAt registrationAt).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((HybridKernel.signalRequestCtr cert size uuidAt keyAt deviceAt registrationAt).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 2 [], byte = 0 :=
  TlsMpc.KernelSpecs.signalRequestCtr_rejects cert size uuidAt keyAt deviceAt registrationAt assign refused

open TlsMpc.KernelSpecs Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-fetch-ctr` seals the frame with the contact's UUID and base64 access key from one
record inserted; valid when the record is live.** **K** (wire). T7(a). -/
theorem bundleFetchCtr_spec (size payloadAt uuidAt keyAt : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (fetchInputs size) name).map (BVExpr.eval assign)
    (BundleKernel.bundleFetchCtr size payloadAt uuidAt keyAt).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (insertSlots ByteAuth.concrete 0 (get "frame") (get "mask") payloadAt
          [(uuidAt, RelayEncoding.uuid ByteAuth.concrete (((get "record").drop 262).take 16)),
            (keyAt, RelayEncoding.base64 ByteAuth.concrete (((get "record").drop 278).take 16))])
        (liveValue (get "record")) :=
  TlsMpc.KernelSpecs.bundleFetchCtr_spec size payloadAt uuidAt keyAt assign

open TlsMpc.KernelSpecs Std.Tactic.BVDecide TlsMpc.Signal in
/-- **A refused `bundle-fetch-ctr` opens an all-zero ciphertext.** **K**. -/
theorem bundleFetchCtr_rejects (size payloadAt uuidAt keyAt : Nat) (assign : BVExpr.Assignment)
    (refused : ((BundleKernel.bundleFetchCtr size payloadAt uuidAt keyAt).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((BundleKernel.bundleFetchCtr size payloadAt uuidAt keyAt).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 2 [], byte = 0 :=
  TlsMpc.KernelSpecs.bundleFetchCtr_rejects size payloadAt uuidAt keyAt assign refused

open TlsMpc.KernelSpecs Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-request-ctr` seals the frame with the first record's UUID and access key and
every device's padded ids inserted; valid when every device's record is live and its numbers
fit.** **K** (wire). T7(a). -/
theorem bundleRequestCtr_spec (size payloadAt uuidAt keyAt : Nat) (devices : List (Nat × Nat))
    (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (requestInputsOf size devices.length) name).map (BVExpr.eval assign)
    let value := bundleRequestValue (get "records") uuidAt keyAt devices
    (BundleKernel.bundleRequestCtr size payloadAt uuidAt keyAt devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (insertSlots ByteAuth.concrete 0 (get "frame") (get "mask") payloadAt value.2) value.1 :=
  TlsMpc.KernelSpecs.bundleRequestCtr_spec size payloadAt uuidAt keyAt devices assign

open TlsMpc.KernelSpecs Std.Tactic.BVDecide TlsMpc.Signal in
/-- **A refused `bundle-request-ctr` opens an all-zero ciphertext.** **K**. -/
theorem bundleRequestCtr_rejects (size payloadAt uuidAt keyAt : Nat) (devices : List (Nat × Nat))
    (assign : BVExpr.Assignment)
    (refused : ((BundleKernel.bundleRequestCtr size payloadAt uuidAt keyAt devices).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((BundleKernel.bundleRequestCtr size payloadAt uuidAt keyAt devices).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 2 [], byte = 0 :=
  TlsMpc.KernelSpecs.bundleRequestCtr_rejects size payloadAt uuidAt keyAt devices assign refused

open TlsMpc.KernelSpecs Std.Tactic.BVDecide in
/-- **Where the frame built in the clear is zero, the inserted byte is the slot byte XOR the
WebSocket mask byte** (the first slot covering the index). Value level. **K** (with the specs
above). -/
theorem insertSlots_inside_zero (frame mask : List (BitVec 8)) (payloadAt : Nat)
    (before : List (Nat × List (BitVec 8))) (start : Nat) (bytes : List (BitVec 8)) (after : List (Nat × List (BitVec 8)))
    (i : Nat) (hi : i < frame.length) (blank : frame[i] = 0)
    (earlier : ∀ slot ∈ before, ¬ (slot.1 ≤ i ∧ i < slot.1 + slot.2.length))
    (lo : start ≤ i) (up : i < start + bytes.length) :
    (insertSlots ByteAuth.concrete 0 frame mask payloadAt (before ++ (start, bytes) :: after))[i]'(by
        simpa [insertSlots] using hi) =
      bytes.getD (i - start) 0 ^^^ mask.getD ((i - payloadAt) % 4) 0 :=
  TlsMpc.KernelSpecs.insertSlots_inside_zero frame mask payloadAt before start bytes after i hi blank earlier lo up

open TlsMpc.KernelSpecs.SealFixed Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-seal-official` / `signal-seal-built` compute their composition of
`SpqrSend.acceptedMask`, `SpqrSend.prepare`, `SealedSenderV1.boundSeal`, `TlsProviderGate.gate`
and `ChainSend.selectState` on concrete values** (status, next record, timestamp, envelope).
**K** (wire). The value of `boundSeal` and of the whole kernel: `boundSeal_value`,
`signalSeal_value` below. SECURITY_MAP C.2. -/
theorem signalSealBuilt_spec (cert counterWidth previousWidth epochWidth indexWidth classes : Nat) (official : Bool)
    (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (sealInputs cert classes official) name).map (BVExpr.eval assign)
    (HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes official).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealFixedWith Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete 0
        cert counterWidth previousWidth epochWidth indexWidth (contentBytes classes official)
        (get "conversation") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
        (get "staticAgreement") :=
  TlsMpc.KernelSpecs.SealFixed.signalSealBuilt_spec cert counterWidth previousWidth epochWidth indexWidth classes
    official assign

open TlsMpc.KernelSpecs.SealValue TlsMpc.KernelSpecs.SealValue.Reference TlsMpc.Signal in
/-- **`SealedSenderV1.sealCore` is sealed sender v1 on concrete values:** it equals
`Reference.sealV1`, a transcription of libsignal's sealed-sender v1 encryption (not machine-linked
to libsignal, section 8) (`TlsMpc/KernelSpecs/SealValue.lean`). **K-fn**. T7(b). -/
theorem sealCore_value (recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List (BitVec 8))
    (he : ephemeralPublic.length < 2 ^ 32) (hs : senderPublic.length < 2 ^ 32)
    (hc : certificate.length < 2 ^ 32) (hi : inner.length < 2 ^ 32) :
    SealedSenderV1.sealCore Aes.concrete Sha256.concrete ByteAuth.concrete recipient ephemeralPublic senderPublic
        ephemeralDh staticDh certificate inner =
      sealV1 recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner :=
  TlsMpc.KernelSpecs.SealValue.sealCore_value recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate
    inner he hs hc hi

open TlsMpc.KernelSpecs.SealValue TlsMpc.KernelSpecs.SealValue.Reference TlsMpc.Signal in
/-- **What `boundSeal` produces:** status 255 and sealed sender v1 (`Reference.sealV1`) of `inner`
when both agreements are nonzero and the computed sender key is the stored one; otherwise status 0
and as many zero bytes. **K-fn**. T7(b). -/
theorem boundSeal_value (recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner
    expectedSender : List (BitVec 8))
    (he : ephemeralPublic.length < 2 ^ 32) (hs : senderPublic.length < 2 ^ 32)
    (hc : certificate.length < 2 ^ 32) (hi : inner.length < 2 ^ 32) :
    SealedSenderV1.boundSeal Aes.concrete Sha256.concrete ByteAuth.concrete recipient ephemeralPublic senderPublic
        ephemeralDh staticDh certificate inner expectedSender =
      if boundAccepted ephemeralDh staticDh senderPublic expectedSender then
        255 :: sealV1 recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner
      else 0 :: List.replicate
        (sealV1 recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner).length 0 :=
  TlsMpc.KernelSpecs.SealValue.boundSeal_value recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate
    inner expectedSender he hs hc hi

open TlsMpc.KernelSpecs.SealFixed TlsMpc.KernelSpecs.SealSend Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-seal-official` / `signal-seal-built` on every input assignment:** the four outputs
(status, conversation record, timestamp, envelope) are `sealValue` of the input fields: on accepted
inputs the envelope is sealed sender v1 of the Signal message of the reference send step
`SpqrSend.canonical` on the stored state, and the record carries the advanced ratchet state;
otherwise status 0, an all-zero envelope and the old ratchet state
(`TlsMpc/KernelSpecs/SealSend.lean`). **K**. T7(b). -/
theorem signalSeal_value (cert counterWidth previousWidth epochWidth indexWidth classes : Nat) (official : Bool)
    (assign : BVExpr.Assignment)
    (hbound : cert + contentBytes classes official + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 31) :
    let get := fun name => (lookup (sealInputs cert classes official) name).map (BVExpr.eval assign)
    (HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes official).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealValue cert counterWidth previousWidth epochWidth indexWidth (contentBytes classes official)
        (get "conversation") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
        (get "staticAgreement") :=
  TlsMpc.KernelSpecs.SealSend.signalSeal_value cert counterWidth previousWidth epochWidth indexWidth classes official
    assign hbound

open TlsMpc.KernelSpecs.SealFixed TlsMpc.KernelSpecs.SealSend TlsMpc.KernelSpecs.SealValue.Reference TlsMpc.Signal in
/-- **An accepted seal (opened status 255):** the reference send step accepts, both agreements and
the sender key check pass, the text is valid, the stored record is the advanced one, and the opened
envelope is sealed sender v1 of the reference send step's Signal message. **K**. T7(b). -/
theorem sealValue_accepted (cert counterWidth previousWidth epochWidth indexWidth content : Nat)
    (record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement : List (BitVec 8))
    (opened : (sealValue cert counterWidth previousWidth epochWidth indexWidth content record text ephemeralPublic
      senderPublic ephemeralAgreement staticAgreement).getD 0 [] = [255]) :
    let shape : Serialization.Shape := ⟨counterWidth, previousWidth, false⟩
    let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 1, false⟩
    let certificate := (record.drop 0).take cert
    let staged := stagedOf ((record.drop cert).take (182 + 80)) text
    let i := inputOf 0 staged text content
    let p := SpqrSend.canonical shape pqShape i
    SpqrSend.accepted shape pqShape i ∧
      boundAccepted ephemeralAgreement staticAgreement senderPublic i.sender ∧ text.getD 0 0 = 255 ∧
      (sealValue cert counterWidth previousWidth epochWidth indexWidth content record text ephemeralPublic
        senderPublic ephemeralAgreement staticAgreement).getD 1 [] = advancedRecord cert record staged p ∧
      (sealValue cert counterWidth previousWidth epochWidth indexWidth content record text ephemeralPublic
        senderPublic ephemeralAgreement staticAgreement).getD 3 [] =
        sealV1 i.receiver ephemeralPublic senderPublic ephemeralAgreement staticAgreement certificate p.wire :=
  TlsMpc.KernelSpecs.SealSend.sealValue_accepted cert counterWidth previousWidth epochWidth indexWidth content record
    text ephemeralPublic senderPublic ephemeralAgreement staticAgreement opened

/-! `bundle-seal` (a device refresh's first message to a new session) and `establish-session`, by
value (`TlsMpc/KernelSpecs/{EstablishSealValue, EstablishFirstMessage}.lean`): the PreKey message,
its sealed-sender envelope against `Reference` transcriptions, the session keys. **K** / **K-fn**.
T7(b). -/

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishSeal TlsMpc.KernelSpecs.EstablishSeal.Reference TlsMpc.KernelSpecs.SealValue.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
/-- `EstablishSeal.preKeyMessage_value`. -/
theorem establishSeal_preKeyMessage_value (withOneTime : Bool) (version : Byte) (pending identity signal : List Byte)
    (hp : pending.length < 2 ^ 32) (hi : identity.length < 2 ^ 32) (hs : signal.length < 2 ^ 32) :
    Establish.preKeyMessage Sha256.concrete ByteAuth.concrete withOneTime version pending identity signal =
      preKeySignalMessage varint5 version (u32BE (Establish.part pending 0 4))
        (if withOneTime then some (u32BE (Establish.part pending 4 4)) else none)
        (u32BE (Establish.part pending 8 4)) (u32BE (Establish.part pending 12 4))
        (pending.drop 48) (Establish.part pending 16 32) identity signal :=
  TlsMpc.KernelSpecs.EstablishSeal.preKeyMessage_value withOneTime version pending identity signal hp hi hs

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishSeal TlsMpc.KernelSpecs.EstablishSeal.Reference TlsMpc.KernelSpecs.SealValue.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
/-- **`Establish.sealedSender` is sealed sender v1 with message type `kind`.** -/
theorem establishSeal_sealedSender_value (kind : Nat) (hk : kind < 128)
    (recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List Byte)
    (he : ephemeralPublic.length < 2 ^ 32) (hs : senderPublic.length < 2 ^ 32)
    (hc : certificate.length < 2 ^ 32) (hi : inner.length < 2 ^ 32) :
    Establish.sealedSender Aes.concrete Sha256.concrete ByteAuth.concrete kind recipient ephemeralPublic senderPublic
        ephemeralDh staticDh certificate inner =
      sealV1Typed kind recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner :=
  TlsMpc.KernelSpecs.EstablishSeal.sealedSender_value kind hk recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner he hs hc hi

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishSeal TlsMpc.KernelSpecs.EstablishSeal.Reference TlsMpc.KernelSpecs.SealValue.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
/-- **`Establish.sealMessage` on concrete values** (the body of `bundle-seal` and `establish-seal`). -/
theorem establishSeal_sealMessage_value (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (size : Nat) (session metadata pending certificate localAddress text ephemeralPublic senderPublic
      ephemeralAgreement staticAgreement : List Byte)
    (hsession : session.length = 262) (hchunk : pqShape.hasChunk = false)
    (hbound : pending.length + certificate.length + localAddress.length + size + shape.counterWidth +
      shape.previousWidth + pqShape.epochWidth + pqShape.indexWidth < 2 ^ 31)
    (he : ephemeralPublic.length < 2 ^ 32) (hs : senderPublic.length < 2 ^ 32) :
    Establish.sealMessage Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete withOneTime shape pqShape
        size session metadata pending certificate localAddress text ephemeralPublic senderPublic ephemeralAgreement
        staticAgreement =
      sealMessageValue withOneTime shape pqShape size session metadata pending certificate localAddress text
        ephemeralPublic senderPublic ephemeralAgreement staticAgreement :=
  TlsMpc.KernelSpecs.EstablishSeal.sealMessage_value withOneTime shape pqShape size session metadata pending certificate localAddress text ephemeralPublic senderPublic ephemeralAgreement staticAgreement hsession hchunk hbound he hs

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishSeal TlsMpc.KernelSpecs.EstablishSeal.Reference TlsMpc.KernelSpecs.SealValue.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-seal` on every input assignment**: its four outputs (status, conversation record,
timestamp, envelope) are `sealMessageValue` of the values of its input fields, the record framed by
the stored certificate and metadata. The only hypothesis bounds the public parameters. -/
theorem establishSeal_bundleSeal_value (cert : Nat) (withOneTime : Bool) (content counterWidth previousWidth epochWidth indexWidth : Nat)
    (assign : BVExpr.Assignment)
    (hbound : cert + content + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 30) :
    let get := fun name => (lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval assign)
    let record := get "conversation"
    let out := sealMessageValue withOneTime ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩
      content ((record.drop cert).take 262) ((record.drop (cert + 262)).take 57) (get "pending")
      ((record.drop 0).take cert) (get "localAddress") (get "text") (get "ephemeralPublic") (get "senderPublic")
      (get "ephemeralAgreement") (get "staticAgreement")
    ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth epochWidth
        indexWidth) assign =
      [out.getD 0 [], (record.drop 0).take cert ++ (out.getD 1 []).take 262 ++ (record.drop (cert + 262)).take 57,
        ((get "text").drop (2 + content)).take 8, out.getD 2 []] :=
  TlsMpc.KernelSpecs.EstablishSeal.bundleSeal_value cert withOneTime content counterWidth previousWidth epochWidth indexWidth assign hbound

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishSeal TlsMpc.KernelSpecs.EstablishSeal.Reference TlsMpc.KernelSpecs.SealValue.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-seal`, opened status 255**: the opened envelope (output 3) is the reference PreKey
sealed-sender envelope `envelopeOf` of the kernel's inputs, and the send was accepted. -/
theorem establishSeal_bundleSeal_accepted (cert : Nat) (withOneTime : Bool)
    (content counterWidth previousWidth epochWidth indexWidth : Nat) (assign : BVExpr.Assignment)
    (hbound : cert + content + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 30)
    (opened : (ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth
      epochWidth indexWidth) assign).getD 0 [] = [255]) :
    let get := fun name => (lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval assign)
    let record := get "conversation"
    let session := (record.drop cert).take 262
    let metadata := (record.drop (cert + 262)).take 57
    let shape : Serialization.Shape := ⟨counterWidth, previousWidth, true⟩
    let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 0, false⟩
    let i := inputOf content session metadata (get "localAddress") (get "text")
    SpqrSend.accepted shape pqShape i ∧
      boundAccepted (get "ephemeralAgreement") (get "staticAgreement") (get "senderPublic") i.sender ∧
      OpenResult.get ByteAuth.concrete (get "text") 0 = 255 ∧
      (ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth epochWidth
        indexWidth) assign).getD 3 [] =
        envelopeOf withOneTime shape pqShape content session metadata (get "pending") ((record.drop 0).take cert)
          (get "localAddress") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
          (get "staticAgreement") :=
  TlsMpc.KernelSpecs.EstablishSeal.bundleSeal_accepted cert withOneTime content counterWidth previousWidth epochWidth indexWidth assign hbound opened

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishSeal TlsMpc.KernelSpecs.EstablishSeal.Reference TlsMpc.KernelSpecs.SealValue.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
/-- The kernel's five groups decode to the value (`n < 2^35`, so every `uint32`). -/
theorem establishSeal_varint5_decode (n : Nat) (h : n < 2 ^ 35) : leb128 (varint5 n) = n :=
  TlsMpc.KernelSpecs.EstablishSeal.varint5_decode n h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishSeal TlsMpc.KernelSpecs.EstablishSeal.Reference TlsMpc.KernelSpecs.SealValue.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
/-- libsignal's canonical varint decodes to the value. -/
theorem establishSeal_varint_decode (n : Nat) : leb128 (varint n) = n :=
  TlsMpc.KernelSpecs.EstablishSeal.varint_decode n
open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishFirst TlsMpc.KernelSpecs.EstablishFirst.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
open TlsMpc.KernelSpecs.SealValue.Reference (hkdfSha256) in
open TlsMpc.KernelSpecs.EstablishSeal.Reference (sealV1Typed prekeyMessage preKeySignalMessage varint5 u32BE) in
/-- `EstablishFirst.keys_value`. -/
theorem establishFirst_keys_value (dh1 dh2 dh3 oneTime kem ratchetAgreement : List Byte) :
    Establish.keys Sha256.concrete dh1 dh2 dh3 oneTime kem ratchetAgreement =
      createChain ((handshakeKeys dh1 dh2 dh3 oneTime kem).take 32) ratchetAgreement ++
        (handshakeKeys dh1 dh2 dh3 oneTime kem).drop 32 ++
        spqrChainStart ((handshakeKeys dh1 dh2 dh3 oneTime kem).drop 64) :=
  TlsMpc.KernelSpecs.EstablishFirst.keys_value dh1 dh2 dh3 oneTime kem ratchetAgreement

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishFirst TlsMpc.KernelSpecs.EstablishFirst.Reference Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
open TlsMpc.KernelSpecs.SealValue.Reference (hkdfSha256) in
open TlsMpc.KernelSpecs.EstablishSeal.Reference (sealV1Typed prekeyMessage preKeySignalMessage varint5 u32BE) in
open TlsMpc.HybridKernel (lookup) in
/-- **The first message to a new device, end to end over the two kernels.** When
`establish-session` opened status 255, `bundle-seal`'s `conversation` and `pending` inputs are that
run's `conversation` and `pending` outputs (the worker's wiring, a hypothesis), and `bundle-seal`
opened status 255, the opened envelope is `firstEnvelope` of the key agreements (`dh1` … `dh4`,
`kemSecret`, `ratchetAgreement`), the Kyber ciphertext, the public keys and ids
`establish-session` was given, and `bundle-seal`'s own text and sealed-sender inputs. -/
theorem establishFirst_firstMessage_envelope (cert : Nat) (withOneTime : Bool)
    (content counterWidth previousWidth epochWidth indexWidth : Nat) (sessionAssign sealAssign : BVExpr.Assignment)
    (hbound : cert + content + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 30)
    (established : (EstablishKernel.Kernel.values (EstablishKernel.establishSession cert withOneTime)
      sessionAssign).getD 0 [] = [255])
    (hconversation : (lookup (BundleKernel.sealInputs cert content) "conversation").map (BVExpr.eval sealAssign) =
      (EstablishKernel.Kernel.values (EstablishKernel.establishSession cert withOneTime) sessionAssign).getD 1 [])
    (hpending : (lookup (BundleKernel.sealInputs cert content) "pending").map (BVExpr.eval sealAssign) =
      (EstablishKernel.Kernel.values (EstablishKernel.establishSession cert withOneTime) sessionAssign).getD 2 [])
    (opened : (ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth
      epochWidth indexWidth) sealAssign).getD 0 [] = [255]) :
    let est := fun name =>
      (lookup (EstablishKernel.sessionInputs cert withOneTime) name).map (BVExpr.eval sessionAssign)
    let sealIn := fun name => (lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval sealAssign)
    (ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth epochWidth
        indexWidth) sealAssign).getD 3 [] =
      firstEnvelope withOneTime ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩ content
        (est "dh1") (est "dh2") (est "dh3") (est "dh4") (est "kemSecret") (est "ratchetAgreement")
        (est "kemCiphertext") (est "basePublic") (est "ratchetPublic") (est "senderPublic") (est "identityKey")
        (est "certificate") (est "uuid") (est "deviceId") (est "localRegistrationId") (est "oneTimePrekeyId")
        (est "signedPrekeyId") (est "kyberPrekeyId") (sealIn "localAddress") (sealIn "text")
        (sealIn "ephemeralPublic") (sealIn "senderPublic") (sealIn "ephemeralAgreement") (sealIn "staticAgreement") :=
  TlsMpc.KernelSpecs.EstablishFirst.firstMessage_envelope cert withOneTime content counterWidth previousWidth epochWidth indexWidth sessionAssign sealAssign hbound established hconversation hpending opened

open TlsMpc.KernelSpecs.SealFixed Std.Tactic.BVDecide TlsMpc.Signal in
/-- **A refused seal (opened status 0) opens an all-zero envelope.** **K**. -/
theorem signalSealBuilt_rejects (cert counterWidth previousWidth epochWidth indexWidth classes : Nat) (official : Bool)
    (assign : BVExpr.Assignment)
    (refused : ((HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes
      official).outputs.map (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes
      official).outputs.map (fun field => field.value.map (BVExpr.eval assign))).getD 3 [], byte = 0 :=
  TlsMpc.KernelSpecs.SealFixed.signalSealBuilt_rejects cert counterWidth previousWidth epochWidth indexWidth classes
    official assign refused

open TlsMpc.KernelSpecs.TlsHandshake Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`tls-derive` outputs the client and server handshake traffic blocks and the main secret of
the RFC 8446 key schedule** (`TlsKdf.handshakeSecrets`, no PSK). **K**. -/
theorem tlsDerive_spec (assign : BVExpr.Assignment) :
    let get := fun name => (lookup deriveInputs name).map (BVExpr.eval assign)
    let secrets := TlsKdf.handshakeSecrets Sha256.concrete (get "agreement") (get "helloHash")
    HybridKernel.tlsDerive.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [trafficBlockValue secrets.client, trafficBlockValue secrets.server, secrets.main] :=
  TlsMpc.KernelSpecs.TlsHandshake.tlsDerive_spec assign

open TlsMpc.KernelSpecs.TlsHandshake Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`tls-verify-finished` opens 255 exactly when the received message is the server Finished
message under the server handshake secret, else 0.** **K**. -/
theorem tlsVerifyFinished_spec (assign : BVExpr.Assignment) :
    let get := fun name => (lookup verifyInputs name).map (BVExpr.eval assign)
    HybridKernel.tlsVerifyFinished.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[if TlsHandshake.finishedMessage Sha256.concrete ((get "serverHandshake").take 32) (get "transcriptHash") =
          get "message" then 255 else 0]] :=
  TlsMpc.KernelSpecs.TlsHandshake.tlsVerifyFinished_spec assign

open TlsMpc.KernelSpecs.TlsHandshake Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`tls-finish` outputs the application traffic blocks and opens the client Finished record
sealed under the client handshake key** (sequence 0, type 22, after the certificate). **K**
(wire). -/
theorem tlsFinish_spec (certificateSize : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (finishInputs certificateSize) name).map (BVExpr.eval assign)
    let application := TlsKdf.applicationSecrets Sha256.concrete (get "mainSecret") (get "serverHash")
    let client := get "clientHandshake"
    (HybridKernel.tlsFinish certificateSize).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [trafficBlockValue application.1, trafficBlockValue application.2,
        TlsRecord.sealCore Gcm.concrete ((client.drop 32).take 16) ((client.drop 48).take 12) (List.replicate 8 0)
          (get "certificate" ++ [20, 0, 0, 32] ++
            TlsKdf.finished Sha256.concrete (client.take 32) (get "clientHash")) 22 0] :=
  TlsMpc.KernelSpecs.TlsHandshake.tlsFinish_spec certificateSize assign

open TlsMpc.KernelSpecs.TlsHandshake Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`tls-open-handshake` opens the public-handshake gate of the RFC record opening under the
server handshake key and IV.** **K**. -/
theorem tlsOpenHandshake_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (openInputs size) name).map (BVExpr.eval assign)
    let block := get "serverHandshake"
    (HybridKernel.tlsOpenHandshake size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [TlsPublicHandshake.gate ByteAuth.concrete
        (TlsReceive.spec ((block.drop 32).take 16) ((block.drop 48).take 12) (get "sequence") (get "record"))] :=
  TlsMpc.KernelSpecs.TlsHandshake.tlsOpenHandshake_spec size assign

open TlsMpc.KernelSpecs.TlsHandshake Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`tls-open-handshake` opens all zeros for an application-data record.** **K**. C.3. -/
theorem tlsOpenHandshake_application_zero (size : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (openInputs size) name).map (BVExpr.eval assign)
    let block := get "serverHandshake"
    let parsed := TlsReceive.spec ((block.drop 32).take 16) ((block.drop 48).take 12) (get "sequence") (get "record")
    parsed[1]?.getD 0 = 23 →
      (HybridKernel.tlsOpenHandshake size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
        [List.replicate parsed.length 0] :=
  TlsMpc.KernelSpecs.TlsHandshake.tlsOpenHandshake_application_zero size assign

open TlsMpc.KernelSpecs.Reveal Std.Tactic.BVDecide in
open TlsMpc.HybridKernel (lookup) in
/-- **`tls-reveal-masked` opens the length and the content below that length, zero above it;
all zero when the length exceeds the capacity** (capacity < 65536). **K**. Independent of
`bv_decide` (re-proves `run_correct`). C.3. -/
theorem tlsRevealMasked_value (size : Nat) (bound : size < 65536) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (revealInputs size) name).map (BVExpr.eval assign)
    let n := TlsPrivateSeal.lengthValue ((get "length").getD 0 0) ((get "length").getD 1 0)
    (HybridKernel.tlsRevealMasked size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [get "length", if n ≤ size then keepBelow 0 n (get "content") else List.replicate size 0] :=
  TlsMpc.KernelSpecs.Reveal.tlsRevealMasked_value size bound assign

open TlsMpc.KernelSpecs.SignalKernels Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-upgrade` = `RelayUpgrade.request` on the credentials and nonce.** **K**. -/
theorem signalUpgrade_spec (passwordBytes : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (upgradeInputs passwordBytes) name).map (BVExpr.eval assign)
    (HybridKernel.signalUpgrade passwordBytes).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [RelayUpgrade.request ByteAuth.concrete passwordBytes (get "credentials" ++ get "nonce")] :=
  TlsMpc.KernelSpecs.SignalKernels.signalUpgrade_spec passwordBytes assign

open TlsMpc.KernelSpecs.SignalKernels Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-upgrade-shared` = `RelayUpgrade.request` on the XOR of the two credential shares.**
**K**. -/
theorem signalUpgradeShared_spec (passwordBytes : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (sharedInputs passwordBytes) name).map (BVExpr.eval assign)
    (HybridKernel.signalUpgradeShared passwordBytes).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [RelayUpgrade.request ByteAuth.concrete passwordBytes
        (List.zipWith (· ^^^ ·) (get "credentialsA") (get "credentialsB") ++ get "nonce")] :=
  TlsMpc.KernelSpecs.SignalKernels.signalUpgradeShared_spec passwordBytes assign

open TlsMpc.KernelSpecs.SignalKernels Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-conversation-view` outputs two slices of the record.** **K**. -/
theorem signalConversationView_spec (cert size : Nat) (assign : BVExpr.Assignment) :
    let record := (lookup (viewInputs cert size) "conversation").map (BVExpr.eval assign)
    (HybridKernel.signalConversationView cert size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [(record.drop (cert + 150)).take 32, (record.drop (cert + 182 + size + 40)).take 8] :=
  TlsMpc.KernelSpecs.SignalKernels.signalConversationView_spec cert size assign

open TlsMpc.KernelSpecs.SignalKernels Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-widths` opens the width flags of the counters and epoch.** **K**. What a flag means
(255 exactly when the value is ≥ 2^(7(k+1))) is `signalWidths_value` (section 2d). -/
theorem signalWidths_spec (cert : Nat) (assign : BVExpr.Assignment) :
    let session := (((lookup (widthsInputs cert) "conversation").map (BVExpr.eval assign)).drop cert).take 262
    let flags := fun (bytes : List (BitVec 8)) groups => widthFlagsWith ByteAuth.concrete 0 bytes groups
    (HybridKernel.signalWidths cert).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [flags ((session.drop 1).take 4) 4, flags ((session.drop 5).take 4) 4, flags ((session.drop 109).take 8) 9,
        flags (ChainSend.nextCounter Sha256.concrete ByteAuth.concrete ((session.drop 105).take 4)) 4] :=
  TlsMpc.KernelSpecs.SignalKernels.signalWidths_spec cert assign

open TlsMpc.KernelSpecs.SignalKernels Std.Tactic.BVDecide in
/-- **`tls-parser-initial` outputs 11 zero bytes.** **K**. -/
theorem tlsParserInitial_spec (assign : BVExpr.Assignment) :
    HybridKernel.tlsParserInitial.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [List.replicate 11 0] :=
  TlsMpc.KernelSpecs.SignalKernels.tlsParserInitial_spec assign

open TlsMpc.KernelSpecs.SignalKernels Std.Tactic.BVDecide in
/-- **`ws-initial` outputs the concrete initial parser states.** **K**. -/
theorem wsInitial_spec (assign : BVExpr.Assignment) :
    HybridKernel.wsInitial.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [(initialValues.drop 0).take 180, (initialValues.drop 180).take 26, (initialValues.drop 206).take 636,
        (initialValues.drop 842).take 932] :=
  TlsMpc.KernelSpecs.SignalKernels.wsInitial_spec assign

open TlsMpc.KernelSpecs.PointsAndItem Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`establish-points` passes the three keys through unchanged.** **K**. -/
theorem establishPoints_spec (withOneTime : Bool) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (pointsInputs withOneTime) name).map (BVExpr.eval assign)
    values (EstablishKernel.establishPoints withOneTime) assign =
      [get "identityKey", get "signedPrekey"] ++ (if withOneTime then [get "oneTimePrekey"] else []) :=
  TlsMpc.KernelSpecs.PointsAndItem.establishPoints_spec withOneTime assign

open TlsMpc.KernelSpecs.PointsAndItem Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-item` = `BundleResponse.device` on the reassembled body.** **K**. The link to
`device` on the whole response body is `bundleItem_whole` (section 2d). -/
theorem bundleItem_spec (first last : Bool) (w : BundleResponse.Widths) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (BundleItemKernel.itemInputs first last w) name).map (BVExpr.eval assign)
    let body := get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end"
    let out := BundleResponse.device ByteAuth.concrete body.length
      (BundleResponse.firstItem + (if first then 0 else 1)) w body
    values (BundleItemKernel.bundleItem first last w) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) :=
  TlsMpc.KernelSpecs.PointsAndItem.bundleItem_spec first last w assign

open TlsMpc.KernelSpecs.PointsAndItem Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-item` with `valid` 0 outputs only zeros.** **K**. -/
theorem bundleItem_rejects (first last : Bool) (w : BundleResponse.Widths) (assign : BVExpr.Assignment)
    (failed : (values (BundleItemKernel.bundleItem first last w) assign).getD 0 [] = [0]) :
    ∀ field ∈ values (BundleItemKernel.bundleItem first last w) assign, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.KernelSpecs.PointsAndItem.bundleItem_rejects first last w assign failed

/-! ### 2d. What the request sealers send, `bundle-item` on the whole body, the width flags, the
slot encoders (TlsMpc/KernelSpecs/{RequestFrame, SealFrame, BundleItemWhole, WidthFlags,
SlotEncoders, SlotBase64, SlotDecimal}.lean)

The entries below are about the request builders the controller runs,
`PublicRequest.build`/`buildFetch`/`buildDevices` and the messages they frame
(`sendMessage`/`fetchMessage`/`devicesMessage`), in `TlsMpc/Node/Policy/Request.lean` (moved out of
the controller's executable root in stage S2; there is no restated copy). Those entries are **C**
(the builders) composed with **K** (the kernels). -/

open TlsMpc.KernelSpecs.RequestFrame PublicRequest in
/-- **Every frame `build` returns has the 8-byte WebSocket header** `[130, 254, size / 256, size] ‖
mask` (payload of 126..65535 bytes), followed by the built payload (text masked, slots zero); the
offsets are those the slot pieces set. So `signal-request-ctr`'s fixed payload start 8 is right for
every frame the controller builds for it. **C**. T8. -/
theorem requestBuild_ok (envelope : List (BitVec 8)) (timestamp id : Nat)
    (mask frame : List (BitVec 8)) (official : Bool) (offsets : List Nat)
    (built : build envelope timestamp id mask official = .ok (frame, offsets)) :
    let msg := sendMessage envelope timestamp id official
    126 ≤ total msg ∧ total msg < 65536 ∧ mask.length = 4 ∧ (buildHeader (total msg) mask).length = 8 ∧
      frame = buildHeader (total msg) mask ++ body mask 0 msg ∧ offsets = (offsetsFold #[0, 0, 0, 0] 8 msg).toList :=
  TlsMpc.KernelSpecs.RequestFrame.build_ok envelope timestamp id mask frame official offsets built

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.RequestFrame PublicRequest in
/-- **Slots never overlap, the built frame is zero in each, and inserting values of the slots'
widths at the builder's offsets gives the frame of the filled message**: `header ‖ masked(render
values msg)`, whatever the order of the kernel's slot list. Value level. **C**. T7(a), T8. -/
theorem requestInsertSlots_offsets (header mask : List (BitVec 8)) (msg : List Piece) (values : Nat → List (BitVec 8))
    (O : Array Nat) (ks : List Nat) (fits : Fits values (slotTable header.length msg))
    (same : ∀ k, k ∈ ks ↔ k ∈ indicesOf msg) (nodup : (indicesOf msg).Nodup)
    (small : ∀ k ∈ indicesOf msg, k < O.size) :
    insertSlots ByteAuth.concrete 0 (header ++ body mask 0 msg) mask header.length
        (ks.map (fun k => ((offsetsFold O header.length msg).toList.getD k 0, values k))) =
      header ++ maskFrom mask 0 (render values msg) :=
  TlsMpc.KernelSpecs.RequestFrame.insertSlots_offsets header mask msg values O ks fits same nodup small

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.RequestFrame PublicRequest Std.Tactic.BVDecide
  TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-request-ctr` on a frame `build` returned seals exactly the WebSocket frame of the
request with the contact's UUID, base64 access key and space-padded device and registration ids in
place of its four slots** (masked with the frame's mask), released under `valid`. **K** + **C**.
T7(a), T8. -/
theorem signalRequestCtr_built (envelope : List (BitVec 8)) (timestamp id : Nat)
    (mask frame : List (BitVec 8)) (official : Bool) (offsets : List Nat)
    (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (cert : Nat) (assign : BVExpr.Assignment)
    (hframe : (lookup (signalRequestInputs cert frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (signalRequestInputs cert frame.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (signalRequestInputs cert frame.length) name).map (BVExpr.eval assign)
    let msg := sendMessage envelope timestamp id official
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (buildHeader (total msg) mask ++ maskFrom mask 0 (render (requestValues cert (get "conversation")) msg))
        (signalRequestSlots cert 0 0 0 0 (get "conversation")).1 :=
  TlsMpc.KernelSpecs.RequestFrame.signalRequestCtr_built envelope timestamp id mask frame official offsets built
    cert assign hframe hmask

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.RequestFrame PublicRequest Std.Tactic.BVDecide
  TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-fetch-ctr` on a frame `buildFetch` returned seals exactly the frame of
`GET /v2/keys/{uuid}/*` with the contact's UUID and base64 access key in place**, valid when the
record is live. **K** + **C**. T7(a), T8. -/
theorem bundleFetchCtr_built (id : Nat) (mask frame : List (BitVec 8)) (payloadAt : Nat) (offsets : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets)) (assign : BVExpr.Assignment)
    (hframe : (lookup (fetchInputs frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (fetchInputs frame.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (fetchInputs frame.length) name).map (BVExpr.eval assign)
    (BundleKernel.bundleFetchCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0)).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total (fetchMessage id)) mask ++ maskFrom mask 0 (render (fetchValues (get "record")) (fetchMessage id)))
        (liveValue (get "record")) :=
  TlsMpc.KernelSpecs.RequestFrame.bundleFetchCtr_built id mask frame payloadAt offsets built assign hframe hmask

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.RequestFrame PublicRequest Std.Tactic.BVDecide
  TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-request-ctr` on a frame `buildDevices` returned seals exactly the frame of
`PUT /v1/messages/{uuid}` with the UUID, access key and every device's padded ids in place**, the
kernel named with the device offsets paired as `find` pairs them. **K** + **C**. T7(a), T8. -/
theorem bundleRequestCtr_built (envelopes : List (List (BitVec 8))) (timestamp id : Nat)
    (mask frame : List (BitVec 8)) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let msg := devicesMessage envelopes timestamp id official
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total msg) mask ++ maskFrom mask 0 (render (devicesValues (get "records")) msg))
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 :=
  TlsMpc.KernelSpecs.RequestFrame.bundleRequestCtr_built envelopes timestamp id mask frame official payloadAt
    offsets built devices paired assign hframe hmask

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.SealFixed TlsMpc.KernelSpecs.SealValue.Reference
  TlsMpc.KernelSpecs.RequestFrame Std.Tactic.BVDecide TlsMpc.Signal in
open PublicRequest (sendMessage build total) in
open TlsMpc.HybridKernel (lookup) in
/-- **What the Signal server receives for an accepted send** (T7 (b) composed with (a)): when
`signal-seal-official` / `signal-seal-built` opened status 255 and the controller built the request
frame with the opened envelope (`PublicRequest.build`), the reference send step accepts and the
`signal-request-ctr` kernel's outputs are the TLS record of the masked WebSocket frame of
`sendMessage envelope …` with the contact's UUID, access key, device and registration ids in their
slots, where `envelope` is sealed sender v1 (`Reference.sealV1`) of the Signal message of
`SpqrSend.canonical` on the stored state (`TlsMpc/KernelSpecs/SealFrame.lean`). Trusted: the C++
worker passes the opened envelope, frame, mask and offsets unchanged. **K** + **C**. T7. -/
theorem serverReceives_accepted (cert counterWidth previousWidth epochWidth indexWidth classes : Nat)
    (official : Bool) (sealAssign : BVExpr.Assignment)
    (hbound : cert + contentBytes classes official + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 31)
    (accepted : ((HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes
      official).outputs.map (fun field => field.value.map (BVExpr.eval sealAssign))).getD 0 [] = [255])
    (timestamp id : Nat) (mask frame : List (BitVec 8)) (offsets : List Nat)
    (built : build (((HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes
      official).outputs.map (fun field => field.value.map (BVExpr.eval sealAssign))).getD 3 [])
      timestamp id mask official = .ok (frame, offsets))
    (assign : BVExpr.Assignment)
    (hframe : (lookup (signalRequestInputs cert frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (signalRequestInputs cert frame.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (sealInputs cert classes official) name).map (BVExpr.eval sealAssign)
    let record := get "conversation"
    let text := get "text"
    let shape : Serialization.Shape := ⟨counterWidth, previousWidth, false⟩
    let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 1, false⟩
    let i := inputOf 0 (stagedOf ((record.drop cert).take (182 + 80)) text) text (contentBytes classes official)
    let envelope := sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
      (get "staticAgreement") ((record.drop 0).take cert) (SpqrSend.canonical shape pqShape i).wire
    let msg := sendMessage envelope timestamp id official
    let requestGet := fun name => (lookup (signalRequestInputs cert frame.length) name).map (BVExpr.eval assign)
    SpqrSend.accepted shape pqShape i ∧
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (requestGet "clientApplication") (requestGet "sequence")
        (buildHeader (total msg) mask ++ maskFrom mask 0 (render (requestValues cert (requestGet "conversation")) msg))
        (signalRequestSlots cert 0 0 0 0 (requestGet "conversation")).1 :=
  TlsMpc.KernelSpecs.SealFrame.serverReceives_accepted cert counterWidth previousWidth epochWidth indexWidth classes
    official sealAssign hbound accepted timestamp id mask frame offsets built assign hframe hmask

/-! What the server receives for a send after a device refresh (`bundle-seal` per device, then
`bundle-request-ctr` over the opened envelopes; `TlsMpc/KernelSpecs/{EstablishDevices,
EstablishRequest}.lean`), about the controller's own `buildDevices`. **K** + **C**. T7. -/

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishDevices Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
open TlsMpc.HybridKernel (lookup) in
/-- **Every device accepted ⇒ the opened envelopes are the reference envelopes, in order.** -/
theorem establishDevices_openedEnvelopes_reference (cert content : Nat) (ds : List DeviceSeal)
    (hb : ∀ d ∈ ds, d.bounded cert content)
    (opened : ∀ d ∈ ds, (d.outputs cert content).getD 0 [] = [255]) :
    ds.map (fun d => (d.outputs cert content).getD 3 []) = ds.map (fun d => d.reference cert content) :=
  TlsMpc.KernelSpecs.EstablishDevices.openedEnvelopes_reference cert content ds hb opened

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishDevices Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
open TlsMpc.HybridKernel (lookup) in
/-- **The first message after a refresh**: device by device, the opened envelope is the first
PreKey sealed-sender message of the session its `establish-session` run set up. -/
theorem establishDevices_openedEnvelopes_first (cert content : Nat) (ps : List (DeviceSession × DeviceSeal))
    (hb : ∀ p ∈ ps, p.2.bounded cert content) (hw : ∀ p ∈ ps, wired cert content p) :
    ps.map (fun p => (p.2.outputs cert content).getD 3 []) = ps.map (firstOf cert content) :=
  TlsMpc.KernelSpecs.EstablishDevices.openedEnvelopes_first cert content ps hb hw
open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishRequest Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
open TlsMpc.KernelSpecs.EstablishDevices (DeviceSeal DeviceSession firstOf wired) in
open PublicRequest (buildDevices devicesMessage total) in
open TlsMpc.KernelSpecs.RequestFrame (assembleHeader maskFrom render devicesValues) in
open TlsMpc.HybridKernel (lookup) in
/-- **The bytes the server receives for an accepted send to several unanswered devices.** -/
theorem establishRequest_serverReceives_refresh (cert content : Nat) (ds : List DeviceSeal)
    (hb : ∀ d ∈ ds, d.bounded cert content) (opened : ∀ d ∈ ds, (d.outputs cert content).getD 0 [] = [255])
    (timestamp id : Nat) (mask frame : List Byte) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices (ds.map (fun d => (d.outputs cert content).getD 3 [])) timestamp id mask official =
      .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let msg := devicesMessage (ds.map (fun d => d.reference cert content)) timestamp id official
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total msg) mask ++ maskFrom mask 0 (render (devicesValues (get "records")) msg))
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 :=
  TlsMpc.KernelSpecs.EstablishRequest.serverReceives_refresh cert content ds hb opened timestamp id mask frame official payloadAt offsets built devices paired assign hframe hmask

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.EstablishRequest Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.KernelSpecs.SealValue (Byte) in
open TlsMpc.KernelSpecs.EstablishDevices (DeviceSeal DeviceSession firstOf wired) in
open PublicRequest (buildDevices devicesMessage total) in
open TlsMpc.KernelSpecs.RequestFrame (assembleHeader maskFrom render devicesValues) in
open TlsMpc.HybridKernel (lookup) in
/-- **The first message after a refresh, as the server receives it**: each device's envelope is the
first PreKey sealed-sender message of the session its `establish-session` run set up. -/
theorem establishRequest_serverReceives_refresh_first (cert content : Nat) (ps : List (DeviceSession × DeviceSeal))
    (hb : ∀ p ∈ ps, p.2.bounded cert content) (hw : ∀ p ∈ ps, wired cert content p)
    (timestamp id : Nat) (mask frame : List Byte) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices (ps.map (fun p => (p.2.outputs cert content).getD 3 [])) timestamp id mask official =
      .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let msg := devicesMessage (ps.map (firstOf cert content)) timestamp id official
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total msg) mask ++ maskFrom mask 0 (render (devicesValues (get "records")) msg))
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 :=
  TlsMpc.KernelSpecs.EstablishRequest.serverReceives_refresh_first cert content ps hb hw timestamp id mask frame official payloadAt offsets built devices paired assign hframe hmask

open TlsMpc.KernelSpecs.BundleItemWhole TlsMpc.Signal BundleResponse in
/-- **Locality of `BundleResponse.device`:** it reads only the header, the item, the separator
before it, what follows it and the last two bytes; two bodies that agree there give the same
outputs. **K-fn**. -/
theorem bundleDevice_local {B : Type} (a : ByteAuth.Ops B) (R X : List B) (start' start : Nat) (w : Widths)
    (hw : Windows a R X start' start (size (item w))) :
    BundleResponse.device a R.length start' w R = BundleResponse.device a X.length start w X :=
  TlsMpc.KernelSpecs.BundleItemWhole.device_local a R X start' start w hw

open TlsMpc.KernelSpecs.BundleItemWhole Std.Tactic.BVDecide TlsMpc.Signal BundleResponse in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-item` computes `BundleResponse.device` on the whole response body** at the item's
real offset, for every assignment whose five inputs are the cut of that body around the item (as
`layout?` places it). **K**. -/
theorem bundleItem_whole (first last : Bool) (w : Widths) (assign : BVExpr.Assignment) (X : List (BitVec 8))
    (start : Nat) (placed : Placed X.length first last start (size (item w)))
    (inputs : let get := fun name => (lookup (BundleItemKernel.itemInputs first last w) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" = cut X first last start (size (item w))) :
    let out := BundleResponse.device ByteAuth.concrete X.length start w X
    values (BundleItemKernel.bundleItem first last w) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) :=
  TlsMpc.KernelSpecs.BundleItemWhole.bundleItem_whole first last w assign X start placed inputs

open TlsMpc.KernelSpecs.BundleItemWhole Std.Tactic.BVDecide TlsMpc.Signal BundleResponse in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` computes `BundleSlots.deviceSlots` on the whole response body with the item
spliced into the slot layout.** **K**. That this is `device` on the original item (the body the
server sent) is `bundleSlot_device` below. -/
theorem bundleSlot_whole (first last oneTime : Bool) (assign : BVExpr.Assignment) (X : List (BitVec 8))
    (start : Nat) (placed : Placed X.length first last start (size (item (BundleSlots.slots oneTime))))
    (inputs : let get := fun name => (lookup (BundleSlotKernel.slotInputs first last oneTime) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        cut X first last start (size (item (BundleSlots.slots oneTime)))) :
    let get := fun name => (lookup (BundleSlotKernel.slotInputs first last oneTime) name).map (BVExpr.eval assign)
    let out := BundleSlots.deviceSlots ByteAuth.concrete X.length start oneTime (get "widths") X
    values (BundleSlotKernel.bundleSlot first last oneTime) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if oneTime then [out.getD 10 [], out.getD 11 []] else []) :=
  TlsMpc.KernelSpecs.BundleItemWhole.bundleSlot_whole first last oneTime assign X start placed inputs

/-! `bundle-slot` against `BundleResponse.device` on the body the server sent
(`TlsMpc/KernelSpecs/BundleSlotWhole.lean`). The slot check, the splice, the item: **K-fn**; the
kernel on the cut of the body: **K**. Trusted: the C++ worker binds `head`/`before`/`item`/`after`/
`end` as stated and pads the splice with the filler byte 0 (`service_kernels.h`,
`bundle_establish`). Since the emitter batch (effective after the re-lowering) the padding is the
filler 0, not `0`, and a `widths` input that disagrees with the splice no longer matters:
`bundleSlot_any_widths` holds for any item, not only one `device` accepts, and the former caveat
`inconsistent_width_accepts` is `bundleSlot_inconsistent_width_refused` (NEEDS_REVIEW.md 3f,
defect 2). -/

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
/-- **A slot of `m` bytes holding `m − n` filler bytes (0) and then `n` characters, checked with
the declared width `n`, is accepted exactly when `numberValid` accepts the `n` characters.** -/
theorem slotValid_pad (limit : Nat) (cs : List Byte) (m : Nat) (h1 : 1 ≤ cs.length) (hnm : cs.length ≤ m)
    (hm : m < 256) :
    BundleSlots.slotValid ByteAuth.concrete limit (BitVec.ofNat 8 cs.length) (List.replicate (m - cs.length) 0 ++ cs) =
      numberValid ByteAuth.concrete limit cs :=
  TlsMpc.KernelSpecs.BundleSlotWhole.slotValid_pad limit cs m h1 hnm hm

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
/-- **(a) `deviceSlots` on the item spliced with the digit counts `w` is `device` with `w` on the
item as it was**, the response around it unchanged (`pre` holds the header and the byte before
the item, `post` what follows it). -/
theorem deviceSlots_splice (w : Widths) (ok : w.ok = true) (pre I post : List Byte)
    (hI : I.length = size (item w)) (hpre : firstItem ≤ pre.length) (hpost : 2 ≤ post.length) :
    BundleSlots.deviceSlots ByteAuth.concrete
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post).length
        pre.length (w.oneTime != 0) (widthBytes w)
        (pre ++ applyRuns 0 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post) =
      BundleResponse.device ByteAuth.concrete (pre ++ I ++ post).length pre.length w (pre ++ I ++ post) :=
  TlsMpc.KernelSpecs.BundleSlotWhole.deviceSlots_splice w ok pre I post hI hpre hpost

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
/-- **(b) The splice produces the slot layout.** For an item laid out for the digit counts `w`
(`size (item w)` bytes), `BundleSlots.spliced w` (what the runtime does, from `splice w`) has
the size of the slot item; its template text is in place exactly when the original's is; and
each of its fields is the original field preceded by `z`s up to the slot's size (base64 fields,
whose sizes do not change, are copied as they are). -/
theorem spliced_layout {B : Type} (a : ByteAuth.Ops B) (z : B) (w : Widths) (ok : w.ok = true) (I : List B)
    (hI : I.length = size (item w)) :
    (BundleSlots.spliced w I z).length = size (item (BundleSlots.slots (w.oneTime != 0))) ∧
      literals a (BundleSlots.spliced w I z) 0 (item (BundleSlots.slots (w.oneTime != 0))) = literals a I 0 (item w) ∧
      ∀ k, fieldOf (BundleSlots.spliced w I z) 0 (item (BundleSlots.slots (w.oneTime != 0))) k =
        List.replicate (fieldSize (item (BundleSlots.slots (w.oneTime != 0))) k - fieldSize (item w) k) z ++
          fieldOf I 0 (item w) k :=
  TlsMpc.KernelSpecs.BundleSlotWhole.spliced_layout a z w ok I hI

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` computes `BundleResponse.device` on the body the server sent.** Let `X` be
the response body and the item of digit counts `w` (`w.ok`, as `layout?` returns them) start at
`start`, placed as `layout?` places it. If the kernel `bundle-slot FIRST LAST ONETIME` (with
`ONETIME` = whether `w` has a one-time prekey, as `BundleSlotKernel.arguments` chooses it) gets
as `head`, `before`, `item`, `after`, `end` the header, the byte before the item, the item spliced
by `BundleSlots.spliced w`, the byte after it and the body's last two bytes, and as `widths` the
five digit counts, then its outputs are `BundleResponse.device` on `X` at `start` with `w`:
exactly the outputs `bundle-item` has (`BundleItemWhole.bundleItem_whole`). -/
theorem bundleSlot_device (first last : Bool) (w : Widths) (ok : w.ok = true) (assign : BVExpr.Assignment)
    (X : List Byte) (start : Nat) (placed : BundleItemWhole.Placed X.length first last start (size (item w)))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w (part X start (size (item w))) 0 ++
          (if last then [] else part X (start + size (item w)) 1) ++ part X (X.length - 2) 2)
    (widths : (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) "widths").map (BVExpr.eval assign) =
      widthBytes w) :
    let out := BundleResponse.device ByteAuth.concrete X.length start w X
    values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) :=
  TlsMpc.KernelSpecs.BundleSlotWhole.bundleSlot_device first last w ok assign X start placed inputs widths

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` and `bundle-item` give the same outputs** on the same item of the same body:
the first fed the splice and the digit counts, the second the item as it is. -/
theorem bundleSlot_eq_bundleItem (first last : Bool) (w : Widths) (ok : w.ok = true) (X : List Byte) (start : Nat)
    (placed : BundleItemWhole.Placed X.length first last start (size (item w)))
    (assign assign' : BVExpr.Assignment)
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w (part X start (size (item w))) 0 ++
          (if last then [] else part X (start + size (item w)) 1) ++ part X (X.length - 2) 2)
    (widths : (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) "widths").map (BVExpr.eval assign) =
      widthBytes w)
    (inputs' : let get := fun name => (lookup (BundleItemKernel.itemInputs first last w) name).map (BVExpr.eval assign')
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        BundleItemWhole.cut X first last start (size (item w))) :
    values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign =
      values (BundleItemKernel.bundleItem first last w) assign' :=
  TlsMpc.KernelSpecs.BundleSlotWhole.bundleSlot_eq_bundleItem first last w ok X start placed assign assign' inputs widths inputs'

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
/-- **Only one set of digit counts parses an item.** If `device` accepts the item at `s` with
digit counts `w` and with `w'`, then `w = w'`. -/
theorem device_unique (X : List Byte) (s : Nat) (w w' : Widths)
    (hv : (BundleResponse.device ByteAuth.concrete X.length s w X).getD 0 [] = [255])
    (hv' : (BundleResponse.device ByteAuth.concrete X.length s w' X).getD 0 [] = [255]) : w = w' :=
  TlsMpc.KernelSpecs.BundleSlotWhole.device_unique X s w w' hv hv'

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **Wrong digit counts: `bundle-slot` refuses.** If the item at `start` of the body `X` is
accepted by `device` with its true digit counts `w`, and the runtime instead splices it with,
and passes as `widths`, other counts `w'` (within `Widths.ok`, the cut placed for `w'`), every
output of the kernel is zero, the validity byte included: nothing is released, in particular
no other number. -/
theorem bundleSlot_wrong_counts (first last : Bool) (w w' : Widths) (ok' : w'.ok = true) (assign : BVExpr.Assignment)
    (X : List Byte) (start : Nat) (placed : BundleItemWhole.Placed X.length first last start (size (item w')))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w'.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w' (part X start (size (item w'))) 0 ++
          (if last then [] else part X (start + size (item w')) 1) ++ part X (X.length - 2) 2)
    (widths : (lookup (BundleSlotKernel.slotInputs first last (w'.oneTime != 0)) "widths").map (BVExpr.eval assign) =
      widthBytes w')
    (accepted : (BundleResponse.device ByteAuth.concrete X.length start w X).getD 0 [] = [255]) (wrong : w' ≠ w) :
    ∀ field ∈ values (BundleSlotKernel.bundleSlot first last (w'.oneTime != 0)) assign, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.KernelSpecs.BundleSlotWhole.bundleSlot_wrong_counts first last w w' ok' assign X start placed inputs widths accepted wrong

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` either parses the item exactly as `device` does with the only digit counts
that fit, or releases nothing.** For whatever digit counts `w'` (within `Widths.ok`) the runtime
splices the item with and passes as `widths`: either `device` accepts the item with `w'`, `w'` is
the only set of digit counts with which it does, and the kernel's outputs are `device`'s; or every
output of the kernel, the validity byte included, is zero. -/
theorem bundleSlot_parses_or_refuses (first last : Bool) (w' : Widths) (ok' : w'.ok = true)
    (assign : BVExpr.Assignment) (X : List Byte) (start : Nat)
    (placed : BundleItemWhole.Placed X.length first last start (size (item w')))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w'.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w' (part X start (size (item w'))) 0 ++
          (if last then [] else part X (start + size (item w')) 1) ++ part X (X.length - 2) 2)
    (widths : (lookup (BundleSlotKernel.slotInputs first last (w'.oneTime != 0)) "widths").map (BVExpr.eval assign) =
      widthBytes w') :
    ((BundleResponse.device ByteAuth.concrete X.length start w' X).getD 0 [] = [255] ∧
      (∀ w, (BundleResponse.device ByteAuth.concrete X.length start w X).getD 0 [] = [255] → w = w') ∧
      let out := BundleResponse.device ByteAuth.concrete X.length start w' X
      values (BundleSlotKernel.bundleSlot first last (w'.oneTime != 0)) assign =
        [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
          out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
        (if w'.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []])) ∨
    (∀ field ∈ values (BundleSlotKernel.bundleSlot first last (w'.oneTime != 0)) assign, ∀ byte ∈ field, byte = 0) :=
  TlsMpc.KernelSpecs.BundleSlotWhole.bundleSlot_parses_or_refuses first last w' ok' assign X start placed inputs widths

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
open TlsMpc.HybridKernel (lookup) in
open TlsMpc.ReceiveKernel (values) in
/-- **`bundle-slot` on an item the server wrote, whatever the `widths` input.** If the runtime
splices the item at `start` of `X` with digit counts `w` (no field of the item starting with a NUL
byte, the filler), then for ANY five bytes as `widths` the kernel either gives exactly `device`'s
outputs with `w` (those of `bundle-item`; all zero when `device` refuses) or releases nothing at
all. Since the emitter batch: no longer needs `device` to accept the item. -/
theorem bundleSlot_any_widths (first last : Bool) (w : Widths) (ok : w.ok = true) (assign : BVExpr.Assignment)
    (X : List Byte) (start : Nat) (placed : BundleItemWhole.Placed X.length first last start (size (item w)))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w (part X start (size (item w))) 0 ++
          (if last then [] else part X (start + size (item w)) 1) ++ part X (X.length - 2) 2)
    (lead : ∀ k, 1 ≤ (fieldOf X start (item w) k).length →
      OpenResult.get ByteAuth.concrete (fieldOf X start (item w) k) 0 ≠ 0) :
    (let out := BundleResponse.device ByteAuth.concrete X.length start w X;
      values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign =
        [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
          out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
        (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []])) ∨
    (∀ field ∈ values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign, ∀ byte ∈ field, byte = 0) :=
  TlsMpc.KernelSpecs.BundleSlotWhole.bundleSlot_any_widths first last w ok assign X start placed inputs lead

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
/-- **A slot accepts only its true width byte** (filler padding; the number's first byte not the
filler), whatever the number: the `widths` input cannot disagree with the splice. -/
theorem bundleSlot_slotValid_width (L : Nat) (cs : List Byte) (m : Nat) (v : Byte) (h1 : 1 ≤ cs.length)
    (hnm : cs.length ≤ m) (hm : m < 256) (hfirst : OpenResult.get ByteAuth.concrete cs 0 ≠ 0)
    (acc : BundleSlots.slotValid ByteAuth.concrete L v (List.replicate (m - cs.length) 0 ++ cs) = 255) :
    v = BitVec.ofNat 8 cs.length :=
  TlsMpc.KernelSpecs.BundleSlotWhole.slotValid_width L cs m v h1 hnm hm hfirst acc

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
/-- **The former DEFECT (`inconsistent_width_accepts`), now refused (emitter batch; NEEDS_REVIEW.md
3f, defect 2).** The non-canonical device id `05` spliced with its two digits is refused by the
slot check for every width byte. -/
theorem bundleSlot_inconsistent_width_refused :
    (∀ v : Byte, BundleSlots.slotValid ByteAuth.concrete 7 v (List.replicate (3 - 2) 0 ++ [48, 53]) = 0) ∧
      numberValid ByteAuth.concrete 7 [48, 53] = 0 :=
  TlsMpc.KernelSpecs.BundleSlotWhole.inconsistent_width_refused

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
/-- **Why the padding byte changed**: with `0` padding, `05` spliced with two digits and `5` with
one were the same slot (so no kernel on the same inputs could tell them apart); with the filler 0
they differ. -/
theorem bundleSlot_zero_padding_ambiguous :
    List.replicate (3 - 2) (48 : Byte) ++ [48, 53] = List.replicate (3 - 1) 48 ++ [53] ∧
      List.replicate (3 - 2) (0 : Byte) ++ [48, 53] ≠ List.replicate (3 - 1) 0 ++ [53] :=
  TlsMpc.KernelSpecs.BundleSlotWhole.zero_padding_ambiguous

open TlsMpc.KernelSpecs.WidthFlags TlsMpc.KernelSpecs.SignalKernels in
/-- **A width flag is 255 exactly when the big-endian value is at least 2^(7(k+1))** (flag k,
k = 0, 1, …), else 0. **K-fn**. -/
theorem widthFlags_value (bytes : List (BitVec 8)) (groups : Nat) :
    widthFlagsWith ByteAuth.concrete 0 bytes groups =
      (List.range groups).map (fun k => if 2 ^ (7 * (k + 1)) ≤ bigEndian bytes then 255 else 0) :=
  TlsMpc.KernelSpecs.WidthFlags.widthFlags_value bytes groups

open TlsMpc.KernelSpecs.WidthFlags Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-widths` opens, for the counter, previous counter, SPQR epoch and next counter, the
comparisons "value ≥ 2^(7(k+1))"** (as 255/0). **K**. -/
theorem signalWidths_value (cert : Nat) (assign : BVExpr.Assignment) :
    let session := (((lookup (TlsMpc.KernelSpecs.SignalKernels.widthsInputs cert) "conversation").map
      (BVExpr.eval assign)).drop cert).take 262
    let flags := fun (bytes : List (BitVec 8)) (groups : Nat) =>
      (List.range groups).map (fun k => if 2 ^ (7 * (k + 1)) ≤ bigEndian bytes then (255 : BitVec 8) else 0)
    (HybridKernel.signalWidths cert).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [flags ((session.drop 1).take 4) 4, flags ((session.drop 5).take 4) 4, flags ((session.drop 109).take 8) 9,
        flags (ChainSend.nextCounter Sha256.concrete ByteAuth.concrete ((session.drop 105).take 4)) 4] :=
  TlsMpc.KernelSpecs.WidthFlags.signalWidths_value cert assign

open TlsMpc.KernelSpecs.SlotEncoders TlsMpc.Signal in
/-- **The UUID slot encoder is the RFC 4122 string form** (8-4-4-4-12 lower-case hex) of the 16
bytes, against the independent `refUuid`. **K-fn**. -/
theorem slotUuid_eq (raw : List (BitVec 8)) (h : raw.length = 16) :
    RelayEncoding.uuid ByteAuth.concrete raw = refUuid raw :=
  TlsMpc.KernelSpecs.SlotEncoders.uuid_eq raw h

open TlsMpc.KernelSpecs.SlotEncoders in
/-- **The UUID string form parses back to the 16 bytes** (so it is injective). **K-fn**. -/
theorem slotUuid_parse (raw : List (BitVec 8)) (h : raw.length = 16) : refUuidParse (refUuid raw) = raw :=
  TlsMpc.KernelSpecs.SlotEncoders.uuid_parse raw h

open TlsMpc.KernelSpecs.SlotBase64 TlsMpc.Signal in
/-- **The base64 slot encoder is RFC 4648 base64 with padding**, against the independent
`refBase64`, for every input length. **K-fn**. -/
theorem slotBase64_eq (raw : List (BitVec 8)) : RelayEncoding.base64 ByteAuth.concrete raw = refBase64 raw :=
  TlsMpc.KernelSpecs.SlotBase64.base64_eq raw

open TlsMpc.KernelSpecs.SlotBase64 in
/-- **RFC 4648 base64 decodes back to the bytes** (so it is injective). **K-fn**. -/
theorem slotBase64_decode (raw : List (BitVec 8)) : refBase64Decode (refBase64 raw) = raw :=
  TlsMpc.KernelSpecs.SlotBase64.base64_decode raw

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.SlotDecimal TlsMpc.Signal in
/-- **The padded decimal slot (device id 3, registration id 10 bytes) holds the decimal digits of
the number followed by spaces, and its validity byte is 255 exactly when the digits fit**, against
the independent `refDecimal` / `refPadded`, for every 64-bit number and slot width below 20.
**K-fn**. -/
theorem slotDecimal_value (w : BitVec 64) (width : Nat) (hw : width < 20) :
    paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0 w width =
      (if numDigits w.toNat ≤ width then 255 else 0, refPadded w.toNat width) :=
  TlsMpc.KernelSpecs.SlotDecimal.paddedDecimal_value w width hw

open TlsMpc.KernelSpecs.SlotDecimal in
/-- **A padded decimal slot whose digits fit reads back to the number** (the digits before the
first space). **K-fn**. -/
theorem slotDecimal_parse (n width : Nat) (h : numDigits n ≤ width) : parsePadded (refPadded n width) = n :=
  TlsMpc.KernelSpecs.SlotDecimal.parsePadded_refPadded n width h

/-! ### 2e. The `kem-*` kernels composed (`TlsMpc/KernelSpecs/KemCompose.lean`)

The six ML-KEM kernels, wired as the worker wires them (the name-binding hypotheses `h*` of
`kemc_kernels_compose`: a hypothesis about the C++ worker), compute `pipeline`; `pipeline` is the
repository's reference `MlKem.encapsulate` (`specEnc`) on a valid key and zero on an invalid one.
That the reference is Kyber-1024 rests on test vectors against libcrux; the 2⁻¹⁰⁵ probability that
the matrix sampling exhausts its budget is a calculation, not a theorem. -/

section KemCompose
open TlsMpc.Signal TlsMpc.KernelSpecs.KemCompose

/-- **A valid key and sampling within budget: the composed kernels' outputs are the reference
encapsulation** (status 255, the ciphertext, the shared secret). -/
theorem kemc_pipeline_valid_accept (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) (hvalid : KeyValid key)
    (hlen : kyber = true ∨ (entropyA.length = 32 ∧ entropyB.length = 32))
    (hs : (specEnc kyber key entropyA entropyB).success = 255) :
    pipeline kyber key entropyA entropyB =
      [[255], (specEnc kyber key entropyA entropyB).bytes.take 1568, (specEnc kyber key entropyA entropyB).bytes.drop 1568] :=
  TlsMpc.KernelSpecs.KemCompose.pipeline_valid_accept kyber key entropyA entropyB hvalid hlen hs

/-- A valid key whose matrix sampling exhausted its budget: everything is zero. -/
theorem kemc_pipeline_valid_reject (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) (hvalid : KeyValid key)
    (hlen : kyber = true ∨ (entropyA.length = 32 ∧ entropyB.length = 32))
    (hs : (specEnc kyber key entropyA entropyB).success ≠ 255) :
    ∀ field ∈ pipeline kyber key entropyA entropyB, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.KernelSpecs.KemCompose.pipeline_valid_reject kyber key entropyA entropyB hvalid hlen hs

/-- An invalid key: everything is zero. -/
theorem kemc_pipeline_invalid (kyber : Bool) (key entropyA entropyB : List (BitVec 8)) (h : ¬ KeyValid key) :
    ∀ field ∈ pipeline kyber key entropyA entropyB, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.KernelSpecs.KemCompose.pipeline_invalid kyber key entropyA entropyB h

section
open TlsMpc.MlKemFastKernel Std.Tactic.BVDecide

/-- **The kernels compose to `pipeline`** when each input is bound to the output the worker binds
it to (hypotheses `h*`, the name binding between kernels: trusted C++). -/
theorem kemc_kernels_compose (kyber : Bool) (key entropyA entropyB : List (BitVec 8))
    (aH aN aV aF : BVExpr.Assignment) (aM aU : Nat → BVExpr.Assignment)
    (hH1 : (HybridKernel.lookup hashInputs "kyberPrekey").map (BVExpr.eval aH) = key)
    (hH2 : (HybridKernel.lookup hashInputs "entropyA").map (BVExpr.eval aH) = entropyA)
    (hH3 : (HybridKernel.lookup hashInputs "entropyB").map (BVExpr.eval aH) = entropyB)
    (hN : (HybridKernel.lookup nttInputs "coins").map (BVExpr.eval aN) = outVal (kemHash kyber) aH 2)
    (hM : ∀ i, (HybridKernel.lookup matrixInputs "kyberPrekey").map (BVExpr.eval (aM i)) = key)
    (hU1 : ∀ i, (HybridKernel.lookup (uInputs i) s!"row{i}").map (BVExpr.eval (aU i)) = outVal (kemMatrix i) (aM i) 0)
    (hU2 : ∀ i, (HybridKernel.lookup (uInputs i) "rhat").map (BVExpr.eval (aU i)) = outVal (kemNtt ()) aN 0)
    (hU3 : ∀ i, (HybridKernel.lookup (uInputs i) "coins").map (BVExpr.eval (aU i)) = outVal (kemHash kyber) aH 2)
    (hV1 : (HybridKernel.lookup vInputs "kyberPrekey").map (BVExpr.eval aV) = key)
    (hV2 : (HybridKernel.lookup vInputs "rhat").map (BVExpr.eval aV) = outVal (kemNtt ()) aN 0)
    (hV3 : (HybridKernel.lookup vInputs "coins").map (BVExpr.eval aV) = outVal (kemHash kyber) aH 2)
    (hV4 : (HybridKernel.lookup vInputs "message").map (BVExpr.eval aV) = outVal (kemHash kyber) aH 0)
    (hFu0 : (HybridKernel.lookup finishInputs "u0").map (BVExpr.eval aF) = outVal (kemU 0) (aU 0) 0)
    (hFu1 : (HybridKernel.lookup finishInputs "u1").map (BVExpr.eval aF) = outVal (kemU 1) (aU 1) 0)
    (hFu2 : (HybridKernel.lookup finishInputs "u2").map (BVExpr.eval aF) = outVal (kemU 2) (aU 2) 0)
    (hFu3 : (HybridKernel.lookup finishInputs "u3").map (BVExpr.eval aF) = outVal (kemU 3) (aU 3) 0)
    (hFv : (HybridKernel.lookup finishInputs "v").map (BVExpr.eval aF) = outVal (kemV ()) aV 0)
    (hFk : (HybridKernel.lookup finishInputs "kbar").map (BVExpr.eval aF) = outVal (kemHash kyber) aH 1)
    (hFo0 : (HybridKernel.lookup finishInputs "ok0").map (BVExpr.eval aF) = outVal (kemMatrix 0) (aM 0) 1)
    (hFo1 : (HybridKernel.lookup finishInputs "ok1").map (BVExpr.eval aF) = outVal (kemMatrix 1) (aM 1) 1)
    (hFo2 : (HybridKernel.lookup finishInputs "ok2").map (BVExpr.eval aF) = outVal (kemMatrix 2) (aM 2) 1)
    (hFo3 : (HybridKernel.lookup finishInputs "ok3").map (BVExpr.eval aF) = outVal (kemMatrix 3) (aM 3) 1)
    (hFkv : (HybridKernel.lookup finishInputs "keyValid").map (BVExpr.eval aF) = outVal (kemHash kyber) aH 3) :
    EstablishKernel.Kernel.values (kemFinish kyber) aF = pipeline kyber key entropyA entropyB :=
  TlsMpc.KernelSpecs.KemCompose.kernels_compose kyber key entropyA entropyB aH aN aV aF aM aU hH1 hH2 hH3 hN hM
    hU1 hU2 hU3 hV1 hV2 hV3 hV4 hFu0 hFu1 hFu2 hFu3 hFv hFk hFo0 hFo1 hFo2 hFo3 hFkv

end
end KemCompose

/-! ## 3. Gating and what each opening reveals (SECURITY_MAP C.3)

"Gating": an opened output is forced to a constant (usually zeros) when a check fails, so a
failed check reveals nothing but the failure. Only `typedOpen_gated` quantifies over a
deployed kernel's opened-field flags; the rest are at function or spec level and reach kernels
through the `_spec` theorems of section 2. The open marks themselves (which outputs the worker
lets out) are printed as the kernels declare them (section 1b, `layout_parse`,
`layout_openCode`; emitter batch). -/

open TlsMpc.TypedOpenKernel Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.HybridKernel (Kernel Shape lookup lookupFrom pub priv sl) in
/-- **`tls-open-typed` opens nothing on a rejected record:** for every input with
`accepted = 0`, the kernel's opened fields are exactly `[[0], [0, 0]]`. **K**. The only theorem
that quantifies over a kernel's opened-field flags. SECURITY_MAP C.3. -/
theorem typedOpen_gated (capacity : Nat) (assign : BVExpr.Assignment)
    (h : BVExpr.eval assign (HybridService.at' (lookup (typedInputs capacity) "accepted") 0) = 0) :
    ((tlsOpenTyped capacity).outputs.filter (·.opened)).map (fun field => field.value.map (BVExpr.eval assign)) =
      [[0], [0, 0]] :=
  TlsMpc.TypedOpenKernel.tlsOpenTyped_gated capacity assign h

open TlsMpc.TypedOpen Std.Tactic.BVDecide in
/-- **A rejected record parses to all zeros** (`accepted = 0`). **K-fn**. SECURITY_MAP C.3. -/
theorem typedOpen_rejected_parse (expanded nonce wire : List (BitVec 8)) (high low : BitVec 8) :
    RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0 =
      List.replicate
        ((RecordClass.openPlaintext Gcm.concrete ByteAuth.concrete expanded nonce wire high low).2.length + 4) 0 :=
  TlsMpc.TypedOpen.rejected_parse expanded nonce wire high low

open TlsMpc.TypedOpen Std.Tactic.BVDecide in
/-- **A rejected record's parse depends only on the record length:** the same for any keys,
nonces, contents and length bytes. **K-fn**. SECURITY_MAP C.3. -/
theorem typedOpen_rejected_independent (expanded nonce wire expanded' nonce' wire' : List (BitVec 8))
    (high low high' low' : BitVec 8) (he : expanded.length = 176) (he' : expanded'.length = 176)
    (hw : wire.length = wire'.length) :
    RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0 =
      RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded' nonce' wire' high' low' 0 :=
  TlsMpc.TypedOpen.rejected_independent expanded nonce wire expanded' nonce' wire' high low high' low' he he' hw

open TlsMpc.TypedOpen Std.Tactic.BVDecide in
/-- **On a rejected record the handshake bit is 0 and the two event bytes are `[0, 0]`.**
**K-fn**. SECURITY_MAP C.3. -/
theorem typedOpen_gating (state expanded nonce wire : List (BitVec 8)) (high low : BitVec 8) :
    handshakeBit ByteAuth.concrete
        (RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0) = 0 ∧
      (direct TlsMpc.Signal.Word64.concrete ByteAuth.concrete state
        (RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0)).take 2 = [0, 0] :=
  TlsMpc.TypedOpen.gating state expanded nonce wire high low

open TlsMpc.TypedOpen Std.Tactic.BVDecide in
/-- **The opened handshake bit is always 0 or 255** (one bit of information). **K-fn**.
SECURITY_MAP C.3. -/
theorem typedOpen_handshakeBit_cases (parsed : List (BitVec 8)) :
    handshakeBit ByteAuth.concrete parsed = 0 ∨ handshakeBit ByteAuth.concrete parsed = 255 :=
  TlsMpc.TypedOpen.handshakeBit_cases parsed

open TlsMpc.TypedOpen Std.Tactic.BVDecide in
/-- **A rejected record parses to `wire.length − 21 + 4` zeros.** **K-fn**. SECURITY_MAP C.3. -/
theorem typedOpen_rejected_parse_length (expanded nonce wire : List (BitVec 8)) (high low : BitVec 8)
    (he : expanded.length = 176) :
    RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0 =
      List.replicate (wire.length - 21 + 4) 0 :=
  TlsMpc.TypedOpen.rejected_parse_length expanded nonce wire high low he

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **On an application-data record the opened event does not depend on the content** (only
on the parser state, status and length bytes). **K** (through `class_fields` and
`frame_fields`). SECURITY_MAP C.3. -/
theorem tlsOpenApplication_event_private (parser : TlsPostHandshake.State (BitVec 8) (BitVec 64))
    (status high low : BitVec 8) (xs ys : List (BitVec 8)) (h : xs.length = ys.length) :
    (TlsPostHandshake.process Word64.concrete ByteAuth.concrete parser (status :: 23 :: high :: low :: xs)).take 2 =
    (TlsPostHandshake.process Word64.concrete ByteAuth.concrete parser (status :: 23 :: high :: low :: ys)).take 2 :=
  TlsMpc.HybridKernel.tlsOpenApplication_event_private parser status high low xs ys h

open TlsMpc.TlsPostHandshake Std.Tactic.BVDecide in
/-- **The parser's `finish` step gives the same event for any two application contents of the
same length.** **K-fn**. SECURITY_MAP C.3. -/
theorem postHandshake_application_event_independent (s : State (BitVec 8) (BitVec 64))
    (status high low : BitVec 8) (xs ys : List (BitVec 8))
    (left right : Scan (BitVec 8) (BitVec 64)) (h : xs.length = ys.length) :
    (finish TlsMpc.Signal.Word64.concrete ByteAuth.concrete s (status :: 23 :: high :: low :: xs) left).take 2 =
    (finish TlsMpc.Signal.Word64.concrete ByteAuth.concrete s (status :: 23 :: high :: low :: ys) right).take 2 :=
  TlsMpc.TlsPostHandshake.application_event_independent s status high low xs ys left right h

open TlsMpc.TlsPostHandshake Std.Tactic.BVDecide in
/-- **The parser's `process` gives the same event for any two application contents of the same
length.** **K-fn**. SECURITY_MAP C.3. -/
theorem postHandshake_process_event_independent (s : State (BitVec 8) (BitVec 64))
    (status high low : BitVec 8) (xs ys : List (BitVec 8)) (h : xs.length = ys.length) :
    (process TlsMpc.Signal.Word64.concrete ByteAuth.concrete s (status :: 23 :: high :: low :: xs)).take 2 =
    (process TlsMpc.Signal.Word64.concrete ByteAuth.concrete s (status :: 23 :: high :: low :: ys)).take 2 :=
  TlsMpc.TlsPostHandshake.process_application_event_independent s status high low xs ys h

open TlsMpc.TlsPostHandshake Std.Tactic.BVDecide in
/-- **An unauthenticated record (status ≠ 255) yields the event `[0, 0]`.** **K-fn**.
SECURITY_MAP C.3. -/
theorem postHandshake_reject_unauthenticated (s : State (BitVec 8) (BitVec 64)) (parsed : List (BitVec 8))
    (h : get ByteAuth.concrete parsed 0 ≠ 255) :
    (process TlsMpc.Signal.Word64.concrete ByteAuth.concrete s parsed).take 2 = [0,0] :=
  TlsMpc.TlsPostHandshake.reject_unauthenticated s parsed h

open TlsMpc.TlsPostHandshake Std.Tactic.BVDecide in
/-- **Once the parser has failed, every later event is `[0, 0]`.** **K-fn**. SECURITY_MAP
C.3. -/
theorem postHandshake_reject_failed (s : State (BitVec 8) (BitVec 64)) (parsed : List (BitVec 8))
    (h : s.bad ≠ 0) :
    (process TlsMpc.Signal.Word64.concrete ByteAuth.concrete s parsed).take 2 = [0,0] :=
  TlsMpc.TlsPostHandshake.reject_failed s parsed h

open TlsMpc.TlsPublicHandshake Std.Tactic.BVDecide in
/-- **The handshake-record gate passes only alert (21) and handshake (22) records; anything
else becomes zeros.** **K-fn** (inside `tls-open-handshake`, which has no kernel-level spec).
SECURITY_MAP C.3. -/
theorem publicHandshake_gate_value (parsed : List (BitVec 8)) : gate ByteAuth.concrete parsed =
    if parsed[1]?.getD 0 = 21 ∨ parsed[1]?.getD 0 = 22 then parsed else List.replicate parsed.length 0 :=
  TlsMpc.TlsPublicHandshake.gate_value parsed

open TlsMpc.TlsPublicHandshake Std.Tactic.BVDecide in
/-- **An application-data record (type 23) is never released by the handshake opener.**
**K-fn**. SECURITY_MAP C.3. -/
theorem publicHandshake_application_not_released (parsed : List (BitVec 8)) (kind : parsed[1]?.getD 0 = 23) :
    gate ByteAuth.concrete parsed = List.replicate parsed.length 0 :=
  TlsMpc.TlsPublicHandshake.application_not_released parsed kind

open TlsMpc.TlsProviderGate Std.Tactic.BVDecide in
/-- **The provider gate is 255 only when both the producer and upstream flags are 255.**
**K-fn**: `signal-seal-official`/`-built` gate their output twice with it
(HybridKernels.lean:458). Not listed in SECURITY_MAP C.3; found while building this file. -/
theorem providerGate_gate_value (producer upstream : BitVec 8) :
    gate ByteAuth.concrete producer upstream = if producer=255 ∧ upstream=255 then 255 else 0 :=
  TlsMpc.TlsProviderGate.gate_value producer upstream

open TlsMpc.TlsReceive Std.Tactic.BVDecide in
/-- **The exact-size opener outputs zeros on a wrong header.** **M**: about `openCore`/
`openParts` of the exact-size `tls-open-application`, not deployed. SECURITY_MAP C.3. -/
theorem tlsReceive_bad_header_zero (key iv sequence receivedHeader ciphertext receivedTag : List (BitVec 8))
    (hk : key.length = 16)
    (bad : receivedHeader ≠ TlsRecord.header Gcm.concrete (ciphertext.length + 16)) :
    openParts Gcm.concrete ByteAuth.concrete key iv sequence receivedHeader ciphertext receivedTag =
      List.replicate (ciphertext.length + 4) 0 :=
  TlsMpc.TlsReceive.bad_header_zero key iv sequence receivedHeader ciphertext receivedTag hk bad

open TlsMpc.TlsReceive Std.Tactic.BVDecide in
/-- **The exact-size opener outputs zeros on a wrong tag.** **M** (as above). SECURITY_MAP C.3. -/
theorem tlsReceive_bad_tag_zero (key iv sequence receivedHeader ciphertext receivedTag : List (BitVec 8))
    (hk : key.length = 16)
    (bad : Gcm.tag Gcm.concrete (Gcm.prepare Gcm.concrete key)
      (TlsRecord.nonce Gcm.concrete iv sequence) receivedHeader ciphertext ≠ receivedTag) :
    openParts Gcm.concrete ByteAuth.concrete key iv sequence receivedHeader ciphertext receivedTag =
      List.replicate (ciphertext.length + 4) 0 :=
  TlsMpc.TlsReceive.bad_tag_zero key iv sequence receivedHeader ciphertext receivedTag hk bad

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **A status of 0 releases only zeros:** the status and every field released under it are
zero. Generic helper of the receive `_rejects` lemmas. **K-fn**. SECURITY_MAP C.3. -/
theorem receive_released_zero (status : BitVec 8) (fields : List (List (BitVec 8))) (failed : status = 0) :
    ∀ field ∈ [status] :: fields.map (ByteAuth.release ByteAuth.concrete status), ∀ byte ∈ field, byte = 0 :=
  TlsMpc.ReceiveKernel.released_zero status fields failed

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`unsealStatic` with status 0 outputs only zeros.** **K** (via `receive_unsealStatic_spec`).
SECURITY_MAP C.3. -/
theorem receive_unsealStatic_rejects (size : Nat) (ourIdentity envelope agreement : List (BitVec 8))
    (failed : (ReceiveFirst.unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope
      agreement).getD 0 [] = [0]) :
    ∀ field ∈ ReceiveFirst.unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope
      agreement, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.ReceiveKernel.unsealStatic_rejects size ourIdentity envelope agreement failed

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`unsealMessage` with status 0 outputs only zeros.** **K**. SECURITY_MAP C.3. -/
theorem receive_unsealMessage_rejects (size : Nat) (envelope staticValid chain agreement : List (BitVec 8))
    (failed : (ReceiveFirst.unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid
      chain agreement).getD 0 [] = [0]) :
    ∀ field ∈ ReceiveFirst.unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid
      chain agreement, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.ReceiveKernel.unsealMessage_rejects size envelope staticValid chain agreement failed

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`contentParts` with status 0 outputs only zeros.** **K**. SECURITY_MAP C.3. -/
theorem receive_content_rejects (size cert : Nat) (hint : Bool) (content valid : List (BitVec 8))
    (failed : (ReceiveFirst.contentParts ByteAuth.concrete size cert hint content valid).getD 0 [] = [0]) :
    ∀ field ∈ ReceiveFirst.contentParts ByteAuth.concrete size cert hint content valid, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.ReceiveKernel.content_rejects size cert hint content valid failed

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`prekeyOpen` with status 0 outputs only zeros.** **K**. SECURITY_MAP C.3. -/
theorem receive_prekeyOpen_rejects (p : ReceiveFirst.PreKeyShape) (size : Nat)
    (message valid messageType senderIdentity : List (BitVec 8))
    (failed : (ReceiveFirst.prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity).getD 0 [] =
      [0]) :
    ∀ field ∈ ReceiveFirst.prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity,
      ∀ byte ∈ field, byte = 0 :=
  TlsMpc.ReceiveKernel.prekeyOpen_rejects p size message valid messageType senderIdentity failed

open TlsMpc.ReceiveKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`session` with status 0 outputs only zeros.** **K**. The accept direction (status 255 ⇒
MAC verified): `receiveAccept_session_status_iff` (section 3a). SECURITY_MAP C.3. -/
theorem receive_session_rejects (p : ReceiveFirst.PreKeyShape) (q : ReceiveFirst.SignalShape) (size jump : Nat)
    (message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement
      sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId : List (BitVec 8))
    (failed : (ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks
      senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
      ratchetPublic baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [0]) :
    ∀ field ∈ ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks
      senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
      ratchetPublic baseValid torsionX torsionY certificate accessKey requestId, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.ReceiveKernel.session_rejects p q size jump message checks senderIdentity ourIdentity localAddress uuid
    device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY
    certificate accessKey requestId failed

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`rebind` with status 0 outputs only zeros.** **K** (`bundle-rebind`). SECURITY_MAP C.3. -/
theorem bundle_rebind_rejects (record valid verified identityKey : List (BitVec 8))
    (failed : (BundleResponse.rebind ByteAuth.concrete record valid verified identityKey).getD 0 [] = [0]) :
    ∀ field ∈ BundleResponse.rebind ByteAuth.concrete record valid verified identityKey, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.BundleKernel.rebind_rejects record valid verified identityKey failed

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`bind` with status 0 outputs only zeros.** **M** (`bundle-bind` not deployed). -/
theorem bundle_bind_rejects (record valid verified identityKey : List (BitVec 8))
    (failed : (BundleResponse.bind ByteAuth.concrete record valid verified identityKey).getD 0 [] = [0]) :
    ∀ field ∈ BundleResponse.bind ByteAuth.concrete record valid verified identityKey, ∀ byte ∈ field, byte = 0 :=
  TlsMpc.BundleKernel.bind_rejects record valid verified identityKey failed

open TlsMpc.EstablishKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`Establish.establish` outputs only zeros when its checks fail.** **K** (`establish-session`).
SECURITY_MAP C.3. -/
theorem establish_rejects (size : Nat) (checks : List (BitVec 8))
    (dh1 dh2 dh3 oneTime kem ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey
      certificate uuid accessKey requestId device registration localRegistration oneTimeId signedId kyberId
      ciphertext : List (BitVec 8))
    (failed : Establish.accepted ByteAuth.concrete checks
      ([dh1, dh2, dh3] ++ (if oneTime.length = 0 then [] else [oneTime]) ++ [ratchetAgreement]) = 0) :
    ∀ field ∈ Establish.establish Sha256.concrete ByteAuth.concrete size checks dh1 dh2 dh3 oneTime kem
      ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey certificate uuid accessKey
      requestId device registration localRegistration oneTimeId signedId kyberId ciphertext,
      ∀ byte ∈ field, byte = 0 :=
  TlsMpc.EstablishKernel.establish_rejects size checks dh1 dh2 dh3 oneTime kem ratchetAgreement basePublic
    ratchetPublic senderPublic identityKey signedPrekey certificate uuid accessKey requestId device registration
    localRegistration oneTimeId signedId kyberId ciphertext failed

open TlsMpc.Signal TlsMpc.Signal.MlKemFast Std.Tactic.BVDecide in
/-- **ML-KEM finish outputs only zeros when a check fails.** **K** (`kem-finish`). SECURITY_MAP
C.3. -/
theorem mlkem_finish_rejects (kyber : Bool) (ciphertext kbar checks : List (BitVec 8))
    (failed : checks.foldl ByteAuth.concrete.and (ByteAuth.concrete.const 255) ≠ ByteAuth.concrete.const 255) :
    ∀ field ∈ finishStage ByteAuth.concrete Keccak.concrete kyber ciphertext kbar checks,
      ∀ byte ∈ field, byte = 0 :=
  TlsMpc.Signal.MlKemFast.finish_rejects kyber ciphertext kbar checks failed

open TlsMpc.Signal TlsMpc.Signal.MlKemFast Std.Tactic.BVDecide in
/-- **ML-KEM finish, when every check passes, outputs status 255, the ciphertext and the shared
secret** (accept direction). **K**. SECURITY_MAP C.3. -/
theorem mlkem_finish_accepts (kyber : Bool) (ciphertext kbar checks : List (BitVec 8))
    (passed : checks.foldl ByteAuth.concrete.and (ByteAuth.concrete.const 255) = ByteAuth.concrete.const 255) :
    finishStage ByteAuth.concrete Keccak.concrete kyber ciphertext kbar checks =
      [[255], ciphertext,
        if kyber then Keccak.shake256 Keccak.concrete 32 (kbar ++ Keccak.sha3_256 Keccak.concrete ciphertext) else kbar] :=
  TlsMpc.Signal.MlKemFast.finish_accepts kyber ciphertext kbar checks passed

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`contact-open` releases only zeros when its check fails.** **K**. SECURITY_MAP C.3. -/
theorem contactOpen_rejected (size : Nat) (assign : BVExpr.Assignment) (accepted : BitVec 8)
    (content : List (BitVec 8))
    (out : (contactOpen size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[accepted], content])
    (reject : accepted ≠ 255) : content = List.replicate size 0 :=
  TlsMpc.HybridKernel.contactOpen_rejected size assign accepted content out reject

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`contact-open` accepts iff the stored check equals the key's check value** (both
directions). **K**. SECURITY_MAP C.3. -/
theorem contactOpen_accepted_iff (size : Nat) (assign : BVExpr.Assignment) (accepted : BitVec 8)
    (content : List (BitVec 8))
    (out : (contactOpen size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[accepted], content]) :
    accepted = 255 ↔ inputValue assign (68 + size) 16 = checkOf (inputValue assign 0 60) :=
  TlsMpc.HybridKernel.contactOpen_accepted_iff size assign accepted content out

open TlsMpc.Signal TlsMpc.Signal.OpenResult Std.Tactic.BVDecide in
/-- **An unauthenticated Signal message opens to zeros.** **K-fn** (receive path). SECURITY_MAP
C.3. -/
theorem openResult_finish_reject_auth (candidate : List (BitVec 8)) (hlen : 16 ≤ candidate.length) :
    finish ByteAuth.concrete 0 candidate = List.replicate (9 + candidate.length) 0 :=
  TlsMpc.Signal.OpenResult.finish_reject_auth candidate hlen

open TlsMpc.Signal TlsMpc.Signal.OpenResult Std.Tactic.BVDecide in
/-- **A Signal message with bad padding opens to zeros.** **K-fn**. SECURITY_MAP C.3. -/
theorem openResult_finish_reject_padding (authenticated : BitVec 8) (candidate : List (BitVec 8))
    (hlen : 16 ≤ candidate.length)
    (bad : get ByteAuth.concrete
      (Unpad.decode ByteAuth.concrete (candidate.drop (candidate.length - 16))) 0 = 0) :
    finish ByteAuth.concrete authenticated candidate = List.replicate (9 + candidate.length) 0 :=
  TlsMpc.Signal.OpenResult.finish_reject_padding authenticated candidate hlen bad

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **The opened bundle shape flag is 255 exactly on JSON punctuation bytes** (it reveals the
response's structure, not its content). **K** (`bundle-shape`). SECURITY_MAP C.3. -/
theorem bundle_structural_value (c : BitVec 8) :
    BundleResponse.structural ByteAuth.concrete c = if c.toNat ∈ BundleResponse.punctuation then 255 else 0 :=
  TlsMpc.BundleKernel.structural_value c

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **The bundle shape has one flag per body byte.** **K**. SECURITY_MAP C.3. -/
theorem bundle_shape_length (body : List (BitVec 8)) :
    ((BundleResponse.shape ByteAuth.concrete body).getD 0 []).length = body.length :=
  TlsMpc.BundleKernel.shape_length body

open TlsMpc.BundleItemKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **The shape of a zero-padded body is the shape of the body followed by zeros** (padding
reveals nothing extra). **K**. SECURITY_MAP C.3. -/
theorem bundleItem_shape_padded (body : List (BitVec 8)) (k : Nat) :
    BundleResponse.shape ByteAuth.concrete (body ++ List.replicate k 0) =
      [(BundleResponse.shape ByteAuth.concrete body).getD 0 [] ++ List.replicate k 0] :=
  TlsMpc.BundleItemKernel.shape_padded body k

open TlsMpc.Ceremony in
/-- **A per-byte one-time pad hides the value:** for any opened word, any other party's share
and any target value there is exactly one mask that makes the opened result equal the target.
**ceremony** (the masked password). SECURITY_MAP C.3. -/
theorem ceremony_masked_hides (word other value : BitVec 8) :
    ∃ mask : BitVec 8, word ^^^ (other ^^^ mask) = value ∧ ∀ m : BitVec 8, word ^^^ (other ^^^ m) = value → m = mask :=
  TlsMpc.Ceremony.masked_hides word other value

open TlsMpc.Signal TlsMpc.Signal.PreKeyValidation Std.Tactic.BVDecide in
/-- **Prekey validation's result: status 255 and the bundle when the code is 0, otherwise
zeros.** **M** (the deployment does not use `PreKeyValidation`). SECURITY_MAP C.5. -/
theorem preKeyValidation_finish_spec (constructed : List (BitVec 8)) (trust ec pq : BitVec 8) :
    finish ByteAuth.concrete constructed trust ec pq =
      let missing := OpenResult.get ByteAuth.concrete constructed 1
      let code := if missing = 0 then prefixSpec trust ec pq else missing
      [if code = 0 then 255 else 0,code] ++
        (if code = 0 then constructed.drop 2 else List.replicate (constructed.length-2) 0) :=
  TlsMpc.Signal.PreKeyValidation.finish_spec constructed trust ec pq

/-! ### 3a. Receive, accept direction (T13): what an accepted receive implies and opens
(`TlsMpc/KernelSpecs/{ReceiveAccept, ReceiveAcceptText, ReceiveAcceptAccessKey}.lean`)

`receive-session` status 255 holds exactly when the MAC verified under libsignal's keys and the
other checks passed; with the controller's wiring it also implies the certificate checks; every
receive kernel's refusal releases nothing, and what an accepted one opens is stated. The opened
field names of every receive kernel are listed (`receiveAccept_opened_*`). **K** (the session,
text and access-key kernels on concrete values), **K-fn** where stated. The DEFECT recorded here
before (`receive-text` accepted a body longer than its DataMessage) is fixed in the emitter batch
and takes effect after the re-lowering: `receiveAcceptText_overlongBody_refused`, and
`receive-text` now accepts exactly what the reference parse accepts for covered widths
(`receiveAcceptText_accepted_iff_reference`; NEEDS_REVIEW.md 3f). -/

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`receive-session` status 255, exactly.** The status is 255 if and only if

* every earlier check byte (`prekeyValid`, `verified`) is 255 and no agreement is all zero;
* the PreKeySignalMessage has layout `p`, carries the sender identity `senderIdentity`;
* the base key is a valid, torsion-free point (`baseValid`, `torsionX`, `torsionY`);
* the SignalMessage has layout `q` and, if it carries addresses, they are (sender, us);
* its counter is some `n ≤ jump` and its post-quantum index some `1 + i ≤ 1 + jump`;
* the MAC verifies under libsignal's MAC key for chain key `n` and post-quantum key `i`
  (`MessageMac.tag`: HMAC-SHA256 over `05 ‖ sender ‖ 05 ‖ us ‖ message`, first 8 bytes); and
* the AES-256-CBC decryption under the cipher key and IV of those same keys has valid padding. -/
theorem receiveAccept_session_status_iff (p : PreKeyShape) (q : SignalShape) (size : Nat) (jump : Nat) (message : List (BitVec 8)) (checks : List (BitVec 8)) (senderIdentity : List (BitVec 8)) (ourIdentity : List (BitVec 8)) (localAddress : List (BitVec 8)) (uuid : List (BitVec 8)) (device : List (BitVec 8)) (dh1 : List (BitVec 8)) (dh2 : List (BitVec 8)) (dh3 : List (BitVec 8)) (oneTime : List (BitVec 8)) (kem : List (BitVec 8)) (receiveAgreement : List (BitVec 8)) (sendAgreement : List (BitVec 8)) (ratchetPublic : List (BitVec 8)) (baseValid : List (BitVec 8)) (torsionX : List (BitVec 8)) (torsionY : List (BitVec 8)) (certificate : List (BitVec 8)) (accessKey : List (BitVec 8)) (requestId : List (BitVec 8)) (hjump : jump ≤ 16) :
    (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [255] ↔
    ((∀ c ∈ checks, c = 255) ∧
      (∀ g ∈ [dh1, dh2, dh3, oneTime, receiveAgreement, sendAgreement], g ≠ List.replicate 32 0) ∧
      prekeyMask ByteAuth.concrete p size message = 255 ∧
      Establish.part message (p.keysAt + 38) 32 = senderIdentity ∧
      baseValid = ByteAuth.concrete.const 1 :: List.replicate 31 (ByteAuth.concrete.const 0) ∧
      torsionX = List.replicate 32 (ByteAuth.concrete.const 0) ∧
      torsionY = List.replicate 32 (ByteAuth.concrete.const 0) ∧
      signalMask ByteAuth.concrete q (p.signalSize size) (signalWire p size message)
        (expectedAddresses localAddress uuid device) = 255) ∧
    ∃ n, (n ≤ jump ∧ counterBytes q (signalWire p size message) = numberBytes ByteAuth.concrete n) ∧
    ∃ i, (i ≤ jump ∧ pqIndexBytes q (p.signalSize size) (signalWire p size message) =
        numberBytes ByteAuth.concrete (1 + i)) ∧
      MessageMac.tag Sha256.concrete
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.macKey
          senderIdentity ourIdentity (MessageMac.content (signalWire p size message)) =
        MessageMac.receivedTag (signalWire p size message) ∧
      OpenResult.get ByteAuth.concrete (CbcOpen.openCore AesInverse.concrete ByteAuth.concrete
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.cipherKey
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.iv
          (Establish.part (signalWire p size message) q.cipherAt q.ciphertext)) 0 = 255 :=
  TlsMpc.KernelSpecs.ReceiveAccept.session_status_iff p q size jump message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId hjump

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **What `receive-session` releases when its status is 255.** For the counter `n` and
post-quantum index `1 + i` of `session_status_iff`:

* `plaintext` (output 3, the input of `receive-text` and `receive-access-key`) is exactly the
  AES-256-CBC decryption with PKCS#7 unpadding (`CbcOpen.openCore`, without its status byte) of the
  message's ciphertext under libsignal's cipher key and IV for that counter;
* the receiver record (output 2) stores the root key, the NEXT chain key (`n + 1`), the sender's
  ratchet key, the next counter, the post-quantum root, the next post-quantum chain key, the index
  and the sender's base key;
* the conversation record (output 1) is the send kernels' record built from the session keys. -/
theorem receiveAccept_session_accept_outputs (p : PreKeyShape) (q : SignalShape) (size : Nat) (jump : Nat) (message : List (BitVec 8)) (checks : List (BitVec 8)) (senderIdentity : List (BitVec 8)) (ourIdentity : List (BitVec 8)) (localAddress : List (BitVec 8)) (uuid : List (BitVec 8)) (device : List (BitVec 8)) (dh1 : List (BitVec 8)) (dh2 : List (BitVec 8)) (dh3 : List (BitVec 8)) (oneTime : List (BitVec 8)) (kem : List (BitVec 8)) (receiveAgreement : List (BitVec 8)) (sendAgreement : List (BitVec 8)) (ratchetPublic : List (BitVec 8)) (baseValid : List (BitVec 8)) (torsionX : List (BitVec 8)) (torsionY : List (BitVec 8)) (certificate : List (BitVec 8)) (accessKey : List (BitVec 8)) (requestId : List (BitVec 8)) (hjump : jump ≤ 16)
    (h : (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [255]) :
    ∃ n i, (n ≤ jump ∧ counterBytes q (signalWire p size message) = numberBytes ByteAuth.concrete n) ∧
      (i ≤ jump ∧ pqIndexBytes q (p.signalSize size) (signalWire p size message) =
        numberBytes ByteAuth.concrete (1 + i)) ∧
      (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
        ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
        baseValid torsionX torsionY certificate accessKey requestId).getD 1 [] =
        certificate ++ Establish.session ByteAuth.concrete 80 ratchetPublic
          (Establish.part (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) 96 32)
          (Establish.part (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) 192 32)
          ourIdentity senderIdentity ++
        Establish.metadata ByteAuth.concrete uuid accessKey requestId device
          (varintValue ByteAuth.concrete (Establish.part message (p.idsAt size + 1) p.registration)) ∧
      (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
        ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
        baseValid torsionX torsionY certificate accessKey requestId).getD 2 [] =
        Establish.part (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) 64 32 ++
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).nextChainKey ++
          Establish.part (signalWire p size message) 4 32 ++
          ChainSend.nextCounter Sha256.concrete ByteAuth.concrete (counterBytes q (signalWire p size message)) ++
          Establish.part (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) 128 32 ++
          Establish.part (pqMaterial (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump i) 0 32 ++
          pqIndexBytes q (p.signalSize size) (signalWire p size message) ++
          Establish.part message (p.keysAt + 3) 32 ∧
      (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
        ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
        baseValid torsionX torsionY certificate accessKey requestId).getD 3 [] =
        (CbcOpen.openCore AesInverse.concrete ByteAuth.concrete
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.cipherKey
          (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.iv
          (Establish.part (signalWire p size message) q.cipherAt q.ciphertext)).drop 1 :=
  TlsMpc.KernelSpecs.ReceiveAccept.session_accept_outputs p q size jump message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId hjump h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`receive-session`'s status is 255 or 0** (so `session_rejects` covers every non-accepted
status: nothing is ever released under a partial mask). -/
theorem receiveAccept_session_status_cases (p : PreKeyShape) (q : SignalShape) (size : Nat) (jump : Nat) (message : List (BitVec 8)) (checks : List (BitVec 8)) (senderIdentity : List (BitVec 8)) (ourIdentity : List (BitVec 8)) (localAddress : List (BitVec 8)) (uuid : List (BitVec 8)) (device : List (BitVec 8)) (dh1 : List (BitVec 8)) (dh2 : List (BitVec 8)) (dh3 : List (BitVec 8)) (oneTime : List (BitVec 8)) (kem : List (BitVec 8)) (receiveAgreement : List (BitVec 8)) (sendAgreement : List (BitVec 8)) (ratchetPublic : List (BitVec 8)) (baseValid : List (BitVec 8)) (torsionX : List (BitVec 8)) (torsionY : List (BitVec 8)) (certificate : List (BitVec 8)) (accessKey : List (BitVec 8)) (requestId : List (BitVec 8)) :
    (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [255] ∨
    (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [0] :=
  TlsMpc.KernelSpecs.ReceiveAccept.session_status_cases p q size jump message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **T13, accept direction, composed.** With the controller's wiring (the session's `verified`
check byte is `receive-certificate-verified`'s output on `receive-certificate`'s validity and
signature), `receive-session` status 255 implies:

* the message MAC verified under libsignal's keys for some counter `n ≤ jump` and post-quantum
  index `1 + i` (`session_status_iff`);
* the certificate's validity checks passed (`certificate_valid`: identity key, trusted signer,
  device id, expiry, layout);
* the server key decoded to a curve point and the signature's `R` is the compression of the field
  engine's `[s]B − [h]A` (`rx`, `ry`) with `s < 2^253` (`certificateVerified_iff`), where `h` is
  `receive-certificate`'s challenge over the certificate body. -/
theorem receiveAccept_session_accept_certificate {H R : Type} (hh : XEdDsaSha512.Ops (BitVec 8) H) (rr : XEdDsaScalar.Ops (BitVec 8) R)
    (p : PreKeyShape) (q : SignalShape) (size jump : Nat) (hjump : jump ≤ 16)
    (message prekeyValid senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement
      sendAgreement ratchetPublic baseValid torsionX torsionY certificate' accessKey requestId : List (BitVec 8))
    (cert : Nat) (c : CertShape) (bytes contentValid signer now serverX serverY serverValid rx ry : List (BitVec 8))
    (h : (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message
      (prekeyValid ++ (certificateVerified ByteAuth.concrete
        ((certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 0 [])
        ((certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 3 [])
        serverValid rx ry).getD 0 [])
      senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
      ratchetPublic baseValid torsionX torsionY certificate' accessKey requestId).getD 0 [] = [255]) :
    (∃ n, (n ≤ jump ∧ counterBytes q (signalWire p size message) = numberBytes ByteAuth.concrete n) ∧
      ∃ i, (i ≤ jump ∧ pqIndexBytes q (p.signalSize size) (signalWire p size message) =
          numberBytes ByteAuth.concrete (1 + i)) ∧
        MessageMac.tag Sha256.concrete
            (messageStep (keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement) jump n i).material.macKey
            senderIdentity ourIdentity (MessageMac.content (signalWire p size message)) =
          MessageMac.receivedTag (signalWire p size message)) ∧
    (certificate ByteAuth.concrete hh rr cert c bytes contentValid senderIdentity signer now serverX serverY).getD 0 [] =
      [255] ∧
    Establish.part bytes (bodyAt cert + c.e164 + 14) 32 = senderIdentity ∧
    Establish.part bytes (if c.embedded then bodyAt cert + c.e164 + 48 else bodyAt cert + c.e164 + 46 + 2 + c.uuidSize + 1)
      c.signerSize = signer ∧
    atMost ByteAuth.concrete now (Establish.part bytes (bodyAt cert + c.e164 + 3) 8).reverse = 255 ∧
    serverValid = ByteAuth.concrete.const 1 :: List.replicate 31 (ByteAuth.concrete.const 0) ∧
    (OpenResult.get ByteAuth.concrete (Establish.part bytes (bodyAt cert + c.body + 2) 64) 63 &&& 127).toNat < 32 ∧
    (Establish.part bytes (bodyAt cert + c.body + 2) 64).take 32 = XEdDsa.compress ByteAuth.concrete rx ry :=
  TlsMpc.KernelSpecs.ReceiveAccept.session_accept_certificate hh rr p q size jump hjump message prekeyValid senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY certificate' accessKey requestId cert c bytes contentValid signer now serverX serverY serverValid rx ry h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`receive-text` is gated by `receive-session`** (definition level): if the session's status
is not 255, every output of `receive-text` on the session's plaintext is zero (status, length,
text and layout). -/
theorem receiveAccept_text_zero_unless_accepted (p : PreKeyShape) (q : SignalShape) (size : Nat) (jump : Nat) (message : List (BitVec 8)) (checks : List (BitVec 8)) (senderIdentity : List (BitVec 8)) (ourIdentity : List (BitVec 8)) (localAddress : List (BitVec 8)) (uuid : List (BitVec 8)) (device : List (BitVec 8)) (dh1 : List (BitVec 8)) (dh2 : List (BitVec 8)) (dh3 : List (BitVec 8)) (oneTime : List (BitVec 8)) (kem : List (BitVec 8)) (receiveAgreement : List (BitVec 8)) (sendAgreement : List (BitVec 8)) (ratchetPublic : List (BitVec 8)) (baseValid : List (BitVec 8)) (torsionX : List (BitVec 8)) (torsionY : List (BitVec 8)) (certificate : List (BitVec 8)) (accessKey : List (BitVec 8)) (requestId : List (BitVec 8)) (capacity : Nat)
    (hne : (session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
      ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
      baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] ≠ [255]) :
    ∀ field ∈ text ByteAuth.concrete capacity
        ((session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks senderIdentity
          ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic
          baseValid torsionX torsionY certificate accessKey requestId).getD 3 []),
      ∀ b ∈ field, b = 0 :=
  TlsMpc.KernelSpecs.ReceiveAccept.text_zero_unless_accepted p q size jump message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId capacity hne

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`receive-text` is gated by `receive-session`** (kernel level): when the `plaintext` input of
`receive-text` is the `plaintext` output of `receive-session` (the controller's wiring) and the
session's opened `status` is not 255, every output of `receive-text` (all four opened) is zero. -/
theorem receiveAccept_receiveText_gated (cert size : Nat) (p : PreKeyShape) (q : SignalShape) (jump ciphertext capacity : Nat)
    (assign assign' : BVExpr.Assignment)
    (wired : (HybridKernel.lookup (ReceiveKernel.textInputs ciphertext) "plaintext").map (BVExpr.eval assign') =
      (values (ReceiveKernel.session cert size p q jump) assign).getD 3 [])
    (rejected : (values (ReceiveKernel.session cert size p q jump) assign).getD 0 [] ≠ [255]) :
    ∀ field ∈ values (ReceiveKernel.text ciphertext capacity) assign', ∀ b ∈ field, b = 0 :=
  TlsMpc.KernelSpecs.ReceiveAccept.receiveText_gated cert size p q jump ciphertext capacity assign assign' wired rejected

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`receive-certificate-verified` is 255 exactly when** the certificate's other checks passed
(`certificateValid` 255), the server key decoded to a curve point (`serverValid` is the field
value 1), and the point `rx, ry` (the field engine's `[s]B − [h]A` for the signature's `s` and the
challenge `h` of `receive-certificate`) compresses to the signature's `R`, with `s`'s bits 253, 254
clear (libsignal's `xeddsa` verify, `R == [s]B − [h]A`). -/
theorem receiveAccept_certificateVerified_iff (certificateValid signature serverValid rx ry : List (BitVec 8)) :
    (certificateVerified ByteAuth.concrete certificateValid signature serverValid rx ry).getD 0 [] = [255] ↔
      OpenResult.get ByteAuth.concrete certificateValid 0 = 255 ∧
      serverValid = ByteAuth.concrete.const 1 :: List.replicate 31 (ByteAuth.concrete.const 0) ∧
      signature.length = 64 ∧ rx.length = 32 ∧ ry.length = 32 ∧
      (OpenResult.get ByteAuth.concrete signature 63 &&& 127).toNat < 32 ∧
      signature.take 32 = XEdDsa.compress ByteAuth.concrete rx ry :=
  TlsMpc.KernelSpecs.ReceiveAccept.certificateVerified_iff certificateValid signature serverValid rx ry

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **What `receive-certificate`'s validity says** (for the public shape `cert`, `c`): the content
stage was valid; the certificate's identity key is `senderIdentity` (the key decrypted from the
envelope's static part); its signer (embedded server certificate, or server id) is the trusted
`signer`; its device id is in 1..127; `now ≤ expires` (`atMost` is the big-endian comparison,
`atMost_value`); and the layout masks (field tags, lengths, the UUID's form) hold. -/
theorem receiveAccept_certificate_valid {H R : Type} (h : XEdDsaSha512.Ops (BitVec 8) H) (r : XEdDsaScalar.Ops (BitVec 8) R)
    (cert : Nat) (c : CertShape) (bytes valid senderIdentity signer now serverX serverY : List (BitVec 8))
    (hv : (certificate ByteAuth.concrete h r cert c bytes valid senderIdentity signer now serverX serverY).getD 0 [] =
      [255]) :
    OpenResult.get ByteAuth.concrete valid 0 = 255 ∧
    Establish.part bytes (bodyAt cert + c.e164 + 14) 32 = senderIdentity ∧
    Establish.part bytes (if c.embedded then bodyAt cert + c.e164 + 48 else bodyAt cert + c.e164 + 46 + 2 + c.uuidSize + 1)
      c.signerSize = signer ∧
    (OpenResult.get ByteAuth.concrete bytes (bodyAt cert + c.e164 + 1)).toNat < 128 ∧
    OpenResult.get ByteAuth.concrete bytes (bodyAt cert + c.e164 + 1) ≠ 0 ∧
    atMost ByteAuth.concrete now (Establish.part bytes (bodyAt cert + c.e164 + 3) 8).reverse = 255 ∧
    Establish.part bytes (bodyAt cert + c.e164) 1 = lit ByteAuth.concrete [16] ∧
    Establish.part bytes (bodyAt cert + c.e164 + 2) 1 = lit ByteAuth.concrete [25] ∧
    Establish.part bytes (bodyAt cert + c.e164 + 11) 3 = lit ByteAuth.concrete [34, 33, 5] ∧
    Establish.part bytes (bodyAt cert + c.body) 2 = lit ByteAuth.concrete [18, 64] :=
  TlsMpc.KernelSpecs.ReceiveAccept.certificate_valid h r cert c bytes valid senderIdentity signer now serverX serverY hv

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`receive-unseal-static` is valid exactly when** the envelope has the v1 layout, the
encrypted static key's 10-byte MAC verifies under the MAC key of `ephemeralKeys`, the agreement is
not all zero, and the decrypted static key starts with the key type `05`. -/
theorem receiveAccept_unsealStatic_valid_iff (size : Nat) (ourIdentity envelope agreement : List (BitVec 8)) :
    (unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope agreement).getD 0 [] =
        [255] ↔
      envelopeMask ByteAuth.concrete size envelope = 255 ∧
      macMatches (Establish.part (ephemeralKeys ourIdentity envelope agreement) 64 32) (Establish.part envelope 38 43) ∧
      agreement ≠ List.replicate 32 0 ∧
      OpenResult.get ByteAuth.concrete
        (ctrOpen (Establish.part (ephemeralKeys ourIdentity envelope agreement) 32 32) (Establish.part envelope 38 43)) 0 =
        ByteAuth.concrete.const 5 :=
  TlsMpc.KernelSpecs.ReceiveAccept.unsealStatic_valid_iff size ourIdentity envelope agreement

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **What `receive-unseal-static` outputs when valid**: the sender's identity key is the
decrypted static key without its type byte, and the chain key is the first 32 bytes of
`ephemeralKeys`. -/
theorem receiveAccept_unsealStatic_outputs (size : Nat) (ourIdentity envelope agreement : List (BitVec 8))
    (h : (unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope agreement).getD 0 [] =
      [255]) :
    (unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope agreement).getD 1 [] =
        (ctrOpen (Establish.part (ephemeralKeys ourIdentity envelope agreement) 32 32)
          (Establish.part envelope 38 43)).drop 1 ∧
      (unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope agreement).getD 2 [] =
        (ephemeralKeys ourIdentity envelope agreement).take 32 :=
  TlsMpc.KernelSpecs.ReceiveAccept.unsealStatic_outputs size ourIdentity envelope agreement h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`receive-unseal-message` is valid exactly when** the first half was valid, the encrypted
message's 10-byte MAC verifies under the MAC key of `staticKeys`, the agreement is not all zero,
and the decrypted UnidentifiedSenderMessageContent starts `08 type 12` followed by a two-byte
varint (the certificate's length prefix). -/
theorem receiveAccept_unsealMessage_valid_iff (size : Nat) (envelope staticValid chain agreement : List (BitVec 8)) :
    (unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid chain agreement).getD 0 [] =
        [255] ↔
      OpenResult.get ByteAuth.concrete staticValid 0 = 255 ∧
      macMatches (Establish.part (staticKeys envelope chain agreement) 64 32) (envelope.drop (messageAt size)) ∧
      agreement ≠ List.replicate 32 0 ∧
      Establish.part (ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32) (envelope.drop (messageAt size)))
        0 1 = lit ByteAuth.concrete [8] ∧
      Establish.part (ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32) (envelope.drop (messageAt size)))
        2 1 = lit ByteAuth.concrete [18] ∧
      varintShape ByteAuth.concrete
        (ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32) (envelope.drop (messageAt size))) 3 2 = 255 :=
  TlsMpc.KernelSpecs.ReceiveAccept.unsealMessage_valid_iff size envelope staticValid chain agreement

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **What `receive-unseal-message` outputs when valid**: the content is the AES-256-CTR decryption
under `staticKeys`, and the opened `certificateLength` is its bytes 3..5 (the length prefix of
field 2, the sender certificate). -/
theorem receiveAccept_unsealMessage_outputs (size : Nat) (envelope staticValid chain agreement : List (BitVec 8))
    (h : (unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid chain agreement).getD 0 [] =
      [255]) :
    (unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid chain agreement).getD 1 [] =
        ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32) (envelope.drop (messageAt size)) ∧
      (unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid chain agreement).getD 2 [] =
        Establish.part (ctrOpen (Establish.part (staticKeys envelope chain agreement) 32 32)
          (envelope.drop (messageAt size))) 3 2 :=
  TlsMpc.KernelSpecs.ReceiveAccept.unsealMessage_outputs size envelope staticValid chain agreement h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`receive-prekey-open` is valid exactly when** the content stage was valid, the message type
is PREKEY_MESSAGE (1), the PreKeySignalMessage has layout `p` (`prekeyMask`), its identity key is
the certificate's (`senderIdentity`), its base key is below `2^255 − 19` (`canonicalRange`), and
the inner SignalMessage starts with the ratchet key's header `0A 21 05`. -/
theorem receiveAccept_prekeyOpen_valid_iff (p : PreKeyShape) (size : Nat) (message valid messageType senderIdentity : List (BitVec 8)) :
    (prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity).getD 0 [] = [255] ↔
      OpenResult.get ByteAuth.concrete valid 0 = 255 ∧
      OpenResult.get ByteAuth.concrete messageType 0 = ByteAuth.concrete.const 1 ∧
      prekeyMask ByteAuth.concrete p size message = 255 ∧
      Establish.part message (p.keysAt + 38) 32 = senderIdentity ∧
      canonicalRange ByteAuth.concrete (Establish.part message (p.keysAt + 3) 32) = 255 ∧
      Establish.part message (p.signalAt size + 1) 3 = lit ByteAuth.concrete [10, 33, 5] :=
  TlsMpc.KernelSpecs.ReceiveAccept.prekeyOpen_valid_iff p size message valid messageType senderIdentity

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **What `receive-prekey-open` releases when valid**: the base key and ratchet key (private), and
the opened ids and Kyber ciphertext are the message's own fields: the varint values of the
one-time, signed and Kyber prekey ids (4 bytes big endian) and the 1,568 bytes after `42 A1 0C 08`. -/
theorem receiveAccept_prekeyOpen_outputs (p : PreKeyShape) (size : Nat) (message valid messageType senderIdentity : List (BitVec 8))
    (h : (prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity).getD 0 [] = [255]) :
    prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity =
      [[255], Establish.part message (p.keysAt + 3) 32, Establish.part message (p.signalAt size + 4) 32,
        varintValue ByteAuth.concrete (Establish.part message 2 p.oneTime),
        varintValue ByteAuth.concrete (Establish.part message (p.idsAt size + 2 + p.registration) p.signed),
        varintValue ByteAuth.concrete (Establish.part message (p.idsAt size + 3 + p.registration + p.signed) p.kyber),
        Establish.part message (p.idsAt size + 3 + p.registration + p.signed + p.kyber + 4) 1568] :=
  TlsMpc.KernelSpecs.ReceiveAccept.prekeyOpen_outputs p size message valid messageType senderIdentity h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.contentShape_rejects`. -/
theorem receiveAccept_contentShape_rejects (size cert : Nat) (content valid : List (BitVec 8))
    (h : OpenResult.get ByteAuth.concrete valid 0 ≠ 255) :
    ∀ field ∈ contentShape ByteAuth.concrete size cert content valid, ∀ b ∈ field, b = 0 :=
  TlsMpc.KernelSpecs.ReceiveAccept.contentShape_rejects size cert content valid h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.prekeyShape_rejects`. -/
theorem receiveAccept_prekeyShape_rejects (size : Nat) (m valid : List (BitVec 8)) (h : OpenResult.get ByteAuth.concrete valid 0 ≠ 255) :
    ∀ field ∈ prekeyShape ByteAuth.concrete size m valid, ∀ b ∈ field, b = 0 :=
  TlsMpc.KernelSpecs.ReceiveAccept.prekeyShape_rejects size m valid h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.signalShape_rejects`. -/
theorem receiveAccept_signalShape_rejects (p : PreKeyShape) (size : Nat) (m valid : List (BitVec 8))
    (h : OpenResult.get ByteAuth.concrete valid 0 ≠ 255) :
    ∀ field ∈ signalShape ByteAuth.concrete p size m valid, ∀ b ∈ field, b = 0 :=
  TlsMpc.KernelSpecs.ReceiveAccept.signalShape_rejects p size m valid h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- **`atMost` is the big-endian comparison**: for byte strings of equal length, 255 exactly when
the value of `x` is at most the value of `y`. -/
theorem receiveAccept_atMost_value (x y : List (BitVec 8)) (hl : x.length = y.length) :
    atMost ByteAuth.concrete x y = mk (val (bitsOf x) ≤ val (bitsOf y)) :=
  TlsMpc.KernelSpecs.ReceiveAccept.atMost_value x y hl

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_unsealStatic`. -/
theorem receiveAccept_opened_unsealStatic (size : Nat) : openedNames (ReceiveKernel.unsealStatic size) = [] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_unsealStatic size

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_unsealMessage`. -/
theorem receiveAccept_opened_unsealMessage (size : Nat) :
    openedNames (ReceiveKernel.unsealMessage size) = ["certificateLength"] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_unsealMessage size

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_contentShape`. -/
theorem receiveAccept_opened_contentShape (size cert : Nat) : openedNames (ReceiveKernel.contentShape size cert) = ["shape"] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_contentShape size cert

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_content`. -/
theorem receiveAccept_opened_content (size cert : Nat) (hint : Bool) : openedNames (ReceiveKernel.content size cert hint) = [] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_content size cert hint

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_certificate`. -/
theorem receiveAccept_opened_certificate (cert : Nat) (c : CertShape) : openedNames (ReceiveKernel.certificate cert c) = [] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_certificate cert c

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_certificateVerified`. -/
theorem receiveAccept_opened_certificateVerified : openedNames (ReceiveKernel.certificateVerified ()) = [] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_certificateVerified

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_prekeyShape`. -/
theorem receiveAccept_opened_prekeyShape (size : Nat) : openedNames (ReceiveKernel.prekeyShape size) = ["shape"] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_prekeyShape size

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_prekeyOpen`. -/
theorem receiveAccept_opened_prekeyOpen (size : Nat) (p : PreKeyShape) :
    openedNames (ReceiveKernel.prekeyOpen size p) =
      ["oneTimePrekeyId", "signedPrekeyId", "kyberPrekeyId", "kyberCiphertext"] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_prekeyOpen size p

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_signalShape`. -/
theorem receiveAccept_opened_signalShape (size : Nat) (p : PreKeyShape) : openedNames (ReceiveKernel.signalShape size p) = ["shape"] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_signalShape size p

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_session`. -/
theorem receiveAccept_opened_session (cert size : Nat) (p : PreKeyShape) (q : SignalShape) (jump : Nat) :
    openedNames (ReceiveKernel.session cert size p q jump) = ["status"] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_session cert size p q jump

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_text`. -/
theorem receiveAccept_opened_text (ciphertext capacity : Nat) :
    openedNames (ReceiveKernel.text ciphertext capacity) = ["status", "length", "text", "layout"] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_text ciphertext capacity

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_accessKey`. -/
theorem receiveAccept_opened_accessKey (cert ciphertext offset : Nat) :
    openedNames (ReceiveKernel.accessKey cert ciphertext offset) = ["status"] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_accessKey cert ciphertext offset

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
open TlsMpc.ReceiveKernel (values) in
/-- `ReceiveAccept.opened_envelopePoint`. -/
theorem receiveAccept_opened_envelopePoint (size : Nat) : openedNames (ReceiveKernel.envelopePoint size) = [] :=
  TlsMpc.KernelSpecs.ReceiveAccept.opened_envelopePoint size
open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **`receive-text`, exactly**, for `capacity < 65536`: with `c` the content (the plaintext after
its 8-byte length), the status is `mk (Accepted c capacity)`; the length is the body length
(released under the status); text byte `i` is content byte `bodyStart + i` when accepted and
`i < bodyLength`, else 0; the layout flags say which of the two prefixes have two bytes (released
under the status). -/
theorem receiveAcceptText_text_eq (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8)) :
    text ByteAuth.concrete capacity plain =
      [[mk (Accepted (plain.drop 8) capacity)],
        ByteAuth.release ByteAuth.concrete (mk (Accepted (plain.drop 8) capacity))
          [BitVec.ofNat 8 ((highByte (plain.drop 8)).toNat / 2),
            BitVec.ofNat 8 ((lowByte (plain.drop 8)).toNat % 128 + 128 * ((highByte (plain.drop 8)).toNat % 2))],
        (List.range capacity).map (fun i =>
          if Accepted (plain.drop 8) capacity ∧ ¬ bodyLength (plain.drop 8) ≤ i then
            g (plain.drop 8) (bodyStart (plain.drop 8) + i) else 0),
        ByteAuth.release ByteAuth.concrete (mk (Accepted (plain.drop 8) capacity))
          [mk (¬Wide (plain.drop 8) ∧ ¬Long (plain.drop 8)), mk (¬(Wide (plain.drop 8) ↔ Long (plain.drop 8))),
            mk (Wide (plain.drop 8) ∧ Long (plain.drop 8))]] :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.text_eq capacity hcap plain

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **`receive-text`'s status is 255 exactly when the content passes `Accepted`** (and 0 otherwise). -/
theorem receiveAcceptText_text_status (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8)) :
    (text ByteAuth.concrete capacity plain).getD 0 [] = [mk (Accepted (plain.drop 8) capacity)] :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.text_status capacity hcap plain

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **A refused `receive-text` releases nothing** (the missing `_rejects` lemma): when the content
fails `Accepted`, every output byte is zero. -/
theorem receiveAcceptText_text_rejects (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8))
    (h : ¬Accepted (plain.drop 8) capacity) :
    ∀ field ∈ text ByteAuth.concrete capacity plain, ∀ b ∈ field, b = 0 :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.text_rejects capacity hcap plain h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **What an accepted `receive-text` opens**: status 255; the body length as two big-endian bytes;
exactly the `bodyLength` content bytes starting at `bodyStart` (4, 5 or 6), then zeros up to
`capacity`; and the flags of `bodyStart = 4, 5, 6`. -/
theorem receiveAcceptText_text_accepted (capacity : Nat) (hcap : capacity < 65536) (plain : List (BitVec 8))
    (h : Accepted (plain.drop 8) capacity) :
    text ByteAuth.concrete capacity plain =
      [[255], [BitVec.ofNat 8 (bodyLength (plain.drop 8) / 256), BitVec.ofNat 8 (bodyLength (plain.drop 8) % 256)],
        (List.range capacity).map (fun i =>
          if i < bodyLength (plain.drop 8) then g (plain.drop 8) (bodyStart (plain.drop 8) + i) else 0),
        [mk (bodyStart (plain.drop 8) = 4), mk (bodyStart (plain.drop 8) = 5), mk (bodyStart (plain.drop 8) = 6)]] :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.text_accepted capacity hcap plain h

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **Converse: a content the reference parses, whose two length prefixes have at most two bytes
each and whose body fits `capacity`, is accepted, and the opened text is exactly the reference
body (zero-padded to `capacity`).** -/
theorem receiveAcceptText_text_of_reference (capacity : Nat) (plain body : List (BitVec 8))
    (href : referenceBody (plain.drop 8) = some body)
    (hw₁ : (g (plain.drop 8) 1).toNat < 128 ∨ (g (plain.drop 8) 2).toNat < 128)
    (hw₂ : (lowByte (plain.drop 8)).toNat < 128 ∨ (highByte (plain.drop 8)).toNat < 128)
    (hfit : body.length ≤ capacity) :
    Accepted (plain.drop 8) capacity ∧ bodyLength (plain.drop 8) = body.length ∧
      (List.range capacity).map (fun i =>
          if i < bodyLength (plain.drop 8) then g (plain.drop 8) (bodyStart (plain.drop 8) + i) else 0) =
        (List.range capacity).map (fun i => body.getD i 0) :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.text_of_reference capacity plain body href hw₁ hw₂ hfit

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **The converse at the level of `receive-text`'s outputs**: for such a content, `receive-text`
opens status 255, the reference body's length, the reference body (zero-padded to `capacity`) and
the layout flags. -/
theorem receiveAcceptText_text_reference (capacity : Nat) (hcap : capacity < 65536) (plain body : List (BitVec 8))
    (href : referenceBody (plain.drop 8) = some body)
    (hw₁ : (g (plain.drop 8) 1).toNat < 128 ∨ (g (plain.drop 8) 2).toNat < 128)
    (hw₂ : (lowByte (plain.drop 8)).toNat < 128 ∨ (highByte (plain.drop 8)).toNat < 128)
    (hfit : body.length ≤ capacity) :
    text ByteAuth.concrete capacity plain =
      [[255], [BitVec.ofNat 8 (body.length / 256), BitVec.ofNat 8 (body.length % 256)],
        (List.range capacity).map (fun i => body.getD i 0),
        [mk (bodyStart (plain.drop 8) = 4), mk (bodyStart (plain.drop 8) = 5), mk (bodyStart (plain.drop 8) = 6)]] :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.text_reference capacity hcap plain body href hw₁ hw₂ hfit

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **The former DEFECT, now refused (emitter batch; NEEDS_REVIEW.md 3f, defect 1).** A content
whose 3-byte DataMessage claims a 5-byte body (`0A 03 0A 05 abcde`): `receive-text` opens status 0
and nothing else. Before the batch it opened status 255 and `abcde`. -/
theorem receiveAcceptText_overlongBody_refused :
    text ByteAuth.concrete 10 overlongBodyPlain =
      [[0], [0, 0], List.replicate 10 0, [0, 0, 0]] :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.overlongBody_refused

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- The reference parse refuses the same plaintext (`receiveAcceptText_overlongBody_refused`). -/
theorem receiveAcceptText_overlongBody_reference : referenceBody (overlongBodyPlain.drop 8) = none :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.overlongBody_reference

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **`receive-text` accepts exactly what the reference protobuf reading accepts**, for length
prefixes of at most two bytes (`Covered`) and a body of at most `capacity` bytes. -/
theorem receiveAcceptText_accepted_iff_reference (capacity : Nat) (c : List (BitVec 8)) :
    Accepted c capacity ↔ (∃ body, referenceBody c = some body ∧ body.length ≤ capacity) ∧ Covered c :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.accepted_iff_reference capacity c

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **`receive-text`'s status is 255 exactly when the reference parses the content** (covered
widths, body within `capacity`); otherwise 0 (`receiveAcceptText_text_rejects`: nothing opened). -/
theorem receiveAcceptText_text_status_iff_reference (capacity : Nat) (hcap : capacity < 65536)
    (plain : List (BitVec 8)) :
    (text ByteAuth.concrete capacity plain).getD 0 [] = [255] ↔
      (∃ body, referenceBody (plain.drop 8) = some body ∧ body.length ≤ capacity) ∧ Covered (plain.drop 8) :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.text_status_iff_reference capacity hcap plain

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **Accept direction, outputs**: whenever `receive-text`'s status is 255, the reference parses
the content and the opened length and text are exactly the reference body's. -/
theorem receiveAcceptText_text_accepted_reference (capacity : Nat) (hcap : capacity < 65536)
    (plain : List (BitVec 8)) (h : (text ByteAuth.concrete capacity plain).getD 0 [] = [255]) :
    ∃ body, referenceBody (plain.drop 8) = some body ∧ body.length ≤ capacity ∧ Covered (plain.drop 8) ∧
      text ByteAuth.concrete capacity plain =
        [[255], [BitVec.ofNat 8 (body.length / 256), BitVec.ofNat 8 (body.length % 256)],
          (List.range capacity).map (fun i => body.getD i 0),
          [mk (bodyStart (plain.drop 8) = 4), mk (bodyStart (plain.drop 8) = 5), mk (bodyStart (plain.drop 8) = 6)]] :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.text_accepted_reference capacity hcap plain h
open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptAccessKey TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **Two layouts never both match** (at the same offset in the same content). -/
theorem receiveAccessKey_gap_unique (c : List (BitVec 8)) (off : Nat) (g g' : Gap)
    (h : gapMask ByteAuth.concrete c off g = 255) (h' : gapMask ByteAuth.concrete c off g' = 255) : g = g' :=
  TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.gap_unique c off g g' h h'

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptAccessKey TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **`receive-access-key`'s status is 255 exactly when one of the 72 layouts matches** (and 0
otherwise). -/
theorem receiveAccessKey_withAccessKey_status (cert offset : Nat) (conversation plain : List (BitVec 8)) :
    (withAccessKey Aes.concrete ByteAuth.concrete cert offset conversation plain).getD 0 [] =
      [mk (Found (plain.drop 8) offset)] :=
  TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.withAccessKey_status cert offset conversation plain

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptAccessKey TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **When a layout `g` matches**, the record is the input record with bytes `cert + 278 ..
cert + 294` (the access key in the metadata) replaced by the access key derived from the 32 bytes
after `g`'s `32 20`. -/
theorem receiveAccessKey_withAccessKey_accepted (cert offset : Nat) (conversation plain : List (BitVec 8))
    (hlen : cert + 294 ≤ conversation.length) (g : Gap) (hg : g ∈ gaps)
    (hm : gapMask ByteAuth.concrete (plain.drop 8) offset g = 255) :
    withAccessKey Aes.concrete ByteAuth.concrete cert offset conversation plain =
      [[255], conversation.take (cert + 278) ++ accessKeyOf (profileKey (plain.drop 8) offset g) ++
        conversation.drop (cert + 294)] :=
  TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.withAccessKey_accepted cert offset conversation plain hlen g hg hm

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptAccessKey TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **When no layout matches**, the record is unchanged. -/
theorem receiveAccessKey_withAccessKey_rejected (cert offset : Nat) (conversation plain : List (BitVec 8))
    (hno : ¬Found (plain.drop 8) offset) :
    withAccessKey Aes.concrete ByteAuth.concrete cert offset conversation plain = [[0], conversation] :=
  TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.withAccessKey_rejected cert offset conversation plain hno

/-! ## 4. The controller: parsers, the reveal policy, templates, results (SECURITY_MAP C.4)

Code that `public_service_controller` executes. The parsers (WebSocket upgrade, frame, control,
chat response) are proved symbolic = concrete; the frame parser, the control queue, the TLS record
splitter and the upgrade's accept value are also related to RFC 6455 / RFC 8446 (section 4c);
the frame parser's acceptance of well-formed frames, its refusals, the control frames' path to the
reply, and the chat-response parser's body extent and fail-closed cases are in section 4e; the
upgrade response parser has no such theorem yet. The reveal policy (`PublicReceive.scan`,
`budget`, `mayReveal`, …) has the T1 pieces of section 4f (bodies passed over are never revealed;
over-long varints refused); `Recovery`, `Circuits` and `CeremonyRequests` have NO theorem (T11 in
section 8). The request templates (`PublicRequest.*`)
have the structural theorems of section 2d (T8, rest in section 8). Since stage S2 the controller's
pure code is in library modules under `TlsMpc/Node/` (no emitter imports them), so the entries
below are about the code it runs, not about copies. -/

/-- **The controller's fast byte operations equal the reference ones**, so every parser and
builder the controller runs with `PublicReceive.fast` is the proved concrete one
(`TlsMpc/Node/Bytes.lean`). **C**. SECURITY_MAP C.4. -/
theorem controller_fast_eq : PublicReceive.fast = TlsMpc.ByteAuth.concrete :=
  PublicReceive.fast_eq

/-! ### 4a. Passing over an unrevealed body in bulk (`TlsMpc/Node/PassOver.lean`, `Policy/Receive.lean`)

Inside the unrevealed body of a server response or request, the three parsers the controller runs
in the clear only count. These are the facts the bulk pass-over rests on, for exactly the inputs
the controller feeds them (an active zero byte in place of the unrevealed one). **C**. -/

/-- **One passed-over payload byte, frame parser:** inside a valid data frame's payload, with more
than one payload byte and message capacity left (`1 ≤ frameRoom f`), the frame parser reports a
valid data byte that ends nothing, and its new state is `frameBulk 1 f` (both 16-bit counts one
lower, everything else kept). **C**. -/
theorem passOver_frame_step_room (cap : Nat) (f : List (BitVec 8)) (h : 1 ≤ PublicReceive.PassOver.frameRoom f) :
    TlsWebSocketFrame.runByte PublicReceive.fast cap (f ++ [255, 0]) =
      [255, 255, 0, 0, 0, 0, 0, 0] ++ PublicReceive.PassOver.frameBulk 1 f :=
  PublicReceive.PassOver.frame_step_room cap f h

/-- After one such byte the frame parser's room is one byte less. **C**. -/
theorem passOver_frameRoom_one (f : List (BitVec 8)) (h : 1 ≤ PublicReceive.PassOver.frameRoom f) :
    PublicReceive.PassOver.frameRoom (PublicReceive.PassOver.frameBulk 1 f) =
      PublicReceive.PassOver.frameRoom f - 1 :=
  PublicReceive.PassOver.frameRoom_one f h

/-- One frame byte then `k` more is `k + 1` at once, within the room. **C**. -/
theorem passOver_frameBulk_succ (f : List (BitVec 8)) (k : Nat) (h : k + 1 ≤ PublicReceive.PassOver.frameRoom f) :
    PublicReceive.PassOver.frameBulk k (PublicReceive.PassOver.frameBulk 1 f) =
      PublicReceive.PassOver.frameBulk (k + 1) f :=
  PublicReceive.PassOver.frameBulk_succ f k h

/-- **One passed-over payload byte, control queue:** with no control data, no frame end and no
opcode (what the frame parser reports for a data payload byte), the queue's step is the identity on
its 636-byte state when its counts are in range (`controlIdle`). **C**. -/
theorem passOver_control_idle (c : List (BitVec 8)) (h : PublicReceive.PassOver.controlIdle c) :
    TlsWebSocketControl.run PublicReceive.fast (c ++ [0, 0, 0, 0]) = c :=
  PublicReceive.PassOver.control_idle c h

/-- **One passed-over body byte, response parser:** inside the body field of the inner response,
with more than one body byte and inner-response byte left and budget left (`1 ≤ responseRoom r`),
the parser stays valid, does not finish, reports a body byte, and its new state is
`responseBulk 1 r` (three 64-bit counts one lower). **C**. -/
theorem passOver_response_step_room (cap : Nat) (r : List (BitVec 8)) (h : 1 ≤ PublicReceive.PassOver.responseRoom r) :
    TlsChatResponse.runByte TlsMpc.Signal.VarintDecode.Spqr.concrete TlsMpc.Signal.Word64.fast PublicReceive.fast cap
        (r ++ [255, 0, 0] ++ [0]) =
      [255, 0, (TlsChatResponse.readState TlsMpc.Signal.Word64.fast PublicReceive.fast r).successful, 255, 0, 0] ++
        PublicReceive.PassOver.responseBulk 1 r :=
  PublicReceive.PassOver.response_step_room cap r h

/-- After one such byte the response parser's room is one byte less. **C**. -/
theorem passOver_responseRoom_one (r : List (BitVec 8)) (h : 1 ≤ PublicReceive.PassOver.responseRoom r) :
    PublicReceive.PassOver.responseRoom (PublicReceive.PassOver.responseBulk 1 r) =
      PublicReceive.PassOver.responseRoom r - 1 :=
  PublicReceive.PassOver.responseRoom_one r h

/-- One response byte then `k` more is `k + 1` at once, within the room. **C**. -/
theorem passOver_responseBulk_succ (r : List (BitVec 8)) (k : Nat)
    (h : k + 1 ≤ PublicReceive.PassOver.responseRoom r) :
    PublicReceive.PassOver.responseBulk k (PublicReceive.PassOver.responseBulk 1 r) =
      PublicReceive.PassOver.responseBulk (k + 1) r :=
  PublicReceive.PassOver.responseBulk_succ r k h

/-- **One passed-over body byte, the controller's step** (`passOne`: `stepPassed` for a response,
`stepSkipped` for a server request): within `passRoom`, it succeeds, completes no response, and
gives `passBulk 1` (`TlsMpc/Node/Policy/Receive.lean`). **C**. -/
theorem passOne_bulk (s : PublicReceive.State) (h : 1 ≤ PublicReceive.passRoom s) :
    PublicReceive.passOne s = .ok (PublicReceive.passBulk 1 s, false) :=
  PublicReceive.passOne_bulk s h

/-- **The bulk pass-over is the byte-by-byte one.** For any `k ≤ passRoom s`, passing over `k`
body bytes one at a time (`passRun`, what the record loop did before) succeeds, completes no
response, and ends in `passBulk k s`, the state the record loop now computes in one step. **C**. -/
theorem passRun_bulk (k : Nat) (s : PublicReceive.State) (h : k ≤ PublicReceive.passRoom s) :
    PublicReceive.passRun k s = .ok (PublicReceive.passBulk k s, false) :=
  PublicReceive.passRun_bulk k s h

/-- Passing over `a + b` bytes is passing over `a`, then `b`: so the record loop's `passBulk` of
`bulk ≤ passRoom s` bytes followed by `count - bulk` single steps is `passRun count`. **C**. -/
theorem passRun_add (b a : Nat) (s : PublicReceive.State) :
    PublicReceive.passRun (a + b) s =
      (do let (s1, d1) ← PublicReceive.passRun a s; let (s2, d2) ← PublicReceive.passRun b s1; pure (s2, d1 || d2)) :=
  PublicReceive.passRun_add b a s

/-! ### 4b. Other controller functions -/

open TlsMpc.Signal TlsMpc.Signal.Word64 in
/-- **The controller's fast 64-bit word operations equal the reference ones.** **C** (the
chat-response parser). SECURITY_MAP C.4. -/
theorem word64_fast_eq : fast = concrete :=
  TlsMpc.Signal.Word64.fast_eq

open TlsMpc.Signal TlsMpc.Signal.VarintDecode.Spqr Std.Tactic.BVDecide in
/-- **The SPQR varint decoder circuit equals the reference decoder.** **C** (the response parser,
controller lines 538 and 595, through `TlsChatResponse.runByte`). SECURITY_MAP C.4. -/
theorem varint_decodeCore_spec (bytes : List (BitVec 8)) :
    decodeCore concrete ByteAuth.concrete bytes = encodeResult (decode bytes) :=
  TlsMpc.Signal.VarintDecode.Spqr.decodeCore_spec bytes

open TlsMpc.Signal TlsMpc.Signal.PrivateTextNotification Std.Tactic.BVDecide in
/-- **The public text-message builder picks the smallest size class that fits:** the result is
the sized build at the chosen class (between 1 and the limit), is valid (first byte 255), has
the class's length, and every smaller class fails. **C** (controller line 2314, legacy
profile). SECURITY_MAP C.4. -/
theorem notification_buildPublic_spec (limit : Nat) (text timestamp : List (BitVec 8)) (chosen : Nat)
    (built : List (BitVec 8)) (h : buildPublic limit text timestamp = some (chosen, built)) :
    1 ≤ chosen ∧ chosen ≤ limit ∧
    built = buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete
      (publicCapacity text.length) chosen (publicInput text timestamp) ∧
    built.head? = some 255 ∧ built.length = builtBytes chosen ∧
    ∀ smaller, 1 ≤ smaller → smaller < chosen →
      (buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete
        (publicCapacity text.length) smaller (publicInput text timestamp)).head? ≠ some 255 :=
  TlsMpc.Signal.PrivateTextNotification.buildPublic_spec limit text timestamp chosen built h

open TlsMpc.Signal TlsMpc.Signal.PrivateTextNotification Std.Tactic.BVDecide in
/-- **The same for the libsignal ("official") padding.** **C** (controller lines 2021, 2314;
the production profile). SECURITY_MAP C.4. -/
theorem notification_buildPublicOfficial_spec (limit : Nat) (text timestamp : List (BitVec 8)) (chosen : Nat)
    (built : List (BitVec 8)) (h : buildPublicOfficial limit text timestamp = some (chosen, built)) :
    1 ≤ chosen ∧ chosen ≤ limit ∧
    built = buildOfficial Sha256.concrete Varint64.concrete ByteAuth.concrete
      (publicCapacity text.length) chosen (publicInput text timestamp) ∧
    built.head? = some 255 ∧ built.length = officialBuiltBytes chosen ∧
    ∀ smaller, 1 ≤ smaller → smaller < chosen →
      (buildOfficial Sha256.concrete Varint64.concrete ByteAuth.concrete
        (publicCapacity text.length) smaller (publicInput text timestamp)).head? ≠ some 255 :=
  TlsMpc.Signal.PrivateTextNotification.buildPublicOfficial_spec limit text timestamp chosen built h

open TlsMpc.Signal TlsMpc.Signal.PrivateTextNotification Std.Tactic.BVDecide in
/-- **A short text (≤ 48 bytes) whose plain build is valid takes the first class.** **C**.
SECURITY_MAP C.4. -/
theorem notification_buildPublic_short (limit : Nat) (text timestamp : List (BitVec 8)) (short : text.length ≤ 48)
    (valid : (build Sha256.concrete Varint64.concrete ByteAuth.concrete
      (publicInput text timestamp)).head? = some 255) :
    buildPublic (limit + 1) text timestamp =
      some (1, build Sha256.concrete Varint64.concrete ByteAuth.concrete (publicInput text timestamp)) :=
  TlsMpc.Signal.PrivateTextNotification.buildPublic_short limit text timestamp short valid

open TlsMpc.Signal TlsMpc.Signal.PrivateTextNotification Std.Tactic.BVDecide in
/-- **`firstFit` returns the first valid class in its search window.** **C**. SECURITY_MAP C.4. -/
theorem notification_firstFit_spec (capacity : Nat) (input : List (BitVec 8)) (fuel first chosen : Nat)
    (built : List (BitVec 8)) (h : firstFit capacity input fuel first = some (chosen, built)) :
    first ≤ chosen ∧ chosen < first + fuel ∧
    built = buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete capacity chosen input ∧
    built.head? = some 255 ∧ built.length = builtBytes chosen ∧
    ∀ smaller, first ≤ smaller → smaller < chosen →
      (buildSized Sha256.concrete Varint64.concrete ByteAuth.concrete capacity smaller input).head? ≠ some 255 :=
  TlsMpc.Signal.PrivateTextNotification.firstFit_spec capacity input fuel first chosen built h

open TlsMpc.BundleKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **The prekey-response layout the controller accepts is the layout of a well-formed
response with the opened punctuation mask:** if `layout?` returns widths, the response built
from them has exactly that mask, and every width is valid. **C** (controller lines 2159, 2651).
SECURITY_MAP C.4. -/
theorem bundle_layout_sound (mask : List Bool) (ws : List BundleResponse.Widths)
    (accepted : BundleResponse.layout? mask = some ws) :
    BundleResponse.maskOf (BundleResponse.response ws) = mask ∧ ws.all BundleResponse.Widths.ok = true :=
  TlsMpc.BundleKernel.layout?_sound mask ws accepted

/-! ### 4c. The parsers against RFC 6455 and RFC 8446, the upgrade's accept value, the clock

`TlsMpc/KernelSpecs/ParseWebSocketFrame.lean`, `ParseWebSocketControl.lean`, `ParseTlsRecord.lean`
and `TlsMpc/Node/Local/WebSocketAccept.lean` (references written from the RFCs, not from the code),
and `TlsMpc/Node/Policy/Clock.lean`. **C** unless marked. Still open: `TlsChatResponse` and the
upgrade response parser have no reference; frame-parser acceptance is not proved (section 8). -/

open TlsMpc.KernelSpecs.ParseWebSocketFrame in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
/-- **One unmasked data frame, as RFC 6455 section 5.2 lays it out**, from a frame boundary: the
frame parser's per-byte flags are the reference's (`expectedFlags` of the parsed header: which
bytes are header, payload, end), and it ends at a frame boundary with no opcode pending. -/
theorem wsFrame_frame_extent (cap : Nat) (S : State Byte) (hS : S.phases = P 0) (f : List Byte) (h : Header)
    (hp : parseHeader f = some h) (hn : f.length = h.size + h.length) (hm : h.masked = false)
    (hf : h.form ≠ 64) :
    Matches (events cap S f) (expectedFlags h) ∧
    (finalState cap S f).phases = P 0 ∧ (finalState cap S f).opcode = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketFrame.frame_extent cap S hS f h hp hn hm hf

open TlsMpc.KernelSpecs.ParseWebSocketFrame in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
/-- **A sequence of such frames:** the flags are the concatenation of each frame's. -/
theorem wsFrame_frames_extent (cap : Nat) : ∀ (fs : List (Header × List Byte)) (S : State Byte), S.phases = P 0 →
    Framed fs →
    Matches (events cap S (fs.flatMap Prod.snd)) (fs.flatMap (fun p => expectedFlags p.1)) ∧
    (finalState cap S (fs.flatMap Prod.snd)).phases = P 0 :=
  TlsMpc.KernelSpecs.ParseWebSocketFrame.frames_extent cap

open TlsMpc.KernelSpecs.ParseWebSocketFrame in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **The controller's byte-serialised run is the structured one** (`runByte` on the state bytes,
byte after byte). -/
theorem wsFrame_controller_run (cap : Nat) : ∀ (f : List Byte) (S : State Byte), Shaped S →
    controllerRun cap (TlsWebSocketFrame.stateBytes S) f =
      ((events cap S f).map eventBytes, TlsWebSocketFrame.stateBytes (finalState cap S f)) :=
  TlsMpc.KernelSpecs.ParseWebSocketFrame.controller_run cap

open TlsMpc.KernelSpecs.ParseWebSocketFrame in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- One active byte of `runByte` is `step`. -/
theorem wsFrame_runByte_active (cap : Nat) (S : State Byte) (h : Shaped S) (x : Byte) :
    TlsWebSocketFrame.runByte fast cap (TlsWebSocketFrame.stateBytes S ++ [255#8, x]) =
      eventBytes (step fast cap S x) ++ TlsWebSocketFrame.stateBytes (step fast cap S x).state :=
  TlsMpc.KernelSpecs.ParseWebSocketFrame.runByte_active cap S h x

open TlsMpc.KernelSpecs.ParseWebSocketFrame in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Refusal (RFC 6455 section 5.2):** a server frame's second byte with the MASK bit set, or the
64-bit length form, makes the parser invalid. -/
theorem wsFrame_reject_second (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 1)
    (hx : 128 ≤ x.toNat ∨ x.toNat % 128 = 127) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_second cap S x h hx

open TlsMpc.KernelSpecs.ParseWebSocketFrame in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- Once invalid, always invalid. -/
theorem wsFrame_reject_sticky (cap : Nat) (S : State Byte) (x : Byte) (h : S.valid = 0#8) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_sticky cap S x h

open TlsMpc.KernelSpecs.ParseWebSocketFrame in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- A 16-bit length below 126 is refused (section 5.2: the minimal number of bytes MUST be used). -/
theorem wsFrame_reject_noncanonical (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 3)
    (hh : S.high = 0#8) (hx : x.toNat < 126) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_noncanonical cap S x h hh hx

open TlsMpc.KernelSpecs.ParseWebSocketFrame in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- A 16-bit length above the capacity is refused. -/
theorem wsFrame_reject_capacity16 (cap : Nat) (hc : cap < 65536) (S : State Byte) (x : Byte) (h : S.phases = P 3)
    (hx : cap < wordValue S.high x) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketFrame.reject_capacity16 cap hc S x h hx

open TlsMpc.KernelSpecs.ParseWebSocketControl in
open TlsMpc.TlsWebSocketControl (State step) in
/-- **The control queue against RFC 6455 sections 5.5.1–5.5.3:** a Ping or a Close with payload
`p ++ [b]` (1 to 125 bytes), from an idle queue, leaves it idle with the reply the RFC requires
appended (Pong for a Ping, Close for a Close; its length; the payload). -/
theorem wsControl_control_frame (S : State Byte) (hI : Idle S) (hs p : List Byte) (b o : Byte)
    (ho : o = 8#8 ∨ o = 9#8) (hn : p.length + 1 ≤ 125) :
    runC S (hs.map idleIn ++ p.map collectIn ++ [(255#8, 255#8, o, b)]) =
      { valid := S.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (S.queued.toNat + 1), kinds := S.kinds.set S.queued.toNat (kindOf o),
        lengths := S.lengths.set S.queued.toNat (BitVec.ofNat 8 (p.length + 1)),
        payloads := blockSet S.payloads S.queued.toNat ((p ++ [b]) ++ List.replicate (125 - (p.length + 1)) 0#8) } :=
  TlsMpc.KernelSpecs.ParseWebSocketControl.control_frame S hI hs p b o ho hn

open TlsMpc.KernelSpecs.ParseWebSocketControl in
open TlsMpc.TlsWebSocketControl (State step) in
open PublicReceive (fast) in
/-- `run` on the serialised queue and the four inputs is `step`. -/
theorem wsControl_run_stateBytes (S : State Byte) (hS : Shaped S) (d e o b : Byte) :
    TlsWebSocketControl.run fast (TlsWebSocketControl.stateBytes S ++ [d, e, o, b]) =
      TlsWebSocketControl.stateBytes (step fast S d e o b) :=
  TlsMpc.KernelSpecs.ParseWebSocketControl.run_stateBytes S hS d e o b

open TlsMpc.KernelSpecs.ParseWebSocketControl in
open PublicReceive (fast) in
/-- **What `replies` sends is RFC 6455's masked client frame** (section 5.3) for a queued Pong or
Close of at most 125 bytes, with the given masking key. -/
theorem wsControl_encode_frame (kind len : Byte) (hk : kind = 8#8 ∨ kind = 10#8) (hl : len.toNat ≤ 125)
    (key blk : List Byte) (hkey : key.length = 4) (hblk : blk.length = 125) :
    (TlsWebSocketControl.encode fast ([255#8, 0#8, len, kind] ++ key ++ blk)).take 3 =
      [255#8, 0#8, BitVec.ofNat 8 (len.toNat + 6)] ∧
    ((TlsWebSocketControl.encode fast ([255#8, 0#8, len, kind] ++ key ++ blk)).drop 3).take (len.toNat + 6) =
      clientFrame kind.toNat key (blk.take len.toNat) :=
  TlsMpc.KernelSpecs.ParseWebSocketControl.encode_frame kind len hk hl key blk hkey hblk

open TlsMpc.KernelSpecs.ParseWebSocketControl in
/-- **One masking key per control reply (RFC 6455 section 5.3).** Formerly a recorded DEFECT
(`replies_reuse_mask`: every reply of one drain had the same key); fixed in stage S4: two queued
Pongs with two keys are each masked with their own. -/
theorem wsControl_replies_fresh_masks :
    framesOf (PublicReceive.replies { PublicReceive.start [] with control := twoPongs } [[1, 2, 3, 4], [5, 6, 7, 8]]) =
      [(10, [0x8a, 0x81, 1, 2, 3, 4, 0x40]), (10, [0x8a, 0x81, 5, 6, 7, 8, 0x47])] :=
  TlsMpc.KernelSpecs.ParseWebSocketControl.replies_fresh_masks

open TlsMpc.KernelSpecs.ParseWebSocketControl in
/-- With fewer masking keys than queued replies, `replies` sends nothing. -/
theorem wsControl_replies_missing_mask :
    framesOf (PublicReceive.replies { PublicReceive.start [] with control := twoPongs } [[1, 2, 3, 4]]) = [] :=
  TlsMpc.KernelSpecs.ParseWebSocketControl.replies_missing_mask

open TlsMpc.TlsWire TlsMpc.KernelSpecs.ParseTlsRecord in
/-- **The TLS record splitter (RFC 8446 section 5.1):** it returns exactly one record and no rest
iff the bytes are that record's encoding and the record is well formed. -/
theorem tlsRecord_receive_one (wire : Bytes) (r : Record) :
    records 2 wire = .ok ([r], []) ↔ WellFormed r ∧ wire = encode r :=
  TlsMpc.KernelSpecs.ParseTlsRecord.receive_one wire r

open TlsMpc.TlsWire TlsMpc.KernelSpecs.ParseTlsRecord in
/-- Soundness: what the splitter returns re-encodes to its input, every record is well formed and
the rest is an incomplete record. -/
theorem tlsRecord_records_sound : ∀ (fuel : Nat) (b : Bytes) (rs : List Record) (p : Bytes),
    records fuel b = .ok (rs, p) →
    b = rs.flatMap encode ++ p ∧ (∀ r ∈ rs, WellFormed r) ∧ Incomplete p :=
  TlsMpc.KernelSpecs.ParseTlsRecord.records_sound

open TlsMpc.TlsWire TlsMpc.KernelSpecs.ParseTlsRecord in
/-- Completeness: well-formed records followed by an incomplete one are split back exactly. -/
theorem tlsRecord_records_complete : ∀ (rs : List Record) (tail : Bytes) (fuel : Nat),
    (∀ r ∈ rs, WellFormed r) → Incomplete tail → rs.length < fuel →
    records fuel (rs.flatMap encode ++ tail) = .ok (rs, tail) :=
  TlsMpc.KernelSpecs.ParseTlsRecord.records_complete

open TlsMpc.TlsWire TlsMpc.KernelSpecs.ParseTlsRecord in
/-- A record announcing more than 2¹⁴ + 256 bytes is refused (RFC 8446 section 5.2). -/
theorem tlsRecord_records_overflow (f : Nat) (b : Bytes) (h5 : 5 ≤ b.length) (h : 16640 < announced b) :
    records (f + 1) b = .error "TLS record overflow" :=
  TlsMpc.KernelSpecs.ParseTlsRecord.records_overflow f b h5 h

open TlsMpc.Local.WebSocketAccept in
/-- **The WebSocket accept value (RFC 6455 section 4.2.2):** worker operation 45's Lean
counterpart on a 16-byte nonce replies the nonce and `base64(SHA-1(base64(nonce) ++ GUID))`
(`TlsMpc/Node/Local/WebSocketAccept.lean`; the C++ in `service_kernels.h` is not yet replaced). -/
theorem wsAccept_accept_spec (nonce : List Byte) (h : nonce.length = 16) :
    upgradePublic nonce = .ok (nonce ++ acceptOf (keyOf nonce)) :=
  TlsMpc.Local.WebSocketAccept.accept_spec nonce h

open TlsMpc.Local.WebSocketAccept in
/-- RFC 6455's own example: the accept value of `dGhlIHNhbXBsZSBub25jZQ==`. -/
theorem wsAccept_rfc6455_accept :
    acceptOf (ascii "dGhlIHNhbXBsZSBub25jZQ==") = ascii "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=" :=
  TlsMpc.Local.WebSocketAccept.rfc6455_accept

open TlsMpc.Local.WebSocketAccept in
/-- The SHA-1 reference against FIPS 180-4's "abc" example. -/
theorem wsAccept_sha1_abc : Sha1.digest [0x61, 0x62, 0x63] =
    [0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a, 0xba, 0x3e,
     0x25, 0x71, 0x78, 0x50, 0xc2, 0x6c, 0x9c, 0xd0, 0xd8, 0x9d] :=
  TlsMpc.Local.WebSocketAccept.sha1_abc

/-- **The agreed clock is within two minutes of this party's own** (SECURITY_MAP D.11; stage S4,
brought forward to S0): an agreed value is at least this party's clock and at most `maxSkew` ahead
of it, so the other party cannot push back-off, keepalive or message timestamps further. -/
theorem clock_agreed_within {mine theirs t : Nat} (h : TlsMpc.Node.Policy.Clock.agree mine theirs = .ok t) :
    mine ≤ t ∧ t ≤ mine + TlsMpc.Node.Policy.Clock.maxSkew :=
  TlsMpc.Node.Policy.Clock.agreed_within h

/-- Both parties compute the same agreed clock (or both refuse). -/
theorem clock_agree_symm (mine theirs : Nat) :
    TlsMpc.Node.Policy.Clock.agree mine theirs = TlsMpc.Node.Policy.Clock.agree theirs mine :=
  TlsMpc.Node.Policy.Clock.agree_symm mine theirs

/-! ### 4d. T8: the request templates against protobuf, JSON and RFC 6455 references

`TlsMpc/Node/Policy/RequestSpec.lean` (references: protobuf encoding, the Signal request JSON, the
RFC 6455 client frame and its decoder) and `RequestProofs.lean` (about the controller's own
builders in `Policy/Request.lean` and replies in `Policy/Receive.lean`). **C**. Still open (section
8): the id `reply` answers is shown to be the one `varintAt` reads only under a hypothesis (`scan`'s
loop invariant is not proved), and `replies` (pong/close echoes) is not covered here (see 4c). -/

section RequestT8
open TlsMpc.Signal TlsMpc.Node.RequestSpec
open TlsMpc.Node.RequestProofs (devicesOf sentFrame)
open PublicRequest (Piece total field text sendMessage fetchMessage devicesMessage officialJson build assemble
  buildFetch buildDevices)
open TlsMpc.KernelSpecs.RequestFrame (render maskFrom body pairsOf buildHeader assembleHeader)

/-- **The send message, its slots filled, is the reference send request** (protobuf
`WebSocketRequestMessage` with the reference JSON body). -/
theorem t8_sendMessage_reference (values : Nat → List Byte) (envelope : List Byte) (timestamp id : Nat) (official : Bool)
    (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (w2 : (values 2).length = 3)
    (w3 : (values 3).length = 10) (hid : id < 2 ^ 70)
    (size : total (sendMessage envelope timestamp id official) < 2 ^ 70) :
    render values (sendMessage envelope timestamp id official) =
      (WebSocketMessage.request (sendRequest (values 0) (values 1) (sendBody [(envelope, values 2, values 3)] timestamp)
        id official)).encode :=
  TlsMpc.Node.RequestProofs.sendMessage_reference values envelope timestamp id official w0 w1 w2 w3 hid size

/-- The prekey fetch message, filled, is the reference keys request. -/
theorem t8_fetchMessage_reference (values : Nat → List Byte) (id : Nat)
    (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (hid : id < 2 ^ 70)
    (size : total (fetchMessage id) < 2 ^ 70) :
    render values (fetchMessage id) = (WebSocketMessage.request (keysRequest (values 0) (values 1) id)).encode :=
  TlsMpc.Node.RequestProofs.fetchMessage_reference values id w0 w1 hid size

/-- The multi-device send message, filled, is the reference send request with one entry per device. -/
theorem t8_devicesMessage_reference (values : Nat → List Byte) (envelopes : List (List Byte)) (timestamp id : Nat)
    (official : Bool) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (wd : ∀ i < envelopes.length, (values (2 + 2 * i)).length = 3 ∧ (values (3 + 2 * i)).length = 10)
    (hid : id < 2 ^ 70) (size : total (devicesMessage envelopes timestamp id official) < 2 ^ 70) :
    render values (devicesMessage envelopes timestamp id official) =
      (WebSocketMessage.request (sendRequest (values 0) (values 1) (sendBody (devicesOf values envelopes) timestamp)
        id official)).encode :=
  TlsMpc.Node.RequestProofs.devicesMessage_reference values envelopes timestamp id official w0 w1 wd hid size

/-- **`build`, filled: RFC 6455's masked client frame of the reference send request**, which the
RFC's decoder reads back. -/
theorem t8_build_reference (envelope : List Byte) (timestamp id : Nat) (mask frame : List Byte) (official : Bool)
    (offsets : List Nat) (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (w2 : (values 2).length = 3) (w3 : (values 3).length = 10) (hid : id < 2 ^ 70) :
    let msg := sendMessage envelope timestamp id official
    let request := WebSocketMessage.request
      (sendRequest (values 0) (values 1) (sendBody [(envelope, values 2, values 3)] timestamp) id official)
    buildHeader (total msg) mask ++ maskFrom mask 0 (render values msg) = clientFrame binary mask request.encode ∧
      decodeFrame (clientFrame binary mask request.encode) =
        some (sentFrame binary mask request.encode) :=
  TlsMpc.Node.RequestProofs.build_reference envelope timestamp id mask frame official offsets built values w0 w1 w2 w3 hid

/-- `buildFetch`, filled: the frame of the reference keys request. -/
theorem t8_buildFetch_reference (id : Nat) (mask frame : List Byte) (payloadAt : Nat) (offsets : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (hid : id < 2 ^ 70) :
    let request := WebSocketMessage.request (keysRequest (values 0) (values 1) id)
    assembleHeader (total (fetchMessage id)) mask ++ maskFrom mask 0 (render values (fetchMessage id)) =
        clientFrame binary mask request.encode ∧
      decodeFrame (clientFrame binary mask request.encode) =
        some (sentFrame binary mask request.encode) :=
  TlsMpc.Node.RequestProofs.buildFetch_reference id mask frame payloadAt offsets built values w0 w1 hid

/-- `buildDevices`, filled: the frame of the reference multi-device send request. -/
theorem t8_buildDevices_reference (envelopes : List (List Byte)) (timestamp id : Nat) (mask frame : List Byte)
    (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (wd : ∀ i < envelopes.length, (values (2 + 2 * i)).length = 3 ∧ (values (3 + 2 * i)).length = 10)
    (hid : id < 2 ^ 70) :
    let msg := devicesMessage envelopes timestamp id official
    let request := WebSocketMessage.request
      (sendRequest (values 0) (values 1) (sendBody (devicesOf values envelopes) timestamp) id official)
    assembleHeader (total msg) mask ++ maskFrom mask 0 (render values msg) = clientFrame binary mask request.encode ∧
      decodeFrame (clientFrame binary mask request.encode) =
        some (sentFrame binary mask request.encode) :=
  TlsMpc.Node.RequestProofs.buildDevices_reference envelopes timestamp id mask frame official payloadAt offsets built
    values w0 w1 wd hid

/-- RFC 6455's decoder reads a client frame back (FIN, opcode, mask, key, payload, minimal length). -/
theorem t8_decode_clientFrame (op : Nat) (key payload : List Byte) (hop : op < 16) (hkey : key.length = 4)
    (hlen : payload.length < 65536) :
    decodeFrame (clientFrame op key payload) =
      some { fin := true, opcode := op, masked := true, key := key, payload := payload, minimalLength := true } :=
  TlsMpc.Node.RequestProofs.decode_clientFrame op key payload hop hkey hlen

/-- The controller's `clientFrame` is the reference binary client frame (payloads under 126 bytes). -/
theorem t8_clientFrame_reference (mask payload : List Byte) (h : payload.length < 126) :
    PublicReceive.clientFrame mask payload = clientFrame binary mask payload :=
  TlsMpc.Node.RequestProofs.clientFrame_reference mask payload h

/-- The WebSocket ping, read by RFC 6455: FIN, opcode 9, masked, minimal, payload the count. -/
theorem t8_ping_decode (count : Nat) (mask : List Byte) (hmask : mask.length = 4) :
    decodeFrame (PublicReceive.ping count mask) = some (sentFrame pingOpcode mask [BitVec.ofNat 8 count]) :=
  TlsMpc.Node.RequestProofs.ping_decode count mask hmask

/-- **The Close sent at a session's orderly end** (libsignal profile, `Policy/Close.lean`): RFC
6455's masked client Close frame (FIN, opcode 8) whose body is status code 1000 and no reason, the
frame libsignal-net sends when it lets a connection go (`Policy/CloseProofs.lean`). -/
theorem t8_close_reference (mask : List Byte) :
    PublicReceive.close mask =
      clientFrame TlsMpc.Node.CloseProofs.closeOpcode mask (TlsMpc.Node.CloseProofs.closeBody 1000 []) :=
  TlsMpc.Node.CloseProofs.close_reference mask

/-- The Close frame, read by RFC 6455: FIN, opcode 8, masked, minimal, payload the code 1000 only. -/
theorem t8_close_decode (mask : List Byte) (hmask : mask.length = 4) :
    decodeFrame (PublicReceive.close mask) =
      some (sentFrame TlsMpc.Node.CloseProofs.closeOpcode mask (TlsMpc.Node.CloseProofs.closeBody 1000 [])) :=
  TlsMpc.Node.CloseProofs.close_decode mask hmask

/-- The keepalive is the frame of the reference `GET /v1/keepalive` request. -/
theorem t8_keepalive_reference (id : Nat) (mask : List Byte) (hmask : mask.length = 4) (hid : id < 2 ^ 70) :
    PublicReceive.keepalive id mask =
      .ok (clientFrame binary mask (WebSocketMessage.request (keepaliveRequest id)).encode) :=
  TlsMpc.Node.RequestProofs.keepalive_reference id mask hmask hid

/-- The keepalive frame, read by RFC 6455. -/
theorem t8_keepalive_decode (id : Nat) (mask frame : List Byte) (hid : id < 2 ^ 70)
    (h : PublicReceive.keepalive id mask = .ok frame) :
    decodeFrame frame = some (sentFrame binary mask (WebSocketMessage.request (keepaliveRequest id)).encode) :=
  TlsMpc.Node.RequestProofs.keepalive_decode id mask frame hid h

/-- The reply to a server request is the frame of the reference `200 OK` for the id `scan` found. -/
theorem t8_reply_reference (request mask frame : List Byte) (delivered : Bool)
    (h : PublicReceive.reply request mask = .ok (frame, delivered)) :
    ∃ id, (PublicReceive.scan request true).2.id = some id ∧ mask.length = 4 ∧
      (id < 2 ^ 70 → frame = clientFrame binary mask (WebSocketMessage.response (okResponse id)).encode) :=
  TlsMpc.Node.RequestProofs.reply_reference request mask frame delivered h

/-- The reply frame, read by RFC 6455. -/
theorem t8_reply_decode (request mask frame : List Byte) (delivered : Bool)
    (h : PublicReceive.reply request mask = .ok (frame, delivered)) :
    ∃ id, (PublicReceive.scan request true).2.id = some id ∧
      (id < 2 ^ 70 → decodeFrame frame =
        some (sentFrame binary mask (WebSocketMessage.response (okResponse id)).encode)) :=
  TlsMpc.Node.RequestProofs.reply_decode request mask frame delivered h

/-- **`build`: outside its four slots, the encrypted frame is the public frame.** -/
theorem t8_build_public (envelope : List Byte) (timestamp id : Nat) (mask frame : List Byte) (official : Bool)
    (offsets : List Nat) (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (w2 : (values 2).length = 3) (w3 : (values 3).length = 10) (hid : id < 2 ^ 70) :
    let plain := clientFrame binary mask (WebSocketMessage.request
      (sendRequest (values 0) (values 1) (sendBody [(envelope, values 2, values 3)] timestamp) id official)).encode
    plain.length = frame.length ∧
      ∀ i, (∀ k ∈ [0, 1, 2, 3], ¬ (offsets.getD k 0 ≤ i ∧ i < offsets.getD k 0 + (values k).length)) →
        plain[i]? = frame[i]? :=
  TlsMpc.Node.RequestProofs.build_public envelope timestamp id mask frame official offsets built values w0 w1 w2 w3 hid

/-- `buildFetch`: outside its two slots, the encrypted frame is the public frame. -/
theorem t8_buildFetch_public (id : Nat) (mask frame : List Byte) (payloadAt : Nat) (offsets : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (hid : id < 2 ^ 70) :
    let plain := clientFrame binary mask (WebSocketMessage.request (keysRequest (values 0) (values 1) id)).encode
    plain.length = frame.length ∧
      ∀ i, (∀ k ∈ [0, 1], ¬ (offsets.getD k 0 ≤ i ∧ i < offsets.getD k 0 + (values k).length)) →
        plain[i]? = frame[i]? :=
  TlsMpc.Node.RequestProofs.buildFetch_public id mask frame payloadAt offsets built values w0 w1 hid

/-- `buildDevices`: outside its `2 + 2n` slots, the encrypted frame is the public frame. -/
theorem t8_buildDevices_public (envelopes : List (List Byte)) (timestamp id : Nat) (mask frame : List Byte)
    (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (wd : ∀ i < envelopes.length, (values (2 + 2 * i)).length = 3 ∧ (values (3 + 2 * i)).length = 10)
    (hid : id < 2 ^ 70) :
    let plain := clientFrame binary mask (WebSocketMessage.request
      (sendRequest (values 0) (values 1) (sendBody (devicesOf values envelopes) timestamp) id official)).encode
    plain.length = frame.length ∧
      ∀ i, (∀ k < 2 + 2 * envelopes.length, ¬ (offsets.getD k 0 ≤ i ∧ i < offsets.getD k 0 + (values k).length)) →
        plain[i]? = frame[i]? :=
  TlsMpc.Node.RequestProofs.buildDevices_public envelopes timestamp id mask frame official payloadAt offsets built
    values w0 w1 wd hid

/-- **Two contacts' frames agree outside the slots**: what the controllers know of a send does not
depend on the contact. -/
theorem t8_build_two_contacts (envelope : List Byte) (timestamp id : Nat) (mask frame : List Byte) (official : Bool)
    (offsets : List Nat) (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (values values' : Nat → List Byte)
    (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (w2 : (values 2).length = 3)
    (w3 : (values 3).length = 10)
    (w0' : (values' 0).length = 36) (w1' : (values' 1).length = 24) (w2' : (values' 2).length = 3)
    (w3' : (values' 3).length = 10) (hid : id < 2 ^ 70) (i : Nat)
    (outside : ∀ k ∈ [0, 1, 2, 3], ¬ (offsets.getD k 0 ≤ i ∧ i < offsets.getD k 0 + (values k).length)) :
    (clientFrame binary mask (WebSocketMessage.request
        (sendRequest (values 0) (values 1) (sendBody [(envelope, values 2, values 3)] timestamp) id official)).encode)[i]? =
      (clientFrame binary mask (WebSocketMessage.request
        (sendRequest (values' 0) (values' 1) (sendBody [(envelope, values' 2, values' 3)] timestamp) id official)).encode)[i]? :=
  TlsMpc.Node.RequestProofs.build_two_contacts envelope timestamp id mask frame official offsets built values values'
    w0 w1 w2 w3 w0' w1' w2' w3' hid i outside

/-- **`build`'s layout depends only on public lengths** (envelope, timestamp digits, id varint). -/
theorem t8_build_layout (e e' : List Byte) (t t' id id' : Nat) (mask mask' frame frame' : List Byte) (official : Bool)
    (offsets offsets' : List Nat)
    (built : build e t id mask official = .ok (frame, offsets))
    (built' : build e' t' id' mask' official = .ok (frame', offsets'))
    (he : e.length = e'.length) (ht : (utf8 (toString t)).length = (utf8 (toString t')).length)
    (hid : (PublicRequest.varint id).length = (PublicRequest.varint id').length) :
    frame.length = frame'.length ∧ offsets = offsets' :=
  TlsMpc.Node.RequestProofs.build_layout e e' t t' id id' mask mask' frame frame' official offsets offsets' built built'
    he ht hid

/-- `buildFetch`'s layout depends only on the length of the id's varint. -/
theorem t8_buildFetch_layout (id id' : Nat) (mask mask' frame frame' : List Byte) (payloadAt payloadAt' : Nat)
    (offsets offsets' : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets))
    (built' : buildFetch id' mask' = .ok (frame', payloadAt', offsets'))
    (hid : (PublicRequest.varint id).length = (PublicRequest.varint id').length) :
    frame.length = frame'.length ∧ payloadAt = payloadAt' ∧ offsets = offsets' :=
  TlsMpc.Node.RequestProofs.buildFetch_layout id id' mask mask' frame frame' payloadAt payloadAt' offsets offsets'
    built built' hid

/-- `buildDevices`'s layout depends only on public lengths. -/
theorem t8_buildDevices_layout (l l' : List (List Byte)) (t t' id id' : Nat) (mask mask' frame frame' : List Byte)
    (official : Bool) (payloadAt payloadAt' : Nat) (offsets offsets' : List Nat)
    (built : buildDevices l t id mask official = .ok (frame, payloadAt, offsets))
    (built' : buildDevices l' t' id' mask' official = .ok (frame', payloadAt', offsets'))
    (hl : l.map List.length = l'.map List.length) (ht : (utf8 (toString t)).length = (utf8 (toString t')).length)
    (hid : (PublicRequest.varint id).length = (PublicRequest.varint id').length) :
    frame.length = frame'.length ∧ payloadAt = payloadAt' ∧ offsets = offsets' :=
  TlsMpc.Node.RequestProofs.buildDevices_layout l l' t t' id id' mask mask' frame frame' official payloadAt payloadAt'
    offsets offsets' built built' hl ht hid

section Kernels
open TlsMpc.KernelSpecs Std.Tactic.BVDecide
open TlsMpc.HybridKernel (lookup)

/-- **What the server receives from `signal-request-ctr`**: the sealed record of the reference send
request's frame, the contact's fields from the engines' record in the slots (T7 + T8). -/
theorem t8_signalRequestCtr_reference (envelope : List Byte) (timestamp id : Nat)
    (mask frame : List Byte) (official : Bool) (offsets : List Nat)
    (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (cert : Nat) (assign : BVExpr.Assignment)
    (hframe : (lookup (signalRequestInputs cert frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (signalRequestInputs cert frame.length) "mask").map (BVExpr.eval assign) = mask)
    (hid : id < 2 ^ 64) :
    let get := fun name => (lookup (signalRequestInputs cert frame.length) name).map (BVExpr.eval assign)
    let values := TlsMpc.KernelSpecs.RequestFrame.requestValues cert (get "conversation")
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (clientFrame binary mask (WebSocketMessage.request (sendRequest (values 0) (values 1)
          (sendBody [(envelope, values 2, values 3)] timestamp) id official)).encode)
        (signalRequestSlots cert 0 0 0 0 (get "conversation")).1 :=
  TlsMpc.Node.RequestProofs.signalRequestCtr_reference envelope timestamp id mask frame official offsets built cert
    assign hframe hmask hid

/-- What the server receives from `bundle-fetch-ctr`: the sealed reference keys request. -/
theorem t8_bundleFetchCtr_reference (id : Nat) (mask frame : List Byte) (payloadAt : Nat) (offsets : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets)) (assign : BVExpr.Assignment)
    (hframe : (lookup (fetchInputs frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (fetchInputs frame.length) "mask").map (BVExpr.eval assign) = mask)
    (hid : id < 2 ^ 64) :
    let get := fun name => (lookup (fetchInputs frame.length) name).map (BVExpr.eval assign)
    let values := TlsMpc.KernelSpecs.RequestFrame.fetchValues (get "record")
    (BundleKernel.bundleFetchCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0)).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (clientFrame binary mask (WebSocketMessage.request (keysRequest (values 0) (values 1) id)).encode)
        (liveValue (get "record")) :=
  TlsMpc.Node.RequestProofs.bundleFetchCtr_reference id mask frame payloadAt offsets built assign hframe hmask hid

/-- What the server receives from `bundle-request-ctr`: the sealed reference multi-device request. -/
theorem t8_bundleRequestCtr_reference (envelopes : List (List Byte)) (timestamp id : Nat)
    (mask frame : List Byte) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask)
    (hid : id < 2 ^ 64) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let values := TlsMpc.KernelSpecs.RequestFrame.devicesValues (get "records")
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (clientFrame binary mask (WebSocketMessage.request (sendRequest (values 0) (values 1)
          (sendBody (devicesOf values envelopes) timestamp) id official)).encode)
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 :=
  TlsMpc.Node.RequestProofs.bundleRequestCtr_reference envelopes timestamp id mask frame official payloadAt offsets
    built devices paired assign hframe hmask hid

end Kernels
end RequestT8

/-! ### 4e. WebSocket and chat-response parsers: acceptance and rejection (KernelSpecs/Parse*)

`TlsMpc/KernelSpecs/ParseWebSocketAccept.lean` (the frame parser accepts RFC 6455's well-formed
server frames; payload-level rejections), `ParseWebSocketControlFrame.lean` (a control frame's bytes
through the parser into the control queue), `ParseWebSocketReplies.lean` (what `replies` then sends),
`ParseChatResponse.lean` (which bytes of a service response are the body; fail-closed cases). All
about the deployed parsers on `PublicReceive.fast` as the controller runs them. **C**. -/

/-! #### Frame parser acceptance (`ParseWebSocketAccept.lean`) -/

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **The frame parser accepts every well-formed server frame (RFC 6455).** From a frame boundary
in context `c`, over a frame `parseHeader` reads (`f` exactly header and payload) that the reference
`Accepts` in that context: every event keeps the validity byte at 255, and the parser ends at a frame
boundary with the reference's next context, closed exactly after a Close. **C**. SECURITY_MAP C.4. -/
theorem wsFrameAccept_frame_accept (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx)
    (hS : Boundary S c false)
    (f : List Byte) (h : Header) (hp : parseHeader f = some h) (hn : f.length = h.size + h.length)
    (hA : Accepts cap c h (f.drop h.size)) :
    AllValid (events cap S f) ∧ Boundary (finalState cap S f) (c.after cap h) (h.opcode == 8) :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.frame_accept cap hcap S c hS f h hp hn hA

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Over an accepted frame the parser's flags are exactly the reference's:** its `data`,
`controlData`, `frameDone` bytes are 255 where `expectedFlags` says so and 0 elsewhere, every event
valid, and it ends at the next boundary as in `frame_accept`. **C**. SECURITY_MAP C.4. -/
theorem wsFrameAccept_frame_exact (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx)
    (hS : Boundary S c false)
    (f : List Byte) (h : Header) (hp : parseHeader f = some h) (hn : f.length = h.size + h.length)
    (hA : Accepts cap c h (f.drop h.size)) :
    (events cap S f).map (fun e => (e.data, e.controlData, e.frameDone)) =
      (expectedFlags h).map (fun t => (mb t.1, mb t.2.1, mb t.2.2)) ∧
    AllValid (events cap S f) ∧ Boundary (finalState cap S f) (c.after cap h) (h.opcode == 8) :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.frame_exact cap hcap S c hS f h hp hn hA

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Any sequence of accepted frames** (each accepted in the context the ones before leave,
nothing after a Close): every event is valid and the parser ends at a frame boundary. **C**.
SECURITY_MAP C.4. -/
theorem wsFrameAccept_frames_accept (cap : Nat) (hcap : cap < 65536) :
    ∀ (fs : List (Header × List Byte)) (S : State Byte) (c : Ctx),
    Boundary S c false → FramesOk cap c fs →
    AllValid (events cap S (fs.flatMap Prod.snd)) ∧ ∃ c' cl, Boundary (finalState cap S (fs.flatMap Prod.snd)) c' cl :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.frames_accept cap hcap

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **The parser's Close status-code check is RFC 6455's list** (section 7.4 and the IANA registry:
1000–1003, 1007–1014, 3000–4999). **C**. SECURITY_MAP C.4. -/
theorem wsFrameAccept_closeCode_value (hi lo : Byte) :
    TlsWebSocketFrame.closeCode fast hi lo = mb (decide (validCloseCode (wordValue hi lo))) :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.closeCode_value hi lo

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
/-- Every RFC 3629 UTF-8 string runs the parser's UTF-8 automaton (`delta`, read left to right)
back to its start state. (The converse is not proved.) **C** (the automaton is the parser's,
`utf_step`). SECURITY_MAP C.4. -/
theorem wsFrameAccept_utf8_drun {w : List Byte} (h : Utf8 w) : drun 0 w = some 0 :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.utf8_drun h

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Refusal:** a Close with a 1-byte payload (RFC 6455 section 5.5.1: a body starts with a 2-byte
code) makes the parser invalid. **C**. SECURITY_MAP C.4. -/
theorem wsFrameAccept_reject_close_one (cap : Nat) (S : State Byte) (h : S.phases = P 1) (ho : S.opcode = 8#8) :
    (step fast cap S 1#8).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.reject_close_one cap S h ho

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Refusal:** a data payload byte beyond the message's capacity. **C**. SECURITY_MAP C.4. -/
theorem wsFrameAccept_reject_message_full (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4)
    (ho : S.opcode = 0#8 ∨ S.opcode = 2#8) (hm : wordValue S.messageHigh S.messageLow = 0) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.reject_message_full cap S x h ho hm

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Refusal:** a byte of a Close's reason that no UTF-8 character can continue with. **C**.
SECURITY_MAP C.4. -/
theorem wsFrameAccept_reject_reason (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4)
    (ho : S.opcode = 8#8)
    (h1 : S.payloadFirst = 0#8) (h2 : S.payloadSecond = 0#8) (i : Nat) (hi : i < 8) (hu : S.utfPhases = U i)
    (hd : delta i x = none) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.reject_reason cap S x h ho h1 h2 i hi hu hd

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Refusal:** the last byte of a 2-byte Close payload whose code RFC 6455 does not allow. **C**.
SECURITY_MAP C.4. -/
theorem wsFrameAccept_reject_close_code (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4)
    (ho : S.opcode = 8#8)
    (h1 : S.payloadFirst = 0#8) (h2 : S.payloadSecond = 255#8) (hcv : S.closeCodeValid = 0#8)
    (hn : wordValue S.high S.low = 1) (hc : ¬ validCloseCode (wordValue S.closeCodeHigh x)) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.reject_close_code cap S x h ho h1 h2 hcv hn hc

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Refusal:** the last byte of a Close with a reason, its code invalid. **C**. SECURITY_MAP C.4. -/
theorem wsFrameAccept_reject_reason_code (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4)
    (ho : S.opcode = 8#8)
    (h1 : S.payloadFirst = 0#8) (h2 : S.payloadSecond = 0#8) (hn : wordValue S.high S.low = 1)
    (hc : S.closeCodeValid = 0#8) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.reject_reason_code cap S x h ho h1 h2 hn hc

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **Refusal:** the last byte of a Close's reason leaves a UTF-8 character unfinished. **C**.
SECURITY_MAP C.4. -/
theorem wsFrameAccept_reject_reason_unfinished (cap : Nat) (S : State Byte) (x : Byte) (h : S.phases = P 4)
    (ho : S.opcode = 8#8)
    (h1 : S.payloadFirst = 0#8) (h2 : S.payloadSecond = 0#8) (hn : wordValue S.high S.low = 1)
    (i j : Nat) (hu : S.utfPhases = U i) (hd : delta i x = some j) (hj : j ≠ 0) :
    (step fast cap S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseWebSocketAccept.reject_reason_unfinished cap S x h ho h1 h2 hn i j hu hd hj

/-! #### Control frames into the control queue (`ParseWebSocketControlFrame.lean`) -/

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.KernelSpecs.ParseWebSocketControlFrame in
open TlsMpc.KernelSpecs.ParseWebSocketControl (runC Idle kindOf reply blockSet) in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **A Ping or Close, from its bytes to the queued answer (RFC 6455 sections 5.5.1–5.5.2).** A Ping
(9) or Close (8) with payload `q ++ [b]` (1 to 125 bytes; for a Close a valid code and UTF-8 reason),
run through the frame parser from a frame boundary, its outputs fed to an idle control queue: the
queue is idle again with `reply`'s answer appended (Pong for a Ping, Close for a Close; the length;
the payload, zero-padded). **C**. SECURITY_MAP C.4. -/
theorem wsControlFrame_control_queue (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx)
    (hS : Boundary S c false)
    (Q : TlsWebSocketControl.State Byte) (hQ : Idle Q) (o : Nat) (ho : o = 8 ∨ o = 9) (q : List Byte) (b : Byte)
    (hp : (q ++ [b]).length ≤ 125) (hc : (q ++ [b]).length ≤ cap) (hclose : o = 8 → CloseBody (q ++ [b])) :
    runC Q (List.zipWith cin (events cap S (controlFrame o (q ++ [b]))) (controlFrame o (q ++ [b]))) =
      { valid := Q.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (Q.queued.toNat + 1),
        kinds := Q.kinds.set Q.queued.toNat (kindOf (BitVec.ofNat 8 o)),
        lengths := Q.lengths.set Q.queued.toNat (BitVec.ofNat 8 (q ++ [b]).length),
        payloads := blockSet Q.payloads Q.queued.toNat
          ((q ++ [b]) ++ List.replicate (125 - (q ++ [b]).length) 0#8) } ∧
    reply o (q ++ [b]) = some ((kindOf (BitVec.ofNat 8 o)).toNat, q ++ [b]) :=
  TlsMpc.KernelSpecs.ParseWebSocketControlFrame.control_queue cap hcap S c hS Q hQ o ho q b hp hc hclose

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.KernelSpecs.ParseWebSocketControlFrame in
open TlsMpc.KernelSpecs.ParseWebSocketControl (runC Idle kindOf reply blockSet) in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **A Pong leaves an idle queue as it is:** no answer is owed (section 5.5.3). **C**.
SECURITY_MAP C.4. -/
theorem wsControlFrame_control_queue_pong (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx)
    (hS : Boundary S c false)
    (Q : TlsWebSocketControl.State Byte) (hQ : Idle Q) (q : List Byte) (b : Byte)
    (hp : (q ++ [b]).length ≤ 125) (hc : (q ++ [b]).length ≤ cap) :
    runC Q (List.zipWith cin (events cap S (controlFrame 10 (q ++ [b]))) (controlFrame 10 (q ++ [b]))) = Q ∧
    reply 10 (q ++ [b]) = none :=
  TlsMpc.KernelSpecs.ParseWebSocketControlFrame.control_queue_pong cap hcap S c hS Q hQ q b hp hc

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.KernelSpecs.ParseWebSocketControlFrame in
open TlsMpc.KernelSpecs.ParseWebSocketControl (runC Idle kindOf reply blockSet) in
open TlsMpc.TlsWebSocketFrame (State step wordValue) in
open PublicReceive (fast) in
/-- **A Ping or Close with no payload:** the answer is queued with length 0. **C**.
SECURITY_MAP C.4. -/
theorem wsControlFrame_control_queue_empty (cap : Nat) (hcap : cap < 65536) (S : State Byte) (c : Ctx)
    (hS : Boundary S c false)
    (Q : TlsWebSocketControl.State Byte) (hQ : Idle Q) (o : Nat) (ho : o = 8 ∨ o = 9) :
    runC Q (List.zipWith cin (events cap S (controlFrame o [])) (controlFrame o [])) =
      { valid := Q.valid, count := 0#8, data := List.replicate 125 0#8,
        queued := BitVec.ofNat 8 (Q.queued.toNat + 1),
        kinds := Q.kinds.set Q.queued.toNat (kindOf (BitVec.ofNat 8 o)),
        lengths := Q.lengths.set Q.queued.toNat 0#8,
        payloads := blockSet Q.payloads Q.queued.toNat (List.replicate 125 0#8) } ∧
    reply o [] = some ((kindOf (BitVec.ofNat 8 o)).toNat, []) :=
  TlsMpc.KernelSpecs.ParseWebSocketControlFrame.control_queue_empty cap hcap S c hS Q hQ o ho

/-! #### The reply sent (`ParseWebSocketReplies.lean`) -/

open TlsMpc.KernelSpecs.ParseWebSocketFrame TlsMpc.KernelSpecs.ParseWebSocketAccept in
open TlsMpc.KernelSpecs.ParseWebSocketControlFrame in
open TlsMpc.KernelSpecs.ParseWebSocketControl (Idle kindOf blockSet clientFrame framesOf) in
open PublicReceive (fast) in
/-- **End to end, a Ping or Close gets RFC 6455's answer.** A Ping or Close (payload `q ++ [b]`, 1
to 125 bytes) read by the frame parser from a frame boundary and fed to a fresh control queue: with
that queue in the controller's state, `replies` sends exactly one masked client frame (section 5.3)
carrying `reply`'s answer (Pong for a Ping, Close echoing a Close), masked with the first key. **C**.
SECURITY_MAP C.4. -/
theorem wsReplies_control_reply (cap : Nat) (hcap : cap < 65536) (S : TlsWebSocketFrame.State Byte) (c : Ctx)
    (hS : Boundary S c false) (o : Nat) (ho : o = 8 ∨ o = 9) (q : List Byte) (b : Byte)
    (hp : (q ++ [b]).length ≤ 125) (hc : (q ++ [b]).length ≤ cap) (hclose : o = 8 → CloseBody (q ++ [b]))
    (s : PublicReceive.State) (mask : List Byte) (hmask : mask.length = 4) (rest : List (List Byte))
    (hs : s.control = TlsWebSocketControl.stateBytes (TlsMpc.KernelSpecs.ParseWebSocketControl.runC
      (TlsWebSocketControl.initial fast)
      (List.zipWith cin (events cap S (controlFrame o (q ++ [b]))) (controlFrame o (q ++ [b]))))) :
    framesOf (PublicReceive.replies s (mask :: rest)) =
      [((kindOf (BitVec.ofNat 8 o)).toNat, clientFrame (kindOf (BitVec.ofNat 8 o)).toNat mask (q ++ [b]))] ∧
    TlsMpc.KernelSpecs.ParseWebSocketControl.reply o (q ++ [b]) =
      some ((kindOf (BitVec.ofNat 8 o)).toNat, q ++ [b]) :=
  TlsMpc.KernelSpecs.ParseWebSocketReplies.control_reply cap hcap S c hS o ho q b hp hc hclose s mask hmask rest hs

/-! #### The chat-response parser: the body's extent (`ParseChatResponse.lean`)

`d`, `o` are `VarintDecode.Spqr.concrete` and `Word64.fast` (abbrevs in `ParseChatResponse`), the
decoder and 64-bit word operations the controller runs the parser with. -/

open TlsMpc.KernelSpecs.ParseChatResponse in
open PublicReceive (fast) in
/-- **The response parser marks exactly the body as body.** From a field key inside the inner
response, with `rem` bytes of it and `bud` of the budget left, over the body field (key `22`, the
length as a varint, a non-empty body) followed by more of the inner response: every event valid;
`bodyData` exactly on the body's bytes (not on the key or the length); `bodyReset` exactly on the
length's last byte; afterwards at a field key again with the counts lowered and the body's length
recorded. **C**. SECURITY_MAP C.4. -/
theorem chatResponse_body_field (S : RState) (hK : KeyIn S) (rem bud : Nat) (hr : rem < 2 ^ 64) (hb : bud < 2 ^ 64)
    (hrem : S.responseRemaining = BitVec.ofNat 64 rem) (hbud : S.budget = BitVec.ofNat 64 bud)
    (body : List Byte) (hne : body ≠ []) (hv9 : (varint body.length).length ≤ 9)
    (hfit : (bodyField body).length < rem) (hbfit : (bodyField body).length ≤ bud) :
    AllValid (sEvents S (bodyField body)) ∧
    (sEvents S (bodyField body)).map (·.bodyData) =
      List.replicate (1 + (varint body.length).length) 0#8 ++ List.replicate body.length 255#8 ∧
    (sEvents S (bodyField body)).map (·.bodyReset) =
      List.replicate (varint body.length).length 0#8 ++ [255#8] ++ List.replicate body.length 0#8 ∧
    sFinal S (bodyField body) = { S with
      modes := [255#8, 0#8, 0#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
      responseRemaining := BitVec.ofNat 64 (rem - (bodyField body).length),
      budget := BitVec.ofNat 64 (bud - (bodyField body).length), skip := 0#64, bodyPresent := 255#8,
      bodyLength := BitVec.ofNat 64 body.length, utf := TlsWebSocketUpgrade.initial fast 7,
      header := TlsChatResponse.headerInitial fast } :=
  TlsMpc.KernelSpecs.ParseChatResponse.body_field S hK rem bud hr hb hrem hbud body hne hv9 hfit hbfit

open TlsMpc.KernelSpecs.ParseChatResponse in
open PublicReceive (fast) in
/-- **The same when the body is the inner response's last field:** the parser leaves the inner
response (`inner` 0, `responseRemaining` 0) at the body's last byte. **C**. SECURITY_MAP C.4. -/
theorem chatResponse_body_field_close (S : RState) (hK : KeyIn S) (rem bud : Nat) (hr : rem < 2 ^ 64)
    (hb : bud < 2 ^ 64)
    (hrem : S.responseRemaining = BitVec.ofNat 64 rem) (hbud : S.budget = BitVec.ofNat 64 bud)
    (body : List Byte) (hne : body ≠ []) (hv9 : (varint body.length).length ≤ 9)
    (hfit : (bodyField body).length = rem) (hbfit : (bodyField body).length ≤ bud) :
    AllValid (sEvents S (bodyField body)) ∧
    (sEvents S (bodyField body)).map (·.bodyData) =
      List.replicate (1 + (varint body.length).length) 0#8 ++ List.replicate body.length 255#8 ∧
    (sEvents S (bodyField body)).map (·.bodyReset) =
      List.replicate (varint body.length).length 0#8 ++ [255#8] ++ List.replicate body.length 0#8 ∧
    sFinal S (bodyField body) = { S with
      modes := [255#8, 0#8, 0#8, 0#8], tag := 4#64, scalarKnown := 0#8, kinds := [0#8, 255#8, 0#8, 0#8],
      inner := 0#8, responseRemaining := 0#64,
      budget := BitVec.ofNat 64 (bud - (bodyField body).length), skip := 0#64, bodyPresent := 255#8,
      bodyLength := BitVec.ofNat 64 body.length, utf := TlsWebSocketUpgrade.initial fast 7,
      header := TlsChatResponse.headerInitial fast } :=
  TlsMpc.KernelSpecs.ParseChatResponse.body_field_close S hK rem bud hr hb hrem hbud body hne hv9 hfit hbfit

open TlsMpc.KernelSpecs.ParseChatResponse in
open PublicReceive (fast) in
/-- **The controller's loop over the parser is `step` iterated:** for payload bytes that neither start
nor end the message (flags `255 0 0`), feeding `runByte` the serialised state byte after byte gives
`step`'s events and final state. **C**. SECURITY_MAP C.4. -/
theorem chatResponse_respRun_active (cap : Nat) : ∀ (xs : List Byte) (S : RState), Shaped S →
    respRun cap (TlsChatResponse.stateBytes o S) (xs.map (fun x => ([255#8, 0#8, 0#8], x))) =
      ((sEvents S xs).map outBytes, TlsChatResponse.stateBytes o (sFinal S xs)) :=
  TlsMpc.KernelSpecs.ParseChatResponse.respRun_active cap

open TlsMpc.KernelSpecs.ParseChatResponse in
open PublicReceive (fast) in
/-- **`body_field` through the deployed `runByte`, as the controller runs it:** over the body field's
bytes, output byte 0 (validity) is 255 throughout, byte 1 (`finished`) 0, byte 3 (`bodyData`) 255
exactly on the body's bytes, byte 4 (`bodyReset`) exactly on the length's last byte. **C**.
SECURITY_MAP C.4. -/
theorem chatResponse_body_field_runByte (cap : Nat) (S : RState) (hK : KeyIn S) (rem bud : Nat) (hr : rem < 2 ^ 64)
    (hb : bud < 2 ^ 64) (hrem : S.responseRemaining = BitVec.ofNat 64 rem) (hbud : S.budget = BitVec.ofNat 64 bud)
    (body : List Byte) (hne : body ≠ []) (hv9 : (varint body.length).length ≤ 9)
    (hfit : (bodyField body).length < rem) (hbfit : (bodyField body).length ≤ bud) :
    let outs := (respRun cap (TlsChatResponse.stateBytes o S)
      ((bodyField body).map (fun x => ([255#8, 0#8, 0#8], x)))).1
    outs.map (fun out : List Byte => out.getD 0 0) = List.replicate (bodyField body).length 255#8 ∧
    outs.map (fun out : List Byte => out.getD 1 0) = List.replicate (bodyField body).length 0#8 ∧
    outs.map (fun out : List Byte => out.getD 3 0) =
      List.replicate (1 + (varint body.length).length) 0#8 ++ List.replicate body.length 255#8 ∧
    outs.map (fun out : List Byte => out.getD 4 0) =
      List.replicate (varint body.length).length 0#8 ++ [255#8] ++ List.replicate body.length 0#8 :=
  TlsMpc.KernelSpecs.ParseChatResponse.body_field_runByte cap S hK rem bud hr hb hrem hbud body hne hv9 hfit hbfit

open TlsMpc.KernelSpecs.ParseChatResponse in
open PublicReceive (fast) in
/-- **Fail closed: a body length beyond the inner response.** A declared body length larger than what
is left of the inner response drops the validity byte at the length's last byte, before any byte is
reported as body. **C**. SECURITY_MAP C.4. -/
theorem chatResponse_reject_body_length (S : RState) (hm : S.modes = [0#8, 0#8, 255#8, 0#8]) (j : Nat) (hj : j < 9)
    (hp : S.positions = Pos j) (hi : S.inner = 255#8) (hS : Shaped S) (x : Byte) (hx : x.toNat < 128)
    (hgt : (S.responseRemaining - 1).toNat < (S.value ||| TlsMpc.Signal.VarintDecode.Spqr.payload x j).toNat) :
    (TlsChatResponse.step d o fast S x).state.valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseChatResponse.reject_body_length S hm j hj hp hi hS x hx hgt

open TlsMpc.KernelSpecs.ParseChatResponse in
open PublicReceive (fast) in
/-- **Fail closed: a message that ends inside a field** (e.g. a truncated body) is not completed:
`finish` drops the validity byte. **C**. SECURITY_MAP C.4. -/
theorem chatResponse_reject_end_in_field (S : RState) (hm : S.modes = [0#8, 0#8, 0#8, 255#8]) :
    (TlsChatResponse.finish o fast S).valid = 0#8 :=
  TlsMpc.KernelSpecs.ParseChatResponse.reject_end_in_field S hm

/-! #### Whole-message vectors (not restated)

`TlsMpc/KernelSpecs/ParseChatResponseVectors.lean` runs the controller's loop (`respRun 16384`,
the deployed `runByte` byte by byte) over three whole WebSocket messages and pins every output and
the final state: `vA_run`, `vB_run`, `vC_run` (with `vA_extent`, `vB_extent`, `vC_extent`: `bodyData`
is 255 exactly on the bytes the reference decoder `wsMessage` puts in the body; and `vA_reference`,
`vB_reference`, `vC_reference`: what that decoder reads). Not imported here: checking that file is
too heavy for this one. **C**. SECURITY_MAP C.4. -/

/-! ### 4f. The reveal policy (T1, Policy/ReceiveProofs.lean)

`TlsMpc/Node/Policy/ReceiveProofs.lean` (proof track P1). The record loop `recordLoop` /
`streamRun` is a Lean model of the controller's `record` loop (handshake_backend/EmpHybridWork/
PublicServiceController.lean): it reveals a run first and checks it after. The functions it calls
(`scan`, `replyScan`, `budget`, `mayReveal`, `passRun`, `passBulk`) are the controller's own
(`TlsMpc/Node/Policy/Receive.lean`). `scanBody` / `replyScanBody` are the scanners' loop bodies
written out, proved equal to the loops by `scan_eq` / `replyScan_eq`. The per-byte glue (that
`step` keeps `request`/`reply` equal to the message so far and sets `skip` from the scanners'
answer) is proved per byte in `Policy/ReceiveInvariant.lean` (below, "4f (continued)"); `T1` for
every stream, about the loop the session runs, is 4g. End-to-end runs of the loop
on the two former too-long-varint counterexamples, `ReceiveTest.overlongRequest_refused` and
`ReceiveTest.overlongResponse_refused` (`TlsMpc/Node/Policy/ReceiveTest.lean`), are not restated: that
file is too heavy to import here. -/

/-- **A body being passed over is never revealed, across records.** If the loop starts a record at
stream position `base` with `skip = n`, none of the positions `base, …, base + n - 1` is ever
revealed, however the rest of the stream is cut into records. **M** (the loop is a model of the
controller's `record`; the steps it calls are **C**). SECURITY_MAP C.4. -/
theorem receivePolicy_go_skip : ∀ (records : List (List PublicReceive.Byte)) (s : PublicReceive.State) (base : Nat)
    (acc : List Nat),
    ∀ q ∈ (ReceiveProofs.streamRun.go s records base acc).1, q ∈ acc ∨ base + s.skip ≤ q :=
  ReceiveProofs.go_skip

/-- **Within one record:** if the loop reaches `offset` with `skip > 0`, it reveals none of the next
`min skip (bytes left)` positions. **M** (as `go_skip`). SECURITY_MAP C.4. -/
theorem receivePolicy_recordLoop_skip (fuel : Nat) (s : PublicReceive.State) (bytes : List PublicReceive.Byte)
    (offset base : Nat) (acc : List Nat)
    (hs : 0 < s.skip) (ho : offset < bytes.length) :
    ∀ q ∈ (ReceiveProofs.recordLoop (fuel + 1) s bytes offset base acc).1,
      q ∈ acc ∨ (base + offset + min s.skip (bytes.length - offset) ≤ q ∧ q < base + bytes.length) :=
  ReceiveProofs.recordLoop_skip fuel s bytes offset base acc hs ho

/-- **A server request's body is found exactly and no run reaches it.** For a server request in the
server's layout (verb, path, body key and length; any verb and path bytes, any varint encodings of at
most 10 bytes): on every proper prefix of its head, `scan` asks for more (neither skips nor refuses)
and the controller's next run (`budget`) ends at or before the body's first byte; at the end of the
body's length, `scan` says to pass over exactly the body. With `go_skip`: no body byte is revealed.
**C**. SECURITY_MAP C.4. -/
theorem receivePolicy_request_body_unrevealed {lw vv verb pv path bv : List PublicReceive.Byte} {L n : Nat}
    (hl : ReceiveProofs.Varint lw L) (hl10 : lw.length ≤ 10) (hv : ReceiveProofs.Varint vv verb.length)
    (hv10 : vv.length ≤ 10)
    (hp : ReceiveProofs.Varint pv path.length) (hp10 : pv.length ≤ 10) (hb : ReceiveProofs.Varint bv n)
    (hb10 : bv.length ≤ 10)
    (hn : 0 < n) :
    (∀ (s : PublicReceive.State) (k : Nat), 2 ≤ k → k < (ReceiveProofs.requestHead lw vv verb pv path bv).length →
      s.request = (ReceiveProofs.requestHead lw vv verb pv path bv).take k → s.upgraded = true →
      (PublicReceive.get s.frame 0 == PublicReceive.on) = false →
      (PublicReceive.get s.frame 2 == PublicReceive.on) = false →
      (PublicReceive.get s.frame 4 == PublicReceive.on) = true →
      (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0 →
      (PublicReceive.get s.frame 7).toNat < 8 → s.message = [8, 1] →
      (PublicReceive.scan s.request false).1 = .more ∧
        k + PublicReceive.budget s ≤ (ReceiveProofs.requestHead lw vv verb pv path bv).length) ∧
    PublicReceive.scan (ReceiveProofs.requestHead lw vv verb pv path bv) false =
      (.skip n, { verb, path, id := none, body := some n }) :=
  ReceiveProofs.request_body_unrevealed hl hl10 hv hv10 hp hp10 hb hb10 hn

/-- **The same for a response** (id, status, message, body; e.g. the `200` to a prekey fetch, whose
body is the contact's bundle): no run reaches the body, and at the end of its length `replyScan` says
to pass over exactly the body, with the id and status read. **C**. SECURITY_MAP C.4. -/
theorem receivePolicy_response_body_unrevealed {lw iv sv mv msg bv : List PublicReceive.Byte} {L i st n : Nat}
    (hl : ReceiveProofs.Varint lw L) (hl10 : lw.length ≤ 10) (hi : ReceiveProofs.Varint iv i)
    (hi10 : iv.length ≤ 10)
    (hs : ReceiveProofs.Varint sv st) (hs10 : sv.length ≤ 10) (hm : ReceiveProofs.Varint mv msg.length)
    (hm10 : mv.length ≤ 10)
    (hb : ReceiveProofs.Varint bv n) (hb10 : bv.length ≤ 10) (hn : 0 < n) :
    (∀ (s : PublicReceive.State) (k : Nat), 2 ≤ k → k < (ReceiveProofs.responseHead lw iv sv mv msg bv).length →
      s.reply = (ReceiveProofs.responseHead lw iv sv mv msg bv).take k → s.openBody = false →
      s.upgraded = true →
      (PublicReceive.get s.frame 0 == PublicReceive.on) = false →
      (PublicReceive.get s.frame 2 == PublicReceive.on) = false →
      (PublicReceive.get s.frame 4 == PublicReceive.on) = true →
      (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0 →
      (PublicReceive.get s.frame 7).toNat < 8 → s.message = [8, 2] →
      (PublicReceive.replyScan s.reply false s.openBody).1 = .more ∧
        k + PublicReceive.budget s ≤ (ReceiveProofs.responseHead lw iv sv mv msg bv).length) ∧
    PublicReceive.replyScan (ReceiveProofs.responseHead lw iv sv mv msg bv) false false =
      (.skip n, { id := some i, status := some st, body := some n }) :=
  ReceiveProofs.response_body_unrevealed hl hl10 hi hi10 hs hs10 hm hm10 hb hb10 hn

/-- **No payload byte of a delivered envelope is revealed** (scanner level, every byte string `E`,
the body of a delivered message). Every byte the envelope walk reveals has a public class in the
reference `ReceiveSpec.envelope`: a key, a length or a varint value, never a field's payload, never
a byte after the envelope left the protocol. **C** (`TlsMpc/Node/Policy/ReceiveEnvelope.lean`).
SECURITY_MAP C.4. -/
theorem receivePolicy_envelope_payload_unrevealed (E : List PublicReceive.Byte) :
    ReceiveProofs.SafeFor (ReceiveProofs.envWalk [] 0 0 E) (ReceiveSpec.envelope (E.length + 1) E) :=
  ReceiveProofs.envelope_payload_unrevealed E

/-! #### 4f (continued). The controller's step, byte by byte (`Policy/ReceiveInvariant.lean`)

`PublicReceive.step` is `frameByte` (the WebSocket frame layer) then `payloadByte` (the message's
own fields), proved equal to the former `step`. `EnvAt s h p k r`: the controller is walking a
delivered envelope (revealed bytes `h`, `p` payloads passed over, `k` bytes still to pass over, `r`
bytes of the body left). `EnvRun s E F`: any sequence of the controller's moves over the body bytes
`E` (revealed by `step`, passed over by `stepSkipped`, frame headers and control frames between
fragments, stopping), `F` saying which body bytes were revealed. -/

section ReceiveInvariant
open PublicReceive ReceiveProofs TlsMpc.Signal
open TlsMpc.KernelSpecs.ParseWebSocketFrame (Shaped eventBytes)

/-- **A delivered message's envelope, end to end (controller level, every byte string).** At the
byte that completes the body's length of a server request whose path is `/api/v1/message`, and
over the body's `n` bytes `E`, whatever the controller's moves (`EnvRun`), every body byte it
reveals has a public class in the reference's reading of that body (`ReceiveSpec.requestBody` of
`/api/v1/message`: an envelope): a key, a length or a varint value, never a field's payload.
**C** (the moves are the controller's own `step`/`stepSkipped`). SECURITY_MAP C.4. -/
theorem receivePolicy_request_envelope_safe {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {n : Nat} {f : Fields} {E : List Byte} {F : List Bool} (hm : s.message = [8, 1]) (hi : s.inner = none)
    (hs : s.skip = 0)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.skip n, f))
    (hpath : (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = true)
    (hok : payloadByte s b true done false flags = .ok (s', c)) (hE : E.length = n) (hrun : EnvRun s' E F) :
    f.path = ReceiveSpec.messagePath ∧ SafeFor F (ReceiveSpec.requestBody f.path E) :=
  ReceiveProofs.request_envelope_safe hm hi hs hscan hpath hok hE hrun

/-- **No payload byte of a delivered envelope is revealed (controller level).** From the state in
which the controller starts walking an envelope of `E.length` bytes (`EnvAt s [] 0 0 E.length`),
whatever moves it makes over the body (`EnvRun`), every revealed body byte has a public class in
`ReceiveSpec.envelope`. **C**. SECURITY_MAP C.4. -/
theorem receivePolicy_envRun_safe {s : State} {E : List Byte} {F : List Bool} (hs : EnvAt s [] 0 0 E.length)
    (h : EnvRun s E F) : SafeFor F (ReceiveSpec.envelope (E.length + 1) E) :=
  ReceiveProofs.envRun_safe hs h

/-- **The envelope walk starts where `scan` finds a `/api/v1/message` body:** at the byte completing
the body's length, `EnvAt s' [] 0 0 n` with `n` the body's length. **C**. -/
theorem receivePolicy_payloadByte_request_envelope {s s' : State} {b : Byte} {done : Bool} {flags : List Byte}
    {c : Bool} {n : Nat} {f : Fields} (hm : s.message = [8, 1]) (hi : s.inner = none) (hs : s.skip = 0)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.skip n, f))
    (hpath : (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = true)
    (hok : payloadByte s b true done false flags = .ok (s', c)) :
    EnvAt s' [] 0 0 n ∧ s'.request = (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) :=
  ReceiveProofs.payloadByte_request_envelope hm hi hs hscan hpath hok

/-- **`skip` is set to a server request's body length exactly when `scan` asks to pass over it**
(a body other than a delivered message's, which is walked). **C**. -/
theorem receivePolicy_payloadByte_request_skip {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {n : Nat} {f : Fields} (hm : s.message = [8, 1]) (hi : s.inner = none)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.skip n, f))
    (hpath : (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = false)
    (hok : payloadByte s b true done false flags = .ok (s', c)) :
    s'.skip = n ∧ 0 < n ∧ s'.inner = none ∧ s'.message = [8, 1] ∧ s'.bodySkipped = true ∧
      s'.request = (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) :=
  ReceiveProofs.payloadByte_request_skip hm hi hscan hpath hok

/-- **`scan` asks for more:** the byte joins the request's revealed bytes; nothing to pass over, no
envelope. **C**. -/
theorem receivePolicy_payloadByte_request_more {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {f : Fields} (hm : s.message = [8, 1]) (hi : s.inner = none)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.more, f))
    (hok : payloadByte s b true done false flags = .ok (s', c)) :
    s'.skip = s.skip ∧ s'.inner = none ∧
      (done = false → s'.request = (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) ∧
        s'.message = [8, 1] ∧ s'.bodySkipped = s.bodySkipped) :=
  ReceiveProofs.payloadByte_request_more hm hi hscan hok

/-- **`skip` is set to a response body's length exactly when `replyScan` asks to pass over it**
(the message not ending at this byte). **C**. -/
theorem receivePolicy_payloadByte_reply_skip {s s' : State} {b : Byte} {flags : List Byte} {c : Bool}
    {n : Nat} {f : ReplyFields} (hm : s.message = [8, 2])
    (hscan : replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) s.replySkipped s.openBody =
      (.skip n, f))
    (hok : payloadByte s b true false false flags = .ok (s', c)) :
    s'.skip = n ∧ s'.reply = (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) ∧
      s'.replySkipped = true ∧ s'.message = [8, 2] :=
  ReceiveProofs.payloadByte_reply_skip hm hscan hok

/-- **`replyScan` asks for more:** the byte joins the response's revealed bytes; `skip` is
unchanged. **C**. -/
theorem receivePolicy_payloadByte_reply_more {s s' : State} {b : Byte} {flags : List Byte} {c : Bool}
    {f : ReplyFields} (hm : s.message = [8, 2])
    (hscan : replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) s.replySkipped s.openBody =
      (.more, f))
    (hok : payloadByte s b true false false flags = .ok (s', c)) :
    s'.skip = s.skip ∧ s'.reply = (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) ∧
      s'.replySkipped = s.replySkipped ∧ s'.message = [8, 2] :=
  ReceiveProofs.payloadByte_reply_more hm hscan hok

/-- **The frame parser's state is kept by `step`'s frame side** (once upgraded): if the controller's
frame state serialises a shaped reference state `S`, after a revealed byte `b` it serialises
`TlsWebSocketFrame.step S b`, and `payloadByte` is given that step's event. **C**. -/
theorem receivePolicy_frameByte_frame {s s1 : State} {b : Byte} {ev : List Byte} {S : TlsWebSocketFrame.State Byte}
    (hu : s.upgraded = true) (hf : s.frame = TlsWebSocketFrame.stateBytes S) (hS : Shaped S)
    (h : frameByte s b = .ok (s1, ev)) :
    s1.frame = TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.step fast capacity S b).state ∧
      ev = eventBytes (TlsWebSocketFrame.step fast capacity S b) ∧
      Shaped (TlsWebSocketFrame.step fast capacity S b).state :=
  ReceiveProofs.frameByte_frame hu hf hS h

end ReceiveInvariant

/-! #### 4g. T1 for every stream (proof track P1; PROOF_GAPS.md C1, C2)

`ReceiveLoop.t1_all` (`TlsMpc/Node/Policy/ReceiveSession.lean`) is about the loop the session runs:
`Session/Common.lean`'s `record` is `RecordLoop.run` (`Policy/RecordLoop.lean`) at the session's
operations, and the theorem is about `RecordLoop.run` at every operations record of a pure monad that
satisfies `Faithful` (the engines' length probe and reveal return the record's length and exactly the
bytes asked for; a theorem for the S12 script backend on its branch, an assumption on the engines for
the legacy operation 43), over every stream, every cut into records, with any steps between records
that keep the policy's view (`replies` then `requests := []`, `expect`, the fetch fields: C2). The
model loop `recordLoop` / `streamRun` (4f) is what the proof runs through (`loop_sub`). Its parts:
`run_safe` (one run, every reachable state, every byte string), `t1_frames` (the model loop), the
simulation (`sim_step`, `sim_pass`), the reference read byte by byte (`classifyFrames_stream`,
`classify_stream`, `message_prefix`), the message level (`rshape_run_c`, `qshape_run_c`,
`reply_run_safe`, `request_run_safe`, `envelope_noErr`), the frame layer (`frameByte_reject`), and the
HTTP head before the upgrade (`upgrade_run_safe`, `frameByte_terminator`), joined with the frames from
the first byte of a fresh connection against `ReceiveSpec.classify` (`t1_start`, `t1_start_model`,
`frameByte_head`, `payloadByte_head`, `headStep`, `keepsHead_afterRecord`; `ReceiveStart.lean`,
PROOF_GAPS D1). -/

section T1All
open PublicReceive ReceiveProofs TlsMpc.Signal
open TlsMpc.KernelSpecs.ParseWebSocketFrame (Shaped)

/-- **T1 for every stream, about the record loop the session runs.** From the upgraded starting
state (any `accept`, `lenient`, `openBody`), over every stream of frames cut into records in any way,
with the engines as assumed (`Faithful`) and any steps between records that keep the view, every
stream position the loop has the engines reveal is public in `ReceiveSpec.classifyFrames`, or is
its first `error` (the one-byte allowance). **C-gen**. PROOF_GAPS C1, C2. -/
theorem receivePolicy_t1_all (openBody : Bool) (accept : List Byte) (lenient : Bool) (records : List (List Byte))
    {β : Type} (O : Nat → List Byte → RecordLoop.Ops ReceiveLoop.RevealM β)
    (hO : ∀ base r, ReceiveLoop.Faithful r base (O base r))
    (g : Nat → State → Except String State) (hg : ∀ i, ReceiveLoop.Keeps (g i)) :
    ∀ q ∈ (ReceiveLoop.sessionRun O g { PublicReceive.start accept with upgraded := true, lenient := lenient, openBody }
        records).1,
      ReceiveSpec.allowedIn (ReceiveSpec.classifyFrames openBody records.flatten) q = true ∨
        ReceiveSpec.firstError (ReceiveSpec.classifyFrames openBody records.flatten) = some q :=
  ReceiveLoop.t1_all openBody accept lenient records O hO g hg

/-- **The loop the session runs, against the model loop** (C1): under `Faithful`, every position
`RecordLoop.loop` reveals is one `recordLoop` reveals, and when it returns a state the model returns
the same state (envelopes handed on before `envelopes := []` do not change it). **C-gen**. -/
theorem receivePolicy_loop_sub {β : Type} {o : RecordLoop.Ops ReceiveLoop.RevealM β} {r : List Byte} {base : Nat}
    (hO : ReceiveLoop.Faithful r base o) (fuel : Nat) (s : State) (cpl : Bool) (off : Nat) (acc : List Nat) :
    (∀ q ∈ (RecordLoop.loop o fuel s cpl off r.length acc).2, q ∈ (recordLoop fuel s r off base acc).1) ∧
      (∀ s' c', (RecordLoop.loop o fuel s cpl off r.length acc).1 = .ok (s', c') →
        (recordLoop fuel s r off base acc).2 = .ok s') :=
  ReceiveLoop.loop_sub hO fuel s cpl off acc

/-- **The record loop's fuel never runs out** (C1): `RecordLoop.run` (fuel: the record's length plus
one) gives the same run as any larger fuel, so it behaves as the unbounded loop. **C-gen**. -/
theorem receivePolicy_run_fuel {β : Type} {o : RecordLoop.Ops ReceiveLoop.RevealM β} {r : List Byte} {base : Nat}
    (hO : ReceiveLoop.Faithful r base o) (s : State) (acc : List Nat) (k : Nat) :
    RecordLoop.loop o (r.length + 1 + k) s false 0 r.length acc = RecordLoop.run o s acc :=
  ReceiveLoop.run_fuel hO s acc k

/-- **`replies` keeps the policy's view** (C2): it changes only the control queue. **C**. -/
theorem receivePolicy_view_replies {s s' : State} {masks : List (List Byte)} {frames : List (Nat × List Byte)}
    (h : replies s masks = .ok (s', frames)) : ReceiveSimByte.view s' = ReceiveSimByte.view s :=
  ReceiveLoop.view_replies h

/-- **The session's step after a record keeps the view** (C2): the control replies (any masks), then
`requests := []`. **C**. -/
theorem receivePolicy_keeps_afterRecord (masks : List (List Byte)) :
    ReceiveLoop.Keeps (fun s => (replies s masks).map (fun p => { p.1 with requests := [] })) :=
  ReceiveLoop.keeps_afterRecord masks

/-- **T1 for the model loop, from any state that simulates the reference's initial state.** **M**. -/
theorem receivePolicy_t1_frames (ob : Bool) (s : State) (records : List (List Byte))
    (hs : ReceiveSim.Sim ob s ReceiveStream.Stream.init records.flatten.length) : T1 ob s records :=
  ReceiveLoop.t1_frames ob s records hs

/-- **One run, every state the controller reaches, every byte string**: with nothing to pass over,
every byte of the run it reveals next is public in the reference, or is its first `error`. **C**. -/
theorem receivePolicy_run_safe {ob : Bool} {s : State} {st1 : ReceiveStream.Stream.St} (Y Z : List Byte)
    (hs : ReceiveSim.Sim ob s (st1, false) (Y.length + Z.length)) (hsk : s.skip = 0)
    (hY : Y.length ≤ budget s) :
    ∀ i < Y.length, ReceiveLoop.SafeR (ReceiveStream.Stream.runF ob (st1, false) (Y ++ Z)) i :=
  ReceiveLoop.run_safe Y Z hs hsk hY

/-- **Every byte the controller accepts keeps the simulation.** **C**. -/
theorem receivePolicy_sim_step {ob : Bool} {s s' : State} {st1 : ReceiveStream.Stream.St} {n : Nat} {b : Byte} {c : Bool}
    (hs : ReceiveSim.Sim ob s (st1, false) (n + 1)) (h : step s b = .ok (s', c)) :
    ReceiveSim.Sim ob s' (ReceiveStream.Stream.stepF ob (st1, false) b n).2 n :=
  ReceiveSim.sim_step hs h

/-- **Every byte the controller passes over keeps the simulation.** **C**. -/
theorem receivePolicy_sim_pass {ob : Bool} {s s' : State} {st1 : ReceiveStream.Stream.St} {n : Nat} {b : Byte} {d : Bool}
    (hs : ReceiveSim.Sim ob s (st1, false) (n + 1)) (h : passOne s = .ok (s', d)) :
    ReceiveSim.Sim ob s' (ReceiveStream.Stream.stepF ob (st1, false) b n).2 n :=
  ReceiveSim.sim_pass hs h

/-- **A delivered envelope walked past its end has no `error` class.** **C**. -/
theorem receivePolicy_envelope_noErr (E : List Byte) (L : List Bool) (hd : List Byte) (p k : Nat)
    (hL : L.length = E.length) (hw : envWalk [] 0 0 (E ++ [0]) = L ++ envWalk hd p k [0]) :
    ∀ x ∈ ReceiveSpec.envelope (E.length + 1) E, x ≠ .error :=
  ReceiveEnvDone.envelope_noErr E L hd p k hL hw

/-- **The response half of T1 at the message level, both values of `complete`.** **C**. -/
theorem receivePolicy_rshape_run_c {ob c : Bool} {H : List Byte} {sk : Bool} {P : List Byte}
    (h : ReceiveReply.RShape ob H sk P)
    (Y Z : List Byte) (hY : Y.length ≤ replyBudget H ob) (hfit : c = true → replyMissing H ob ≤ (Y ++ Z).length)
    (i : Nat) (hi : i < Y.length) :
    ReceiveComplete.Strong (ReceiveSpec.message ob c (8 :: 2 :: (P ++ (Y ++ Z)))) (2 + P.length + i) (i + 1 = Y.length) :=
  ReceiveComplete.rshape_run_c h Y Z hY hfit i hi

/-- **The request half of T1 at the message level, both values of `complete`.** **C**. -/
theorem receivePolicy_qshape_run_c {H : List Byte} {bs : Bool} {P : List Byte} (h : ReceiveRequestScan.QShape H bs P)
    (ob c : Bool) (Y Z : List Byte)
    (hY : Y.length ≤ max 1 (fieldMissing H)) (hfit : c = true → fieldMissing H ≤ (Y ++ Z).length)
    (i : Nat) (hi : i < Y.length) :
    ReceiveRequestScan.PubAt (ReceiveSpec.message ob c (8 :: 1 :: (P ++ (Y ++ Z)))) (2 + P.length + i) :=
  ReceiveComplete.qshape_run_c h ob c Y Z hY hfit i hi

/-- **The frame reference read byte by byte** is the recursive one, for every byte string. **C**. -/
theorem receivePolicy_classifyFrames_stream (ob : Bool) (bytes : List Byte) :
    ReceiveSpec.classifyFrames ob bytes = ReceiveStream.Stream.classes ob bytes :=
  ReceiveStream.Stream.classifyFrames_stream ob bytes

/-- **The whole-stream reference read byte by byte** (head, then frames). **C**. -/
theorem receivePolicy_classify_stream (ob : Bool) (stream : List Byte) :
    ReceiveSpec.classify ob stream = ReceiveStream.classifyStream ob stream :=
  ReceiveStream.classify_stream ob stream

/-- **A message's classes depend only on the bytes before** (with `complete = false`). **C**. -/
theorem receivePolicy_message_prefix (ob : Bool) (A B : List Byte) :
    (ReceiveSpec.message ob false (A ++ B)).take A.length = ReceiveSpec.message ob false A :=
  ReceiveStream.message_prefix ob A B

/-- **The response half of T1 at the controller level.** **C**. -/
theorem receivePolicy_reply_run_safe {s : State} {P : List Byte} (hs : ReceiveReply.ReplyIn s P) (hk : s.skip = 0)
    (hu : s.upgraded = true)
    (h0 : (PublicReceive.get s.frame 0 == on) = false) (h2 : (PublicReceive.get s.frame 2 == on) = false)
    (h4 : (PublicReceive.get s.frame 4 == on) = true)
    (hr : (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0)
    (ho : (PublicReceive.get s.frame 7).toNat < 8) (Y : List Byte) (hY : Y.length ≤ budget s)
    (i : Nat) (hi : i < Y.length) :
    ReceiveReply.SafeAt (ReceiveSpec.message s.openBody false (8 :: 2 :: (P ++ Y))) (2 + P.length + i) :=
  ReceiveReply.reply_run_safe hs hk hu h0 h2 h4 hr ho Y hY i hi

/-- **The request half of T1 at the controller level.** **C**. -/
theorem receivePolicy_request_run_safe {s : State} {P : List Byte} (hs : ReceiveRequestScan.QIn s P) (hk : s.skip = 0)
    (hu : s.upgraded = true)
    (h0 : (PublicReceive.get s.frame 0 == on) = false) (h2 : (PublicReceive.get s.frame 2 == on) = false)
    (h4 : (PublicReceive.get s.frame 4 == on) = true)
    (hr : (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0)
    (ho : (PublicReceive.get s.frame 7).toNat < 8) (ob : Bool) (Y : List Byte) (hY : Y.length ≤ budget s)
    (i : Nat) (hi : i < Y.length) :
    ReceiveRequestScan.PubAt (ReceiveSpec.message ob false (8 :: 1 :: (P ++ Y))) (2 + P.length + i) :=
  ReceiveRequestScan.request_run_safe hs hk hu h0 h2 h4 hr ho ob Y hY i hi

/-- **A byte the frame parser rejects is refused by `frameByte`.** **C**. -/
theorem receivePolicy_frameByte_reject {s : State} {b : Byte} {S : TlsWebSocketFrame.State Byte}
    (hu : s.upgraded = true)
    (hf : s.frame = TlsWebSocketFrame.stateBytes S) (hS : Shaped S)
    (hv : (TlsWebSocketFrame.step fast capacity S b).state.valid = 0#8) : ∀ r, frameByte s b ≠ .ok r :=
  ReceiveFrame.frameByte_reject hu hf hS hv

/-- **Before the upgrade, every run stays inside the HTTP head.** **C**. -/
theorem receivePolicy_upgrade_run_safe (ob : Bool) {s : State} (hu : s.upgraded = false) (S : List Byte)
    (hS : ReceiveStream.Head.find 0 S = none) (ht : s.terminator = ReceiveHead.after 0 S) (Y Z : List Byte)
    (hY : Y.length ≤ budget s) (i : Nat) (hi : i < Y.length) :
    (ReceiveSpec.classify ob (S ++ (Y ++ Z)))[S.length + i]? = some .head :=
  ReceiveHead.upgrade_run_safe ob hu S hS ht Y Z hY i hi

/-- **Before the upgrade, `frameByte` counts CR LF CR LF as the reference does.** **C**. -/
theorem receivePolicy_frameByte_terminator {s s1 : State} {b : Byte} {ev : List Byte} (hu : s.upgraded = false)
    (h : frameByte s b = .ok (s1, ev)) :
    s1.terminator = ReceiveStream.Head.next s.terminator b ∧
      (s1.upgraded = true ↔ ReceiveStream.Head.next s.terminator b = 4) :=
  ReceiveHead.frameByte_terminator hu h

/-- **T1 from the first byte of a connection, about the loop the session runs** (PROOF_GAPS D1). From
the start states the session uses (`{ PublicReceive.start accept with lenient, openBody }`:
`Session/Pool.lean`, `Send.lean`, `Receive.lean`, `Ceremony.lean`), over every stream (the upgrade
response's head, then frames) cut into records in any way, with the engines as assumed (`Faithful`) and
any steps between records that keep the view and the upgrade parser's state (`KeepsHead`), every stream
position the loop has the engines reveal is allowed by `ReceiveSpec.classify` (head included), or is its
first `error`. **C-gen**. -/
theorem receivePolicy_t1_start (openBody : Bool) (accept : List Byte) (lenient : Bool) (records : List (List Byte))
    {β : Type} (O : Nat → List Byte → RecordLoop.Ops ReceiveLoop.RevealM β)
    (hO : ∀ base r, ReceiveLoop.Faithful r base (O base r))
    (g : Nat → State → Except String State) (hg : ∀ i, ReceiveStart.KeepsHead (g i)) :
    ∀ q ∈ (ReceiveLoop.sessionRun O g { PublicReceive.start accept with lenient := lenient, openBody } records).1,
      ReceiveSpec.allowedIn (ReceiveSpec.classify openBody records.flatten) q = true ∨
        ReceiveSpec.firstError (ReceiveSpec.classify openBody records.flatten) = some q :=
  ReceiveStart.t1_start openBody accept lenient records O hO g hg

/-- **T1 from the first byte, about the model loop** (`streamRun`), against `ReceiveSpec.classify`. **M**. -/
theorem receivePolicy_t1_start_model (openBody : Bool) (accept : List Byte) (lenient : Bool)
    (records : List (List Byte)) :
    ReceiveStart.T1Full openBody { PublicReceive.start accept with lenient := lenient, openBody } records :=
  ReceiveStart.t1_start_model openBody accept lenient records

/-- **The head's bytes leave the frame parser at its start state** (D1, lemma (i)): before the upgrade,
`frameByte` changes only `upgraded` and `terminator` of the view, the event is neither data nor a
message's end, and the upgrade parser stays not completed unless the byte completed it. **C**. -/
theorem receivePolicy_frameByte_head {ob : Bool} {s s1 : State} {b : Byte} {ev : List Byte} {k : Nat}
    (hs : ReceiveStart.HeadSim ob s k) (h : frameByte s b = .ok (s1, ev)) :
    ReceiveSimByte.view s1 = { ReceiveSimByte.view s with upgraded := s1.upgraded, terminator := s1.terminator } ∧
      s1.terminator = ReceiveStream.Head.next k b ∧ (s1.upgraded = true ↔ ReceiveStream.Head.next k b = 4) ∧
      PublicReceive.get ev 1 = 0 ∧ PublicReceive.get ev 5 = 0 ∧
      (s1.upgraded = false → 7 ≤ s1.upgrade.length ∧ PublicReceive.get s1.upgrade 6 ≠ on) :=
  ReceiveStart.frameByte_head hs h

/-- **`payloadByte` on a byte that is neither data nor a message's end keeps the view and the upgrade
parser's state** (D1, lemma (ii)). **C**. -/
theorem receivePolicy_payloadByte_head {s s' : State} {y : Byte} {first : Bool} {flags : List Byte} {c : Bool}
    (h : payloadByte s y false false first flags = .ok (s', c)) :
    ReceiveSimByte.view s' = ReceiveSimByte.view s ∧ s'.upgrade = s.upgrade :=
  ReceiveStart.payloadByte_head h

/-- **Every byte accepted before the upgrade keeps the head relation; the byte that completes
CR LF CR LF gives the frame relation at the reference's initial state.** **C**. -/
theorem receivePolicy_headStep {ob : Bool} {s s' : State} {b : Byte} {c : Bool} {k : Nat}
    (hs : ReceiveStart.HeadSim ob s k) (h : step s b = .ok (s', c)) :
    (ReceiveStream.Head.next k b = 4 → ∀ n, ReceiveSim.Sim ob s' ReceiveStream.Stream.init n) ∧
      (ReceiveStream.Head.next k b ≠ 4 → ReceiveStart.HeadSim ob s' (ReceiveStream.Head.next k b)) :=
  ReceiveStart.headStep hs h

/-- **The session's step after a record keeps the view and the upgrade parser's state.** **C**. -/
theorem receivePolicy_keepsHead_afterRecord (masks : List (List Byte)) :
    ReceiveStart.KeepsHead (fun s => (replies s masks).map (fun p => { p.1 with requests := [] })) :=
  ReceiveStart.keepsHead_afterRecord masks

end T1All

/-- **Fail closed: a too-long varint after a key is refused** (`scan`'s loop, at the varint's 10th
byte: `malformed`). **C**. SECURITY_MAP C.4. -/
theorem receivePolicy_scanBody_tooLong {bytes rest : List PublicReceive.Byte} {tag : PublicReceive.Byte} {b : Bool}
    {x : Option (PublicReceive.Need × PublicReceive.Fields)}
    {f : PublicReceive.Fields} {pos : Nat} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a ∨ tag = 0x20)
    (h : bytes.drop pos = tag :: rest) (hl : PublicReceive.varintTooLong bytes (pos + 1) = true) :
    ReceiveProofs.scanBody bytes b ⟨x, f, pos⟩ = .done ⟨some (.malformed, f), f, pos⟩ :=
  ReceiveProofs.scanBody_tooLong ht h hl

/-- **Fail closed: a too-long wrapper length is refused** (`scan` of a server request). **C**.
SECURITY_MAP C.4. -/
theorem receivePolicy_scan_wrapper_tooLong (bytes : List PublicReceive.Byte) (b : Bool)
    (hk : (bytes.take 2 == [8, 1] && PublicReceive.get bytes 2 == 0x12) = true)
    (h : PublicReceive.varintTooLong bytes 3 = true) : (PublicReceive.scan bytes b).1 = .malformed :=
  ReceiveProofs.scan_wrapper_tooLong bytes b hk h

/-- **Fail closed: a too-long varint after a key is refused** (`replyScan`'s loop, at the varint's
10th byte). **C**. SECURITY_MAP C.4. -/
theorem receivePolicy_replyScanBody_tooLong {bytes rest : List PublicReceive.Byte} {tag : PublicReceive.Byte}
    {x : Option (PublicReceive.Need × PublicReceive.ReplyFields)}
    {f : PublicReceive.ReplyFields} {pos : Nat} {b i : Bool}
    (ht : tag = 0x08 ∨ tag = 0x10 ∨ tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22)
    (h : bytes.drop pos = tag :: rest) (hl : PublicReceive.varintTooLong bytes (pos + 1) = true) :
    ReceiveProofs.replyScanBody bytes b i ⟨x, f, pos⟩ = .done ⟨some (.malformed, f), f, pos⟩ :=
  ReceiveProofs.replyScanBody_tooLong ht h hl

/-- **Fail closed: a too-long wrapper length is refused** (`replyScan` of a response). **C**.
SECURITY_MAP C.4. -/
theorem receivePolicy_replyScan_wrapper_tooLong (bytes : List PublicReceive.Byte) (b i : Bool)
    (hk : (bytes.take 2 == [8, 2] && PublicReceive.get bytes 2 == 0x1a) = true)
    (h : PublicReceive.varintTooLong bytes 3 = true) : (PublicReceive.replyScan bytes b i).1 = .malformed :=
  ReceiveProofs.replyScan_wrapper_tooLong bytes b i hk h

/-! ## 5. State and ordering (SECURITY_MAP C.4, C.5)

What is stored, when state advances, and that sequence numbers are not reused. The send-side
ordering (ORD-1: store acknowledged before send; ORD-2) and T11 are in 5b; the stock (T14) and
the connection rotation (T15) in 5c; the database nonce rule (T10) is NOT proved (section 8). -/

/-! ### 5b. Ordering: ORD-1, ORD-2, T11 (proof track P4; `TlsMpc/Node/Session/*Proofs.lean`)

The session functions on these paths are defined once, monad-generically (`Session/Store.lean`,
`Send.lean`, `Serve.lean`); the deployed function IS the definition at `SessionM` and the deployed
operations record (`abbrev f := fG realOps`: `storeSoft = storeSoftG storeReal`, `Send.deliverJob =
Send.deliverJobG Send.deliverReal`, …). The theorems are about those definitions run in the model
monad `Events.Model` at every environment (`storeModel E`, `sendModel E`), and for the loops in the
guarded model at every operations record whose other operations keep the property, with the
operations that matter (`sendSoft`, `sendMessage`, the refreshes, `commitScratch`) the definitions'
own instances. What carries a theorem to a real run (`Session/Events.lean`, header): the real
operations do what their events name; no code but the deployed records hands a message request to
the worker or commits a scratch (`scripts/lint_node.py`, `ordering-sites`); the free theorem of the
generic definition (A8). **C-gen**. PROOF_GAPS.md C3. -/

section Ordering
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session
open TlsMpc.Node.Session.Events

/-- **ORD-1, `sendSoft` (the recovery path).** With the database nodes, every run keeps
`SendsAgreed`: the request it hands to the worker comes after the contact's message was sealed, its
advanced state sealed for storage, acknowledged by this party's nodes and reported acknowledged by the
other party, with no seal of the contact in between. **C-gen**. -/
theorem ord1_sendSoft_agreed (E : SendEnv) (send : Nat × Bytes) (id : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAgreed w.log) :
    Model.wp (Send.sendSoftG (sendModel E) send id) (fun _ _ w' => SendsAgreed w'.log) c st w :=
  Events.sendSoft_agreed E send id c st w hdb hw

/-- **ORD-1, `sendMessage` (the path without recovery):** every request after its own seal, storage
seal and this party's nodes' acknowledgement. **C-gen**. -/
theorem ord1_sendMessage_acked (E : SendEnv) (send : Nat × Bytes) (id : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAcked w.log) :
    Model.wp (Send.sendMessageG (sendModel E) send id) (fun _ _ w' => SendsAcked w'.log) c st w :=
  Events.sendMessage_acked E send id c st w hdb hw

/-- **ORD-1 over every run of `deliverJob`, its refreshes included** (the recovery path; `deliver`
and every job of `serve`). **C-gen**. -/
theorem ord1_deliverJob_sendsAgreed (E : SendEnv) (rest : Send.DeliverOps (Guarded SendsAgreed))
    (R : Send.RefreshOps (Guarded SendsAgreed))
    (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAgreed w.log) :
    SendsAgreed ((Send.deliverJobG (deliverSends E rest R) inputs recipients notifyId journal first).1 c st w).2.2.log :=
  Events.deliverJob_sendsAgreed' E rest R inputs recipients notifyId journal first c st w hdb hw

/-- **ORD-1 over every run of `loop`** (the path without recovery), its refresh-and-resend
included. **C-gen**. -/
theorem ord1_loop_sendsAcked (E : SendEnv) (rest : Send.LoopOps (Guarded SendsAcked)) (R : Send.RefreshOps (Guarded SendsAcked))
    (known : List (Nat × Secret Bytes × Nat)) (recipients : List Nat) (fuel : Nat) (s : PublicReceive.State)
    (inputs : List (Nat × Bytes)) (completed : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAcked w.log) :
    SendsAcked ((Send.loopG (loopSends E rest R) known recipients fuel s inputs completed).1 c st w).2.2.log :=
  Events.loop_sendsAcked E rest R known recipients fuel s inputs completed c st w hdb hw

/-- **ORD-1 over every run of `serve`** (each job through `deliverJob`). **C-gen**. -/
theorem ord1_serve_sendsAgreed (E : SendEnv) (rest : Serve.ServeOps (Guarded SendsAgreed))
    (D : Send.DeliverOps (Guarded SendsAgreed))
    (R : Send.RefreshOps (Guarded SendsAgreed)) (directory : String) (accept : Bytes) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAgreed w.log) :
    SendsAgreed ((Serve.serveG (serveSends E rest D R) directory accept).1 c st w).2.2.log :=
  Events.serve_sendsAgreed E rest D R directory accept c st w hdb hw

/-- **ORD-2 (`commitScratch`).** With the database nodes, every run keeps `CommitsAgreed`: a
refresh's scratch is committed only after it was sealed for storage, this party's nodes acknowledged
that write and the other party reported its nodes' acknowledgement right after. **C-gen**. -/
theorem ord2_commitScratch_agreed (E : StoreEnv) (contact : Nat) (kinds : List Nat) (c : Context) (st : State)
    (w : World) (hdb : c.dbClient.isSome) (hw : CommitsAgreed w.log) :
    Model.wp (commitScratchG (storeModel E) contact kinds) (fun _ _ w' => CommitsAgreed w'.log) c st w :=
  Events.commitScratch_agreed E contact kinds c st w hdb hw

/-- **ORD-2, the outcome:** `true` exactly after the commit, `false` after the drop. **C-gen**. -/
theorem ord2_commitScratch_outcome (E : StoreEnv) (contact : Nat) (kinds : List Nat) (c : Context) (st : State)
    (w : World) (hdb : c.dbClient.isSome) :
    Model.wp (commitScratchG (storeModel E) contact kinds) (fun r _ w' =>
      (r = .ok true → w'.log.head? = some (.scratchCommit contact)) ∧
      (r = .ok false → w'.log.head? = some .scratchDrop)) c st w :=
  Events.commitScratch_outcome E contact kinds c st w hdb

/-- **ORD-2 over every run of `deliverJob`.** **C-gen**. -/
theorem ord2_deliverJob_commitsAgreed (E : SendEnv) (rest : Send.DeliverOps (Guarded CommitsAgreed))
    (R : Send.RefreshOps (Guarded CommitsAgreed))
    (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : CommitsAgreed w.log) :
    CommitsAgreed ((Send.deliverJobG (deliverCommits E rest R) inputs recipients notifyId journal first).1 c st w).2.2.log :=
  Events.deliverJob_commitsAgreed E rest R inputs recipients notifyId journal first c st w hdb hw

/-- **ORD-2 over every run of `loop`.** **C-gen**. -/
theorem ord2_loop_commitsAgreed (E : SendEnv) (rest : Send.LoopOps (Guarded CommitsAgreed))
    (R : Send.RefreshOps (Guarded CommitsAgreed))
    (known : List (Nat × Secret Bytes × Nat)) (recipients : List Nat) (fuel : Nat) (s : PublicReceive.State)
    (inputs : List (Nat × Bytes)) (completed : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : CommitsAgreed w.log) :
    CommitsAgreed ((Send.loopG (loopCommits E rest R) known recipients fuel s inputs completed).1 c st w).2.2.log :=
  Events.loop_commitsAgreed E rest R known recipients fuel s inputs completed c st w hdb hw

/-- **ORD-2 over every run of `serve`.** **C-gen**. -/
theorem ord2_serve_commitsAgreed (E : SendEnv) (rest : Serve.ServeOps (Guarded CommitsAgreed))
    (D : Send.DeliverOps (Guarded CommitsAgreed))
    (R : Send.RefreshOps (Guarded CommitsAgreed)) (directory : String) (accept : Bytes) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : CommitsAgreed w.log) :
    CommitsAgreed ((Serve.serveG (serveCommits E rest D R) directory accept).1 c st w).2.2.log :=
  Events.serve_commitsAgreed E rest D R directory accept c st w hdb hw

/-- **T11 (`deliverJob`).** Whatever the delivery loops did and whatever every operation but the
peer exchange does: when `deliverJob` returns, the newest event is the results-digest exchange in
which the other party's digest is our own, the digest of the results the state reports. **C-gen**. -/
theorem t11_deliverJob_results (P : PeerMsg → Context → Nat → Except String PeerMsg) (o : Send.DeliverOps Model)
    (inputs : List (Nat × Bytes)) (recipients : List Nat) (notifyId journal : Option String)
    (first : PublicReceive.State) (c : Context) (st : State) (w : World) :
    Model.wp (Send.deliverJobG (deliverT11 P o) inputs recipients notifyId journal first)
      (fun r st' w' => ∀ n, r = .ok n → ResultsAgreed st' w') c st w :=
  Events.deliverJob_results P o inputs recipients notifyId journal first c st w

/-- **T11, the tail:** when it returns, `ResultsAgreed`; when it fails, the state (the reported
results included) is unchanged. **C-gen**. -/
theorem t11_resultsTail_spec (P : PeerMsg → Context → Nat → Except String PeerMsg) (o : Send.DeliverOps Model)
    (inputs : List (Nat × Bytes)) (messageOf contactOf : Nat → Nat)
    (outcomes : Array (Option (Recovery.Result × String))) (delivered : Nat) (c : Context) (st : State) (w : World) :
    Model.wp (Send.resultsTailG (deliverT11 P o) inputs messageOf contactOf outcomes delivered) (fun r st' w' =>
      (∀ n, r = .ok n → ResultsAgreed st' w') ∧ (∀ e, r = .error e → st' = st)) c st w :=
  Events.resultsTail_spec P o inputs messageOf contactOf outcomes delivered c st w

/-- **`storeSoft`'s versions:** the version list moves to the contact's next version exactly when
the store was taken. **C-gen**. -/
theorem versions_storeSoft (E : StoreEnv) (contact : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) :
    Model.wp (storeSoftG (storeModel E) contact) (fun r st' _ =>
      (r = .ok true → st'.contacts.versions =
        bumpIn st.contacts.versions contact (versionIn st.contacts.versions contact)) ∧
      (r ≠ .ok true → st'.contacts.versions = st.contacts.versions)) c st w :=
  Events.storeSoft_versions E contact c st w hdb

/-- **`storeAdvanced`'s versions.** **C-gen**. -/
theorem versions_storeAdvanced (E : StoreEnv) (contact : Nat) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) :
    Model.wp (storeAdvancedG (storeModel E) contact) (fun r st' _ =>
      (r = .ok () → st'.contacts.versions =
        bumpIn st.contacts.versions contact (versionIn st.contacts.versions contact)) ∧
      (r ≠ .ok () → st'.contacts.versions = st.contacts.versions)) c st w :=
  Events.storeAdvanced_versions E contact c st w hdb

/-- **A contact the version list holds gets the next version.** **C**. -/
theorem versions_versionIn_bumpIn (versions : List (Nat × Nat)) (contact : Nat) (h : contact ∈ versions.map (·.1)) :
    versionIn (bumpIn versions contact (versionIn versions contact)) contact = versionIn versions contact + 1 :=
  Events.versionIn_bumpIn versions contact h

end Ordering

/-! ### 5c. The stock (T14, proof track X1) and the connection rotation (T15, X2)

`TlsMpc/Node/Stock/Use.lean`: the journal and use model of the precomputed stock (**M**: the engine
instruction and the C ABI are specified, not built; PROOF_GAPS C5). `TlsMpc/Node/Policy/Rotation.lean`:
the rotation planner (**M** until the session uses it). -/

/-- **T14 (stock used once).** In production (journal and key chain), in every trace of the use
rule, with crashes at any step, restarts, reboots, lying or vanishing peers, and a rollback of
either the disk or the boot memory (not both), no item reaches the engine twice. **M**. -/
theorem stock_T14 (evs : List TlsMpc.Node.Stock.Ev)
    (h : (∀ i, TlsMpc.Node.Stock.Ev.restoreBoot i ∉ evs) ∨ (∀ i, TlsMpc.Node.Stock.Ev.restoreDisk i ∉ evs)) :
    (TlsMpc.Node.Stock.run TlsMpc.Node.Stock.production TlsMpc.Node.Stock.init evs).handed.Nodup :=
  TlsMpc.Node.Stock.T14 evs h

open TlsMpc.Node.Stock in
/-- **The boot id:** every item handed to the engine belongs to a stock made in the boot during which
it was handed, and a stock is made in exactly one boot. **M**. -/
theorem stock_T14_boot (cfg : Barriers) (evs : List Ev) :
    ∀ b s j, (b, s, j) ∈ (run cfg init evs).handed →
      (s, b) ∈ (run cfg init evs).stocks ∧ ∀ b', (s, b') ∈ (run cfg init evs).stocks → b' = b :=
  TlsMpc.Node.Stock.T14_boot cfg evs

open TlsMpc.Node.Stock in
/-- **Never back:** the agreed index is at or above this node's next index. **M**. -/
theorem stock_agreeIndex_never_back {mine j : Nat} {claim : Option Nat} (h : agreeIndex (some mine) claim = some j) :
    mine ≤ j :=
  TlsMpc.Node.Stock.agreeIndex_never_back h

open TlsMpc.Node.Stock in
/-- **Waste bound:** each node's next index exceeds the items it handed by at most the number of
interruptions. **M**. -/
theorem stock_waste_bound (rs : List (RoundEnd × RoundEnd)) :
    let p := pairRounds ⟨0, 0, 0, 0, 0⟩ rs
    p.nA ≤ p.uA + p.cuts ∧ p.nB ≤ p.uB + p.cuts :=
  TlsMpc.Node.Stock.waste_bound rs

open TlsMpc.Node.Stock TlsMpc.Node.Engine in
/-- **Within a session, no (shape, index) is used twice.** **M**. -/
theorem stock_stockUses_nodup (sigs : Bytes → Option Sig) :
    ∀ (us : List StockUse) (c : StockCtx), acceptsAll sigs c us →
      (us.map fun u => (u.shape.enc, u.index)).Nodup :=
  TlsMpc.Node.Stock.stockUses_nodup sigs

open Rotation in
/-- **T15 (the actions):** for two input lists of the same length, the composed sender performs
the same actions once the payloads are erased. **M**. -/
theorem rotation_t15_erase {β : Type} (H : Bytes → Bytes) (seed : Bytes) (cfg : Config) (base : Nat)
    (xs ys : List β) (dx dy : β) (h : xs.length = ys.length) :
    (compose H seed cfg base xs dx).map Action.erase = (compose H seed cfg base ys dy).map Action.erase :=
  Rotation.t15_erase H seed cfg base xs ys dx dy h

open Rotation in
/-- **Every position is sent exactly once.** **M**. -/
theorem rotation_plan_sends_perm (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat) :
    List.Perm (sendsOf (plan H seed n cfg base).actions) (List.range n) :=
  Rotation.plan_sends_perm H seed n cfg base

open Rotation in
/-- **At most `poolSize` connections are open at once.** **M**. -/
theorem rotation_plan_pool_bound (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat)
    (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) (j : Nat) :
    ∃ mj, Mon.run cfg.maxLen (Mon.init cfg.poolSize base) ((plan H seed n cfg base).actions.take j) = some mj ∧
      openCount mj.slots ≤ cfg.poolSize :=
  Rotation.plan_pool_bound H seed n cfg base hpool hmax j

open Rotation in
/-- **No generation is reused.** **M**. -/
theorem rotation_plan_generations (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat)
    (hpool : 0 < cfg.poolSize) (hmax : 0 < cfg.maxLen) :
    opensOf (plan H seed n cfg base).actions =
      List.range' base (opensOf (plan H seed n cfg base).actions).length ∧
    (opensOf (plan H seed n cfg base).actions).Nodup :=
  Rotation.plan_generations H seed n cfg base hpool hmax

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **A sealed contact state opens to itself:** if `contact-seal` produced the stored ciphertext
and check under the same key and version, `contact-open` accepts (255) and returns the original
state. **K**. Not listed in SECURITY_MAP C; found while building this file. -/
theorem contact_round_trip (size : Nat) (sealing opening : BVExpr.Assignment)
    (traffic : inputValue opening 0 60 = inputValue sealing 0 60)
    (version : inputValue opening 60 8 = inputValue sealing 60 8)
    (stored : (contactSeal size).outputs.map (fun field => field.value.map (BVExpr.eval sealing)) =
      [inputValue opening 68 size, inputValue opening (68 + size) 16]) :
    (contactOpen size).outputs.map (fun field => field.value.map (BVExpr.eval opening)) =
      [[255], inputValue sealing 68 size] :=
  TlsMpc.HybridKernel.contact_round_trip size sealing opening traffic version stored

open TlsMpc.Signal TlsMpc.Signal.ChainSend Std.Tactic.BVDecide in
/-- **On acceptance (255) the send kernel stores the advanced chain state.** **K-fn**: the same
`selectState` the seal kernel calls; never composed into a kernel-level statement (T7).
SECURITY_MAP C.5. -/
theorem chainSend_selectState_accept (next old : List (BitVec 8)) (hlength : next.length = old.length) :
    selectState ByteAuth.concrete 255 next old = next :=
  TlsMpc.Signal.ChainSend.selectState_accept next old hlength

open TlsMpc.Signal TlsMpc.Signal.ChainSend Std.Tactic.BVDecide in
/-- **On rejection (0) the send kernel keeps the old chain state.** **K-fn**. SECURITY_MAP C.5. -/
theorem chainSend_selectState_reject (next old : List (BitVec 8)) :
    selectState ByteAuth.concrete 0 next old = old :=
  TlsMpc.Signal.ChainSend.selectState_reject next old

open TlsMpc.Signal TlsMpc.Signal.ChainSend Std.Tactic.BVDecide in
/-- **The chain send's acceptance mask is 255 exactly when the counters and addresses are
acceptable.** **K-fn** (`signal-seal-official`). SECURITY_MAP C.3, C.5. -/
theorem chainSend_acceptedMask_value (shape : Serialization.Shape) (present : BitVec 8)
    (counter previous addresses : List (BitVec 8)) :
    acceptedMask Sha256.concrete ByteAuth.concrete shape present counter previous addresses =
      if accepted shape present counter previous addresses then 255 else 0 :=
  TlsMpc.Signal.ChainSend.acceptedMask_value shape present counter previous addresses

open TlsMpc.Signal TlsMpc.Signal.SpqrSend Std.Tactic.BVDecide in
/-- **The SPQR send's acceptance mask is 255 exactly when its input is acceptable.** **K-fn**.
SECURITY_MAP C.3, C.5. -/
theorem spqrSend_acceptedMask_value (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (i : Input (BitVec 8)) :
    acceptedMask Varint64.concrete Sha256.concrete ByteAuth.concrete shape pqShape i =
      if accepted shape pqShape i then 255 else 0 :=
  TlsMpc.Signal.SpqrSend.acceptedMask_value shape pqShape i

open TlsMpc.Signal TlsMpc.Signal.SpqrSend Std.Tactic.BVDecide in
/-- **The SPQR send preparation computes the canonical prepared input.** **K-fn**. SECURITY_MAP
C.5. -/
theorem spqrSend_prepare_concrete_correct (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (i : Input (BitVec 8)) :
    prepare Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete shape pqShape i =
      canonical shape pqShape i :=
  TlsMpc.Signal.SpqrSend.prepare_concrete_correct shape pqShape i

open TlsMpc.Signal TlsMpc.Signal.ChainSend Std.Tactic.BVDecide in
/-- **A rejected chain send outputs status 0 followed by the unchanged key and counter.** **M**:
about the sibling `sealCore` (SECURITY_MAP C.2). -/
theorem chainSend_reject_preserves_state (shape : Serialization.Shape) (version present : BitVec 8)
    (counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses : List (BitVec 8))
    (bad : ¬ accepted shape present counter previous addresses) :
    (sealCore Aes.concrete Sha256.concrete ByteAuth.concrete shape version present
      counter previous ratchet chainKey pqKey sender receiver plaintext pq addresses).take
        (1 + chainKey.length + counter.length) = 0 :: (chainKey ++ counter) :=
  TlsMpc.Signal.ChainSend.reject_preserves_state shape version present counter previous ratchet chainKey pqKey
    sender receiver plaintext pq addresses bad

open TlsMpc.TlsApplicationPolicy in
/-- **An application-record reservation uses the current epoch and next sequence number,
advances the counter by one, and stays below the record limit.** **C** (`TlsApplication`
calls the reservations). SECURITY_MAP C.4. -/
theorem tlsPolicy_application_reservation (s after : State) (ticket : Reservation)
    (h : reserveApplication s = some (ticket,after)) :
    ticket.epoch = s.sendEpoch ∧ ticket.sequence = s.sendNext ∧
    after.sendNext = s.sendNext+1 ∧ ticket.sequence < recordLimit-1 ∧
    after.sendEpoch = s.sendEpoch :=
  TlsMpc.TlsApplicationPolicy.application_reservation s after ticket h

open TlsMpc.TlsApplicationPolicy in
/-- **Two consecutive application records never share a sequence number** (no AES-GCM nonce
reuse within an epoch, as far as the policy goes). **C**. SECURITY_MAP C.4. -/
theorem tlsPolicy_consecutive_application_distinct (s mid after : State) (a b : Reservation)
    (ha : reserveApplication s = some (a,mid))
    (hb : reserveApplication mid = some (b,after)) : a.sequence ≠ b.sequence :=
  TlsMpc.TlsApplicationPolicy.consecutive_application_distinct s mid after a b ha hb

open TlsMpc.TlsApplicationPolicy in
/-- **A KeyUpdate is sent under the old epoch and leaves an update pending.** **C**.
SECURITY_MAP C.4. -/
theorem tlsPolicy_update_uses_old_epoch (s after : State) (ticket : Reservation) (request : Bool)
    (h : reserveUpdate s request = some (ticket,after)) :
    ticket.epoch = s.sendEpoch ∧ after.sendEpoch = s.sendEpoch ∧
    after.sendNext = s.sendNext+1 ∧ after.pendingUpdate = some request :=
  TlsMpc.TlsApplicationPolicy.update_uses_old_epoch s after ticket request h

open TlsMpc.TlsApplicationPolicy in
/-- **While an update is pending, no application record can be reserved.** **C**. SECURITY_MAP
C.4. -/
theorem tlsPolicy_pending_blocks_application (s : State) (request : Bool)
    (h : s.pendingUpdate = some request) : reserveApplication s = none :=
  TlsMpc.TlsApplicationPolicy.pending_blocks_application s request h

open TlsMpc.TlsApplicationPolicy in
/-- **After an abort, nothing can be reserved** (no send, update, receive or close). **C**.
SECURITY_MAP C.4. -/
theorem tlsPolicy_aborted_blocks (s : State) : reserveApplication (abort s) = none ∧
    reserveUpdate (abort s) false = none ∧ reserveUpdate (abort s) true = none ∧
    reserveReceive (abort s) = none ∧ reserveClose (abort s) = none :=
  TlsMpc.TlsApplicationPolicy.aborted_blocks s

open TlsMpc.TlsApplicationPolicy in
/-- **A receive reservation uses the next receive sequence number and advances it by one.**
**C**. SECURITY_MAP C.4. -/
theorem tlsPolicy_receive_reservation (s after : State) (ticket : Reservation)
    (h : reserveReceive s = some (ticket,after)) :
    ticket.sequence = s.receiveNext ∧ after.receiveNext = s.receiveNext+1 ∧ ticket.sequence < 2^64 :=
  TlsMpc.TlsApplicationPolicy.receive_reservation s after ticket h

/-! ## 6. Conversions and helper protocols

Today these protocols are C++ (`dyn_word_mask.h`, `tls_kernels.h`, `x25519_fast.h`,
`split_ecdh.h`, `edwards_points.h`, `gcm_shares.h`; SECURITY_MAP D.5). What exists in Lean is
(a) the circuits and field programs they call (**K**) and (b) arithmetic models of the protocols
(**M**). The protocol properties themselves (P-RAND … P-HINT) are section 8. -/

/-! ### 6a. Word masks and Boolean/field conversion circuits -/

open TlsMpc.WordMask TlsMpc.BoolDag in
/-- **The `modadd` circuit adds two words mod p = 2²⁵⁵ − 19.** Hypotheses: both inputs below
p. **K** (`dyn_word_mask.h`). SECURITY_MAP C.2. -/
theorem wordMask_modAddCircuit_val (env : Nat → Bool) (vx : val env X < P) (vy : val env Y < P) :
    val env modAddCircuit = (val env X + val env Y) % P :=
  TlsMpc.WordMask.modAddCircuit_val env vx vy

open TlsMpc.WordMask TlsMpc.BoolDag in
/-- **The `into-field` circuit outputs (x mod p + y) mod p.** Hypothesis: the mask y is below p.
**K** (`tls_kernels.h` word-to-field). SECURITY_MAP C.2. -/
theorem wordMask_intoField_val (env : Nat → Bool) (vy : val env Y < P) :
    val env intoFieldCircuit = (val env X % P + val env Y) % P :=
  TlsMpc.WordMask.intoField_val env vy

open TlsMpc.WordMask TlsMpc.BoolDag in
/-- **`modAdd` on any two 255-bit words below p adds them mod p.** **K-fn**. -/
theorem wordMask_modAdd_val (env : Nat → Bool) (x y : List Expr) (hx : x.length = 255) (hy : y.length = 255)
    (vx : val env x < P) (vy : val env y < P) :
    val env (modAdd x y) = (val env x + val env y) % P :=
  TlsMpc.WordMask.modAdd_val env x y hx hy vx vy

open TlsMpc.WordMask TlsMpc.BoolDag in
/-- **The `belowP` flag is exactly "value < p".** **K-fn** (the cut-and-choose flags). -/
theorem wordMask_belowP_eval (env : Nat → Bool) (x : List Expr) (hx : x.length = 255) :
    (belowP x).eval env = decide (val env x < P) :=
  TlsMpc.WordMask.belowP_eval env x hx

open TlsMpc.WordMask TlsMpc.BoolDag in
/-- **The `atLeast32` flag is exactly "value ≥ 32".** **K-fn** (bit blocks). -/
theorem wordMask_atLeast32_eval (env : Nat → Bool) (x : List Expr) (hx : x.length = 255) :
    (atLeast32 x).eval env = decide (32 ≤ val env x) :=
  TlsMpc.WordMask.atLeast32_eval env x hx

open TlsMpc.WordMask in
/-- **Word-to-field round trip (arithmetic):** masking u by r and unmasking gives u mod p.
Hypothesis: r < p. **M** (the arithmetic of the C++ protocol, not the protocol). -/
theorem wordMask_into_field_roundtrip (u r : Nat) (hr : r < P) : ((u % P + r) % P + (P - r)) % P = u % P :=
  TlsMpc.WordMask.into_field_roundtrip u r hr

open TlsMpc.WordMask in
/-- **Field-to-word round trip (arithmetic).** Hypotheses: x, r < p. **M**. -/
theorem wordMask_from_field_roundtrip (x r : Nat) (hx : x < P) (hr : r < P) :
    (r + (x + (P - r)) % P) % P = x :=
  TlsMpc.WordMask.from_field_roundtrip x r hx hr

open TlsMpc.X25519SwapBits TlsMpc.BoolDag in
/-- **The `swap-bits` circuit computes the X25519 ladder swap bit t** (2 ≤ t ≤ 253). **K**
(loaded by `x25519_fast.h`). -/
theorem swapBits_eval (env : Nat → Bool) (t : Nat) (h2 : 2 ≤ t) (h : t ≤ 253) :
    (swapBit t).eval env = X25519Fast.swapBitSpec env t :=
  TlsMpc.X25519SwapBits.swapBit_eval env t h2 h

open TlsMpc.X25519SwapBits in
/-- **Swap bits of an XOR-shared scalar are the XOR of locally computed swap bits** (3 ≤ t ≤ 252),
so each party can compute its share locally. **M** (the arithmetic behind C++ `shared_scalar`). -/
theorem swapBits_shares (a b : Nat → Bool) (t : Nat) (h3 : 3 ≤ t) (h : t ≤ 252) :
    X25519Fast.swapBitSpec (fun i => a i ^^ b i) t =
      ((a (t + 1) ^^ a t) ^^ (b (t + 1) ^^ b t)) :=
  TlsMpc.X25519SwapBits.swapBit_shares a b t h3 h

open TlsMpc.FieldBits TlsMpc.FieldDag in
/-- **The `field-bit-check` program is 0 on a bit** (soundness direction only; the converse —
0 implies a bit — is not proved, P-BITS(a)). **K**. -/
theorem fieldBits_bitCheck_bit (input : Nat → F) (b : Bool) (h : input 0 = X25519.bitValue b) :
    bitCheck.eval input = 0 :=
  TlsMpc.FieldBits.bitCheck_bit input b h

open TlsMpc.FieldBits TlsMpc.FieldDag in
/-- **The `field-bit-xor` program XORs two field bits.** **K**. -/
theorem fieldBits_bitXor_bits (input : Nat → F) (a b : Bool)
    (ha : input 0 = X25519.bitValue a) (hb : input 1 = X25519.bitValue b) :
    bitXor.eval input = X25519.bitValue (a ^^ b) :=
  TlsMpc.FieldBits.bitXor_bits input a b ha hb

open TlsMpc.FieldBits TlsMpc.FieldDag in
/-- **The `field-recompose` program is Σ bitᵢ·2ⁱ − value** (zero iff the bits recompose the
value, mod p). **K**. -/
theorem fieldBits_recompose_eval (input : Nat → F) :
    recompose.eval input = hornerValue ((List.range 255).map input) - input 255 :=
  TlsMpc.FieldBits.recompose_eval input

open TlsMpc.FieldBits TlsMpc.FieldDag in
/-- **The `field-mask-pair` program multiplies both inputs by the mask.** **K**. -/
theorem fieldBits_maskPair_eval (input : Nat → F) :
    maskPair.map (Expr.eval input) = [input 0 * input 2, input 1 * input 2] :=
  TlsMpc.FieldBits.maskPair_eval input

/-! ### 6b. Curve helper programs -/

open TlsMpc.EdwardsShare TlsMpc.FieldDag in
/-- **The `edwards-on-curve` program is the Edwards curve equation's residual.** **K**
(`split_ecdh.h`). That it opens to 0 only on curve points needs the converse (P-SPLIT(b)).
Formulas only (H-GROUP: the group law is proved in `proofs/`, `SecurityMathlib.lean` section 7). -/
theorem edwards_onCurve_eval (input : Nat → F) :
    onCurve.eval input =
      ofNat 121666 * (input 1 * input 1 - input 0 * input 0 - ofNat 1) +
        ofNat 121665 * (input 0 * input 0 * (input 1 * input 1)) :=
  TlsMpc.EdwardsShare.onCurve_eval input

open TlsMpc.EdwardsShare TlsMpc.FieldDag in
/-- **The `edwards-add-u` program computes the numerator and denominator of the Montgomery u of
a sum.** **K** (`split_ecdh.h`). Formulas only (H-GROUP: the group law is proved in `proofs/`, `SecurityMathlib.lean` section 7). -/
theorem edwards_addU_eval (input : Nat → F) :
    addU.map (Expr.eval input) =
      [ofNat 121666 + ofNat 121665 * (input 0 * input 2 * (input 1 * input 3)) +
          ofNat 121666 * (input 0 * input 2 + input 1 * input 3),
        ofNat 121666 + ofNat 121665 * (input 0 * input 2 * (input 1 * input 3)) -
          ofNat 121666 * (input 0 * input 2 + input 1 * input 3)] :=
  TlsMpc.EdwardsShare.addU_eval input

open TlsMpc.FieldDag in
/-- **X25519 is the quotient x₂·z₂⁻¹ of the fast ladder** when the swap-bit inputs are right.
**K-fn** (the C++ masked inversion supplies the quotient; not modelled). -/
theorem x25519Fast_spec_eq_quotient (bits : Nat → Bool) (u : F) (input : Nat → F)
    (hin : ∀ t, 2 ≤ t → t ≤ 253 → input t = X25519.bitValue (X25519Fast.swapBitSpec bits t)) :
    X25519.spec bits u = (X25519Fast.compute X25519.concrete input u).x2 *
      X25519.inverse X25519.concrete (X25519Fast.compute X25519.concrete input u).z2 :=
  TlsMpc.X25519Fast.spec_eq_quotient bits u input hin

open TlsMpc.FieldDag TlsMpc.EdwardsAffine TlsMpc.EdwardsHinted in
/-- **The hinted prepare table is the honest window chain whenever the link checks pass**,
whatever hints were supplied. **switch**. -/
theorem edwardsHinted_prepareTable_sound (input : Nat → F)
    (h : LinkedFrom (evalPoint input) window (inputPoint 0) ((List.range (windows - 1)).map (fun i => hinted (prepareHints + 4 * i)))) :
    (entries window (prepareBases ())).map (evalPoint input) = chain windowValue (input 0, input 1) windows :=
  TlsMpc.EdwardsHinted.prepareTable_sound input h

/-! ### 6c. GHASH from key-power shares (`gcm_shares.h`) -/

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`gcm-key-share` is a resharing of H:** A's input mask and the opened (masked) output form
an XOR sharing of the GHASH key of the traffic secret. **K**. -/
theorem gcmKeyShare_reshare (assign : BVExpr.Assignment) (masked : List (BitVec 8))
    (out : gcmKeyShare.outputs.map (fun field => field.value.map (BVExpr.eval assign)) = [masked]) :
    (Gcm.concrete.pack (inputValue assign 60 16), Gcm.concrete.pack masked) =
      Schedule.reshare (Gcm.concrete.pack (inputValue assign 60 16)) (hashKeyOf (inputValue assign 0 60)) :=
  TlsMpc.HybridKernel.gcmKeyShare_reshare assign masked out

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`gcm-multiply` is a resharing of the product of two shared values.** **K**. -/
theorem gcmMultiply_reshare (assign : BVExpr.Assignment) (masked : List (BitVec 8))
    (out : gcmMultiply.outputs.map (fun field => field.value.map (BVExpr.eval assign)) = [masked]) :
    (Gcm.concrete.pack (inputValue assign 64 16), Gcm.concrete.pack masked) =
      Schedule.reshare (Gcm.concrete.pack (inputValue assign 64 16))
        (Schedule.product (Ghash.multiply Ghash.concrete)
          (Gcm.concrete.pack (inputValue assign 0 16), Gcm.concrete.pack (inputValue assign 16 16))
          (Gcm.concrete.pack (inputValue assign 32 16), Gcm.concrete.pack (inputValue assign 48 16))) :=
  TlsMpc.HybridKernel.gcmMultiply_reshare assign masked out

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **`tls-seal-ctr` + `gcm-tag` produce the AES-GCM TLS record** — header ‖ ciphertext ‖ tag
equals `TlsRecord.sealCore` — **provided the two GHASH halves XOR to GHASH** of the header and
ciphertext (hypothesis `halves`). **K**; `halves` is discharged for a modelled schedule
(`gcm_scheduled_halves_are_ghash`) and, since S12, for the Lean code that replaces `gcm_shares.h`
(`s12_tls_seal_is_record`, section 7d: P-GHASH (c)); the C++ `gcm_shares.h` itself stays outside
until the controller switches to the script backend. SECURITY_MAP C.3. -/
theorem sealCtr_with_tag_is_seal (kind size padding : Nat) (sealing tagging : BVExpr.Assignment)
    (header ciphertext pad tag : List (BitVec 8))
    (sealed : (tlsSealCtr kind size padding).outputs.map (fun field => field.value.map (BVExpr.eval sealing)) =
      [header, ciphertext, pad])
    (padInput : inputValue tagging 0 16 = pad)
    (tagged : gcmTag.outputs.map (fun field => field.value.map (BVExpr.eval tagging)) = [tag])
    (halves : Aes.addRoundKey Gcm.concrete.aes (inputValue tagging 16 16) (inputValue tagging 32 16) =
      ghashOf (inputValue sealing 0 60) header ciphertext) :
    header ++ ciphertext ++ tag =
      TlsRecord.sealCore Gcm.concrete (((inputValue sealing 0 60).drop 32).take 16)
        (((inputValue sealing 0 60).drop 48).take 12) (inputValue sealing 60 8) (inputValue sealing 68 size)
        kind padding :=
  TlsMpc.HybridKernel.sealCtr_with_tag_is_seal kind size padding sealing tagging header ciphertext pad tag
    sealed padInput tagged halves

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **If the two parties' key-power shares XOR to the descending powers of H, their local halves
XOR to GHASH.** **M** (models `gcm_shares.h`). SECURITY_MAP C.3. -/
theorem gcm_shared_halves_are_ghash
    (traffic aad ciphertext : List (BitVec 8)) (first second : List (BitVec 128))
    (same : first.length = second.length)
    (shares : List.zipWith (· ^^^ ·) first second =
      GhashShares.descending (Ghash.multiply Ghash.concrete) (hashKeyOf traffic)
        (Gcm.authInput Gcm.concrete aad ciphertext).length) :
    Aes.addRoundKey Gcm.concrete.aes
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext) first))
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext) second)) =
      ghashOf traffic aad ciphertext :=
  TlsMpc.HybridKernel.shared_halves_are_ghash_proved traffic aad ciphertext first second same shares

open TlsMpc.HybridKernel Std.Tactic.BVDecide TlsMpc.Signal in
/-- **The modelled share schedule (`Schedule.ensure`, any masks) yields halves that XOR to
GHASH**, given enough powers. **M** (a Lean model of the schedule, not the C++). SECURITY_MAP
C.3. -/
theorem gcm_scheduled_halves_are_ghash (traffic aad ciphertext : List (BitVec 8)) (mask : Nat → BitVec 128)
    (available : Nat) (enough : (Gcm.authInput Gcm.concrete aad ciphertext).length ≤ available) :
    Aes.addRoundKey Gcm.concrete.aes
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext)
          (((Schedule.ensure (Ghash.multiply Ghash.concrete) (hashKeyOf traffic) mask available).take
            (Gcm.authInput Gcm.concrete aad ciphertext).length).reverse.map Prod.fst)))
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext)
          (((Schedule.ensure (Ghash.multiply Ghash.concrete) (hashKeyOf traffic) mask available).take
            (Gcm.authInput Gcm.concrete aad ciphertext).length).reverse.map Prod.snd))) =
      ghashOf traffic aad ciphertext :=
  TlsMpc.HybridKernel.scheduled_halves_are_ghash traffic aad ciphertext mask available enough

open TlsMpc.GhashShares in
/-- **A key-power share hides the power:** whatever masked value B sees, every candidate value
is consistent with exactly one mask. **M** (models `gcm_shares.h`). SECURITY_MAP C.3. -/
theorem ghash_share_hides (key seen : W) : ∃ mask : W, key ^^^ mask = seen ∧ ∀ other, key ^^^ other = seen → other = mask :=
  TlsMpc.GhashShares.share_hides key seen

open TlsMpc.GhashShares in
/-- **The two local halves XOR to the polynomial at the XOR of the shares**, for any
multiplication additive in the key. **M**. -/
theorem ghash_localTag_shares (mul : W → W → W) (additive : KeyAdditive mul)
    (blocks first second : List W) (same : first.length = second.length) :
    localTag mul blocks first ^^^ localTag mul blocks second =
      localTag mul blocks (List.zipWith (· ^^^ ·) first second) :=
  TlsMpc.GhashShares.localTag_shares mul additive blocks first second same

open TlsMpc.GhashShares in
/-- **For any halves and any received tag, exactly one pad makes the check accept** (with a
pseudorandom pad, a forgery succeeds with probability 2⁻¹²⁸ — that step is outside Lean). **M**.
SECURITY_MAP C.3. -/
theorem ghash_accept_unique_pad (first second received : W) :
    ∃ pad : W, accepts pad first second received = true ∧
      ∀ other, accepts other first second received = true → other = pad :=
  TlsMpc.GhashShares.accept_unique_pad first second received

open TlsMpc.GhashShares in
/-- **A genuine tag is rejected when one half deviates by any nonzero amount.** **M**.
SECURITY_MAP C.3. -/
theorem ghash_genuine_rejected (pad first second deviation : W) (nonzero : deviation ≠ 0) :
    accepts pad (first ^^^ deviation) second (openedTag pad first second) = false :=
  TlsMpc.GhashShares.genuine_rejected pad first second deviation nonzero

open TlsMpc.GhashShares in
/-- **With honest halves the check is the comparison with the true tag.** **M**. SECURITY_MAP
C.3. -/
theorem ghash_honest_accepts (mul : W → W → W) (additive : KeyAdditive mul) (pad received : W)
    (blocks first second : List W) (same : first.length = second.length) :
    accepts pad (localTag mul blocks first) (localTag mul blocks second) received =
      (pad ^^^ localTag mul blocks (List.zipWith (· ^^^ ·) first second) == received) :=
  TlsMpc.GhashShares.honest_accepts mul additive pad received blocks first second same

open TlsMpc.GhashShares in
/-- **Halves of shares of the descending powers XOR to GHASH in Horner form.** Hypotheses: the
multiplication's laws (commutative, associative) and key-additivity. **M**. SECURITY_MAP C.3. -/
theorem ghash_halves_are_ghash (mul : W → W → W) (laws : Laws mul) (additive : KeyAdditive mul) (h : W)
    (blocks first second : List W) (same : first.length = second.length)
    (shares : List.zipWith (· ^^^ ·) first second = descending mul h blocks.length) :
    localTag mul blocks first ^^^ localTag mul blocks second = horner mul h blocks 0 :=
  TlsMpc.GhashShares.halves_are_ghash mul laws additive h blocks first second same shares

open TlsMpc.GhashShares in
/-- **Powers of a shared key are the XOR of powers of the shares** (repository GHASH
multiplication). **M**. -/
theorem ghash_powers_additive (n : Nat) (h k : W) :
    Ghash.powers Ghash.concrete n (h ^^^ k) =
      List.zipWith (· ^^^ ·) (Ghash.powers Ghash.concrete n h) (Ghash.powers Ghash.concrete n k) :=
  TlsMpc.GhashShares.powers_additive n h k

open TlsMpc.GhashShares in
/-- **Squaring is additive** (so even powers can be squared locally). **M**. -/
theorem ghash_square_additive (mul : W → W → W) (laws : Laws mul) (additive : KeyAdditive mul) (a b : W) :
    mul (a ^^^ b) (a ^^^ b) = mul a a ^^^ mul b b :=
  TlsMpc.GhashShares.square_additive mul laws additive a b

/-! ### 6d. Masked and offset key agreement (arithmetic models over any ℤ-module) -/

open TlsMpc.MaskedAgreement in
/-- **The masked split agreement combines to (kA + kB)·R.** **M** (models the masked agreement;
the deployment uses the offset agreement). SECURITY_MAP C.3. -/
theorem maskedAgreement_correct {G : Type} [Lean.Grind.IntModule G] (B R : G) (kA kB mA mB : Int) :
    combine (kA • opened R (mA • B) (mB • B)) ((kA * mA) • B + mA • (kB • B))
        (kB • opened R (mA • B) (mB • B)) ((kB * mB) • B + mB • (kA • B)) =
      (kA + kB) • R :=
  TlsMpc.MaskedAgreement.agreement_correct B R kA kB mA mB

open TlsMpc.MaskedAgreement in
/-- **The opened masked point is the same for R and any other point, with a shifted mask.** **M**. -/
theorem maskedAgreement_mask_hides {G : Type} [Lean.Grind.IntModule G] (R other maskA maskB : G) :
    opened R maskA maskB = opened other maskA (maskB + R - other) :=
  TlsMpc.MaskedAgreement.mask_hides R other maskA maskB

open TlsMpc.MaskedAgreement in
/-- **The guess attack on the masked agreement** (why it was replaced): a party that chooses its
mask as a·B − R learns a·(kB·B) − c·(mB·B). **M** (a negative result). -/
theorem maskedAgreement_guess_attack {G : Type} [Lean.Grind.IntModule G] (B R : G) (a c kB mB : Int) :
    kB • opened R (a • B - R) (mB • B) - ((kB * mB) • B + mB • (c • B)) =
      a • (kB • B) - c • (mB • B) :=
  TlsMpc.MaskedAgreement.guess_attack B R a c kB mB

open TlsMpc.OffsetAgreement in
/-- **Offset public key: initial·B + offset·B = (initial + offset)·B.** **M** (arithmetic of
`edwards_points.h`; not yet about the running `step`, P-OFFSET(a)). -/
theorem offsetAgreement_public_key_correct {G : Type} [Lean.Grind.IntModule G] (B : G) (initial offset : Int) :
    initial • B + offset • B = (initial + offset) • B :=
  TlsMpc.OffsetAgreement.public_key_correct B initial offset

open TlsMpc.OffsetAgreement in
/-- **Offset agreement: initial·R + offset·R = (initial + offset)·R.** **M**. -/
theorem offsetAgreement_correct {G : Type} [Lean.Grind.IntModule G] (R : G) (initial offset : Int) :
    initial • R + offset • R = (initial + offset) • R :=
  TlsMpc.OffsetAgreement.agreement_correct R initial offset

open TlsMpc.OffsetAgreement in
/-- **The table sum over signed digits is (digit value)·R.** **M**. -/
theorem offsetAgreement_table_sum_correct {G : Type} [Lean.Grind.IntModule G] (R : G) (position : Nat)
    (digits : List Int) :
    tableSum R position digits = offsetValue position digits • R :=
  TlsMpc.OffsetAgreement.table_sum_correct R position digits

open TlsMpc.OffsetAgreement in
/-- **The published key is consistent with any other initial scalar** (the offset absorbs the
difference): it reveals nothing about `initial` beyond the key itself. **M**. SECURITY_MAP C.3. -/
theorem offsetAgreement_public_key_independent {G : Type} [Lean.Grind.IntModule G] (B : G)
    (initial other offset : Int) :
    initial • B + offset • B = other • B + (offset + initial - other) • B :=
  TlsMpc.OffsetAgreement.public_key_independent B initial other offset

open TlsMpc.OffsetAgreement in
/-- **Removing the public offset from a candidate agreement leaves initial·candidate** (a
candidate check needs the secret initial scalar). **M**. SECURITY_MAP C.3. -/
theorem offsetAgreement_candidate_needs_initial {G : Type} [Lean.Grind.IntModule G] (candidate : G)
    (initial offset : Int) :
    (initial + offset) • candidate - offset • candidate = initial • candidate :=
  TlsMpc.OffsetAgreement.candidate_needs_initial candidate initial offset

/-! ## 7. Flows and channels

The first flow theorems are in 7a (stage S9: T12, the open rule, P-RAND, T4-UPGRADE, about the
model) and the contact and account flows' T3/T4-CONTACT/T10 theorems (`Flows/Contacts*.lean`,
`Account.lean`, under `Contacts.Loaded`; restated in stage S6 from the S5 draft). The flow API and
the reveal list: 7-reveal (stage S6). The channels: 7-channels (stage S5; T9
by type). The other flows have none yet (T3, T4-x, T11, section 8). Below: a structural fact about the TLS client. -/

open TlsMpc.TlsClient in
/-- **Any TLS `Session` value records that the server certificate and the server Finished were
verified.** **C**, weak: a structure projection (the flags are fields that construction must
supply), not a statement about what the handshake checked. SECURITY_MAP C.4. -/
theorem tlsClient_accepted_session_authenticated {S : Type} (session : Session S) :
    session.serverCertificateVerified = true ∧ session.serverFinishedVerified = true :=
  TlsMpc.TlsClient.accepted_session_authenticated session

/-! ### 7-channels. What leaves a node's controller (stage S5; plan sections 2.1, 3)

`TlsMpc/Node/Messages.lean` lists every message type of the controller's channels (the other
node `PeerMsg`, the database client `DbCall`, the daemon `DaemonLine`, the event record
`RecordEvent`, standard error `LogLine`, the journal, public and share files, the certificate
checker, the ceremony's child session), each with its encoder; `TlsMpc/Node/Channels.lean` is the
only controller file that performs I/O (`scripts/lint_node.py`, check `io-baseline`, strict for
the controller and `TlsMpc/Node`).

**T9 by type (C, a build check, not a theorem).** No constructor of a type declared in
`Messages.lean` mentions `TlsMpc.Node.Secret`, `TlsMpc.Node.Handle` or
`TlsMpc.TlsWorker.BufferHandle`, directly or through any repository type it uses:
`Messages.checkPublic`, run at the end of that file, fails the build otherwise (and the lint's
`message-fields` check rejects the words there). `PeerMsg.flow` (own-secret openings, only from
`Reveal.lean`) does not exist yet (S6/S9). -/

/-- **A peer's reply is read as a message of the kind this node sent** (plan 3.2: "the reply's
constructor is checked here"): whatever bytes the other controller sends back through the
worker's exchange, `Channels.exchange` decodes them as the same `PeerMsg` constructor, or the
session ends. **C**. -/
theorem peerMsg_reply_kind {mine reply : TlsMpc.Node.PeerMsg} {theirs : TlsMpc.TlsWire.Bytes}
    (h : TlsMpc.Node.PeerMsg.decodeReply mine theirs = .ok reply) : reply.name = mine.name :=
  TlsMpc.Node.PeerMsg.decodeReply_kind h

/-! ### 7-reveal. The flow API and the reveal list (stage S6; plan sections 2.1, 4.3, 6.2)

`TlsMpc/Node/Flow.lean` is the only way the controller reaches the engines: one function per worker
operation, with typed inputs (`ContactId`, public values, `Secret`) and outputs (`Opened r α`,
`Secret`, buffer handles). `TlsMpc/Node/Reveal.lean` is the list of everything a flow may open,
one function per kind; `Opened`'s constructor is private there, so a value of type `Opened r α` was
made by `r`'s function (by the type system, **C**, not a theorem), and the lint's `flow-calls` check
allows those functions, the worker pipe and `Secret.inputOwn` only in the legacy flow
implementations. Each function's docstring names the theorems above that bound its kind (or "none
yet"). The flows are still worker operations (C++, trusted); T3/T4 per flow come with their scripts
(S9-S16). -/

/-- **The reveal kinds' codes are pairwise distinct** (so a code, and the engine label mapped to it,
names its kind). **C**, by `decide`. -/
theorem revealKind_codes_distinct : (TlsMpc.Node.RevealKind.all.map TlsMpc.Node.RevealKind.code).Nodup :=
  TlsMpc.Node.RevealKind.codes_distinct

/-- **`RevealKind.all` lists every kind.** **C**, by `decide`. -/
theorem revealKind_mem_all (r : TlsMpc.Node.RevealKind) : r ∈ TlsMpc.Node.RevealKind.all :=
  TlsMpc.Node.RevealKind.mem_all r

/-- **No kind has code 0** (the engine refuses label 0). **C**, by `decide`. -/
theorem revealKind_code_ne_zero (r : TlsMpc.Node.RevealKind) : r.code ≠ 0 :=
  TlsMpc.Node.RevealKind.code_ne_zero r

/-! ### 7a. The engine instruction set, its model, and the first flows (stage S9)

`TlsMpc/Node/Engine.lean` (instructions, scripts, the batch encoding), `Engine/Model.lean` (the
ideal two-party semantics `idealStep`, runs against any adversary `withAdv`), `Flows/Random.lean`
(joint randomness, P-RAND) and `Flows/Upgrade.lean` (T4-UPGRADE). **Trust:** these are statements
about the model. The engines, their C ABI and the Rust shell are assumed to behave as `idealStep`
says (plan section 5.3); the commitment is `idealCommit` (a hypothesis, P-RAND (b)). -/

section EngineModel
open TlsMpc.Node.Engine

/-- **T12 (skeleton determinism).** Two runs of a script in which the honest party received the same
replies reached the same instructions, whatever its private inputs, the adversary and the engines'
state. -/
theorem engine_T12_skeleton_determinism {α : Type} (s : Script α)
    (E₁ E₂ : Env) (me₁ me₂ : Party) (adv₁ adv₂ : Adversary) (σ₁ σ₂ : Store) (I₁ I₂ : Ideal)
    (v₁ v₂ : List Release)
    (h : (withAdv E₁ me₁ adv₁ s σ₁ I₁ v₁).replies = (withAdv E₂ me₂ adv₂ s σ₂ I₂ v₂).replies) :
    (withAdv E₁ me₁ adv₁ s σ₁ I₁ v₁).trace = (withAdv E₂ me₂ adv₂ s σ₂ I₂ v₂).trace :=
  TlsMpc.Node.Engine.T12_skeleton_determinism s E₁ E₂ me₁ me₂ adv₁ adv₂ σ₁ σ₂ I₁ I₂ v₁ v₂ h

/-- The instructions a run reaches are the script's skeletons along the replies it received. -/
theorem engine_trace_eq_skeletons (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv s σ I vD).trace = s.skeletons (withAdv E me adv s σ I vD).replies :=
  TlsMpc.Node.Engine.trace_eq_skeletons E me adv s σ I vD

/-- **The open rule, honest party's view:** what was released to it carries, in order, labels of
release instructions it reached. -/
theorem engine_view_labels_H (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) :
    List.Sublist ((withAdv E me adv s σ I vD).viewH.map (·.label))
      ((withAdv E me adv s σ I vD).trace.filterMap InstrP.label?) :=
  TlsMpc.Node.Engine.view_labels_H E me adv s σ I vD

/-- **The open rule, adversary's view:** the same for what was released to the adversary. -/
theorem engine_view_labels_D (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) :
    List.Sublist ((withAdv E me adv s σ I vD).viewD.map (·.label))
      ((withAdv E me adv s σ I vD).trace.filterMap InstrP.label?) :=
  TlsMpc.Node.Engine.view_labels_D E me adv s σ I vD

/-- **The honest party's result and store are a function of its script, its store and its view.** -/
theorem engine_honest_replay (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) :
    replay E.hash me s σ (withAdv E me adv s σ I vD).viewH (withAdv E me adv s σ I vD).replies.length =
      ((withAdv E me adv s σ I vD).result, (withAdv E me adv s σ I vD).store) :=
  TlsMpc.Node.Engine.honest_replay E me adv s σ I vD

/-- The batch encoding round-trips. -/
theorem engine_decodeBatch_encodeBatch (b : List Wire) (hl : b.length < B64) (hb : ∀ w ∈ b, w.Bounded) :
    decodeBatch (encodeBatch b) = some b :=
  TlsMpc.Node.Engine.decodeBatch_encodeBatch b hl hb

/-- Equal skeleton bytes are equal skeletons (what the two parties agree on per batch). -/
theorem engine_skeletonBytes_inj (b₁ b₂ : List Wire) (h₁ : b₁.length < B64) (h₂ : b₂.length < B64)
    (hb₁ : ∀ w ∈ b₁, w.Bounded) (hb₂ : ∀ w ∈ b₂, w.Bounded) (h : skeletonBytes b₁ = skeletonBytes b₂) :
    b₁.map InstrP.skel = b₂.map InstrP.skel :=
  TlsMpc.Node.Engine.skeletonBytes_inj b₁ b₂ h₁ h₂ hb₁ hb₂ h

/-- Every release a context accepts carries a label (code nonzero). -/
theorem engine_check_label (sigs : Bytes → Option Sig) (c c' : Ctx) (sh : Shape) (s : Skel) (l : Label)
    (h : check sigs c s = some (c', sh)) (hl : s.label? = some l) : l.code ≠ 0 :=
  TlsMpc.Node.Engine.check_label sigs c c' sh s l h hl

/-- **The program instruction in the shell** (opcode 22, P-FIELDPROG shell side): accepted only
for a loaded program with matching counts; the masks were live, marked `never`, and are consumed;
every input is live; every output gets the mark its V3 file declares (so it is openable later
exactly when the file marks it public, `Mark.ofOMark_openable`). -/
theorem engine_check_program (sigs : Bytes → Option Sig) (c c' : Ctx) (sh : Shape) (name : Bytes)
    (copies : Nat) (ins masks outs : List FieldH) (l : Label)
    (h : check sigs c (.program name copies ins masks outs l) = some (c', sh)) :
    ∃ s c₁, c.progs name = some s ∧ sh = .unit ∧ l.code ≠ 0 ∧ 0 < copies ∧
      ins.length = copies * s.inputs ∧ masks.length = copies * s.masks ∧
      outs.length = copies * s.outMarks.length ∧
      c.useMasks masks = some c₁ ∧
      (∀ m ∈ masks, c.field? m = some .never ∧ c₁.field? m = none) ∧
      (∀ x ∈ ins, (c₁.field? x).isSome) ∧
      (∀ e ∈ outs.zip (List.replicate copies s.outMarks).flatten, c'.field? e.1 = some e.2) :=
  TlsMpc.Node.Engine.check_program sigs c c' sh name copies ins masks outs l h

/-- **P-FIELDPROG, the open rule**: after an accepted program step, an output is openable exactly
when the program's V3 file marks it public. -/
theorem engine_check_program_openable (sigs : Bytes → Option Sig) (c c' : Ctx) (sh : Shape) (name : Bytes)
    (copies : Nat) (ins masks outs : List FieldH) (l : Label) (p : TlsMpc.FieldDag.V3.Program)
    (hp : c.progs name = some (ProgSig.ofProgram p))
    (h : check sigs c (.program name copies ins masks outs l) = some (c', sh)) :
    ∀ e ∈ outs.zip (List.replicate copies (p.outputs.map (·.2))).flatten,
      (c'.field? e.1).map Mark.openable = some (e.2 == .pub) :=
  TlsMpc.Node.Engine.check_program_openable sigs c c' sh name copies ins masks outs l p hp h

/-- **What a program step releases** (P-FIELDPROG / P-INV, model side): exactly the openings
`b·m` of its instances' `D`/`Z` rows (V3 semantics), labelled, the same to both parties. -/
theorem engine_idealStep_program (E : Env) (me : Party) (name : Bytes) (copies : Nat)
    (ins masks outs : List FieldH) (l : Label) (peer : PeerPart) (I I' : Ideal) (toH toD : Option Release)
    (h : idealStep E me (.program name copies ins masks outs l) peer I = some (I', toH, toD)) :
    ∃ p vi vm vo opened, E.programs name = some p ∧ ins.mapM (fun h => I.fields h.id) = some vi ∧
      masks.mapM (fun h => I.fields h.id) = some vm ∧ runProgram p copies vi vm = some (vo, opened) ∧
      vo.length = outs.length ∧ I' = I.setFields outs vo ∧
      toH = some ⟨l, .elems opened⟩ ∧ toD = some ⟨l, .elems opened⟩ :=
  TlsMpc.Node.Engine.idealStep_program E me name copies ins masks outs l peer I I' toH toD h

/-- A program step opens exactly one value per `D`/`Z` row per instance. -/
theorem engine_runProgram_lengths (p : TlsMpc.FieldDag.V3.Program) (copies : Nat)
    (vi vm vo opened : List TlsMpc.FieldDag.F) (h : runProgram p copies vi vm = some (vo, opened)) :
    opened.length = copies * p.openings ∧ vo.length = copies * p.outputs.length :=
  TlsMpc.Node.Engine.runProgram_lengths p copies vi vm vo opened h

/-- **`withAdv` over `bind`.** A run of `s.bind f` is the run of `s`, then (if `s` returned `a`)
the run of `f a` from the store and ideal state `s` left, against the same adversary, whose view
then includes everything `s` released to it. -/
theorem engine_withAdv_bind (E : Env) (me : Party) (adv : Adversary) {α β : Type} (s : Script α)
    (f : α → Script β) (σ : Store) (I : Ideal) (vD : List Release) :
    withAdv E me adv (s.bind f) σ I vD =
      match (withAdv E me adv s σ I vD).result with
      | some a => (withAdv E me adv s σ I vD).then
          (withAdv E me adv (f a) (withAdv E me adv s σ I vD).store (withAdv E me adv s σ I vD).ideal
            (vD ++ (withAdv E me adv s σ I vD).viewD))
      | none => (withAdv E me adv s σ I vD).stop :=
  TlsMpc.Node.Engine.withAdv_bind E me adv s f σ I vD

/-- **`jointRun` over `bind`.** When two honest parties' runs of `sA`, `sB` both return (`a`, `b`),
their runs of `sA.bind fA`, `sB.bind fB` are those runs followed by the joint run of `fA a`, `fB b`
from the stores and ideal state they left. -/
theorem engine_jointRun_bind (E : Env) {α β γ δ : Type} (sA : Script α) (sB : Script β)
    (fA : α → Script γ) (fB : β → Script δ) (σA σB : Store) (I : Ideal) (a : α) (b : β)
    (h : (jointRun E sA sB σA σB I).result = some (a, b)) :
    jointRun E (sA.bind fA) (sB.bind fB) σA σB I =
      (jointRun E sA sB σA σB I).then
        (jointRun E (fA a) (fB b) (jointRun E sA sB σA σB I).storeA (jointRun E sA sB σA σB I).storeB
          (jointRun E sA sB σA σB I).ideal) :=
  TlsMpc.Node.Engine.jointRun_bind E sA sB fA fB σA σB I a b h

/-- **The unusable marker is no batch's skeleton bytes.** -/
theorem engine_skeletonBytes_ne_unusable (b : List Wire) : skeletonBytes b ≠ unusable :=
  TlsMpc.Node.Engine.skeletonBytes_ne_unusable b

/-- **An unusable batch is rejected by both parties before any engine call:** if either party's
batch is unusable, neither proceeds past the agreement, whatever the other party's request. -/
theorem engine_unusable_rejected_by_both (reqA reqB : Bytes)
    (h : usableBatch .a reqA = none ∨ usableBatch .b reqB = none) :
    agreeBatch .a reqA (agreedBytes .b reqB) = none ∧ agreeBatch .b reqB (agreedBytes .a reqA) = none :=
  TlsMpc.Node.Engine.unusable_rejected_by_both reqA reqB h

/-- **An unusable batch stops both shells before any engine call:** no instruction reaches the
ideal functionality, and nothing is released to anyone. -/
theorem engine_shellPair_unusable (E : Env) (reqA reqB : Bytes) (I : Ideal)
    (h : usableBatch .a reqA = none ∨ usableBatch .b reqB = none) :
    agreeBatch .a reqA (agreedBytes .b reqB) = none ∧ agreeBatch .b reqB (agreedBytes .a reqA) = none ∧
      shellPair E reqA reqB I = none :=
  TlsMpc.Node.Engine.shellPair_unusable E reqA reqB I h

/-- **Allocated handles are never reused:** the blocks of any sequence of allocations from the
session's counters are pairwise disjoint. -/
theorem engine_counters_blocksB_disjoint (n : Counters) (ks : List Nat) :
    (Counters.blocksB n ks).Pairwise (fun b b' => ∀ j ∈ b, j ∉ b') :=
  TlsMpc.Node.Engine.Counters.blocksB_disjoint n ks

end EngineModel

section FlowsRandom
open TlsMpc.Node.Engine TlsMpc.Node.Flows.Random

/-- **P-RAND (a).** Both honest parties return r_A ⊕ r_B. -/
theorem prand_a_honest (E : Env) (σA σB : Store) (I : Ideal) (nA vA nB vB : Nat)
    (hh : ∀ m, (E.hash m).length = 32)
    (hnA : (σA.bytes nA).length = 32) (hvA : (σA.bytes vA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hvB : (σB.bytes vB).length = 32)
    (hc : E.hash (commitFrame tag .a (σA.bytes nA) (σA.bytes vA)) ≠
      E.hash (commitFrame tag .b (σB.bytes nB) (σB.bytes vB))) :
    (jointRun E (joint E.hash .a nA vA) (joint E.hash .b nB vB) σA σB I).result =
      some (xorBytes (σA.bytes vA) (σB.bytes vB), xorBytes (σA.bytes vA) (σB.bytes vB)) :=
  TlsMpc.Node.Flows.Random.prand_a_honest E σA σB I nA vA nB vB hh hnA hvA hnB hvB hc

/-- **T3 for `Random.joint` (disclosure).** What the honest party releases to the adversary is a
prefix of [its commitment, its opening]. -/
theorem prand_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)
    (nonce value : Nat) (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) :
    (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewD <+:
      [e1 E me σ nonce value, e2 σ nonce value] :=
  TlsMpc.Node.Flows.Random.prand_disclosure E me adv σ I vD nonce value hh hn hv

/-- **Commit before open.** If our opening reached the adversary, it had already committed, from its
prior view and our commitment alone. -/
theorem prand_commit_before_open (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (nonce value : Nat) (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32)
    (h : e2 σ nonce value ∈ (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewD) :
    ∃ p1, adv.act (vD ++ [e1 E me σ nonce value]) skel1 = some p1 ∧ p1.bytes.length = 32 ∧
      (withAdv E me adv (joint E.hash me nonce value) σ I vD).viewH.head? =
        some ⟨Label.jointRandomCommitment, .bytes p1.bytes⟩ :=
  TlsMpc.Node.Flows.Random.prand_commit_before_open E me adv σ I vD nonce value hh hn hv h

/-- **P-RAND (c).** A commitment equal to ours aborts. -/
theorem prand_c_copy_aborts (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (nonce value : Nat) (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) (p1 : PeerPart)
    (h1 : adv.act (vD ++ [e1 E me σ nonce value]) skel1 = some p1)
    (hcopy : p1.bytes = ourCommit E me σ nonce value) :
    (withAdv E me adv (joint E.hash me nonce value) σ I vD).result = none :=
  TlsMpc.Node.Flows.Random.prand_c_copy_aborts E me adv σ I vD nonce value hh hn hv p1 h1 hcopy

/-- **P-RAND (b).** Under `IdealCommit` (a hypothesis), every accepted result is r ⊕ v for one
value `v`, and r ↦ r ⊕ v is a bijection of 32-byte strings: with r uniform, the result is uniform. -/
theorem prand_b_ideal (E : Env) (me : Party) (adv : Adversary) (I : Ideal) (vD : List Release)
    (nonce value : Nat) (hh : ∀ m, (E.hash m).length = 32) (S : Store → Prop)
    (hS : ∀ σ', S σ' → (σ'.bytes nonce).length = 32 ∧ (σ'.bytes value).length = 32)
    (v : Bytes) (hic : IdealCommit E me adv I vD nonce value S v) :
    (∀ σ', S σ' → ∀ x, (withAdv E me adv (joint E.hash me nonce value) σ' I vD).result = some x →
        x = xorBytes (σ'.bytes value) v ∧ v.length = 32) ∧
      ∀ r : Bytes, r.length = 32 → v.length = 32 →
        (xorBytes r v).length = 32 ∧ xorBytes (xorBytes r v) v = r :=
  TlsMpc.Node.Flows.Random.prand_b_ideal E me adv I vD nonce value hh S hS v hic

end FlowsRandom

section FlowsUpgrade
open TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Upgrade
open TlsMpc.Local.WebSocketAccept (acceptOf keyOf)

/-- **T4-UPGRADE (honest parties).** Both return nonce ‖ acceptOf (keyOf nonce), RFC 6455's accept
value for the key base64(nonce), with nonce the first 16 bytes of r_A ⊕ r_B. -/
theorem upgrade_honest (E : Env) (σA σB : Store) (I : Ideal) (nA vA nB vB : Nat)
    (hh : ∀ m, (E.hash m).length = 32)
    (hnA : (σA.bytes nA).length = 32) (hvA : (σA.bytes vA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hvB : (σB.bytes vB).length = 32)
    (hc : E.hash (commitFrame Random.tag .a (σA.bytes nA) (σA.bytes vA)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes nB) (σB.bytes vB))) :
    (jointRun E (publicUpgrade E.hash .a nA vA) (publicUpgrade E.hash .b nB vB) σA σB I).result =
      some ((((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV ++
              acceptOf (keyOf (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV))).map toU8,
            (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV ++
              acceptOf (keyOf (((Random.xorBytes (σA.bytes vA) (σB.bytes vB)).take 16).map toBV))).map toU8) :=
  TlsMpc.Node.Flows.Upgrade.upgrade_honest E σA σB I nA vA nB vB hh hnA hvA hnB hvB hc

end FlowsUpgrade

/-! ### 7a (continued). Contact and account state at rest (stage S9)

`TlsMpc/Node/Flows/Contacts.lean` (`Contacts.key`, `Contacts.seal`, `Contacts.open`: ops 36, 38,
37), `ContactsTable.lean` (the per-contact table, ops 36–38, 40, 52, 63), `Account.lean` (ops 53,
54) and `ContactsWrite.lean` (T10: a state write's fresh nonce). **Trust:** statements about the
ideal model `Engine/Model.lean`, as the rest of 7a; besides, the honest-run and seal/open disclosure
entries assume `Loaded E`: the environment's circuits named `contact-key`, `contact-seal N`,
`contact-open N` compute the Lean kernels (section 8, T2). Nothing else about the engines is
assumed. -/

section FlowsContacts
open TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts

/-! #### Well-formedness: the shell's `check` accepts every instruction -/

/-- **`Contacts.key` is well formed** from any context whose handle counter `n` is fresh, when the
signature table gives `contact-key` its widths and marks. -/
theorem contacts_keyScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n slot : Nat) (hf : Fresh c n)
    (hsig : sigs keyName = some ⟨512, keyMarks⟩) : WF sigs c (keyScript n slot) :=
  TlsMpc.Node.Flows.Contacts.keyScript_wf sigs c n slot hf hsig

/-- **`Contacts.seal` is well formed** on every branch, with the key (480 bits) and state (8·size
bits) handles live below a fresh counter. -/
theorem contacts_sealScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (key state : BoolH) (size : Nat)
    (version : B8) (km sm : List Mark) (hf : Fresh c n) (hkn : key.id < n) (hsn : state.id < n)
    (hk : c.bool? key = some ⟨km, false⟩) (hs : c.bool? state = some ⟨sm, false⟩)
    (hkm : km.length = 480) (hsm : sm.length = 8 * size)
    (hsig : sigs (sealName size) = some ⟨8 * (68 + size), sealMarks size⟩) :
    WF sigs c (sealScript n key state size version) :=
  TlsMpc.Node.Flows.Contacts.sealScript_wf sigs c n key state size version km sm hf hkn hsn hk hs hkm hsm hsig

/-- **`Contacts.open` is well formed** on every branch, with the key handle live below a fresh
counter. -/
theorem contacts_openScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (key : BoolH)
    (version check ct : B8)
    (km : List Mark) (hf : Fresh c n) (hkn : key.id < n) (hk : c.bool? key = some ⟨km, false⟩)
    (hkm : km.length = 480)
    (hsig : sigs (openName ct.length) = some ⟨8 * (84 + ct.length), openMarks ct.length⟩) :
    WF sigs c (openScript n key version check ct) :=
  TlsMpc.Node.Flows.Contacts.openScript_wf sigs c n key version check ct km hf hkn hk hkm hsig

/-! #### T3: what each operation releases, against any adversary -/

/-- **T3 for `Contacts.key`.** Nothing is released, to either party. -/
theorem contacts_key_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (n slot : Nat) :
    (withAdv E me adv (keyScript n slot) σ I vD).viewD = [] ∧
      (withAdv E me adv (keyScript n slot) σ I vD).viewH = [] :=
  TlsMpc.Node.Flows.Contacts.key_disclosure E me adv σ I vD n slot

/-- **T3 for `Contacts.seal`.** At most one release, labelled `sealedBlob`: the `contact-seal`
kernel's output (ciphertext ‖ check) on the key handle's value, the public version and the state
handle's value. -/
theorem contacts_seal_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (hE : Loaded E) (n : Nat) (key state : BoolH) (size : Nat) (version : B8)
    (k s : Bits) (hkn : key.id < n) (hsn : state.id < n) (hk : I.bools key.id = some k)
    (hs : I.bools state.id = some s) :
    (withAdv E me adv (sealScript n key state size version) σ I vD).viewD <+:
      [⟨sealedBlob, .bits (bitsOf (kernelOut (HybridKernel.contactSeal size) (bytesOf (k ++ (bitsOf version ++ s)))))⟩] :=
  TlsMpc.Node.Flows.Contacts.seal_disclosure E me adv σ I vD hE n key state size version k s hkn hsn hk hs

/-- **T3 for `Contacts.open`.** At most one release, labelled `blobAccepted`: the first byte of the
`contact-open` kernel's output (its `accepted` field). The content never leaves the engines. -/
theorem contacts_open_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (hE : Loaded E) (n : Nat) (key : BoolH) (version check ct : B8) (k : Bits)
    (hkn : key.id < n) (hk : I.bools key.id = some k) :
    (withAdv E me adv (openScript n key version check ct) σ I vD).viewD <+:
      [⟨blobAccepted, .bits ((bitsOf (kernelOut (HybridKernel.contactOpen ct.length)
        (bytesOf (k ++ bitsOf (version ++ ct ++ check))))).take 8)⟩] :=
  TlsMpc.Node.Flows.Contacts.open_disclosure E me adv σ I vD hE n key version check ct k hkn hk

/-- **What an open releases is one bit of information:** for a 60-byte key and well-formed
arguments, the released byte is `contactMask K check`, 255 when `check` is this key's check value
and 0 otherwise (`contactMask_accept_iff`). -/
theorem contacts_open_released_byte (K version check ct : B8) (hK : K.length = 60)
    (hargs : openArgsOk version check ct) :
    (bitsOf (kernelOut (HybridKernel.contactOpen ct.length)
      (bytesOf (bitsOf K ++ bitsOf (version ++ ct ++ check))))).take 8 =
      bitsOf [HybridKernel.contactMask K check] :=
  TlsMpc.Node.Flows.Contacts.open_released_byte K version check ct hK hargs

/-- **T3 for op 36 on the table.** Nothing is released. -/
theorem contactsTable_opKey_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (t : Table) (id slot : Nat) :
    (withAdv E me adv (opKey t id slot).script σ I vD).viewD = [] ∧
      (withAdv E me adv (opKey t id slot).script σ I vD).viewH = [] :=
  TlsMpc.Node.Flows.Contacts.opKey_disclosure E me adv σ I vD t id slot

/-- **T3 for op 38 on the table.** At most the sealed blob of the entry's key and state handles. -/
theorem contactsTable_opSeal_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (hE : Loaded E) (t : Table) (id : Nat) (version : B8) (e : Entry) (k s : BoolH)
    (kv sv : Bits) (he : t.find? id = some e) (hk : e.key = some k) (hs : e.state = some s)
    (hkn : k.id < t.next) (hsn : s.id < t.next) (hkv : I.bools k.id = some kv) (hsv : I.bools s.id = some sv) :
    (withAdv E me adv (opSeal t id version).script σ I vD).viewD <+:
      [⟨sealedBlob, .bits (bitsOf (kernelOut (HybridKernel.contactSeal e.size) (bytesOf (kv ++ (bitsOf version ++ sv)))))⟩] :=
  TlsMpc.Node.Flows.Contacts.opSeal_disclosure E me adv σ I vD hE t id version e k s kv sv he hk hs hkn hsn hkv hsv

/-- **T3 for ops 37 and 63 on the table.** At most the `accepted` byte; freeing the derived caches
first releases nothing. -/
theorem contactsTable_opOpen_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (hE : Loaded E) (t : Table) (id : Nat) (kinds : List Nat) (version check ct : B8)
    (e : Entry) (k : BoolH) (kv : Bits) (he : t.find? id = some e) (hk : e.key = some k) (hs : e.state = none)
    (hkn : k.id < t.next) (hkv : I.bools k.id = some kv)
    (hd : ∀ h ∈ e.derived, h.id ≠ k.id) :
    (withAdv E me adv (opOpen t id kinds version check ct).script σ I vD).viewD <+:
      [⟨blobAccepted, .bits ((bitsOf (kernelOut (HybridKernel.contactOpen ct.length)
        (bytesOf (kv ++ bitsOf (version ++ ct ++ check))))).take 8)⟩] :=
  TlsMpc.Node.Flows.Contacts.opOpen_disclosure E me adv σ I vD hE t id kinds version check ct e k kv he hk hs hkn hkv hd

/-- **T3 for op 40 (evict).** Nothing is released. -/
theorem contactsTable_opEvict_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (t : Table) (id : Nat) :
    (withAdv E me adv (opEvict t id).script σ I vD).viewD = [] ∧
      (withAdv E me adv (opEvict t id).script σ I vD).viewH = [] :=
  TlsMpc.Node.Flows.Contacts.opEvict_disclosure E me adv σ I vD t id

/-- **T3 for op 52 (assign a new id).** Nothing is released. -/
theorem contactsTable_opAssign_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (t : Table) (fromId toId : Nat) :
    (withAdv E me adv (opAssign t fromId toId).script σ I vD).viewD = [] ∧
      (withAdv E me adv (opAssign t fromId toId).script σ I vD).viewH = [] :=
  TlsMpc.Node.Flows.Contacts.opAssign_disclosure E me adv σ I vD t fromId toId

/-- **Op 40 is well formed** when the entry's handles are live and distinct. -/
theorem contactsTable_opEvict_wf (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (id : Nat) (e : Entry)
    (he : t.find? id = some e) (hn : (e.handles.map (·.id)).Nodup)
    (hl : ∀ h ∈ e.handles, (c.bool? h).isSome = true) : WF sigs c (opEvict t id).script :=
  TlsMpc.Node.Flows.Contacts.opEvict_wf sigs c t id e he hn hl

/-- **T3 for op 53 (`Account.key`, which is `Contacts.key`).** Nothing is released. -/
theorem account_accountKey_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (n slot : Nat) :
    (withAdv E me adv (Account.keyScript n slot) σ I vD).viewD = [] ∧
      (withAdv E me adv (Account.keyScript n slot) σ I vD).viewH = [] :=
  TlsMpc.Node.Flows.Account.accountKey_disclosure E me adv σ I vD n slot

/-- **T3 for op 54's seal.** At most one release, labelled `sealedBlob`: the `contact-seal` kernel's
output on the key, the version and the content scalar ‖ credentials ‖ certificate. -/
theorem account_accountSeal_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (hE : Loaded E) (n : Nat) (key scalar cred cert : BoolH) (certLen : Nat)
    (version : B8) (kv sv cv tv : Bits) (hkn : key.id < n)
    (hk : I.bools key.id = some kv) (hs : I.bools scalar.id = some sv)
    (hc : I.bools cred.id = some cv) (ht : I.bools cert.id = some tv) :
    (withAdv E me adv (Account.sealScript n key scalar cred cert certLen version) σ I vD).viewD <+:
      [Account.released certLen version kv sv cv tv] :=
  TlsMpc.Node.Flows.Account.accountSeal_disclosure E me adv σ I vD hE n key scalar cred cert certLen version
    kv sv cv tv hkn hk hs hc ht

/-- **T3 for op 54, stored credentials.** At most one release, labelled `sealedBlob`, as
`account_accountSeal_disclosure`. -/
theorem account_opSeal_disclosure_stored (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (hE : Loaded E) (a : Account.State) (n : Nat) (version : B8)
    (k s cr cert : BoolH) (len : Nat) (kv sv cv tv : Bits)
    (hk : a.key = some k) (hs : a.scalar = some s) (ht : a.certificate = some (cert, len))
    (hcr : a.credentials = some cr)
    (hkn : k.id < n)
    (hkv : I.bools k.id = some kv) (hsv : I.bools s.id = some sv) (hcv : I.bools cr.id = some cv)
    (htv : I.bools cert.id = some tv) :
    (withAdv E me adv (Account.opSeal a n version).1 σ I vD).viewD <+: [Account.released len version kv sv cv tv] :=
  TlsMpc.Node.Flows.Account.opSeal_disclosure_stored E me adv σ I vD hE a n version k s cr cert len kv sv cv tv
    hk hs ht hcr hkn hkv hsv hcv htv

/-- **T3 for op 54, credentials from the two shares.** Their XOR stays in the engines; at most one
release, labelled `sealedBlob`: the value of the seal kernel's output handle. (No `Loaded`
hypothesis; the `xor-bit` circuit is not one of the `Loaded` kernels.) -/
theorem account_opSeal_disclosure_shares (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (a : Account.State) (n : Nat) (version : B8)
    (k s cert ca cb : BoolH) (len : Nat)
    (hk : a.key = some k) (hs : a.scalar = some s) (ht : a.certificate = some (cert, len))
    (hcr : a.credentials = none) (hsh : a.shares = some (ca, cb)) :
    (withAdv E me adv (Account.opSeal a n version).1 σ I vD).viewD <+:
      [⟨sealedBlob, .bits (openedAfter E (Account.combineBlock n ca cb ++
        Account.accountBlock (n + 3) k s ⟨n + 2⟩ cert len version) ⟨n + 3 + 3⟩ I)⟩] :=
  TlsMpc.Node.Flows.Account.opSeal_disclosure_shares E me adv σ I vD a n version k s cert ca cb len hk hs ht hcr hsh

/-! #### T4-CONTACT: two honest parties -/

/-- **T4 for `Contacts.key`.** Two honest parties with shares `a` (A) and `b` (B) below the
modulus: the key handle `n + 3` holds `contactKey_spec`'s block (SHA-256's first 28 bytes of
"CONTACT_STATE_KEY_V1" ‖ le32((a + b) mod (2^255 − 19)) after 32 zero bytes); handles below `n` are
untouched. -/
theorem contacts_key_honest (E : Env) (σA σB : Store) (hE : Loaded E) (I : Ideal) (n slotA slotB : Nat)
    (a b : B8)
    (ha : a.length = 32) (hb : b.length = 32)
    (haB : ModAdd.leValue a < HybridKernel.shareModulus) (hbB : ModAdd.leValue b < HybridKernel.shareModulus)
    (hσA : σA.bits slotA = bitsOf a) (hσB : σB.bits slotB = bitsOf b) :
    (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I).result = some (⟨n + 3⟩, ⟨n + 3⟩) ∧
    (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I).ideal.bools (n + 3) =
      some (bitsOf (keyBlock a b)) ∧
    ∀ j, j < n → (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I).ideal.bools j = I.bools j :=
  TlsMpc.Node.Flows.Contacts.key_honest E σA σB hE I n slotA slotB a b ha hb haB hbB hσA hσB

/-- **T4 for `Contacts.seal`.** Both honest parties return checkOf K ‖ ctrOf K version S
(`contactSeal_spec`). -/
theorem contacts_seal_honest (E : Env) (σA σB : Store) (hE : Loaded E) (I : Ideal) (n : Nat)
    (key state : BoolH) (size : Nat) (version K S : B8)
    (hkn : key.id < n) (hsn : state.id < n) (hK : K.length = 60) (hS : S.length = size)
    (h0 : 0 < size) (h1 : size ≤ 16384) (hv : versionOk version = true)
    (hk : I.bools key.id = some (bitsOf K)) (hs : I.bools state.id = some (bitsOf S)) :
    (jointRun E (sealScript n key state size version) (sealScript n key state size version) σA σB I).result =
      some (sealed K version S, sealed K version S) :=
  TlsMpc.Node.Flows.Contacts.seal_honest E σA σB hE I n key state size version K S hkn hsn hK hS h0 h1 hv hk hs

/-- **T4 for `Contacts.open`.** Accepted iff `check = checkOf K`: then the state handle `n + 4`
holds ctrOf K version ct; otherwise the result is `none` and the content handle is freed. -/
theorem contacts_open_honest (E : Env) (σA σB : Store) (hE : Loaded E) (I : Ideal) (n : Nat) (key : BoolH)
    (version check ct K : B8)
    (hkn : key.id < n) (hK : K.length = 60) (hk : I.bools key.id = some (bitsOf K))
    (hargs : openArgsOk version check ct) :
    (check = HybridKernel.checkOf K →
      (jointRun E (openScript n key version check ct) (openScript n key version check ct) σA σB I).result =
        some (some ⟨n + 4⟩, some ⟨n + 4⟩) ∧
      (jointRun E (openScript n key version check ct) (openScript n key version check ct) σA σB I).ideal.bools
        (n + 4) = some (bitsOf (HybridKernel.ctrOf K version ct))) ∧
    (check ≠ HybridKernel.checkOf K →
      (jointRun E (openScript n key version check ct) (openScript n key version check ct) σA σB I).result =
        some (none, none) ∧
      (jointRun E (openScript n key version check ct) (openScript n key version check ct) σA σB I).ideal.bools
        (n + 4) = none) :=
  TlsMpc.Node.Flows.Contacts.open_honest E σA σB hE I n key version check ct K hkn hK hk hargs

/-- **Opening what was sealed returns the sealed state:** opening `sealed K version S` (check value,
then ciphertext) under the same key accepts and the state handle holds `S`. -/
theorem contacts_open_after_seal (E : Env) (σA σB : Store) (hE : Loaded E) (I : Ideal) (n : Nat) (key : BoolH)
    (version K S : B8)
    (hkn : key.id < n) (hK : K.length = 60) (hk : I.bools key.id = some (bitsOf K))
    (hv : versionOk version = true) (hS0 : 0 < S.length) (hS1 : S.length ≤ 16384) :
    (jointRun E (openScript n key version ((sealed K version S).take 16) ((sealed K version S).drop 16))
        (openScript n key version ((sealed K version S).take 16) ((sealed K version S).drop 16)) σA σB I).result =
      some (some ⟨n + 4⟩, some ⟨n + 4⟩) ∧
    (jointRun E (openScript n key version ((sealed K version S).take 16) ((sealed K version S).drop 16))
        (openScript n key version ((sealed K version S).take 16) ((sealed K version S).drop 16)) σA σB I).ideal.bools
        (n + 4) = some (bitsOf S) :=
  TlsMpc.Node.Flows.Contacts.open_after_seal E σA σB hE I n key version K S hkn hK hk hv hS0 hS1

/-- **Key, seal, then open in a later session:** a state sealed under the key derived from shares
`a`, `b` is opened, under a key derived again from the same shares (other slots, other stores), to
the same state. -/
theorem contacts_key_seal_open (E : Env) (σA σB : Store) (hE : Loaded E) (τA τB : Store) (I₁ I₂ : Ideal)
    (n m slotA slotB slotA' slotB' : Nat)
    (st : BoolH) (a b version S : B8) (ha : a.length = 32) (hb : b.length = 32)
    (haB : ModAdd.leValue a < HybridKernel.shareModulus) (hbB : ModAdd.leValue b < HybridKernel.shareModulus)
    (hσA : σA.bits slotA = bitsOf a) (hσB : σB.bits slotB = bitsOf b)
    (hτA : τA.bits slotA' = bitsOf a) (hτB : τB.bits slotB' = bitsOf b)
    (hst : st.id < n) (hS : I₁.bools st.id = some (bitsOf S)) (hv : versionOk version = true)
    (hS0 : 0 < S.length) (hS1 : S.length ≤ 16384) :
    (jointRun E (sealScript (n + 4) ⟨n + 3⟩ st S.length version) (sealScript (n + 4) ⟨n + 3⟩ st S.length version)
        σA σB (jointRun E (keyScript n slotA) (keyScript n slotB) σA σB I₁).ideal).result =
      some (sealed (keyBlock a b) version S, sealed (keyBlock a b) version S) ∧
    (jointRun E
        (openScript (m + 4) ⟨m + 3⟩ version ((sealed (keyBlock a b) version S).take 16)
          ((sealed (keyBlock a b) version S).drop 16))
        (openScript (m + 4) ⟨m + 3⟩ version ((sealed (keyBlock a b) version S).take 16)
          ((sealed (keyBlock a b) version S).drop 16))
        τA τB (jointRun E (keyScript m slotA') (keyScript m slotB') τA τB I₂).ideal).result =
      some (some ⟨m + 4 + 4⟩, some ⟨m + 4 + 4⟩) ∧
    (jointRun E
        (openScript (m + 4) ⟨m + 3⟩ version ((sealed (keyBlock a b) version S).take 16)
          ((sealed (keyBlock a b) version S).drop 16))
        (openScript (m + 4) ⟨m + 3⟩ version ((sealed (keyBlock a b) version S).take 16)
          ((sealed (keyBlock a b) version S).drop 16))
        τA τB (jointRun E (keyScript m slotA') (keyScript m slotB') τA τB I₂).ideal).ideal.bools (m + 4 + 4) =
      some (bitsOf S) :=
  TlsMpc.Node.Flows.Contacts.key_seal_open E σA σB hE τA τB I₁ I₂ n m slotA slotB slotA' slotB' st a b version S
    ha hb haB hbB hσA hσB hτA hτB hst hS hv hS0 hS1

/-- **T4 for `Account.key`** (it is `Contacts.key`): the account key handle holds the block of
`contactKey_spec` from the two shares. -/
theorem account_accountKey_honest (E : Env) (σA σB : Store) (hE : Loaded E) (I : Ideal) (n slotA slotB : Nat)
    (a b : B8)
    (ha : a.length = 32) (hb : b.length = 32)
    (haB : ModAdd.leValue a < HybridKernel.shareModulus) (hbB : ModAdd.leValue b < HybridKernel.shareModulus)
    (hσA : σA.bits slotA = bitsOf a) (hσB : σB.bits slotB = bitsOf b) :
    (jointRun E (Account.keyScript n slotA) (Account.keyScript n slotB) σA σB I).ideal.bools (n + 3) =
      some (bitsOf (keyBlock a b)) :=
  TlsMpc.Node.Flows.Account.accountKey_honest E σA σB hE I n slotA slotB a b ha hb haB hbB hσA hσB

/-! #### T10: a state write's nonce (`ContactsWrite.lean`) -/

/-- **T10 (the worker flows' part).** Against any adversary and any engine state: a write's nonce
is a valid version (8 bytes, not 2^64 − 1) not used before in the session, and its blob is the
nonce followed by the seal's reply (check ‖ ciphertext of the opened `sealedBlob` bundle). The
database write itself is the controller's. -/
theorem contactsWrite_write_fresh (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release)
    (nonceSlot valueSlot : Nat) (used : List B8) (n : Nat) (key state : BoolH) (size : Nat) (x : B8 × B8)
    (h : (withAdv E me adv (writeScript E.hash me nonceSlot valueSlot used n key state size) σ I vD).result = some x) :
    versionOk x.1 = true ∧ x.1 ∉ used ∧ ∃ out : Bits, x.2 = x.1 ++ sealReply size out :=
  TlsMpc.Node.Flows.Contacts.write_fresh E me adv σ I vD nonceSlot valueSlot used n key state size x h

/-- **State nonces never repeat within a session:** adding each write's nonce keeps the session's
list duplicate free. -/
theorem contactsWrite_used_nodup (used : List B8) (v : B8) (hu : used.Nodup) (hv : v ∉ used) :
    (useNonce used v).Nodup :=
  TlsMpc.Node.Flows.Contacts.used_nodup used v hu hv

/-- **T3 for a state write** (against any adversary, any engine state): the adversary's view is a
prefix of `Random.joint`'s commitment and opening followed by the one `sealedBlob` release of the
seal under the nonce `v`, the first 8 bytes of the joint value. -/
theorem contactsWrite_write_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release)
    (hE : Loaded E) (hh : ∀ m, (E.hash m).length = 32) (nonceSlot valueSlot : Nat) (used : List B8) (n : Nat)
    (key state : BoolH) (size : Nat) (kv sv : Bits)
    (hn : (σ.bytes nonceSlot).length = 32) (hv : (σ.bytes valueSlot).length = 32)
    (hkn : key.id < n) (hsn : state.id < n) (hk : I.bools key.id = some kv) (hs : I.bools state.id = some sv) :
    ∃ v : B8, (withAdv E me adv (writeScript E.hash me nonceSlot valueSlot used n key state size) σ I vD).viewD <+:
      [Random.e1 E me σ nonceSlot valueSlot, Random.e2 σ nonceSlot valueSlot, writeRelease size kv sv v] :=
  TlsMpc.Node.Flows.Contacts.write_disclosure E me adv σ I vD hE hh nonceSlot valueSlot used n key state size
    kv sv hn hv hkn hsn hk hs

/-- **T10, two honest parties:** both return the nonce `v`, the first 8 bytes of r_A ⊕ r_B, and the
blob v ‖ checkOf K ‖ ctrOf K v S, when `v` is a valid version not used before in the session. -/
theorem contactsWrite_write_honest (E : Env) (σA σB : Store) (I : Ideal) (hE : Loaded E) (nA vA nB vB : Nat)
    (used : List B8) (n : Nat) (key state : BoolH) (size : Nat) (K S : B8)
    (hh : ∀ m, (E.hash m).length = 32)
    (hnA : (σA.bytes nA).length = 32) (hvA : (σA.bytes vA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hvB : (σB.bytes vB).length = 32)
    (hc : E.hash (commitFrame Random.tag .a (σA.bytes nA) (σA.bytes vA)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes nB) (σB.bytes vB)))
    (hkn : key.id < n) (hsn : state.id < n) (hK : K.length = 60) (hS : S.length = size)
    (h0 : 0 < size) (h1 : size ≤ 16384)
    (hk : I.bools key.id = some (bitsOf K)) (hs : I.bools state.id = some (bitsOf S))
    (hok : versionOk (nonceOf (Random.xorBytes (σA.bytes vA) (σB.bytes vB))) = true ∧
      nonceOf (Random.xorBytes (σA.bytes vA) (σB.bytes vB)) ∉ used) :
    (jointRun E (writeScript E.hash .a nA vA used n key state size)
        (writeScript E.hash .b nB vB used n key state size) σA σB I).result =
      some ((nonceOf (Random.xorBytes (σA.bytes vA) (σB.bytes vB)),
          nonceOf (Random.xorBytes (σA.bytes vA) (σB.bytes vB)) ++
            sealed K (nonceOf (Random.xorBytes (σA.bytes vA) (σB.bytes vB))) S),
        (nonceOf (Random.xorBytes (σA.bytes vA) (σB.bytes vB)),
          nonceOf (Random.xorBytes (σA.bytes vA) (σB.bytes vB)) ++
            sealed K (nonceOf (Random.xorBytes (σA.bytes vA) (σB.bytes vB))) S)) :=
  TlsMpc.Node.Flows.Contacts.write_honest E σA σB I hE nA vA nB vB used n key state size K S hh hnA hvA hnB hvB
    hc hkn hsn hK hS h0 h1 hk hs hok

/-- **A write is well formed** under the seal's hypotheses; it leaves what the seal leaves
(`SealPost`). -/
theorem contactsWrite_writeScript_wfp (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party)
    (nonceSlot valueSlot : Nat) (used : List B8) (c : Ctx) (n : Nat) (key state : BoolH) (size : Nat)
    (km sm : List Mark) (hf : Fresh c n) (hkn : key.id < n) (hsn : state.id < n)
    (hk : c.bool? key = some ⟨km, false⟩) (hs : c.bool? state = some ⟨sm, false⟩)
    (hkm : km.length = 480) (hsm : sm.length = 8 * size)
    (hsig' : 0 < size → size ≤ 16384 → sigs (sealName size) = some ⟨8 * (68 + size), sealMarks size⟩) :
    WFP sigs (fun c' (_ : B8 × B8) => SealPost c n c' []) c
      (writeScript hash me nonceSlot valueSlot used n key state size) :=
  TlsMpc.Node.Flows.Contacts.writeScript_wfp sigs hash me nonceSlot valueSlot used c n key state size km sm hf
    hkn hsn hk hs hkm hsm hsig'

/-! #### The contact table's invariant, preserved by every step -/

/-- **The table invariant holds at session start** (empty context, empty table). -/
theorem contactsTable_inv_empty : Table.Inv {} {} :=
  TlsMpc.Node.Flows.Contacts.Table.Inv.empty

/-- **Op 36 preserves the table invariant** (and is well formed). -/
theorem contactsTable_opKey_inv (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id slot : Nat)
    (hI : t.Inv c) : WFP sigs (fun c' h => ((opKey t id slot).commit h).Inv c') c (opKey t id slot).script :=
  TlsMpc.Node.Flows.Contacts.opKey_inv sigs hs c t id slot hI

/-- **Op 38 preserves the table invariant** (and is well formed). -/
theorem contactsTable_opSeal_inv (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id : Nat)
    (version : B8) (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opSeal t id version).commit r).Inv c') c (opSeal t id version).script :=
  TlsMpc.Node.Flows.Contacts.opSeal_inv sigs hs c t id version hI

/-- **Ops 37 and 63 preserve the table invariant** (and are well formed). -/
theorem contactsTable_opOpen_inv (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id : Nat)
    (kinds : List Nat) (version check ct : B8) (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opOpen t id kinds version check ct).commit r).Inv c') c
      (opOpen t id kinds version check ct).script :=
  TlsMpc.Node.Flows.Contacts.opOpen_inv sigs hs c t id kinds version check ct hI

/-- **Op 40 preserves the table invariant.** -/
theorem contactsTable_opEvict_inv (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (id : Nat) (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opEvict t id).commit r).Inv c') c (opEvict t id).script :=
  TlsMpc.Node.Flows.Contacts.opEvict_inv sigs c t id hI

/-- **Op 52 preserves the table invariant** (and is well formed). -/
theorem contactsTable_opAssign_inv (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (fromId toId : Nat)
    (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opAssign t fromId toId).commit r).Inv c') c (opAssign t fromId toId).script :=
  TlsMpc.Node.Flows.Contacts.opAssign_inv sigs c t fromId toId hI

/-- **A state write on the table preserves the invariant** (and is well formed). -/
theorem contactsWrite_opWrite_inv (sigs : Bytes → Option Sig) (hs : SigsOk sigs) (c : Ctx) (t : Table) (id : Nat)
    (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot : Nat) (used : List B8) (hI : t.Inv c) :
    WFP sigs (fun c' r => ((opWrite t id hash me nonceSlot valueSlot used).commit r).Inv c') c
      (opWrite t id hash me nonceSlot valueSlot used).script :=
  TlsMpc.Node.Flows.Contacts.opWrite_inv sigs hs c t id hash me nonceSlot valueSlot used hI

/-- **T3 for a state write on the table:** `contactsWrite_write_disclosure` for the entry's key and
state handles. -/
theorem contactsWrite_opWrite_disclosure (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release)
    (hE : Loaded E) (hh : ∀ m, (E.hash m).length = 32) (t : Table) (id nonceSlot valueSlot : Nat)
    (used : List B8) (e : Entry) (k s : BoolH) (kv sv : Bits) (he : t.find? id = some e)
    (hk : e.key = some k) (hs : e.state = some s) (hkn : k.id < t.next) (hsn : s.id < t.next)
    (hn : (σ.bytes nonceSlot).length = 32) (hv : (σ.bytes valueSlot).length = 32)
    (hkv : I.bools k.id = some kv) (hsv : I.bools s.id = some sv) :
    ∃ v : B8, (withAdv E me adv (opWrite t id E.hash me nonceSlot valueSlot used).script σ I vD).viewD <+:
      [Random.e1 E me σ nonceSlot valueSlot, Random.e2 σ nonceSlot valueSlot, writeRelease e.size kv sv v] :=
  TlsMpc.Node.Flows.Contacts.opWrite_disclosure E me adv σ I vD hE hh t id nonceSlot valueSlot used e k s kv sv
    he hk hs hkn hsn hn hv hkv hsv

/-- **Op 54 on the session's counters is op 54 at the counter:** `sealStep` is `opSeal a a.ctr.bool`,
the counter moved to `opSeal`'s next free id (so every `opSeal` theorem applies to it). -/
theorem account_sealStep_eq (a : Account.State) (version : B8) :
    (Account.sealStep a version).1 = (Account.opSeal a a.ctr.bool version).1 ∧
      (Account.sealStep a version).2 =
        { (Account.opSeal a a.ctr.bool version).2.2 with
          ctr := { a.ctr with bool := (Account.opSeal a a.ctr.bool version).2.1 } } :=
  TlsMpc.Node.Flows.Account.sealStep_eq a version

end FlowsContacts

/-! ### 7b. Conversions, masks, inversion (stage S10; plan 7.1 P-CHAL, P-CUT, P-PAIR/P-B2F, P-W2F, P-F2W, P-BITS, P-INV)

Status per entry: **M** (in the ideal model of `Engine/Model.lean`) or **K** (a statement about
values, independent of the model); hypotheses named `[hyp: …]`. `WordLoaded E` / `ProgsLoaded E`
(`Flows/ConvertBase.lean`): the environment's word circuits and field programs under the S10 names
compute their Lean specifications — the T2 trust in the pinned files (the word circuits' exact
specifications on every input are `modAdd_exact`, `condSub_exact`, `reduceOnce_exact`).
`FieldInverse` (Fermat for p) is the named hypothesis of FieldDagV3; the Mathlib package discharges
it. SECURITY_MAP: the conversions (B.5–B.6 rows of the conversion kinds 80–87, 90). -/

section FlowsS10
open TlsMpc.Node.Engine TlsMpc.Node.Flows
open TlsMpc.FieldDag (F)

/-- **P-CHAL (b).** [K] The challenge's expansion yields a permutation of [0, n) whenever it
succeeds. -/
theorem s10_pchal_permutation (hash : Bytes → Bytes) (domain seed : Bytes) (n : Nat) (π : List Nat)
    (h : Random.permOf hash domain seed n = some π) : π.Perm (List.range n) :=
  Random.permOf_perm hash domain seed n π h

/-- **P-CHAL (a).** [M] Two honest parties compute the same permutation, that of r_A ⊕ r_B (or
both abort). -/
theorem s10_pchal_honest (E : Env) (σA σB : Store) (I : Ideal) (nA vA nB vB : Nat) (domain : Bytes) (n : Nat)
    (hh : ∀ m, (E.hash m).length = 32)
    (hnA : (σA.bytes nA).length = 32) (hvA : (σA.bytes vA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hvB : (σB.bytes vB).length = 32)
    (hc : E.hash (commitFrame Random.tag .a (σA.bytes nA) (σA.bytes vA)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes nB) (σB.bytes vB))) :
    (jointRun E (Random.challenge E.hash .a nA vA domain n) (Random.challenge E.hash .b nB vB domain n) σA σB I).result =
      (Random.permOf E.hash domain (Random.xorBytes (σA.bytes vA) (σB.bytes vB)) n).map fun π => (π, π) :=
  Random.challenge_honest E σA σB I nA vA nB vB domain n hh hnA hvA hnB hvB hc

/-- **P-CHAL (c).** [M; hyp: `IdealCommit`] Every accepted challenge is the permutation of r ⊕ v
for one adversary value v, and r ↦ r ⊕ v is injective on 32-byte strings. -/
theorem s10_pchal_seed_injective (E : Env) (me : Party) (adv : Adversary) (I : Ideal) (vD : List Release)
    (nonce value : Nat) (domain : Bytes) (n : Nat) (hh : ∀ m, (E.hash m).length = 32) (S : Store → Prop)
    (hS : ∀ σ', S σ' → (σ'.bytes nonce).length = 32 ∧ (σ'.bytes value).length = 32)
    (v : Bytes) (hic : Random.IdealCommit E me adv I vD nonce value S v) :
    (∀ σ', S σ' → ∀ π, (withAdv E me adv (Random.challenge E.hash me nonce value domain n) σ' I vD).result = some π →
        Random.permOf E.hash domain (Random.xorBytes (σ'.bytes value) v) n = some π) ∧
      ∀ r r' : Bytes, r.length = 32 → r'.length = 32 → v.length = 32 → Random.xorBytes r v = Random.xorBytes r' v → r = r' :=
  Random.challenge_seed_injective E me adv I vD nonce value domain n hh S hS v hic

/-- **`commit_open_sound`** [M] (every commit-then-open site of the S10 flows is a `Random.joint`):
an accepted run means the adversary's opening matches the commitment it sent before seeing ours,
which differs from ours; a commitment equal to ours aborts. -/
theorem s10_commit_open_sound (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)
    (nonce value : Nat) (hh : ∀ m, (E.hash m).length = 32)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32) :
    (∀ x, (withAdv E me adv (Random.joint E.hash me nonce value) σ I vD).result = some x →
      ∃ p1 p2, adv.act (vD ++ [Random.e1 E me σ nonce value]) Random.skel1 = some p1 ∧
        adv.act (vD ++ [Random.e1 E me σ nonce value, Random.e2 σ nonce value]) Random.skel2 = some p2 ∧
        E.hash (commitFrame Random.tag me.other (p2.bytes.take 32) (p2.bytes.drop 32)) = p1.bytes ∧
        p1.bytes ≠ Random.ourCommit E me σ nonce value ∧ x = Random.xorBytes (σ.bytes value) (p2.bytes.drop 32)) ∧
    (∀ p1, adv.act (vD ++ [Random.e1 E me σ nonce value]) Random.skel1 = some p1 →
      p1.bytes = Random.ourCommit E me σ nonce value →
      (withAdv E me adv (Random.joint E.hash me nonce value) σ I vD).result = none) :=
  Random.commit_open_sound E me adv σ I vD nonce value hh hn hv

/-- **The word circuits' exact specification** [K]: `modAdd` computes `addModSpec` on every pair
of 255-bit words (canonical or not), which is what `WordLoaded` asks of the pinned file. -/
theorem s10_modAdd_exact (env : Nat → Bool) (x y : List TlsMpc.BoolDag.Expr) (hx : x.length = 255) (hy : y.length = 255) :
    TlsMpc.WordMask.val env (TlsMpc.WordMask.modAdd x y) =
      Conv.addModSpec (TlsMpc.WordMask.val env x) (TlsMpc.WordMask.val env y) :=
  Conv.modAdd_exact env x y hx hy

/-- **P-CUT (d), protocol level** [K]: the cut check passes iff every cut candidate of both owners
is canonical with error 0. -/
theorem s10_pcut_d_cut (x : Masks.Vals) (hw : x.Wide) (cut : List Nat) :
    Masks.cutCheck ((Masks.cutRel x cut).map Prod.fst).flatten ((Masks.cutRel x cut).map Prod.snd) = true ↔
      ∀ o ∈ Masks.owners, ∀ c ∈ cut, x.val o c < Conv.P ∧ x.err o c = 0 :=
  Masks.cutCheck_iff x hw cut

/-- **P-CUT (d), run level** [M]: against any adversary, getting past the cut means every cut
candidate of both owners, in the engines' values, is canonical with error 0. -/
theorem s10_pcut_d_run (E : Env) (me : Party) (adv : Adversary) (p : Masks.Params) (b f : Nat) (π₁ : List Nat)
    (σ : Store) (I : Ideal) (vD : List Release) (v : Bits)
    (hv : I.bools (b + 2) = some v) (hlen : v.length = 2 * (p.M * Masks.W)) (hπ : ∀ c ∈ Masks.cutOf p π₁, c < p.M)
    (hf : ∀ o ∈ Masks.owners, ∀ c ∈ Masks.cutOf p π₁, (I.fields (Masks.fOf p f o c).id).isSome)
    (h : (withAdv E me adv (Masks.cutPhase p b f π₁) σ I vD).result = some ()) :
    ∀ o ∈ Masks.owners, ∀ c ∈ Masks.cutOf p π₁,
      (Masks.valsOf p f v I).val o c < Conv.P ∧ (Masks.valsOf p f v I).err o c = 0 :=
  Masks.cutPhase_sound E me adv p b f π₁ σ I vD v hv hlen hπ hf h

/-- **P-CUT (b) for the cut** [M]: the adversary's view of the cut phase is a prefix of [the cut
candidates' elements, their words], labelled `cutCandidates`. -/
theorem s10_pcut_b_cut (E : Env) (me : Party) (adv : Adversary) (p : Masks.Params) (b f : Nat) (π₁ : List Nat)
    (σ : Store) (I : Ideal) (vD : List Release) (v : Bits)
    (hv : I.bools (b + 2) = some v) (hlen : v.length = 2 * (p.M * Masks.W)) (hπ : ∀ c ∈ Masks.cutOf p π₁, c < p.M)
    (hf : ∀ o ∈ Masks.owners, ∀ c ∈ Masks.cutOf p π₁, (I.fields (Masks.fOf p f o c).id).isSome) :
    (withAdv E me adv (Masks.cutPhase p b f π₁) σ I vD).viewD <+:
      [⟨Label.cutCandidates, .elems ((Masks.cutRel (Masks.valsOf p f v I) (Masks.cutOf p π₁)).map Prod.snd)⟩,
       ⟨Label.cutCandidates, .bits ((Masks.cutRel (Masks.valsOf p f v I) (Masks.cutOf p π₁)).map Prod.fst).flatten⟩] :=
  Masks.cutPhase_disclosure E me adv p b f π₁ σ I vD v hv hlen hπ hf

/-- **P-CUT (b): kept candidates are never cut** [K]: the cut is disjoint from the remaining
candidates (every reference and member). -/
theorem s10_pcut_b_disjoint (p : Masks.Params) (π₁ : List Nat) (hn : π₁.Nodup) :
    ∀ c ∈ Masks.cutOf p π₁, c ∉ Masks.remainOf p π₁ :=
  Masks.cut_disjoint p π₁ hn

/-- **P-CUT (e), protocol level** [K]: for a canonical reference, the bucket check of (reference,
member) passes iff val(ref) + val(member) < 2p and the errors cancel mod p. -/
theorem s10_pcut_e_bucket (vr vm : Nat) (er em : F) (hr : vr < Conv.P) (hm : vm < 2 ^ 255) :
    Masks.bucketOk vr vm er em = true ↔
      vr + vm < 2 * Conv.P ∧ ((vr + (Conv.P - er.val)) % Conv.P + (vm + (Conv.P - em.val)) % Conv.P) % Conv.P = 0 :=
  Masks.bucketOk_iff vr vm er em hr hm

/-- **The counting model's detection rule** [K] (proofs/ `CutAndChoose`: a mixed bucket aborts):
with a canonical reference, a pair of which exactly one has error 0 fails. -/
theorem s10_pcut_e_mixed (x : Masks.Vals) (o r m : Nat) (hr : x.val o r < Conv.P) (hm : x.val o m < 2 ^ 255)
    (hmix : (x.err o r = 0 ∧ x.err o m ≠ 0) ∨ (x.err o r ≠ 0 ∧ x.err o m = 0)) :
    Masks.bucketOk (x.val o r) (x.val o m) (x.elem o r) (x.elem o m) = false :=
  Masks.bucket_mixed_fails x o r m hr hm hmix

/-- **P-CUT (e), run level** [M; hyp: `WordLoaded`]: getting past the buckets means every pair of
both owners passes `bucketOk` in the engines' values. -/
theorem s10_pcut_e_run (E : Env) (me : Party) (adv : Adversary) (p : Masks.Params) (b f : Nat) (π₁ π₂ : List Nat)
    (hW : Conv.WordLoaded E) (σ : Store) (I : Ideal) (vD : List Release) (v : Bits)
    (hv : I.bools (b + 2) = some v) (hlen : v.length = 2 * (p.M * Masks.W))
    (hπ₁ : ∀ x ∈ π₁, x < p.M) (hM : 0 < p.M)
    (hf : ∀ o < 2, ∀ c < p.M, (I.fields (Masks.fOf p f o c).id).isSome)
    (h : (withAdv E me adv (Masks.bucketPhase p b f π₁ π₂) σ I vD).result = some ()) :
    ∀ e ∈ Masks.pairs p, Masks.bucketOk ((Masks.valsOf p f v I).val e.1 (Masks.memOf p π₁ π₂ e.2.1 0))
      ((Masks.valsOf p f v I).val e.1 (Masks.memOf p π₁ π₂ e.2.1 e.2.2))
      ((Masks.valsOf p f v I).elem e.1 (Masks.memOf p π₁ π₂ e.2.1 0))
      ((Masks.valsOf p f v I).elem e.1 (Masks.memOf p π₁ π₂ e.2.1 e.2.2)) = true :=
  Masks.bucketPhase_sound E me adv p b f π₁ π₂ hW σ I vD v hv hlen hπ₁ hM hf h

/-- **P-CUT (f)** [K]: the flag of a word mask is "both references canonical"; of a bit block,
also "both at least 32". -/
theorem s10_pcut_f_flags (a b : Bits) (ha : a.length = Masks.W) (hb : b.length = Masks.W) :
    (Conv.finalizeMaskEval (a ++ b)).getD 255 false = (decide (Conv.natOf a < Conv.P) && decide (Conv.natOf b < Conv.P)) ∧
    (Conv.finalizeBitsEval (a ++ b)).getD 255 false =
      (decide (Conv.natOf a < Conv.P) && decide (Conv.natOf b < Conv.P) && decide (32 ≤ Conv.natOf a) &&
        decide (32 ≤ Conv.natOf b)) :=
  ⟨Masks.finalizeMask_flag a b ha hb, Masks.finalizeBits_flag a b ha hb⟩

/-- **P-CUT (g)** [K; hyp: `FieldInverse`]: field inputs whose bit checks are 0 and whose
recomposition is the reference's value, with 19 ≤ val(b) < p, are exactly the bits of b. -/
theorem s10_pcut_g_bitblock (hinv : TlsMpc.FieldDag.V3.FieldInverse) (cs : List F) (b : Bits) (v : F)
    (hl : cs.length = 255) (hb : b.length = 255)
    (hcheck : ∀ c ∈ cs, c * (c - TlsMpc.FieldDag.ofNat 1) = 0)
    (hrec : TlsMpc.FieldBits.hornerValue cs - v = 0)
    (hv : v.val = Conv.natOf b) (h19 : 19 ≤ Conv.natOf b) (hP : Conv.natOf b < Conv.P) :
    cs = b.map TlsMpc.X25519.bitValue :=
  Masks.bitBlock_unique hinv cs b v hl hb hcheck hrec hv h19 hP

/-- **P-CUT (a)** [K]: from honest references, the word mask is (word of (r_A + r_B) mod p,
r_A + r_B) with val(word) = the field value, and the flag is set. -/
theorem s10_pcut_a_mask (rA rB : Nat) (hA : rA < Conv.P) (hB : rB < Conv.P) :
    (Conv.finalizeMaskEval ((Masks.honest rA).1 ++ (Masks.honest rB).1)).take 255 = Conv.word ((rA + rB) % Conv.P) ∧
      Conv.natOf (Conv.word ((rA + rB) % Conv.P)) = ((Masks.honest rA).2 + (Masks.honest rB).2).val ∧
      (Conv.finalizeMaskEval ((Masks.honest rA).1 ++ (Masks.honest rB).1)).getD 255 false = true :=
  Masks.honest_mask rA rB hA hB

/-- **P-CUT (c), the core lemma** [K]: the cut and bucket releases and the word-mask flags are
unchanged when the honest party's candidates are shifted by d with d ≡ 0 on the cut and
d(ref) + d(member) ≡ 0 in each bucket (a bijection: `Masks.shift_shift`; any target reference:
`Masks.shift_ref`). -/
theorem s10_pcut_c_core (x : Masks.Vals) (oH : Nat) (d : Nat → Nat) (h : Masks.HonestAt x oH) (cut : List Nat)
    (mem : Nat → Nat → Nat) (ps : List (Nat × Nat × Nat))
    (hcut : ∀ c ∈ cut, d c % Conv.P = 0)
    (hbk : ∀ e ∈ ps, (d (mem e.2.1 0) + d (mem e.2.1 e.2.2)) % Conv.P = 0) :
    Masks.cutRel (Masks.shift x oH d) cut = Masks.cutRel x cut ∧
      Masks.bucketRel (Masks.shift x oH d) mem ps = Masks.bucketRel x mem ps ∧
      ∀ c, decide ((Masks.shift x oH d).val oH c < Conv.P) = decide (x.val oH c < Conv.P) :=
  Masks.hiding_releases x oH d h cut mem ps hcut hbk

/-- **P-CUT (h)** [K]: masks taken one after the other are pairwise distinct and leave the pool. -/
theorem s10_pcut_h_takes (k : Nat) (p p' : Conv.MaskPool) (ms : List Conv.WordMask) (hd : p.Distinct)
    (h : Conv.MaskPool.takes k p = some (ms, p')) :
    ms.Nodup ∧ (∀ m ∈ ms, m ∉ p'.words) ∧ p'.Distinct ∧ p.words = ms ++ p'.words :=
  Conv.MaskPool.takes_distinct k p p' ms hd h

/-- **P-W2F (a)** [M; hyp: `WordLoaded`]: two honest parties with a consistent mask end with
u mod p in the field. -/
theorem s10_pw2f_honest (E : Env) (n0 f0 : Nat) (u : BoolH) (m : Conv.WordMask) (hW : Conv.WordLoaded E)
    (σA σB : Store) (I : Ideal) (ub wb : Bits) (fv : F)
    (hu : I.bools u.id = some ub) (hm : I.bools m.bits.id = some wb) (hlu : ub.length = 255) (hlw : wb.length = 255)
    (hf : I.fields m.field.id = some fv) (hcons : Conv.natOf wb = fv.val)
    (hf0 : m.field.id ≠ f0) (hf1 : m.field.id ≠ f0 + 1) :
    (jointRun E (Convert.wordToField n0 f0 u m) (Convert.wordToField n0 f0 u m) σA σB I).result = some (⟨f0 + 1⟩, ⟨f0 + 1⟩) ∧
      (jointRun E (Convert.wordToField n0 f0 u m) (Convert.wordToField n0 f0 u m) σA σB I).ideal.fields (f0 + 1) =
        some (TlsMpc.FieldDag.ofNat (Conv.natOf ub)) :=
  Convert.w2f_honest E n0 f0 u m hW σA σB I ub wb fv hu hm hlu hlw hf hcons hf0 hf1

/-- **T3 for word to field** [M; hyp: `WordLoaded`]: the adversary sees c and its re-comparison. -/
theorem s10_pw2f_disclosure (E : Env) (me : Party) (adv : Adversary) (n0 f0 : Nat) (u : BoolH) (m : Conv.WordMask)
    (hW : Conv.WordLoaded E) (σ : Store) (I : Ideal) (vD : List Release) (ub wb : Bits)
    (hu : I.bools u.id = some ub) (hm : I.bools m.bits.id = some wb) (hlu : ub.length = 255) (hlw : wb.length = 255) :
    (withAdv E me adv (Convert.wordToField n0 f0 u m) σ I vD).viewD <+:
      [⟨Label.maskedWord, .bits (Conv.intoFieldEval (ub ++ wb))⟩,
       ⟨Label.maskedWord, .bytes (le 32 (Conv.natOf (Conv.intoFieldEval (ub ++ wb))))⟩] :=
  Convert.w2f_disclosure E me adv n0 f0 u m hW σ I vD ub wb hu hm hlu hlw

/-- **P-W2F (b)** [K] (plan 7.0's form): for any two words the opened values correspond under a
bijection of the mask. -/
theorem s10_pw2f_hides (u u' : Nat) :
    ∃ σ : Nat → Nat, (∀ r < Conv.P, σ r < Conv.P) ∧ (∃ τ : Nat → Nat, ∀ r < Conv.P, τ (σ r) = r) ∧
      ∀ r < Conv.P, Convert.w2fOpen u r = Convert.w2fOpen u' (σ r) :=
  Convert.w2f_hides u u'

/-- **P-F2W (a)** [M; hyp: `WordLoaded`, `ProgsLoaded`]: two honest parties end with the word of
v's canonical value. -/
theorem s10_pf2w_honest (E : Env) (n0 f0 : Nat) (v : FieldH) (m : Conv.WordMask) (hW : Conv.WordLoaded E)
    (hP : Conv.ProgsLoaded E) (σA σB : Store) (I : Ideal) (vv fv : F) (wb : Bits)
    (hv : I.fields v.id = some vv) (hf : I.fields m.field.id = some fv) (hm : I.bools m.bits.id = some wb)
    (hlw : wb.length = 255) (hcons : Conv.natOf wb = fv.val) (hb0 : m.bits.id ≠ n0) (hb2 : m.bits.id ≠ n0 + 2) :
    (jointRun E (Convert.fieldToWord n0 f0 v m) (Convert.fieldToWord n0 f0 v m) σA σB I).result = some (⟨n0 + 2⟩, ⟨n0 + 2⟩) ∧
      (jointRun E (Convert.fieldToWord n0 f0 v m) (Convert.fieldToWord n0 f0 v m) σA σB I).ideal.bools (n0 + 2) =
        some (Conv.word vv.val) :=
  Convert.f2w_honest E n0 f0 v m hW hP σA σB I vv fv wb hv hf hm hlw hcons hb0 hb2

/-- **T3 for field to word** [M; hyp: `ProgsLoaded`]: the adversary sees the program's empty
openings, c = v − f, and its re-comparison. -/
theorem s10_pf2w_disclosure (E : Env) (me : Party) (adv : Adversary) (n0 f0 : Nat) (v : FieldH) (m : Conv.WordMask)
    (hP : Conv.ProgsLoaded E) (σ : Store) (I : Ideal) (vD : List Release) (vv fv : F)
    (hv : I.fields v.id = some vv) (hf : I.fields m.field.id = some fv) :
    (withAdv E me adv (Convert.fieldToWord n0 f0 v m) σ I vD).viewD <+:
      [⟨Label.maskedFieldValue, .elems []⟩, ⟨Label.maskedFieldValue, .elems [vv - fv]⟩,
       ⟨Label.maskedFieldValue, .bytes (le 32 (vv - fv).val)⟩] :=
  Convert.f2w_disclosure E me adv n0 f0 v m hP σ I vD vv fv hv hf

/-- **P-F2W (b)** [K]: f ↦ v − f is a bijection of F. -/
theorem s10_pf2w_hides (vv : F) : (∀ f f' : F, vv - f = vv - f' → f = f') ∧ ∀ f : F, vv - (vv - f) = f :=
  Convert.f2w_hides vv

/-- **P-B2F (a), (b)** [K]: for a consistent pair the result is x's bit; ρ ↦ x ⊕ ρ is a bijection. -/
theorem s10_pb2f (x ρ : Bool) :
    ((if (x ^^ ρ) then TlsMpc.FieldDag.ofNat 1 - TlsMpc.X25519.bitValue ρ else TlsMpc.X25519.bitValue ρ - TlsMpc.FieldDag.ofNat 0) =
      TlsMpc.X25519.bitValue x) ∧ (∀ ρ ρ' : Bool, (x ^^ ρ) = (x ^^ ρ') → ρ = ρ') :=
  ⟨Convert.b2f_value x ρ, (Convert.b2f_hides x).1⟩

/-- **T3 for bits to field** [M]: at most one release, `maskedBit`: the xor output. -/
theorem s10_pb2f_disclosure (E : Env) (me : Party) (adv : Adversary) (n0 f0 : Nat) (x : BoolH) (ps : List Conv.BitPair)
    (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv (Convert.bitsToField n0 f0 x ps) σ I vD).viewD <+:
      [⟨Label.maskedBit, .bits (Contacts.openedAfter E (Convert.b2fBlock n0 x ps) ⟨n0 + 3⟩ I)⟩] :=
  Convert.b2f_disclosure E me adv n0 f0 x ps σ I vD

/-- **P-BITS (a)** [K; hyp: `FieldInverse`]: the checks open to 0 iff every input is 0 or 1. -/
theorem s10_pbits_checks (hinv : TlsMpc.FieldDag.V3.FieldInverse) (cs : List F) :
    (cs.map fun c => c * (c - TlsMpc.FieldDag.ofNat 1)).all (· == 0) = true ↔
      ∀ c ∈ cs, c = 0 ∨ c = TlsMpc.FieldDag.ofNat 1 :=
  Convert.bits_checks_zero_iff hinv cs

/-- **P-BITS (b)** [K]: honest inputs give the bits of the XOR. -/
theorem s10_pbits_xor (a b : Bits) :
    (List.zipWith (fun x y => Conv.bitXorValue (TlsMpc.X25519.bitValue x) (TlsMpc.X25519.bitValue y)) a b) =
      (List.zipWith (· ^^ ·) a b).map TlsMpc.X25519.bitValue :=
  Convert.bits_xor a b

/-- **T3 for the masked quotient** [M]: the adversary sees z·m and the zero flag only. -/
theorem s10_pinv_disclosure (E : Env) (me : Party) (adv : Adversary) (f0 slot : Nat) (x z : FieldH)
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient) (σ : Store) (I : Ideal)
    (vD : List Release) (xv zv : F) (hx : I.fields x.id = some xv) (hz : I.fields z.id = some zv)
    (hfx : x.id ≠ f0 ∧ x.id ≠ f0 + 1 ∧ x.id ≠ f0 + 2) (hfz : z.id ≠ f0 ∧ z.id ≠ f0 + 1 ∧ z.id ≠ f0 + 2) :
    ∃ mv : F, (withAdv E me adv (Inversion.quotientScript f0 slot x z) σ I vD).viewD <+:
      [⟨Label.maskedDenominator, .elems [zv * mv]⟩,
       ⟨Label.maskedDenominator, .elems [if zv * mv = 0 then TlsMpc.FieldDag.ofNat 1 else TlsMpc.FieldDag.ofNat 0]⟩] :=
  Inversion.quotient_disclosure E me adv f0 slot x z hq σ I vD xv zv hx hz hfx hfz

/-- **P-INV (a), run level** [M; hyp: `FieldInverse`]: two honest parties with a nonzero mask end
with x·z⁻¹ and the flag "z = 0". -/
theorem s10_pinv_honest (hinv : TlsMpc.FieldDag.V3.FieldInverse) (E : Env)
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
    (σA σB : Store) (I : Ideal) (f0 slot : Nat) (x z : FieldH) (xv zv mA mB : F)
    (hx : I.fields x.id = some xv) (hz : I.fields z.id = some zv)
    (hfx : x.id ≠ f0 ∧ x.id ≠ f0 + 1 ∧ x.id ≠ f0 + 2) (hfz : z.id ≠ f0 ∧ z.id ≠ f0 + 1 ∧ z.id ≠ f0 + 2)
    (hA : σA.elems slot = [mA]) (hB : σB.elems slot = [mB]) (hm : mA + mB ≠ 0) :
    (jointRun E (Inversion.quotientScript f0 slot x z) (Inversion.quotientScript f0 slot x z) σA σB I).result =
      some ((⟨f0 + 3⟩, decide (zv = 0)), (⟨f0 + 3⟩, decide (zv = 0))) ∧
    (jointRun E (Inversion.quotientScript f0 slot x z) (Inversion.quotientScript f0 slot x z) σA σB I).ideal.fields (f0 + 3) =
      some (xv * TlsMpc.FieldDag.inverse zv) :=
  Inversion.quotient_honest hinv E hq σA σB I f0 slot x z xv zv mA mB hx hz hfx hfz hA hB hm

/-- **Op 55 (T3 in the reveal list's vocabulary)** [M]: every release is the accepted byte or a
masked bit. -/
theorem s10_account_open_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (a : Account.State) (n f : Nat) (pool : Conv.MaskPool) (hinted : Bool) (version check ct : Contacts.B8) :
    ∀ r ∈ (withAdv E me adv (Account.openStep a n f pool hinted version check ct) σ I vD).viewD,
      ∃ k ∈ Account.openKinds55, r.label = Label.ofKind k :=
  Account.openStep_viewD_kinds E me adv σ I vD a n f pool hinted version check ct

/-- **Op 55's swap bits** [K]: the `swap-bits` circuit's output k is the swap bit of ladder step
k + 2 (`X25519Fast.swapBitSpec`). -/
theorem s10_swapBits_spec (v : Bits) :
    Conv.swapBitsEval v = (List.range 252).map fun k => X25519Fast.swapBitSpec (fun i => v.getD i false) (k + 2) :=
  Account.swapBits_spec v

/-- **The S10 flows declare their kinds** [M] (`Reveals`, on every branch). -/
theorem s10_flows_reveal :
    (∀ hash me nonce value dom n, Reveals Random.jointKinds (Random.challenge hash me nonce value dom n)) ∧
    (∀ p b f hash me s, Reveals Masks.generateKinds (Masks.generate p b f hash me s)) ∧
    (∀ n0 f0 u m, Reveals Convert.w2fKinds (Convert.wordToField n0 f0 u m)) ∧
    (∀ n0 f0 v m, Reveals Convert.f2wKinds (Convert.fieldToWord n0 f0 v m)) ∧
    (∀ n0 f0 x ps, Reveals Convert.b2fKinds (Convert.bitsToField n0 f0 x ps)) ∧
    (∀ f0 n slot, Reveals Convert.bitsKinds (Convert.sharedBits f0 n slot)) ∧
    (∀ f0 slot x z, Reveals Inversion.inversionKinds (Inversion.quotientScript f0 slot x z)) ∧
    (∀ a n f pool hinted version check ct,
      Reveals Account.openKinds55 (Account.openStep a n f pool hinted version check ct)) :=
  Registry.s10_flows_reveal

/-- **The challenge is well formed** [K] (the shell's `check` accepts it in every context). -/
theorem s10_challenge_wf (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonce value : Nat)
    (domain : Bytes) (n : Nat) (c : Ctx) : WF sigs c (Random.challenge hash me nonce value domain n) :=
  Random.challenge_wf sigs hash me nonce value domain n c

/-- **The masked quotient is well formed** [K]: from any context where x and z are live, the five
field ids from `f0` fresh and `field-quotient` loaded, the shell's `check` accepts every
instruction on every branch. -/
theorem s10_quotient_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 slot : Nat) (x z : FieldH)
    (hp : c.progs Inversion.quotientName = some (ProgSig.ofProgram TlsMpc.FieldDag.V3.quotient))
    (hx : (c.field? x).isSome) (hz : (c.field? z).isSome)
    (hfx : x.id ≠ f0 ∧ x.id ≠ f0 + 1 ∧ x.id ≠ f0 + 2) (hfz : z.id ≠ f0 ∧ z.id ≠ f0 + 1 ∧ z.id ≠ f0 + 2)
    (hfresh : ∀ k < 5, f0 + k ∉ c.seenF) :
    WF sigs c (Inversion.quotientScript f0 slot x z) :=
  Inversion.quotient_wf sigs c f0 slot x z hp hx hz hfx hfz hfresh

/-! #### 7b (continued). P-CUT at the level of whole runs of `Masks.generate` (S10 follow-up)

`Run.Agree o o'` (`Flows/RunAgree.lean`): two runs with the same views of BOTH parties, the same
trace, replies and result. `Masks.HonestStore p s σ r`: the honest party's store holds the
candidates `r` (canonical), as bits, elements and coins, and 32-byte challenge randomness.
`Masks.Holds p b f I v x`: the engines hold the candidates `x`. -/

/-- **P-CUT (c), composed with the model** [M; hyp: `WordLoaded`, `ProgsLoaded`]: against any
adversary, two runs of `generate` whose honest stores hold candidates `r`, `r'` (same challenge
randomness) agree, when for the challenges the first run reaches `r' = r` on the cut, every
bucket pair has the same sum mod p, and each bit block's reference is at least 32 in both or in
neither. -/
theorem s10_pcut_c_agree (E : Env) (me : Party) (adv : Adversary) (p : Masks.Params) (b f : Nat)
    (hh : ∀ m, (E.hash m).length = 32) (hW : Conv.WordLoaded E) (hP : Conv.ProgsLoaded E)
    (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Masks.Slots) (σ σ' : Store) (I : Ideal) (vD : List Release)
    (r r' : Nat → Nat) (hσ : Masks.HonestStore p s σ r) (hσ' : Masks.HonestStore p s σ' r')
    (hbytes : σ'.bytes = σ.bytes)
    (hcut : ∀ π₁, (withAdv E me adv (Masks.cutChallenge p b f E.hash me s) σ I vD).result = some π₁ →
      ∀ c ∈ Masks.cutOf p π₁, r' c = r c)
    (hbk : ∀ π₁ π₂, (withAdv E me adv (Masks.bucketChallenge p b f E.hash me s) σ I vD).result = some (π₁, π₂) →
      (∀ e ∈ Masks.pairs p, (r' (Masks.member p π₁ π₂ e.2.1 0) + r' (Masks.member p π₁ π₂ e.2.1 e.2.2)) % Conv.P =
        (r (Masks.member p π₁ π₂ e.2.1 0) + r (Masks.member p π₁ π₂ e.2.1 e.2.2)) % Conv.P) ∧
      (∀ j, j < p.bits → (32 ≤ r' (Masks.refOf p π₁ π₂ j) ↔ 32 ≤ r (Masks.refOf p π₁ π₂ j)))) :
    Run.Agree (fun _ _ _ _ _ => True) (withAdv E me adv (Masks.generate p b f E.hash me s) σ I vD)
      (withAdv E me adv (Masks.generate p b f E.hash me s) σ' I vD) :=
  Masks.generate_agree E me adv p b f hh hW hP hM hbits s σ σ' I vD r r' hσ hσ' hbytes hcut hbk

/-- **P-CUT (c) in plan 7.0's form: `generate_hides`** [M; hyp: `WordLoaded`, `ProgsLoaded`]:
against any adversary, the adversary's view of a run of `generate` with honest candidates `r`,
together with the honest kept references moved by `δ` (`Masks.moveRef`), equals its view of the run
with the re-randomised candidates `reRand π δ r` together with their kept references; π are the
challenges of r's run. The form `proofs/` `hiding_of_bijection` consumes (view := `hideView`,
s := δ, s′ := 0, σ := `reRand π δ`; bijection: `s10_reRand_bijection`). -/
theorem s10_generate_hides (E : Env) (me : Party) (adv : Adversary) (p : Masks.Params) (b f : Nat)
    (hh : ∀ m, (E.hash m).length = 32) (hW : Conv.WordLoaded E) (hP : Conv.ProgsLoaded E)
    (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Masks.Slots)
    (hslots : s.elems < s.coins ∨ s.coins + p.M ≤ s.elems) (σ : Store) (h32 : Masks.Bytes32 s σ) (I : Ideal)
    (vD : List Release) (δ : Nat → Nat) (r : Nat → Nat) (hr : ∀ c, c < p.M → r c < Conv.P) :
    Masks.hideView E me adv p b f s σ I vD δ r =
      Masks.hideView E me adv p b f s σ I vD (fun _ => 0)
        (Masks.reRand p (Masks.permsOf E me adv p b f s (Masks.setCands p s σ r) I vD) δ r) :=
  Masks.generate_hides E me adv p b f hh hW hP hM hbits s hslots σ h32 I vD δ r hr

/-- **The re-randomisation is a bijection of the canonical candidate vectors** [M]: it yields
canonical values, and `reRand (negShift δ)`, for the challenges of the re-randomised run, undoes
it. -/
theorem s10_reRand_bijection (E : Env) (me : Party) (adv : Adversary) (p : Masks.Params) (b f : Nat)
    (hh : ∀ m, (E.hash m).length = 32) (hW : Conv.WordLoaded E) (hP : Conv.ProgsLoaded E)
    (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Masks.Slots)
    (hslots : s.elems < s.coins ∨ s.coins + p.M ≤ s.elems) (σ : Store) (h32 : Masks.Bytes32 s σ) (I : Ideal)
    (vD : List Release) (δ : Nat → Nat) (r : Nat → Nat) (hr : ∀ c, c < p.M → r c < Conv.P) :
    (∀ c, c < p.M →
      Masks.reRand p (Masks.permsOf E me adv p b f s (Masks.setCands p s σ r) I vD) δ r c < Conv.P) ∧
    (∀ c, c < p.M →
      Masks.reRand p (Masks.permsOf E me adv p b f s
          (Masks.setCands p s σ (Masks.reRand p (Masks.permsOf E me adv p b f s (Masks.setCands p s σ r) I vD) δ r))
          I vD) (Masks.negShift p δ)
        (Masks.reRand p (Masks.permsOf E me adv p b f s (Masks.setCands p s σ r) I vD) δ r) c = r c) :=
  ⟨fun c hc => Masks.reRand_lt _ δ r c (hr c hc),
    fun c hc => Masks.reRand_inverse E me adv p b f hh hW hP hM hbits s hslots σ h32 I vD δ r hr c hc⟩

/-- **`moveRef`, the move of a kept reference** [K]: canonical, undone by `negAmt`, and for a bit
block it keeps "at least 32" (the bit-block flag under a shift). -/
theorem s10_moveRef (b : Bool) (δ v : Nat) (hv : v < Conv.P) :
    Masks.moveRef b δ v < Conv.P ∧ Masks.moveRef b (Masks.negAmt b δ) (Masks.moveRef b δ v) = v ∧
      Masks.moveRef b (Masks.negAmt b (Masks.negAmt b δ)) v = Masks.moveRef b δ v ∧
      (32 ≤ Masks.moveRef true δ v ↔ 32 ≤ v) :=
  ⟨Masks.moveRef_lt b δ v hv, Masks.moveRef_neg b δ v hv, Masks.moveRef_negneg b δ v, Masks.moveRef_32 δ v⟩

/-- **Any target reference is reached** [K]: any canonical value for a word mask; any value in
[32, p) for a bit block. -/
theorem s10_moveRef_reach (v t : Nat) (hv : v < Conv.P) (ht : t < Conv.P) :
    Masks.moveRef false ((t + (Conv.P - v)) % Conv.P) v = t ∧
      (32 ≤ v → 32 ≤ t → Masks.moveRef true ((t - 32 + (Conv.P - 32 - (v - 32))) % (Conv.P - 32)) v = t) :=
  ⟨Masks.moveRef_reach_word v t hv ht, fun h1 h2 => Masks.moveRef_reach_bits v t hv h1 ht h2⟩

/-- **P-CUT (f), (g), run level** [M; hyp: `WordLoaded`, `ProgsLoaded`, `FieldInverse`]: against any
adversary, if `finishPhase` returns a pool from a state holding the candidates `x`, every kept
reference of both owners is canonical (at least 32 for bit blocks), the pool is
`maskList`/`pairList`, each word mask's handles hold `modAdd` of the references' words and the sum
of their elements, and each bit pair of a bit block whose references have error 0 holds the XOR of
the references' bits in both engines. -/
theorem s10_pcut_fg_run (E : Env) (me : Party) (adv : Adversary) (p : Masks.Params) (b f : Nat)
    (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hW : Conv.WordLoaded E) (hP : Conv.ProgsLoaded E) (s : Masks.Slots)
    (π₁ π₂ : List Nat) (σ : Store) (I : Ideal) (vD : List Release) (v : Bits) (x : Masks.Vals)
    (pool : Conv.MaskPool) (h : Masks.Holds p b f I v x) (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M)
    (hbits : p.bits ≤ p.N)
    (hres : (withAdv E me adv (Masks.finishPhase p b f s π₁ π₂) σ I vD).result = some pool) :
    pool = ⟨Masks.maskList p b f, Masks.pairList p b f⟩ ∧
    (∀ j, j < p.N → x.val 0 (Masks.refOf p π₁ π₂ j) < Conv.P ∧ x.val 1 (Masks.refOf p π₁ π₂ j) < Conv.P ∧
      (j < p.bits → 32 ≤ x.val 0 (Masks.refOf p π₁ π₂ j) ∧ 32 ≤ x.val 1 (Masks.refOf p π₁ π₂ j))) ∧
    (∀ j, j < p.words →
      (withAdv E me adv (Masks.finishPhase p b f s π₁ π₂) σ I vD).ideal.bools (b + 12 + j) =
        some (Conv.word (Conv.addModSpec (x.val 0 (Masks.refOf p π₁ π₂ (p.bits + j)))
          (x.val 1 (Masks.refOf p π₁ π₂ (p.bits + j))))) ∧
      (withAdv E me adv (Masks.finishPhase p b f s π₁ π₂) σ I vD).ideal.fields (Masks.maskBase p f + j) =
        some (x.elem 0 (Masks.refOf p π₁ π₂ (p.bits + j)) + x.elem 1 (Masks.refOf p π₁ π₂ (p.bits + j)))) ∧
    (∀ j, j < p.bits → x.err 0 (Masks.refOf p π₁ π₂ j) = 0 → x.err 1 (Masks.refOf p π₁ π₂ j) = 0 →
      ∀ i, i < Masks.W →
      (withAdv E me adv (Masks.finishPhase p b f s π₁ π₂) σ I vD).ideal.bools (Masks.bitBase p b + j * Masks.W + i) =
        some [(x.bits 0 (Masks.refOf p π₁ π₂ j)).getD i false ^^ (x.bits 1 (Masks.refOf p π₁ π₂ j)).getD i false] ∧
      (withAdv E me adv (Masks.finishPhase p b f s π₁ π₂) σ I vD).ideal.fields
          (Masks.xorH p f (j * Masks.W + i)).id =
        some (TlsMpc.X25519.bitValue
          ((x.bits 0 (Masks.refOf p π₁ π₂ j)).getD i false ^^ (x.bits 1 (Masks.refOf p π₁ π₂ j)).getD i false))) :=
  Masks.finishPhase_sound E me adv p b f hinv hW hP s π₁ π₂ σ I vD v x pool h hπ₁ hM hbits hres

/-- **A mask from two error-free canonical references is consistent** [K]: val(w) = f =
(val_A + val_B) mod p. -/
theorem s10_mask_consistent (x : Masks.Vals) (cA cB : Nat) (hA : x.val 0 cA < Conv.P) (hB : x.val 1 cB < Conv.P)
    (eA : x.err 0 cA = 0) (eB : x.err 1 cB = 0) :
    Conv.natOf (Conv.word (Conv.addModSpec (x.val 0 cA) (x.val 1 cB))) = (x.elem 0 cA + x.elem 1 cB).val ∧
      (x.elem 0 cA + x.elem 1 cB).val = (x.val 0 cA + x.val 1 cB) % Conv.P :=
  Masks.mask_consistent x cA cB hA hB eA eB

/-- **P-CUT (a) for a whole honest run, deployed profiles** [M; hyp: `WordLoaded`, `ProgsLoaded`]:
two honest parties running `generate` for `profile N bits` both return the pool, keep their stores,
and every word mask is a Boolean word and a field element of the same value `(rA c + rB c) mod p`,
every bit pair the XOR of the references' bits in both engines. [hyp: the challenges' commitments
differ, their expansions succeed, the bit blocks' references are at least 32.] -/
theorem s10_pcut_a_run (E : Env) (p : Masks.Params) (b f : Nat) (hh : ∀ m, (E.hash m).length = 32)
    (hW : Conv.WordLoaded E) (hP : Conv.ProgsLoaded E) (N nbits : Nat) (hprof : Masks.profile N nbits = some p)
    (sA sB : Masks.Slots) (σA σB : Store) (I : Ideal) (rA rB : Nat → Nat)
    (hA : Masks.HonestStore p sA σA rA) (hB : Masks.HonestStore p sB σB rB)
    (hc1 : E.hash (commitFrame Random.tag .a (σA.bytes sA.cutNonce) (σA.bytes sA.cutValue)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes sB.cutNonce) (σB.bytes sB.cutValue)))
    (hc2 : E.hash (commitFrame Random.tag .a (σA.bytes sA.bucketNonce) (σA.bytes sA.bucketValue)) ≠
      E.hash (commitFrame Random.tag .b (σB.bytes sB.bucketNonce) (σB.bytes sB.bucketValue)))
    (π₁ π₂ : List Nat)
    (hπ₁ : Random.permOf E.hash (Masks.domain p "cut")
      (Random.xorBytes (σA.bytes sA.cutValue) (σB.bytes sB.cutValue)) p.M = some π₁)
    (hπ₂ : Random.permOf E.hash (Masks.domain p "bucket")
      (Random.xorBytes (σA.bytes sA.bucketValue) (σB.bytes sB.bucketValue)) p.K = some π₂)
    (h32 : ∀ j, j < p.bits → 32 ≤ rA (Masks.refOf p π₁ π₂ j) ∧ 32 ≤ rB (Masks.refOf p π₁ π₂ j)) :
    ∃ J, Run.JRet (jointRun E (Masks.generate p b f E.hash .a sA) (Masks.generate p b f E.hash .b sB) σA σB I)
        ⟨Masks.maskList p b f, Masks.pairList p b f⟩ ⟨Masks.maskList p b f, Masks.pairList p b f⟩ J σA σB ∧
      (∀ j, j < p.words →
        J.bools (b + 12 + j) = some (Conv.word
          ((rA (Masks.refOf p π₁ π₂ (p.bits + j)) + rB (Masks.refOf p π₁ π₂ (p.bits + j))) % Conv.P)) ∧
        J.fields (Masks.maskBase p f + j) = some (TlsMpc.FieldDag.ofNat
          ((rA (Masks.refOf p π₁ π₂ (p.bits + j)) + rB (Masks.refOf p π₁ π₂ (p.bits + j))) % Conv.P))) ∧
      (∀ j, j < p.bits → ∀ i, i < Masks.W →
        J.bools (Masks.bitBase p b + j * Masks.W + i) =
          some [(Conv.word (rA (Masks.refOf p π₁ π₂ j))).getD i false ^^
            (Conv.word (rB (Masks.refOf p π₁ π₂ j))).getD i false] ∧
        J.fields (Masks.xorH p f (j * Masks.W + i)).id = some (TlsMpc.X25519.bitValue
          ((Conv.word (rA (Masks.refOf p π₁ π₂ j))).getD i false ^^
            (Conv.word (rB (Masks.refOf p π₁ π₂ j))).getD i false))) :=
  Masks.generate_honest_profile E p b f hh hW hP N nbits hprof sA sB σA σB I rA rB hA hB hc1 hc2 π₁ π₂ hπ₁ hπ₂ h32

/-- **`generate` is well formed** [K]: from a context where the Boolean ids from `b` and the field
ids from `f` were never defined, with the circuits' and programs' signatures and the widths within
the shell's limit (`Sizes`; `Masks.profile_sizes`: every deployed profile), the shell's `check`
accepts every instruction on every branch. -/
theorem s10_generate_wf (sigs : Bytes → Option Sig) (ws : Masks.WordSigs sigs) (p : Masks.Params)
    (sz : Masks.Sizes p) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Masks.Slots) (c : Ctx)
    (hfb : Contacts.Fresh c b) (hff : ∀ j, f ≤ j → j ∉ c.seenF) (hp : Masks.ProgSigs c) :
    WF sigs c (Masks.generate p b f hash me s) :=
  Masks.generate_wf sigs ws p sz b f hash me s c hfb hff hp

/-- **The deployed profiles are within the shell's limits** [K]. -/
theorem s10_profile_sizes (N bits : Nat) (p : Masks.Params) (h : Masks.profile N bits = some p) : Masks.Sizes p :=
  Masks.profile_sizes N bits p h

/-- **`sharedBits` is well formed** [K]. -/
theorem s10_sharedBits_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 n slot : Nat) (hn : 0 < n)
    (hw : 2 * n ≤ maxWidth) (hfresh : ∀ j, f0 ≤ j → j < f0 + 5 * n → j ∉ c.seenF)
    (hp1 : c.progs Conv.bitCheckName = some ⟨1, 0, [.pub]⟩) (hp2 : c.progs Conv.bitXorName = some ⟨2, 0, [.never]⟩) :
    WF sigs c (Convert.sharedBits f0 n slot) :=
  Convert.sharedBits_wf sigs c f0 n slot hn hw hfresh hp1 hp2

/-- **The counting model's hypotheses, for any run of `generate` that returns** [M; hyp:
`WordLoaded`, `ProgsLoaded`, `FieldInverse`] (`Flows/MasksModel.lean`): the other party's candidates
are its choice from its view BEFORE the run (so the bad set is fixed before the challenges); every
cut candidate of both owners is canonical with error 0 (d); every bucket pair passes `bucketOk` (e);
every kept reference is canonical, at least 32 for a bit block (f); the pool is
`maskList`/`pairList`. (The masks' values in the final state: `Masks.generate_sound`'s last two
conjuncts, not restated; with `s10_mask_consistent`.) -/
theorem s10_generate_sound (E : Env) (me : Party) (adv : Adversary) (p : Masks.Params) (b f : Nat)
    (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hh : ∀ m, (E.hash m).length = 32) (hW : Conv.WordLoaded E)
    (hP : Conv.ProgsLoaded E) (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Masks.Slots) (σ : Store) (I : Ideal)
    (vD : List Release) (r : Nat → Nat) (hσ : Masks.HonestStore p s σ r) (pool : Conv.MaskPool)
    (hres : (withAdv E me adv (Masks.generate p b f E.hash me s) σ I vD).result = some pool) :
    ∃ (pb pe : PeerPart) (π₁ π₂ : List Nat),
      adv.act vD (.boolInputBoth ⟨b⟩ ⟨b + 1⟩ (p.M * Masks.W) false true ()) = some pb ∧
      adv.act vD (.fieldInput ((List.range p.M).map (Masks.fOf p f 0)) ((List.range p.M).map (Masks.fOf p f 1))
        .elements true ()) = some pe ∧
      Masks.Perms p π₁ π₂ ∧
      (∀ o ∈ Masks.owners, ∀ c ∈ Masks.cutOf p π₁,
        (Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).val o c < Conv.P ∧
        (Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).err o c = 0) ∧
      (∀ e ∈ Masks.pairs p, Masks.bucketOk
        ((Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).val e.1
          (Masks.member p π₁ π₂ e.2.1 0))
        ((Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).val e.1
          (Masks.member p π₁ π₂ e.2.1 e.2.2))
        ((Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).elem e.1
          (Masks.member p π₁ π₂ e.2.1 0))
        ((Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).elem e.1
          (Masks.member p π₁ π₂ e.2.1 e.2.2)) = true) ∧
      (∀ j, j < p.N →
        (Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 0 (Masks.refOf p π₁ π₂ j) <
          Conv.P ∧
        (Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 1 (Masks.refOf p π₁ π₂ j) <
          Conv.P ∧
        (j < p.bits →
          32 ≤ (Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 0
            (Masks.refOf p π₁ π₂ j) ∧
          32 ≤ (Masks.inVals p me r (Masks.inBundle me (σ.bits s.bits) pb.bits) pe.elems).val 1
            (Masks.refOf p π₁ π₂ j))) ∧
      pool = ⟨Masks.maskList p b f, Masks.pairList p b f⟩ := by
  obtain ⟨pb, pe, π₁, π₂, h1, h2, h3, h4, h5, h6, h7, -, -⟩ :=
    Masks.generate_sound E me adv p b f hinv hh hW hP hM hbits s σ I vD r hσ pool hres
  exact ⟨pb, pe, π₁, π₂, h1, h2, h3, h4, h5, h6, h7⟩

/-- **The model's rule in its own words** [K]: when every bucket pair passes and the reference is
canonical, a bucket member is good exactly when its reference is: no mixed bucket survives. -/
theorem s10_bucket_uniform (x : Masks.Vals) (hw : x.Wide) (p : Masks.Params) (π₁ π₂ : List Nat)
    (he : ∀ e ∈ Masks.pairs p, Masks.bucketOk (x.val e.1 (Masks.member p π₁ π₂ e.2.1 0))
      (x.val e.1 (Masks.member p π₁ π₂ e.2.1 e.2.2)) (x.elem e.1 (Masks.member p π₁ π₂ e.2.1 0))
      (x.elem e.1 (Masks.member p π₁ π₂ e.2.1 e.2.2)) = true)
    (e : Nat × Nat × Nat) (hmem : e ∈ Masks.pairs p) (hc : x.val e.1 (Masks.member p π₁ π₂ e.2.1 0) < Conv.P) :
    x.err e.1 (Masks.member p π₁ π₂ e.2.1 0) = 0 ↔ x.err e.1 (Masks.member p π₁ π₂ e.2.1 e.2.2) = 0 :=
  Masks.bucket_uniform x hw p π₁ π₂ he e hmem hc

/-- **The two challenge permutations as the model's one arrangement** [K]: `arrangement π₁ π₂`
(the cut, then the bucket slots in order) is a permutation of the candidates [0, M); its first K
entries are the cut; its entry K + B·j + k is member k of bucket j. (That it is uniform for uniform
π₁, π₂ is argued, not proved: section 8.) -/
theorem s10_arrangement (p : Masks.Params) (π₁ π₂ : List Nat) (h1 : π₁.Perm (List.range p.M))
    (h2 : π₂.Perm (List.range p.K)) :
    (Masks.arrangement p π₁ π₂).Perm (List.range p.M) ∧
      (Masks.arrangement p π₁ π₂).take p.K = Masks.cutOf p π₁ ∧
      ∀ j k, p.B * j + k < π₂.length →
        (Masks.arrangement p π₁ π₂).getD (p.K + (p.B * j + k)) 0 = Masks.member p π₁ π₂ j k :=
  ⟨Masks.arrangement_perm p π₁ π₂ h1 h2,
    Masks.arrangement_cut p π₁ π₂ (by rw [h1.length_eq, List.length_range]),
    fun j k h => Masks.arrangement_slot p π₁ π₂ (by rw [h1.length_eq, List.length_range]) j k h⟩

/-- **P-BITS (a), (b) at run level, against any adversary** [M; hyp: `ProgsLoaded`, `FieldInverse`]:
if `sharedBits` returns, it returns `bitsOuts`; every input of BOTH parties in the engines is 0 or 1;
and output `i` holds the field XOR of the two parties' inputs `i`. -/
theorem s10_pbits_run (E : Env) (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hP : Conv.ProgsLoaded E) (me : Party)
    (adv : Adversary) (f0 n slot : Nat) (σ : Store) (I : Ideal) (vD : List Release) (outs : List FieldH)
    (hres : (withAdv E me adv (Convert.sharedBits f0 n slot) σ I vD).result = some outs) :
    outs = Convert.bitsOuts f0 n ∧ ∃ pe : List F, pe.length = n ∧ (σ.elems slot).length = n ∧
      (∀ c ∈ σ.elems slot ++ pe, c = 0 ∨ c = TlsMpc.FieldDag.ofNat 1) ∧
      ∀ i, i < n → (withAdv E me adv (Convert.sharedBits f0 n slot) σ I vD).ideal.fields (f0 + 4 * n + i) =
        some (Conv.bitXorValue ((if me = .a then σ.elems slot else pe).getD i 0)
          ((if me = .a then pe else σ.elems slot).getD i 0)) :=
  Convert.sharedBits_sound E hinv hP me adv f0 n slot σ I vD outs hres

/-- **P-BITS (b), two honest parties** [M; hyp: `ProgsLoaded`]: with local bits `as`, `bs` as 0/1
coins, both return `bitsOuts`, keep their stores, and output `i` holds the field bit of
`as_i ⊕ bs_i`. -/
theorem s10_pbits_honest (E : Env) (hP : Conv.ProgsLoaded E) (f0 n slotA slotB : Nat) (σA σB : Store)
    (I : Ideal) (as bs : Bits) (hla : as.length = n) (hlb : bs.length = n)
    (hA : σA.elems slotA = as.map TlsMpc.X25519.bitValue) (hB : σB.elems slotB = bs.map TlsMpc.X25519.bitValue) :
    ∃ J, Run.JRet (jointRun E (Convert.sharedBits f0 n slotA) (Convert.sharedBits f0 n slotB) σA σB I)
        (Convert.bitsOuts f0 n) (Convert.bitsOuts f0 n) J σA σB ∧
      ∀ i, i < n → J.fields (f0 + 4 * n + i) =
        some (TlsMpc.X25519.bitValue (as.getD i false ^^ bs.getD i false)) :=
  Convert.sharedBits_honest E hP f0 n slotA slotB σA σB I as bs hla hlb hA hB

/-- **P-B2F (a) through `jointRun`, the whole bundle** [M; hyp: `WordLoaded`]: two honest parties
convert the bits `xb` behind `x` with consistent pairs (pair `i`: the Boolean bit `ρ_i` and the field
bit of `ρ_i`, on handles other than the script's own): both return `b2fOuts`, keep their stores, and
output `i` holds the field bit of `xb_i`. -/
theorem s10_pb2f_honest (E : Env) (hW : Conv.WordLoaded E) (n0 f0 : Nat) (x : BoolH) (ps : List Conv.BitPair)
    (σA σB : Store) (I : Ideal) (xb ρ : Bits) (hx : I.bools x.id = some xb) (hxl : xb.length = ps.length)
    (hρl : ρ.length = ps.length)
    (hbits : (ps.map (·.bit)).mapM (fun h => I.bools h.id) = some (ρ.map fun r => [r]))
    (hflds : ∀ i, i < ps.length →
      I.fields (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id = some (TlsMpc.X25519.bitValue (ρ.getD i false)))
    (hx0 : x.id ≠ n0)
    (hfid : ∀ i, i < ps.length → (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id ≠ f0 ∧
      (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id ≠ f0 + 1 ∧
      ∀ j, j < ps.length → (ps.getD i ⟨⟨0⟩, ⟨0⟩⟩).field.id ≠ f0 + 2 + j) :
    ∃ J, Run.JRet (jointRun E (Convert.bitsToField n0 f0 x ps) (Convert.bitsToField n0 f0 x ps) σA σB I)
        (Convert.b2fOuts f0 ps.length) (Convert.b2fOuts f0 ps.length) J σA σB ∧
      ∀ i, i < ps.length → J.fields (f0 + 2 + i) = some (TlsMpc.X25519.bitValue (xb.getD i false)) :=
  Convert.b2f_honest E hW n0 f0 x ps σA σB I xb ρ hx hxl hρl hbits hflds hx0 hfid

end FlowsS10

/-! ### 7c. Local arithmetic and the curve flows (stage S11; plan 7.1 P-SPLIT, P-OFFSET, P-HINT)

Status per entry: **M** (ideal model of `Engine/Model.lean`) or **K** (values, independent of the
model); hypotheses named `[hyp: …]`. `FieldInverse` (Fermat for p) is FieldDagV3's named
hypothesis (discharged in `proofs/`: `FieldBridge.toZMod_inverse`). H-QR (`Curve.TwoNonSquare`)
and Euler's criterion (`Curve.EulerCriterion`) are named hypotheses here, discharged in `proofs/`
by `two_not_square` and `euler_criterion` (with `Local.Field.pow_eq`). H-GROUP enters only as named
hypotheses of the liveness entries (`Curve.CompleteAddition` ← `edwards_complete`, `Curve.AddClosed` ←
`pointAddValue_is_group_add`, `Curve.ExtClosed` ← `extAddValue_is_group_add`,
`Curve.RecipientOnCurve` ← `recipient_on_curve`); otherwise the entries state the main-package
values the `proofs/` group-law theorems
(`pointAddValue_is_group_add`, `extAddValue_is_group_add`, `window_table`, `bitTable_entries`,
`offsetSum_scalar_mult`/`offsetSum_recoded`, `bitSum_is_x25519`, `prepareHinted_initial_point`,
`montQ_square_iff`, `liftPoint_valid_point`) are about. SECURITY_MAP: the curve kinds 91–95, 102.
Checked standalone in the S11 branch (the full closure needs more than 4 GB): standard axioms only. -/

section FlowsS11
open TlsMpc.Node.Engine TlsMpc.Node.Flows
open TlsMpc.FieldDag (F ofNat inverse)

/-- **`Local/Edwards` uses the programs' formulas** [K]: affine addition is
`EdwardsAffine.pointAddValue`, extended to affine is `EdwardsHinted.toAffineValue`, the Montgomery
map is `(1 + y)·(1 − y)⁻¹` (the form `offsetSum` outputs). -/
theorem s11_local_formulas (p q : TlsMpc.Node.Local.Edwards.Value) (e : TlsMpc.Node.Local.Edwards.ExtV) :
    TlsMpc.Node.Local.Edwards.add p q = TlsMpc.EdwardsAffine.pointAddValue p q ∧
    TlsMpc.Node.Local.Edwards.toAffine e = TlsMpc.EdwardsHinted.toAffineValue e ∧
    TlsMpc.Node.Local.Edwards.montU p = (ofNat 1 + p.2) * inverse (ofNat 1 - p.2) :=
  ⟨TlsMpc.Node.Local.Edwards.add_eq p q, TlsMpc.Node.Local.Edwards.toAffine_eq e, TlsMpc.Node.Local.Edwards.montU_eq p⟩

/-- **`xeddsa-recover` on a public input, locally** [K] (replaces `field_program.h` `evaluate_clear`):
the local evaluation is the program's expressions at that input. -/
theorem s11_recoverPublic (u : F) :
    TlsMpc.Node.Local.Edwards.recoverPublic u =
      TlsMpc.EstablishField.recover.map (TlsMpc.FieldDag.Expr.eval (fun _ => u)) :=
  TlsMpc.Node.Local.Edwards.recoverPublic_eq u

/-- **A local square root squares to its argument** [K]. -/
theorem s11_sqrt_sq (x r : F) (h : TlsMpc.Node.Local.Field.sqrt x = some r) : r * r = x :=
  TlsMpc.Node.Local.Field.sqrt_sq x r h

/-- **P-OFFSET (a): the recoding lemma** [K], about the flow's own `recode` (the C++ rule): for an
offset below 2^252 the 64 digits encode it exactly, lie in −8 … 8, and leave no carry. -/
theorem s11_recode64 (n : Nat) (hn : n < 2 ^ 252) :
    Curve.digitsValue (Curve.recode 0 n 64).1 = n ∧ (Curve.recode 0 n 64).2 = 0 ∧
      (Curve.recode 0 n 64).1.length = 64 ∧ ∀ d ∈ (Curve.recode 0 n 64).1, -8 ≤ d ∧ d ≤ 8 :=
  Curve.recode64_value n hn

/-- **P-OFFSET (a): the selected multiples** [K]: in any commutative group, the step's digits select
multiples summing to τ·R (`OffsetAgreement.table_sum_correct`). -/
theorem s11_step_tableSum {G : Type} [Lean.Grind.IntModule G] (R : G) (n : Nat) (hn : n < 2 ^ 252) :
    TlsMpc.OffsetAgreement.tableSum R 0 (Curve.recode 0 n 64).1 = (n : Int) • R :=
  Curve.step_tableSum R n hn

/-- **P-OFFSET (a): the step's program inputs** [K]: window `w`'s three inputs are the table entry
`entryAt w d` (x, y) and the sign, or the neutral element: what `proofs/` `offsetSum_recoded`
assumes. -/
theorem s11_stepIns_window (f0 : Nat) (st : Curve.OffsetState) (τ w : Nat) (hw : w < 64) :
    ((Curve.stepIns f0 st τ).drop (2 + 3 * w)).take 3 =
      (let d := (Curve.recode 0 τ 64).1.getD w 0
       if d = 0 then [⟨f0⟩, ⟨f0 + 1⟩, ⟨f0 + 1⟩]
       else [st.table.getD (Curve.entryAt w d) ⟨f0⟩, st.table.getD (Curve.entryAt w d + 1) ⟨f0⟩,
         if 0 < d then ⟨f0 + 1⟩ else ⟨f0 + 2⟩]) :=
  Curve.stepIns_window f0 st τ w hw

/-- **P-OFFSET (b) on the script's output** [K]: the ephemeral key a step returns is
`montU (K₀ + τ·B)` (a valid point): a function of the public K₀ and τ only. -/
theorem s11_ephemeralKey (key : TlsMpc.Node.Local.Edwards.Value) (τ : Nat) (u : F)
    (h : Curve.ephemeralKey key τ = some u) :
    u = TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add key
      (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
    TlsMpc.Node.Local.Edwards.isValid (TlsMpc.Node.Local.Edwards.add key
      (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) = true :=
  Curve.ephemeralKey_spec key τ u h

/-- **P-HINT (a): the order of the lift's openings** [K]: checks (all zero) before `w`, `w` before
`Z`. -/
theorem s11_lift_order (f0 : Nat) (s : Curve.LiftSlots) (us : List FieldH) (hn : us.length ≠ 0) :
    Curve.lift f0 s us = Contacts.seqs (Curve.liftBlock f0 s us) (Run.openFieldThen (Curve.liftChecks f0 us.length)
      Label.curveChecks (Curve.liftAfterChecks f0 s us)) ∧
    (∀ z, ¬ (z.length = 4 * us.length ∧ Curve.allZero z = true) → ∃ r, Curve.liftAfterChecks f0 s us z = .abort r) ∧
    (∀ z, z.length = 4 * us.length ∧ Curve.allZero z = true →
      Curve.liftAfterChecks f0 s us z = Run.openFieldThen (Curve.liftWs f0 us.length) Label.liftW (Curve.liftAfterW f0 s us)) ∧
    (∀ ws rs, ws.length = us.length → Curve.roots ws = some rs →
      Curve.liftAfterW f0 s us ws = Contacts.seqs (Curve.pointBlock f0 s us rs)
        (Run.openFieldThen (Curve.liftZs f0 us.length) Label.liftZ (Curve.liftAfterZ f0 us.length rs))) :=
  Curve.lift_order f0 s us hn

/-- **P-HINT (b), soundness** [K; hyp: `FieldInverse`]: a valid lift bit means `q` is a square. -/
theorem s11_lift_valid_sound (hinv : TlsMpc.FieldDag.V3.FieldInverse) (q r w : F) (b sel : Bool) (c : F)
    (hw : w = q * r * r * (ofNat 1 + TlsMpc.X25519.bitValue b)) (hr : r ≠ 0)
    (hroot : TlsMpc.Node.Local.Edwards.root w = some (sel, c)) (hvalid : (sel ^^ b) = true) : ∃ v, v * v = q :=
  Curve.lift_valid_sound hinv q r w b sel c hw hr hroot hvalid

/-- **The op 66 status reveals only curve membership** [K; hyp: `FieldInverse`, H-QR, Euler]: 255
exactly when `q(u) = u(u² + 486662u + 1)` is a nonzero square (with `proofs/` `montQ_square_iff`:
when `u ≠ 0` is the Montgomery coordinate of a curve point). -/
theorem s11_prepareStatus_iff (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hE : Curve.EulerCriterion)
    (hQR : Curve.TwoNonSquare) (u r w : F) (b sel : Bool) (c : F)
    (hw : w = u * (u * u + ofNat 486662 * u + ofNat 1) * r * r * (ofNat 1 + TlsMpc.X25519.bitValue b)) (hr : r ≠ 0)
    (hroot : w ≠ 0 → TlsMpc.Node.Local.Edwards.root w = some (sel, c)) :
    (TlsMpc.X25519.bitValue (sel ^^ b) == ofNat 1 && !(w == 0)) = true ↔
      (u * (u * u + ofNat 486662 * u + ofNat 1) ≠ 0 ∧ ∃ v, v * v = u * (u * u + ofNat 486662 * u + ofNat 1)) :=
  Curve.prepareStatus_iff hinv hE hQR u r w b sel c hw hr hroot

/-- **P-SPLIT (a), algebraic** [K; hyp: `FieldInverse`]: the agreement's quotient is the Montgomery
coordinate of `T_A + T_B`. -/
theorem s11_addU_montU (hinv : TlsMpc.FieldDag.V3.FieldInverse) (x1 y1 x2 y2 : F)
    (hden : ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) ≠ 0) :
    (ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) + ofNat 121666 * (x1 * x2 + y1 * y2)) *
      inverse (ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) - ofNat 121666 * (x1 * x2 + y1 * y2)) =
    TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add (x1, y1) (x2, y2)) :=
  Curve.addU_montU hinv x1 y1 x2 y2 hden

/-- **P-SPLIT (a), run level** [M; hyp: `FieldInverse`, the programs loaded]: two honest parties
end with `(den + num)/(den − num)` of their points (= `montU (T_A + T_B)` by `s11_addU_montU`). -/
theorem s11_splitAgree_honest (hinv : TlsMpc.FieldDag.V3.FieldInverse) (E : Env) (pOn pAdd : TlsMpc.FieldDag.V3.Program)
    (hOn : E.programs Curve.onCurveName = some pOn) (hAdd : E.programs Curve.addUName = some pAdd)
    (hOnC : Conv.Computes pOn 2 [.pub] (fun i => [TlsMpc.EdwardsShare.onCurve.eval i]))
    (hAddC : Conv.Computes pAdd 4 [.never, .never] (fun i => TlsMpc.EdwardsShare.addU.map (TlsMpc.FieldDag.Expr.eval i)))
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
    (σA σB : Store) (I : Ideal) (f0 tSlot maskSlot : Nat) (xA yA xB yB mA mB : F)
    (hA : σA.elems tSlot = [xA, yA]) (hB : σB.elems tSlot = [xB, yB])
    (hmA : σA.elems maskSlot = [mA]) (hmB : σB.elems maskSlot = [mB]) (hm : mA + mB ≠ 0)
    (hcA : TlsMpc.Node.Local.Edwards.curveValue (xA, yA) = 0) (hcB : TlsMpc.Node.Local.Edwards.curveValue (xB, yB) = 0) :
    let den := ofNat 121666 + ofNat 121665 * (xA * xB * (yA * yB))
    let num := ofNat 121666 * (xA * xB + yA * yB)
    (jointRun E (Curve.splitAgree f0 tSlot maskSlot) (Curve.splitAgree f0 tSlot maskSlot) σA σB I).result =
      some ((⟨f0 + 11⟩, decide (den - num = 0)), (⟨f0 + 11⟩, decide (den - num = 0))) ∧
    (jointRun E (Curve.splitAgree f0 tSlot maskSlot) (Curve.splitAgree f0 tSlot maskSlot) σA σB I).ideal.fields (f0 + 11) =
      some ((den + num) * inverse (den - num)) :=
  Curve.splitAgree_honest hinv E pOn pAdd hOn hAdd hOnC hAddC hq σA σB I f0 tSlot maskSlot xA yA xB yB mA mB hA hB hmA hmB hm hcA hcB

/-- **T3 for op 66** [M]: every release of `prepareContacts` (both scripts and the local step between
them), against any adversary, carries one of `prepareKinds`; the validity bits only under
`pointValid`. -/
theorem s11_prepareContacts_kinds (E : Env) (me : Party) (adv : Adversary) (hash : Bytes → Bytes) (f0 : Nat)
    (s : Curve.PrepareSlots) (us identityBits : List FieldH) (σ : Store) (I : Ideal) (vD : List Release) :
    ∀ r ∈ ((Curve.prepareContacts hash me f0 s us identityBits).withAdv E me adv σ I vD).viewD,
      ∃ k ∈ Curve.prepareKinds, r.label = Label.ofKind k :=
  Curve.prepareContacts_viewD_kinds E me adv hash f0 s us identityBits σ I vD

/-- **The S11 curve flows declare their kinds** [M] (`Reveals`, on every branch). -/
theorem s11_flows_reveal :
    (∀ hash me nonce share, Reveals Curve.splitKinds (Curve.splitBegin hash me nonce share)) ∧
    (∀ f0 tSlot maskSlot, Reveals Curve.splitKinds (Curve.splitAgree f0 tSlot maskSlot)) ∧
    (∀ f0 slot jobs, Reveals Curve.agreeKinds (Curve.agree f0 slot jobs)) ∧
    (∀ hash me f0 s u, Reveals Curve.offsetKinds (Curve.offsetPrepare hash me f0 s u)) ∧
    (∀ f0 maskSlot st τ, Reveals Curve.offsetKinds (Curve.offsetStep f0 maskSlot st τ)) ∧
    (∀ f0 slot st τ, Reveals Curve.offsetKinds (Curve.offsetStepFast f0 slot st τ)) ∧
    (∀ f0 s us, Reveals Curve.liftKinds (Curve.lift f0 s us)) ∧
    (∀ f0 s pts, Reveals Curve.tableKinds (Curve.tables f0 s pts)) ∧
    (∀ f0 rho qslot jobs, Reveals Curve.agreeKinds (Curve.agreeHinted f0 rho qslot jobs)) ∧
    (∀ f0 rho qslot jobs, Reveals Curve.agreeKinds (Curve.agreeAffine f0 rho qslot jobs)) ∧
    (∀ f0 maskSlot baseT jobs, Reveals Curve.signatureKinds (Curve.signatures f0 maskSlot baseT jobs)) ∧
    (∀ f0 hintSlot rSlot maskSlot pts, Reveals Curve.signatureKinds (Curve.torsion f0 hintSlot rSlot maskSlot pts)) ∧
    (∀ f0 slot, Reveals Convert.bitsKinds (Curve.sharedBits f0 slot)) ∧
    (∀ hash me f0 s us ids, Reveals Curve.prepareKinds (Curve.prepareContacts hash me f0 s us ids).first) ∧
    (∀ hash me f0 s us ids r, Reveals Curve.prepareKinds ((Curve.prepareContacts hash me f0 s us ids).second r)) :=
  Registry.s11_flows_reveal

/-- **The curve scripts are well formed** [M] (F23): from any context whose field counter is ahead
of `f0`, with the curve programs loaded under their V3 signatures (`Curve.WFB.CurveProgs`) and the
handles each script reads live below `f0`, the shell's `check` admits every instruction on every
branch. (Split ECDH, the ladders, the offset preparation and step.) -/
theorem s11_wf_split_offset (sigs : Bytes → Option Sig) (c : Ctx) (f0 : Nat)
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : Curve.WFB.CurveProgs c.progs) :
    (∀ tSlot maskSlot, WF sigs c (Curve.splitAgree f0 tSlot maskSlot)) ∧
    (∀ hash me nonce share, WF sigs c (Curve.splitBegin hash me nonce share)) ∧
    (∀ slot (jobs : List (List FieldH × FieldH)), jobs.length ≤ maxWidth →
      (∀ jb ∈ jobs, (∀ x ∈ jb.1, (c.field? x).isSome = true ∧ x.id < f0) ∧
        (c.field? jb.2).isSome = true ∧ jb.2.id < f0) → WF sigs c (Curve.agree f0 slot jobs)) ∧
    (∀ hash me s u, (c.field? u).isSome = true ∧ u.id < f0 → WF sigs c (Curve.offsetPrepare hash me f0 s u)) ∧
    (∀ maskSlot st τ, Curve.StateLive c f0 st → WF sigs c (Curve.offsetStep f0 maskSlot st τ)) ∧
    (∀ slot st τ, Curve.StateLive c f0 st → WF sigs c (Curve.offsetStepFast f0 slot st τ)) :=
  ⟨fun tSlot maskSlot => Curve.splitAgree_wf sigs c f0 tSlot maskSlot hfresh hP,
   fun hash me nonce share => Curve.splitBegin_wf sigs c hash me nonce share,
   fun slot jobs hw hj => Curve.agree_wf sigs c f0 slot jobs hfresh hP hw hj,
   fun hash me s u hu => Curve.offsetPrepare_wf sigs c hash me f0 s u hfresh hP hu,
   fun maskSlot st τ hst => Curve.offsetStep_wf sigs c f0 maskSlot st τ hfresh hP hst,
   fun slot st τ hst => Curve.offsetStepFast_wf sigs c f0 slot st τ hfresh hP hst⟩

/-- **The hinted scripts are well formed** [M] (F23): the lift, bit tables, agreements from tables,
signatures, torsion, shared bits. -/
theorem s11_wf_hinted (sigs : Bytes → Option Sig) (c : Ctx) (f0 : Nat)
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : Curve.WFB.CurveProgs c.progs) :
    (∀ s (us : List FieldH), us.length ≤ maxWidth → (∀ u ∈ us, (c.field? u).isSome = true ∧ u.id < f0) →
      WF sigs c (Curve.lift f0 s us)) ∧
    (∀ s (pts : List Curve.Lifted), pts.length ≤ maxWidth →
      (∀ l ∈ pts, (c.field? l.x).isSome = true ∧ (c.field? l.y).isSome = true ∧ l.x.id < f0 ∧ l.y.id < f0) →
      WF sigs c (Curve.tables f0 s pts) ∧ ∀ hintSlot rSlot maskSlot, WF sigs c (Curve.torsion f0 hintSlot rSlot maskSlot pts)) ∧
    (∀ rho qslot (jobs : List Curve.HintedJob), jobs.length ≤ maxWidth → (∀ jb ∈ jobs, Curve.JobLive c f0 jb) →
      WF sigs c (Curve.agreeHinted f0 rho qslot jobs)) ∧
    (∀ rho qslot (jobs : List (List FieldH × List FieldH)), jobs.length ≤ maxWidth →
      (∀ jb ∈ jobs, ∀ x ∈ jb.1 ++ jb.2, (c.field? x).isSome = true ∧ x.id < f0) →
      WF sigs c (Curve.agreeAffine f0 rho qslot jobs)) ∧
    (∀ maskSlot (baseT : List FieldH) (jobs : List (List FieldH × List FieldH)), jobs.length ≤ maxWidth →
      (∀ x ∈ baseT, (c.field? x).isSome = true ∧ x.id < f0) →
      (∀ jb ∈ jobs, ∀ x ∈ jb.1 ++ jb.2, (c.field? x).isSome = true ∧ x.id < f0) →
      WF sigs c (Curve.signatures f0 maskSlot baseT jobs)) ∧
    (∀ slot, c.progs Conv.bitCheckName = some ⟨1, 0, [.pub]⟩ → c.progs Conv.bitXorName = some ⟨2, 0, [.never]⟩ →
      WF sigs c (Curve.sharedBits f0 slot)) :=
  ⟨fun s us hw hus => Curve.lift_wf sigs c f0 s us hfresh hP hw hus,
   fun s pts hw hp => ⟨Curve.tables_wf sigs c f0 s pts hfresh hP hw hp,
     fun hintSlot rSlot maskSlot => Curve.torsion_wf sigs c f0 hintSlot rSlot maskSlot pts hfresh hP hw hp⟩,
   fun rho qslot jobs hw hj => Curve.agreeHinted_wf sigs c f0 rho qslot jobs hfresh hP hw hj,
   fun rho qslot jobs hw hj => Curve.agreeAffine_wf sigs c f0 rho qslot jobs hfresh hP hw hj,
   fun maskSlot baseT jobs hw hb hj => Curve.signatures_wf sigs c f0 maskSlot baseT jobs hfresh hP hw hb hj,
   fun slot hp1 hp2 => Curve.sharedBits_wf sigs c f0 slot hfresh hp1 hp2⟩

/-- **Op 66 is well formed as a staged flow** [M] (F23): the first script with the lift's
postcondition, the second script (after the local step, which does not touch the handle table)
from every context satisfying it; at most 2047 recipients (one point exchange carries every K₀). -/
theorem s11_prepareContacts_wf (sigs : Bytes → Option Sig) (c : Ctx) (hash : Bytes → Bytes) (me : Party) (f0 : Nat)
    (s : Curve.PrepareSlots) (us identityBits : List FieldH) (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF)
    (hP : Curve.WFB.CurveProgs c.progs) (hw : us.length ≤ 2047)
    (hus : ∀ u ∈ us, (c.field? u).isSome = true ∧ u.id < f0)
    (hid : ∀ x ∈ identityBits, (c.field? x).isSome = true ∧ x.id < f0) :
    Curve.Staged.WellFormed sigs (fun c' r => Curve.LiftPost (fun j => c.field? ⟨j⟩) f0 us.length c.progs c' r.1) c
      (Curve.prepareContacts hash me f0 s us identityBits) :=
  Curve.prepareContacts_wf sigs c hash me f0 s us identityBits hfresh hP hw hus hid

/-- **Split ECDH key generation, two honest parties** [M] (F22): both obtain the same key share
`u(P_A + P_B)` (32 bytes), engines and stores unchanged. -/
theorem s11_splitBegin_honest (E : Env) (hh : ∀ m, (E.hash m).length = 32) (σA σB : Store) (I : Ideal)
    (nA sA nB sB : Nat) (PA PB : TlsMpc.Node.Local.Edwards.Value)
    (hnA : (σA.bytes nA).length = 32) (hsA : (σA.bytes sA).length = 32)
    (hnB : (σB.bytes nB).length = 32) (hsB : (σB.bytes sB).length = 32)
    (hdA : TlsMpc.Node.Local.Edwards.decode (σA.bytes sA) = some PA)
    (hdB : TlsMpc.Node.Local.Edwards.decode (σB.bytes sB) = some PB)
    (hvA : TlsMpc.Node.Local.Edwards.isValid PA = true) (hvB : TlsMpc.Node.Local.Edwards.isValid PB = true)
    (hvS : TlsMpc.Node.Local.Edwards.isValid (TlsMpc.Node.Local.Edwards.add PA PB) = true)
    (hc : E.hash (commitFrame Curve.splitTag .a (σA.bytes nA) (σA.bytes sA)) ≠
      E.hash (commitFrame Curve.splitTag .b (σB.bytes nB) (σB.bytes sB))) :
    Run.JRet (jointRun E (Curve.splitBegin E.hash .a nA sA) (Curve.splitBegin E.hash .b nB sB) σA σB I)
      (TlsMpc.Node.Local.Field.toBytes (TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add PA PB)))
      (TlsMpc.Node.Local.Field.toBytes (TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add PA PB)))
      I σA σB :=
  Curve.splitBegin_honest E hh σA σB I nA sA nB sB PA PB hnA hsA hnB hsB hdA hdB hvA hvB hvS hc

/-- **The split agreement, no denominator hypothesis** [M] (F22, F28 with `CompleteAddition`
[hyp: discharged by `proofs/` `edwards_complete`]): the handle holds `montU (T_A + T_B)`. -/
theorem s11_splitAgree_montU (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hC : Curve.CompleteAddition) (E : Env)
    (pOn pAdd : TlsMpc.FieldDag.V3.Program)
    (hOn : E.programs Curve.onCurveName = some pOn) (hAdd : E.programs Curve.addUName = some pAdd)
    (hOnC : Conv.Computes pOn 2 [.pub] (fun i => [TlsMpc.EdwardsShare.onCurve.eval i]))
    (hAddC : Conv.Computes pAdd 4 [.never, .never] (fun i => TlsMpc.EdwardsShare.addU.map (TlsMpc.FieldDag.Expr.eval i)))
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
    (σA σB : Store) (I : Ideal) (f0 tSlot maskSlot : Nat) (xA yA xB yB mA mB : F)
    (hA : σA.elems tSlot = [xA, yA]) (hB : σB.elems tSlot = [xB, yB])
    (hmA : σA.elems maskSlot = [mA]) (hmB : σB.elems maskSlot = [mB]) (hm : mA + mB ≠ 0)
    (hcA : TlsMpc.Node.Local.Edwards.curveValue (xA, yA) = 0) (hcB : TlsMpc.Node.Local.Edwards.curveValue (xB, yB) = 0) :
    (jointRun E (Curve.splitAgree f0 tSlot maskSlot) (Curve.splitAgree f0 tSlot maskSlot) σA σB I).ideal.fields (f0 + 11) =
      some (TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add (xA, yA) (xB, yB))) :=
  Curve.splitAgree_montU hinv hC E pOn pAdd hOn hAdd hOnC hAddC hq σA σB I f0 tSlot maskSlot xA yA xB yB mA mB
    hA hB hmA hmB hm hcA hcB

/-- **`commit_open_sound` for the point exchanges** [M] (F25): an accepted exchange used the
adversary's commitment chosen before our opening, opened under its own frame, different from ours,
and the returned points are our continuation on the two openings; a copied commitment aborts. -/
theorem s11_pointExchange_sound (E : Env) (me : Party) (adv : Adversary) (tag : Bytes) (nonce points count : Nat)
    (σ : Store) (I : Ideal) (vD : List Release) :
    (∀ xs, (withAdv E me adv (Curve.pointExchange E.hash me tag nonce points count) σ I vD).result = some xs →
      ∃ p1 p2,
        adv.act (vD ++ [⟨Curve.commitLabel, .bytes (Curve.ourCommitP E me σ tag nonce points)⟩])
            (InstrP.exchange 32 Curve.commitLabel (Payload.commitment tag nonce points) : Instr).skel = some p1 ∧
        adv.act (vD ++ [⟨Curve.commitLabel, .bytes (Curve.ourCommitP E me σ tag nonce points)⟩,
            ⟨Label.ownPublicPoint, .bytes (Curve.ourOpeningP σ nonce points)⟩])
            (InstrP.exchange (32 + 32 * count) Label.ownPublicPoint (Payload.opening [nonce, points]) : Instr).skel =
          some p2 ∧
        E.hash (commitFrame tag me.other (p2.bytes.take 32) (p2.bytes.drop 32)) = p1.bytes ∧
        p1.bytes ≠ Curve.ourCommitP E me σ tag nonce points ∧
        (withAdv E me adv (Curve.pointsOf me count (Curve.ourOpeningP σ nonce points) p2.bytes) σ I
          (vD ++ [⟨Curve.commitLabel, .bytes (Curve.ourCommitP E me σ tag nonce points)⟩,
            ⟨Label.ownPublicPoint, .bytes (Curve.ourOpeningP σ nonce points)⟩])).result = some xs) ∧
    (∀ p1, adv.act (vD ++ [⟨Curve.commitLabel, .bytes (Curve.ourCommitP E me σ tag nonce points)⟩])
        (InstrP.exchange 32 Curve.commitLabel (Payload.commitment tag nonce points) : Instr).skel = some p1 →
      p1.bytes = Curve.ourCommitP E me σ tag nonce points →
      (withAdv E me adv (Curve.pointExchange E.hash me tag nonce points count) σ I vD).result = none) :=
  ⟨fun xs h => Curve.pointExchange_sound E me adv tag nonce points count σ I vD xs h,
   fun p1 h1 hc => Curve.pointExchange_copy_aborts E me adv tag nonce points count σ I vD p1 h1 hc⟩

/-- **Liveness facts** [K] (F33): under `FieldInverse`, `EulerCriterion` [hyp: `proofs/`
`euler_criterion`] and `TwoNonSquare` [hyp: `proofs/` `two_not_square`], `sqrt` finds a root of
every square and the lift's public roots never fail (its "lift root" abort cannot fire); F28: the
split agreement's denominator is nonzero on curve points under `CompleteAddition`. -/
theorem s11_liveness (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hE : Curve.EulerCriterion) (hQR : Curve.TwoNonSquare) :
    (∀ x : F, (∃ r, r * r = x) → (TlsMpc.Node.Local.Field.sqrt x).isSome = true) ∧
    (∀ ws : List F, (Curve.roots ws).isSome = true) ∧
    (Curve.CompleteAddition → ∀ x1 y1 x2 y2 : F, TlsMpc.Node.Local.Edwards.curveValue (x1, y1) = 0 →
      TlsMpc.Node.Local.Edwards.curveValue (x2, y2) = 0 → ofNat 121666 + ofNat 121665 * (x1 * x2 * (y1 * y2)) ≠ 0) :=
  ⟨Curve.sqrt_complete hinv hE, Curve.roots_isSome hinv hE hQR,
   fun hC x1 y1 x2 y2 h1 h2 => Curve.addU_den_ne_zero hinv hC x1 y1 x2 y2 h1 h2⟩

/-- **Value-level disclosure of the point exchanges** [M] (F24, part): against any adversary, the
adversary's view of `pointExchange` (hence of `splitBegin`'s and the offset preparation's K₀
exchange) is a prefix of [our commitment, our opening]. -/
theorem s11_pointExchange_disclosure (E : Env) (me : Party) (adv : Adversary) (tag : Bytes)
    (nonce points count : Nat) (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv (Curve.pointExchange E.hash me tag nonce points count) σ I vD).viewD <+:
      [⟨Curve.commitLabel, .bytes (Curve.ourCommitP E me σ tag nonce points)⟩,
       ⟨Label.ownPublicPoint, .bytes (Curve.ourOpeningP σ nonce points)⟩] :=
  Curve.pointExchange_disclosure E me adv tag nonce points count σ I vD

/-- **n masked quotients in one round, two honest parties** [M] (F22, the block-level lemma):
with the pairs' values below `f`, nonzero mask sums and `field-quotient` loaded, both return
`(quotResult f n j, z_j = 0)`, handle `f + 3n + 2j` holds `x_j · z_j⁻¹`, nothing outside the
block changes. [hyp: `FieldInverse`] -/
theorem s11_quotientMany_honest (hinv : TlsMpc.FieldDag.V3.FieldInverse) (E : Env)
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
    (σA σB : Store) (I : Ideal) (f slot : Nat) (pairs : List (FieldH × FieldH)) (x z mA mB : Nat → F)
    (hx : ∀ j, j < pairs.length → I.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).1.id = some (x j))
    (hz : ∀ j, j < pairs.length → I.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).2.id = some (z j))
    (hlo : ∀ p ∈ pairs, p.1.id < f ∧ p.2.id < f)
    (hA : σA.elems slot = (List.range pairs.length).map mA) (hB : σB.elems slot = (List.range pairs.length).map mB)
    (hm : ∀ j, j < pairs.length → mA j + mB j ≠ 0) :
    ∃ J, Run.JRet (jointRun E (Curve.quotientMany f slot pairs) (Curve.quotientMany f slot pairs) σA σB I)
        ((List.range pairs.length).map fun j => (Curve.quotResult f pairs.length j, decide (z j = 0)))
        ((List.range pairs.length).map fun j => (Curve.quotResult f pairs.length j, decide (z j = 0))) J σA σB ∧
      (∀ j, j < pairs.length → J.fields (f + 3 * pairs.length + 2 * j) = some (x j * inverse (z j))) ∧
      (∀ k, (k < f ∨ f + 5 * pairs.length ≤ k) → J.fields k = I.fields k) :=
  Curve.quotientMany_honest E hinv hq σA σB I f slot pairs x z mA mB hx hz hlo hA hB hm

/-- **n X25519 agreements, two honest parties** [M] (F22): with job `j`'s swap-bit handles holding
the RFC swap bits of `bits_j` and its point handle `u_j`, `x25519-fast` computing its expressions,
the quotient handle of job `j` holds `X25519.spec bits_j u_j` (`X25519Fast.spec_eq_quotient`,
`Curve.x25519_inverse_eq`). [hyp: `FieldInverse`; programs loaded; mask sums nonzero] -/
theorem s11_agree_honest (hinv : TlsMpc.FieldDag.V3.FieldInverse) (E : Env) (px : TlsMpc.FieldDag.V3.Program)
    (hP : E.programs Curve.x25519Name = some px)
    (hPC : Conv.Computes px 257 [.never, .never] (fun i => X25519Fast.exprs.map (TlsMpc.FieldDag.Expr.eval i)))
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
    (σA σB : Store) (I : Ideal) (f0 slot : Nat) (jobs : List (List FieldH × FieldH))
    (bits : Nat → Nat → Bool) (u mA mB : Nat → F)
    (hsw : ∀ j, j < jobs.length → (jobs.getD j ([], ⟨0⟩)).1.length = 252 ∧
      ∀ k, k < 252 → I.fields ((jobs.getD j ([], ⟨0⟩)).1.getD k ⟨0⟩).id =
        some (X25519.bitValue (X25519Fast.swapBitSpec (bits j) (k + 2))))
    (hu : ∀ j, j < jobs.length → I.fields (jobs.getD j ([], ⟨0⟩)).2.id = some (u j))
    (hlo : ∀ j, j < jobs.length → (∀ h ∈ (jobs.getD j ([], ⟨0⟩)).1, h.id < f0) ∧ (jobs.getD j ([], ⟨0⟩)).2.id < f0)
    (hA : σA.elems slot = (List.range jobs.length).map mA) (hB : σB.elems slot = (List.range jobs.length).map mB)
    (hm : ∀ j, j < jobs.length → mA j + mB j ≠ 0) :
    ∃ (J : Ideal) (zf : Nat → Bool), Run.JRet (jointRun E (Curve.agree f0 slot jobs) (Curve.agree f0 slot jobs) σA σB I)
        ((List.range jobs.length).map fun j => (Curve.quotResult (f0 + 1 + 2 * jobs.length) jobs.length j, zf j))
        ((List.range jobs.length).map fun j => (Curve.quotResult (f0 + 1 + 2 * jobs.length) jobs.length j, zf j))
        J σA σB ∧
      (∀ j, j < jobs.length →
        J.fields (f0 + 1 + 2 * jobs.length + 3 * jobs.length + 2 * j) = some (X25519.spec (bits j) (u j))) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  Curve.agree_honest E hinv px hP hPC hq σA σB I f0 slot jobs bits u mA mB hsw hu hlo hA hB hm

/-- **The offset agreement, two honest parties** [M] (F22; P-OFFSET at run level). Preparation:
both return `prepState f0 (P_A + P_B)` (K₀ = P_A + P_B, the initial point and table handles holding
`edwards-prepare`'s outputs 505 … on the honest inputs) when the 505 checks vanish there. Step: both
return `(u, f0 + 387)`, `u = montU (K₀ + τ·B)`, the handle holding `(1 + y)/(1 − y)` of the sum of
the initial point and the signed entries the recoded digits select (`offsetSum_eval`; with
`s11_step_tableSum`, `u((k₀ + τ)·R)` when the table holds the multiples of R). Fast step: handle
`f0 + 8` holds `X · Z⁻¹` of the projective sum. [hyp: `ComputesD`, `Live` (discharged for translated
artifacts by `FieldDagV3.eval_compileAll`, `eval_ofArtifact_some`); `FieldInverse` for the fast step;
the byte slots as `s11_splitBegin_honest`] -/
theorem s11_offset_honest (E : Env) :
    (∀ (hh : ∀ m, (E.hash m).length = 32) (pp : TlsMpc.FieldDag.V3.Program) (f : (Nat → F) → List F)
      (hP : E.programs Curve.prepareName = some pp) (hC : Curve.ComputesD pp 506 2031 1531 f)
      (σA σB : Store) (I : Ideal) (f0 : Nat) (s : Curve.OffsetSlots) (u : FieldH) (uv : F)
      (hu : I.fields u.id = some uv) (hul : u.id < f0)
      (rA rB : F) (hrA : σA.elems s.r = [rA]) (hrB : σB.elems s.r = [rB])
      (bA bB : Nat → Bool) (hbA : σA.elems s.bits = (List.range 252).map fun i => X25519.bitValue (bA i))
      (hbB : σB.elems s.bits = (List.range 252).map fun i => X25519.bitValue (bB i))
      (mA mB : Nat → F) (hmA : σA.elems s.masks = (List.range 2031).map mA)
      (hmB : σB.elems s.masks = (List.range 2031).map mB) (hm : ∀ i, i < 2031 → mA i + mB i ≠ 0)
      (hL : Curve.Live pp (fun i => (Curve.prepVals uv rA rB bA bB).getD i 0))
      (hck : ∀ i, i < 505 → (f (fun i => (Curve.prepVals uv rA rB bA bB).getD i 0)).getD i 0 = 0)
      (PA PB : TlsMpc.Node.Local.Edwards.Value)
      (hnA : (σA.bytes s.nonce).length = 32) (hsA : (σA.bytes s.share).length = 32)
      (hnB : (σB.bytes s.nonce).length = 32) (hsB : (σB.bytes s.share).length = 32)
      (hdA : TlsMpc.Node.Local.Edwards.decode (σA.bytes s.share) = some PA)
      (hdB : TlsMpc.Node.Local.Edwards.decode (σB.bytes s.share) = some PB)
      (hvA : TlsMpc.Node.Local.Edwards.isValid PA = true) (hvB : TlsMpc.Node.Local.Edwards.isValid PB = true)
      (hvS : TlsMpc.Node.Local.Edwards.isValid (TlsMpc.Node.Local.Edwards.add PA PB) = true)
      (hc : E.hash (commitFrame Curve.offsetTag .a (σA.bytes s.nonce) (σA.bytes s.share)) ≠
        E.hash (commitFrame Curve.offsetTag .b (σB.bytes s.nonce) (σB.bytes s.share))),
      ∃ J, Run.JRet (jointRun E (Curve.offsetPrepare E.hash .a f0 s u) (Curve.offsetPrepare E.hash .b f0 s u) σA σB I)
          (Curve.prepState f0 (TlsMpc.Node.Local.Edwards.add PA PB))
          (Curve.prepState f0 (TlsMpc.Node.Local.Edwards.add PA PB)) J σA σB ∧
        (∀ i, i < 1026 → J.fields (Curve.prepOuts f0 + 505 + i) =
          some ((f (fun i => (Curve.prepVals uv rA rB bA bB).getD i 0)).getD (505 + i) 0)) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) ∧
    (∀ (po : TlsMpc.FieldDag.V3.Program) (hP : E.programs Curve.offsetSumName = some po)
      (hC : Curve.ComputesD po 194 128 1 (fun i => TlsMpc.EdwardsAffine.offsetSum.map (TlsMpc.FieldDag.Expr.eval i)))
      (σA σB : Store) (I : Ideal) (f0 maskSlot : Nat) (st : Curve.OffsetState) (τ : Nat)
      (u : F) (hkey : Curve.ephemeralKey st.key τ = some u) (hτ : τ < 2 ^ 252) (hst : Curve.StateBelow I f0 st)
      (mA mB : Nat → F) (hA : σA.elems maskSlot = (List.range 128).map mA)
      (hB : σB.elems maskSlot = (List.range 128).map mB) (hm : ∀ i, i < 128 → mA i + mB i ≠ 0)
      (hL : Curve.Live po (fun i => (Curve.stepVals I f0 st τ).getD i 0)),
      ∃ J, Run.JRet (jointRun E (Curve.offsetStep f0 maskSlot st τ) (Curve.offsetStep f0 maskSlot st τ) σA σB I)
          (u, ⟨f0 + 387⟩) (u, ⟨f0 + 387⟩) J σA σB ∧
        J.fields (f0 + 387) = some
          (let input := fun i => (Curve.stepVals I f0 st τ).getD i 0
           let sum := TlsMpc.EdwardsAffine.sumTreeValue ((input 0, input 1) :: (List.range TlsMpc.EdwardsAffine.windows).map
              (fun w => (input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1))))
           (ofNat 1 + sum.2) * inverse (ofNat 1 - sum.2)) ∧
        u = TlsMpc.Node.Local.Edwards.montU
          (TlsMpc.Node.Local.Edwards.add st.key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) ∧
    (∀ (hinv : TlsMpc.FieldDag.V3.FieldInverse) (po : TlsMpc.FieldDag.V3.Program) (f : (Nat → F) → List F)
      (hP : E.programs Curve.offsetSumFastName = some po) (hC : Conv.Computes po 194 [.never, .never] f)
      (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
      (σA σB : Store) (I : Ideal) (f0 slot : Nat) (st : Curve.OffsetState) (τ : Nat) (u : F)
      (hkey : Curve.ephemeralKey st.key τ = some u) (hτ : τ < 2 ^ 252) (hst : Curve.StateBelow I f0 st)
      (mA mB : F) (hA : σA.elems slot = [mA]) (hB : σB.elems slot = [mB]) (hm : mA + mB ≠ 0)
      (hz : (f (fun i => (Curve.stepVals I f0 st τ).getD i 0)).getD 1 0 ≠ 0),
      ∃ J, Run.JRet (jointRun E (Curve.offsetStepFast f0 slot st τ) (Curve.offsetStepFast f0 slot st τ) σA σB I)
          (u, ⟨f0 + 8⟩) (u, ⟨f0 + 8⟩) J σA σB ∧
        J.fields (f0 + 8) = some ((f (fun i => (Curve.stepVals I f0 st τ).getD i 0)).getD 0 0 *
          inverse ((f (fun i => (Curve.stepVals I f0 st τ).getD i 0)).getD 1 0)) ∧
        u = TlsMpc.Node.Local.Edwards.montU
          (TlsMpc.Node.Local.Edwards.add st.key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) :=
  ⟨fun hh pp f hP hC σA σB I f0 s u uv hu hul rA rB hrA hrB bA bB hbA hbB mA mB hmA hmB hm hL hck PA PB hnA hsA hnB
      hsB hdA hdB hvA hvB hvS hc =>
    Curve.offsetPrepare_honest E hh pp f hP hC σA σB I f0 s u uv hu hul rA rB hrA hrB bA bB hbA hbB mA mB hmA hmB hm
      hL hck PA PB hnA hsA hnB hsB hdA hdB hvA hvB hvS hc,
   fun po hP hC σA σB I f0 maskSlot st τ u hkey hτ hst mA mB hA hB hm hL =>
    Curve.offsetStep_value E po hP hC σA σB I f0 maskSlot st τ u hkey hτ hst mA mB hA hB hm hL,
   fun hinv po f hP hC hq σA σB I f0 slot st τ u hkey hτ hst mA mB hA hB hm hz =>
    Curve.offsetStepFast_honest E hinv po f hP hC hq σA σB I f0 slot st τ u hkey hτ hst mA mB hA hB hm hz⟩

/-- **The hinted programs, two honest parties** [M] (F22): `tables` (the link checks open to zero;
point `j`'s 1024 table handles hold `edwards-bit-table`'s outputs 126 …), `agreeAffine` (job `j`'s
quotient handle holds `X_j · Z_j⁻¹` of `edwards-affine-bit-sum`), `signatures` and `torsion` (the
output handles hold their programs' outputs on each instance's values). Each run returns the
handles the script names, leaves both stores unchanged and nothing below `f0` changed. [hyp:
`ComputesD`/`Conv.Computes`, `Live`; mask sums nonzero; for `tables`, the honest hints make the link
checks vanish (`EdwardsHinted.bitTable_sound`); `FieldInverse` for `agreeAffine`] -/
theorem s11_hinted_honest (E : Env) :
    (∀ (pb : TlsMpc.FieldDag.V3.Program) (f : (Nat → F) → List F) (hP : E.programs Curve.bitTableName = some pb)
      (hC : Curve.ComputesD pb 380 252 1150 f) (σA σB : Store) (I : Ideal) (f0 : Nat) (s : Curve.TableSlots)
      (pts : List Curve.Lifted)
      (hpts : ∀ j, j < pts.length → (pts.getD j Curve.liftedD).x.id < f0 ∧ (pts.getD j Curve.liftedD).y.id < f0 ∧
        (I.fields (pts.getD j Curve.liftedD).x.id).isSome ∧ (I.fields (pts.getD j Curve.liftedD).y.id).isSome)
      (ha hb lA lB mA mB : Nat → F)
      (hhA : σA.elems s.hints = (List.range (126 * pts.length)).map ha)
      (hhB : σB.elems s.hints = (List.range (126 * pts.length)).map hb)
      (hlA : σA.elems s.links = (List.range (126 * pts.length)).map lA)
      (hlB : σB.elems s.links = (List.range (126 * pts.length)).map lB)
      (hmA : σA.elems s.masks = (List.range (252 * pts.length)).map mA)
      (hmB : σB.elems s.masks = (List.range (252 * pts.length)).map mB)
      (hm : ∀ i, i < 252 * pts.length → mA i + mB i ≠ 0)
      (hL : ∀ j, j < pts.length →
        Curve.Live pb (fun i => (Curve.tableVals I (pts.getD j Curve.liftedD) ha hb (fun i => lA i + lB i) j).getD i 0))
      (hck : ∀ j, j < pts.length → ∀ i, i < 126 →
        (f (fun i => (Curve.tableVals I (pts.getD j Curve.liftedD) ha hb (fun i => lA i + lB i) j).getD i 0)).getD i 0 = 0),
      ∃ J, Run.JRet (jointRun E (Curve.tables f0 s pts) (Curve.tables f0 s pts) σA σB I)
          ((List.range pts.length).map fun j =>
            Curve.hs (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126) 1024)
          ((List.range pts.length).map fun j =>
            Curve.hs (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126) 1024) J σA σB ∧
        (∀ j t, j < pts.length → t < 1024 →
          J.fields (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126 + t) =
            some ((f (fun i => (Curve.tableVals I (pts.getD j Curve.liftedD) ha hb (fun i => lA i + lB i) j).getD i 0)).getD
              (126 + t) 0)) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) ∧
    (∀ (hinv : TlsMpc.FieldDag.V3.FieldInverse) (pa : TlsMpc.FieldDag.V3.Program) (f : (Nat → F) → List F)
      (hP : E.programs Curve.affineBitSumName = some pa) (hC : Conv.Computes pa 757 [.never, .never] f)
      (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
      (σA σB : Store) (I : Ideal) (f0 rho qslot : Nat) (jobs : List (List FieldH × List FieldH))
      (hjobs : ∀ j, j < jobs.length → (jobs.getD j ([], [])).1.length = 251 ∧ (jobs.getD j ([], [])).2.length = 504)
      (hdef : ∀ j, j < jobs.length → ∀ h ∈ (jobs.getD j ([], [])).2 ++ (jobs.getD j ([], [])).1,
        h.id < f0 ∧ (I.fields h.id).isSome)
      (ρA ρB qA qB : Nat → F) (hrA : σA.elems rho = (List.range jobs.length).map ρA)
      (hrB : σB.elems rho = (List.range jobs.length).map ρB)
      (hqA : σA.elems qslot = (List.range jobs.length).map qA) (hqB : σB.elems qslot = (List.range jobs.length).map qB)
      (hqm : ∀ j, j < jobs.length → qA j + qB j ≠ 0),
      ∃ (J : Ideal) (zf : Nat → Bool),
        Run.JRet (jointRun E (Curve.agreeAffine f0 rho qslot jobs) (Curve.agreeAffine f0 rho qslot jobs) σA σB I)
          ((List.range jobs.length).map fun j =>
            (Curve.quotResult (f0 + 1 + 3 * jobs.length + 2 * jobs.length) jobs.length j, zf j))
          ((List.range jobs.length).map fun j =>
            (Curve.quotResult (f0 + 1 + 3 * jobs.length + 2 * jobs.length) jobs.length j, zf j)) J σA σB ∧
        (∀ j, j < jobs.length →
          J.fields (f0 + 1 + 3 * jobs.length + 2 * jobs.length + 3 * jobs.length + 2 * j) =
            some ((f (fun i => (Curve.affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).getD i 0)).getD 0 0 *
              inverse ((f (fun i => (Curve.affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).getD i 0)).getD 1 0))) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) ∧
    (∀ (ps : TlsMpc.FieldDag.V3.Program) (f : (Nat → F) → List F) (hP : E.programs Curve.signatureSumName = some ps)
      (hC : Curve.ComputesD ps 2546 2 2 f) (σA σB : Store) (I : Ideal) (f0 maskSlot : Nat) (baseT : List FieldH)
      (jobs : List (List FieldH × List FieldH))
      (hjobs : ∀ j, j < jobs.length → (jobs.getD j ([], [])).1.length = 1024 ∧ (jobs.getD j ([], [])).2.length = 510)
      (hbase : baseT.length = 1024)
      (hdef : ∀ j, j < jobs.length → ∀ h ∈ Curve.sigIns baseT (jobs.getD j ([], [])), h.id < f0 ∧ (I.fields h.id).isSome)
      (mA mB : Nat → F) (hA : σA.elems maskSlot = (List.range (2 * jobs.length)).map mA)
      (hB : σB.elems maskSlot = (List.range (2 * jobs.length)).map mB)
      (hm : ∀ i, i < 2 * jobs.length → mA i + mB i ≠ 0)
      (hL : ∀ j, j < jobs.length →
        Curve.Live ps (fun i => (Curve.valsOf I (Curve.sigIns baseT (jobs.getD j ([], [])))).getD i 0)),
      ∃ J, Run.JRet (jointRun E (Curve.signatures f0 maskSlot baseT jobs) (Curve.signatures f0 maskSlot baseT jobs) σA σB I)
          ((List.range jobs.length).map fun j => (⟨f0 + 6 * jobs.length + 2 * j⟩, ⟨f0 + 6 * jobs.length + 2 * j + 1⟩))
          ((List.range jobs.length).map fun j => (⟨f0 + 6 * jobs.length + 2 * j⟩, ⟨f0 + 6 * jobs.length + 2 * j + 1⟩))
          J σA σB ∧
        (∀ j t, j < jobs.length → t < 2 → J.fields (f0 + 6 * jobs.length + (j * 2 + t)) =
          some ((f (fun i => (Curve.valsOf I (Curve.sigIns baseT (jobs.getD j ([], [])))).getD i 0)).getD t 0)) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) ∧
    (∀ (pt : TlsMpc.FieldDag.V3.Program) (f : (Nat → F) → List F) (hP : E.programs Curve.torsionName = some pt)
      (hC : Curve.ComputesD pt 7 4 2 f) (σA σB : Store) (I : Ideal) (f0 hintSlot rSlot maskSlot : Nat)
      (pts : List Curve.Lifted)
      (hpts : ∀ j, j < pts.length → (pts.getD j Curve.liftedD).x.id < f0 ∧ (pts.getD j Curve.liftedD).y.id < f0 ∧
        (I.fields (pts.getD j Curve.liftedD).x.id).isSome ∧ (I.fields (pts.getD j Curve.liftedD).y.id).isSome)
      (ha hb rA rB mA mB : Nat → F)
      (hhA : σA.elems hintSlot = (List.range (2 * pts.length)).map ha)
      (hhB : σB.elems hintSlot = (List.range (2 * pts.length)).map hb)
      (hrA : σA.elems rSlot = (List.range pts.length).map rA) (hrB : σB.elems rSlot = (List.range pts.length).map rB)
      (hmA : σA.elems maskSlot = (List.range (4 * pts.length)).map mA)
      (hmB : σB.elems maskSlot = (List.range (4 * pts.length)).map mB)
      (hm : ∀ i, i < 4 * pts.length → mA i + mB i ≠ 0)
      (hL : ∀ j, j < pts.length →
        Curve.Live pt (fun i => (Curve.torsionVals I (pts.getD j Curve.liftedD) ha hb (fun j => rA j + rB j) j).getD i 0)),
      ∃ J, Run.JRet (jointRun E (Curve.torsion f0 hintSlot rSlot maskSlot pts) (Curve.torsion f0 hintSlot rSlot maskSlot pts)
          σA σB I)
          ((List.range pts.length).map fun j =>
            (⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j⟩,
             ⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j + 1⟩))
          ((List.range pts.length).map fun j =>
            (⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j⟩,
             ⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j + 1⟩)) J σA σB ∧
        (∀ j t, j < pts.length → t < 2 →
          J.fields (f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + (j * 2 + t)) =
            some ((f (fun i => (Curve.torsionVals I (pts.getD j Curve.liftedD) ha hb (fun j => rA j + rB j) j).getD i 0)).getD
              t 0)) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) :=
  ⟨fun pb f hP hC σA σB I f0 s pts hpts ha hb lA lB mA mB hhA hhB hlA hlB hmA hmB hm hL hck =>
    Curve.tables_honest E pb f hP hC σA σB I f0 s pts hpts ha hb lA lB mA mB hhA hhB hlA hlB hmA hmB hm hL hck,
   fun hinv pa f hP hC hq σA σB I f0 rho qslot jobs hjobs hdef ρA ρB qA qB hrA hrB hqA hqB hqm =>
    Curve.agreeAffine_honest E hinv pa f hP hC hq σA σB I f0 rho qslot jobs hjobs hdef ρA ρB qA qB hrA hrB hqA hqB hqm,
   fun ps f hP hC σA σB I f0 maskSlot baseT jobs hjobs hbase hdef mA mB hA hB hm hL =>
    Curve.signatures_honest E ps f hP hC σA σB I f0 maskSlot baseT jobs hjobs hbase hdef mA mB hA hB hm hL,
   fun pt f hP hC σA σB I f0 hintSlot rSlot maskSlot pts hpts ha hb rA rB mA mB hhA hhB hrA hrB hmA hmB hm hL =>
    Curve.torsion_honest E pt f hP hC σA σB I f0 hintSlot rSlot maskSlot pts hpts ha hb rA rB mA mB hhA hhB hrA hrB
      hmA hmB hm hL⟩

/-- **The hinted lift and the agreements from bit tables, two honest parties** [M] (F22).
`lift`: the four checks per point open to zero, the `w_j` are opened, their public roots `rs`,
`lift-point`, the `Z_j` are opened and are curve points; both return `liftResult` with the opened
`Z_j` and the zero flags of `rs`, the validity/`x`/`y` handles hold `lift-point`'s outputs.
`agreeHinted`: the result in job order (`assembleH`), handle `f0` holds 0, live job `i`'s quotient
handle holds `X_i · Z_i⁻¹` of `edwards-bit-sum`. [hyp: `Conv.Computes`/`ComputesD`, `Live`; the
honest checks vanish (`hchk`), the roots exist (`hroots`, never fails: `s11_liveness`), the `Z_j` on
the curve (`hZ`); mask sums nonzero; `FieldInverse` for `agreeHinted`] -/
theorem s11_lift_agreeHinted_honest (E : Env) :
    (∀ (po pp : TlsMpc.FieldDag.V3.Program) (fO fP : (Nat → F) → List F) (mk : List TlsMpc.FieldDag.V3.OMark)
      (hPo : E.programs Curve.liftOpenName = some po) (hCo : Conv.Computes po 8 mk fO) (hmk : mk.length = 6)
      (hPp : E.programs Curve.liftPointName = some pp) (hCp : Curve.ComputesD pp 9 5 5 fP)
      (σA σB : Store) (I : Ideal) (f0 : Nat) (s : Curve.LiftSlots) (us : List FieldH)
      (uv rA rB pA pB mA mB : Nat → F) (bA bB : Nat → Bool)
      (hu : ∀ j, j < us.length → (us.getD j ⟨0⟩).id < f0 ∧ I.fields (us.getD j ⟨0⟩).id = some (uv j))
      (hcA : σA.elems s.coins = (List.range us.length).map fun j => X25519.bitValue (bA j))
      (hcB : σB.elems s.coins = (List.range us.length).map fun j => X25519.bitValue (bB j))
      (hpA : σA.elems s.points = (List.range (2 * us.length)).map pA)
      (hpB : σB.elems s.points = (List.range (2 * us.length)).map pB)
      (hrA : σA.elems s.r = (List.range us.length).map rA) (hrB : σB.elems s.r = (List.range us.length).map rB)
      (hmA : σA.elems s.masks = (List.range (5 * us.length)).map mA)
      (hmB : σB.elems s.masks = (List.range (5 * us.length)).map mB)
      (hm : ∀ i, i < 5 * us.length → mA i + mB i ≠ 0)
      (ov : Nat → List F) (hov : ∀ j, ov j = fO (fun i => (Curve.liftOpenVals uv rA rB pA pB bA bB j).getD i 0))
      (hchk : ∀ j, j < us.length → ∀ i, i < 4 → (ov j).getD (1 + i) 0 = 0)
      (rs : List (F × F × Bool)) (hroots : Curve.roots ((List.range us.length).map fun j => (ov j).getD 0 0) = some rs)
      (pv : Nat → List F) (hpv : ∀ j, pv j = fP (fun i => (Curve.liftPointVals uv rA rB pA pB ov rs j).getD i 0))
      (hL : ∀ j, j < us.length → Curve.Live pp (fun i => (Curve.liftPointVals uv rA rB pA pB ov rs j).getD i 0))
      (hZ : ∀ j, j < us.length → TlsMpc.Node.Local.Edwards.onCurve ((pv j).getD 3 0, (pv j).getD 4 0) = true),
      ∃ J, Run.JRet (jointRun E (Curve.lift f0 s us) (Curve.lift f0 s us) σA σB I)
          (Curve.liftResult f0 us.length ((List.range us.length).map fun j => [(pv j).getD 3 0, (pv j).getD 4 0]).flatten rs)
          (Curve.liftResult f0 us.length ((List.range us.length).map fun j => [(pv j).getD 3 0, (pv j).getD 4 0]).flatten rs)
          J σA σB ∧
        (∀ j t, j < us.length → t < 3 → J.fields (Curve.lfl f0 us.length + 5 * j + t) = some ((pv j).getD t 0)) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) ∧
    (∀ (hinv : TlsMpc.FieldDag.V3.FieldInverse) (pb : TlsMpc.FieldDag.V3.Program) (f : (Nat → F) → List F)
      (hP : E.programs Curve.bitSumName = some pb) (hC : Conv.Computes pb 1261 [.never, .never] f)
      (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient)
      (σA σB : Store) (I : Ideal) (f0 rho qslot : Nat) (jobs : List Curve.HintedJob)
      (hjobs : ∀ i, i < (Curve.liveJobs jobs).length → ((Curve.liveJobs jobs).getD i Curve.liveD).1.bits.length = 251 ∧
        ((Curve.liveJobs jobs).getD i Curve.liveD).2.length = 1024)
      (hdef : ∀ i, i < (Curve.liveJobs jobs).length → ∀ h ∈ ((Curve.liveJobs jobs).getD i Curve.liveD).1.valid ::
        ((((Curve.liveJobs jobs).getD i Curve.liveD).2.drop 12).take 1008 ++ ((Curve.liveJobs jobs).getD i Curve.liveD).1.bits),
        h.id < f0 ∧ (I.fields h.id).isSome)
      (ρA ρB qA qB : Nat → F) (hrA : σA.elems rho = (List.range (Curve.liveJobs jobs).length).map ρA)
      (hrB : σB.elems rho = (List.range (Curve.liveJobs jobs).length).map ρB)
      (hqA : σA.elems qslot = (List.range (Curve.liveJobs jobs).length).map qA)
      (hqB : σB.elems qslot = (List.range (Curve.liveJobs jobs).length).map qB)
      (hqm : ∀ i, i < (Curve.liveJobs jobs).length → qA i + qB i ≠ 0),
      ∃ (J : Ideal) (zf : Nat → Bool),
        Run.JRet (jointRun E (Curve.agreeHinted f0 rho qslot jobs) (Curve.agreeHinted f0 rho qslot jobs) σA σB I)
          (Curve.assembleH f0 jobs ((List.range (Curve.liveJobs jobs).length).map fun i =>
            (Curve.quotResult (f0 + 1 + 3 * (Curve.liveJobs jobs).length + 2 * (Curve.liveJobs jobs).length)
              (Curve.liveJobs jobs).length i, zf i)))
          (Curve.assembleH f0 jobs ((List.range (Curve.liveJobs jobs).length).map fun i =>
            (Curve.quotResult (f0 + 1 + 3 * (Curve.liveJobs jobs).length + 2 * (Curve.liveJobs jobs).length)
              (Curve.liveJobs jobs).length i, zf i)))
          J σA σB ∧
        J.fields f0 = some (ofNat 0) ∧
        (∀ i, i < (Curve.liveJobs jobs).length →
          J.fields (f0 + 1 + 3 * (Curve.liveJobs jobs).length + 2 * (Curve.liveJobs jobs).length +
              3 * (Curve.liveJobs jobs).length + 2 * i) =
            some ((f (fun k => (Curve.hintedVals I ((Curve.liveJobs jobs).getD i Curve.liveD) (ρA i + ρB i)).getD k 0)).getD 0 0 *
              inverse ((f (fun k => (Curve.hintedVals I ((Curve.liveJobs jobs).getD i Curve.liveD) (ρA i + ρB i)).getD k 0)).getD
                1 0))) ∧
        (∀ k, k < f0 → J.fields k = I.fields k)) :=
  ⟨fun po pp fO fP mk hPo hCo hmk hPp hCp σA σB I f0 s us uv rA rB pA pB mA mB bA bB hu hcA hcB hpA hpB hrA hrB hmA hmB
      hm ov hov hchk rs hroots pv hpv hL hZ =>
    Curve.lift_honest E po pp fO fP mk hPo hCo hmk hPp hCp σA σB I f0 s us uv rA rB pA pB mA mB bA bB hu hcA hcB hpA hpB
      hrA hrB hmA hmB hm ov hov hchk rs hroots pv hpv hL hZ,
   fun hinv pb f hP hC hq σA σB I f0 rho qslot jobs hjobs hdef ρA ρB qA qB hrA hrB hqA hqB hqm =>
    Curve.agreeHinted_honest E hinv pb f hP hC hq σA σB I f0 rho qslot jobs hjobs hdef ρA ρB qA qB hrA hrB hqA hqB hqm⟩

/-- **Value-level disclosure of the quotient round** [M] (F24, part): against any adversary, the
adversary's view of `quotientMany` (the last step of `agree`, `offsetStepFast`, `agreeHinted`,
`agreeAffine`) is a prefix of [the masked denominators `z_j · m_j`, the zero flags], for the masks
`m_j` the engines hold; each flag is 1 exactly when its denominator opening is 0. -/
theorem s11_quotientMany_disclosure (E : Env) (me : Party) (adv : Adversary)
    (hq : E.programs Inversion.quotientName = some TlsMpc.FieldDag.V3.quotient) (σ : Store) (I : Ideal)
    (vD : List Release) (f slot : Nat) (pairs : List (FieldH × FieldH)) (x z : Nat → F)
    (hx : ∀ j, j < pairs.length → I.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).1.id = some (x j))
    (hz : ∀ j, j < pairs.length → I.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).2.id = some (z j))
    (hlo : ∀ p ∈ pairs, p.1.id < f ∧ p.2.id < f) :
    ∃ mv : Nat → F, (withAdv E me adv (Curve.quotientMany f slot pairs) σ I vD).viewD <+:
      [⟨Label.maskedDenominator, .elems ((List.range pairs.length).map fun j => z j * mv j)⟩,
       ⟨Label.maskedDenominator, .elems ((List.range pairs.length).map fun j =>
          if z j * mv j = 0 then ofNat 1 else ofNat 0)⟩] :=
  Curve.quotientMany_disclosure E me adv hq σ I vD f slot pairs x z hx hz hlo

/-! #### F22a, F22b, F25b, F22 (part): the programs as loaded, honest inputs, the local inversions

Named hypotheses added (each a theorem of `proofs/`, SecurityMathlib section 7): `Curve.AddClosed`
(`pointAddValue_is_group_add` with `curveCheck_zero_iff`), `Curve.ExtClosed`
(`extAddValue_is_group_add`; `Curve.ExtGood` is `ExtRep` in field elements),
`Curve.RecipientOnCurve` (`recipient_on_curve`), with `Curve.CompleteAddition` (`edwards_complete`)
and `FieldInverse`. The loader's facts are hypotheses `dX.program = some p` (the text under the
name is the declaration's validated compilation: pins, `parse_render`) and `p.masks = m` (the
count the shell checks, F25c). -/

/-- **A compiled program is live where its SOURCE divisions are nonzero** [K] (F22a, generic): every
node of an accepted `compileAll` is a subterm of the source expressions (an invariant of the
memoising generator), so a declaration's V3 program never aborts, with masks nonzero below its mask
count, on an input where every division `a / b` of its expressions has `b ≠ 0` (`DivOk`). -/
theorem s11_decl_live (hinv : TlsMpc.FieldDag.V3.FieldInverse) (d : TlsMpc.FieldProgramsV3.Decl)
    (p : TlsMpc.FieldDag.V3.Program) (hp : d.program = some p) (input : Nat → F)
    (hd : ∀ e ∈ d.exprs, TlsMpc.FieldDag.Compiled.DivOk input e) (mask : Nat → F)
    (hm : ∀ j, j < p.masks → mask j ≠ 0) : (TlsMpc.FieldDag.V3.eval p input mask).isSome :=
  TlsMpc.FieldDag.Compiled.Decl.live hinv d p hp input hd mask hm

/-- **F22a: every masked curve program computes its declaration and is live on its honest inputs**
[K; hyp: `FieldInverse`, `CompleteAddition`, `AddClosed`, `ExtClosed`, `RecipientOnCurve`]. The
input conditions (`Curve.PL.*In`): `edwards-prepare` — `u + 1`, `121666 − 121665·y²`, `2·x²` nonzero,
the recipient check zero, the 504 scalar inputs bits; `edwards-offset-sum` — the initial and the 64
signed window points on the curve, the sum's `y ≠ 1`; `lift-point` — both mask points and the
selected point on the curve, `1 + valid·u ≠ 0`; `edwards-prepare-hinted` and `edwards-bit-table` —
the point and the 2·63 hint points on the curve (and the scalar bits bits); `edwards-signature-sum` —
the selection bits and `flip` bits, the 509 entries represented points; `edwards-torsion-hinted` —
both hint points on the curve. -/
theorem s11_programs_live (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hC : Curve.CompleteAddition)
    (hA : Curve.AddClosed) (hX : Curve.ExtClosed) (hR : Curve.RecipientOnCurve) (p : TlsMpc.FieldDag.V3.Program)
    (input : Nat → F) :
    (Curve.dPrepare.program = some p → p.masks = 2031 →
      Curve.ComputesD p 506 2031 1531 (fun i => TlsMpc.EdwardsAffine.prepare.map (TlsMpc.FieldDag.Expr.eval i)) ∧
      (Curve.PL.PrepareIn input → Curve.Live p input)) ∧
    (Curve.dOffsetSum.program = some p → p.masks = 128 →
      Curve.ComputesD p 194 128 1 (fun i => TlsMpc.EdwardsAffine.offsetSum.map (TlsMpc.FieldDag.Expr.eval i)) ∧
      (Curve.PL.OffsetSumIn input → Curve.Live p input)) ∧
    (Curve.dLiftPoint.program = some p → p.masks = 5 →
      Curve.ComputesD p 9 5 5 (fun i => (TlsMpc.EdwardsHinted.liftPoint ()).map (TlsMpc.FieldDag.Expr.eval i)) ∧
      (Curve.PL.LiftPointIn input → Curve.Live p input)) ∧
    (Curve.dPrepareHinted.program = some p → p.masks = 1150 →
      Curve.ComputesD p 884 1150 1656 (fun i => (TlsMpc.EdwardsHinted.prepareHinted ()).map (TlsMpc.FieldDag.Expr.eval i)) ∧
      (Curve.PL.PrepareHintedIn input → Curve.Live p input)) ∧
    (Curve.dBitTable.program = some p → p.masks = 252 →
      Curve.ComputesD p 380 252 1150 (fun i => (TlsMpc.EdwardsHinted.bitTable ()).map (TlsMpc.FieldDag.Expr.eval i)) ∧
      (Curve.PL.BitTableIn input → Curve.Live p input)) ∧
    (Curve.dSignatureSum.program = some p → p.masks = 2 →
      Curve.ComputesD p 2546 2 2 (fun i => (TlsMpc.EdwardsHinted.signatureSum ()).map (TlsMpc.FieldDag.Expr.eval i)) ∧
      (Curve.PL.SignatureIn input → Curve.Live p input)) ∧
    (Curve.dTorsion.program = some p → p.masks = 4 →
      Curve.ComputesD p 7 4 2 (fun i => (TlsMpc.EdwardsHinted.torsionHinted ()).map (TlsMpc.FieldDag.Expr.eval i)) ∧
      (Curve.PL.TorsionIn input → Curve.Live p input)) :=
  ⟨fun hd hm => ⟨Curve.prepare_computesD hinv p hd hm, Curve.prepare_live hinv hC hA hR p hd input⟩,
   fun hd hm => ⟨Curve.offsetSum_computesD hinv p hd hm, Curve.offsetSum_live hinv hC hA p hd input⟩,
   fun hd hm => ⟨Curve.liftPoint_computesD hinv p hd hm, Curve.liftPoint_live hinv hC hA p hd input⟩,
   fun hd hm => ⟨Curve.prepareHinted_computesD hinv p hd hm, Curve.prepareHinted_live hinv hC hA hX p hd input⟩,
   fun hd hm => ⟨Curve.bitTable_computesD hinv p hd hm, Curve.bitTable_live hinv hC hA hX p hd input⟩,
   fun hd hm => ⟨Curve.signatureSum_computesD hinv p hd hm, Curve.signatureSum_live hinv hX p hd input⟩,
   fun hd hm => ⟨Curve.torsion_computesD hinv p hd hm, Curve.torsion_live hinv hC hA hX p hd input⟩⟩

/-- **F22a: the mask-free curve programs compute their declarations on every input** [K; hyp:
`FieldInverse`] (`x25519-fast`, `edwards-offset-sum-fast`, `edwards-bit-sum`,
`edwards-affine-bit-sum`, `lift-open`, `edwards-on-curve`, `edwards-add-u`; `Live` is then
automatic: `Curve.live_of_computes`). -/
theorem s11_maskfree_computes (hinv : TlsMpc.FieldDag.V3.FieldInverse) (p : TlsMpc.FieldDag.V3.Program)
    (hm : p.masks = 0) :
    (Curve.dX25519.program = some p →
      Conv.Computes p 257 [.never, .never] (fun i => X25519Fast.exprs.map (TlsMpc.FieldDag.Expr.eval i))) ∧
    (Curve.dOffsetSumFast.program = some p →
      Conv.Computes p 194 [.never, .never] (fun i => (TlsMpc.EdwardsHinted.offsetSumFast ()).map (TlsMpc.FieldDag.Expr.eval i))) ∧
    (Curve.dBitSum.program = some p →
      Conv.Computes p 1261 [.never, .never] (fun i => (TlsMpc.EdwardsHinted.bitSum ()).map (TlsMpc.FieldDag.Expr.eval i))) ∧
    (Curve.dAffineBitSum.program = some p →
      Conv.Computes p 757 [.never, .never] (fun i => (TlsMpc.EdwardsHinted.affineBitSum ()).map (TlsMpc.FieldDag.Expr.eval i))) ∧
    (Curve.dLiftOpen.program = some p →
      Conv.Computes p 8 [.pub, .pub, .pub, .pub, .pub, .never]
        (fun i => (TlsMpc.EdwardsHinted.liftOpen ()).map (TlsMpc.FieldDag.Expr.eval i))) ∧
    (Curve.dOnCurve.program = some p → Conv.Computes p 2 [.pub] (fun i => [TlsMpc.EdwardsShare.onCurve.eval i])) ∧
    (Curve.dAddU.program = some p →
      Conv.Computes p 4 [.never, .never] (fun i => TlsMpc.EdwardsShare.addU.map (TlsMpc.FieldDag.Expr.eval i))) :=
  ⟨fun hd => Curve.x25519_computes hinv p hd hm, fun hd => Curve.offsetSumFast_computes hinv p hd hm,
   fun hd => Curve.bitSum_computes hinv p hd hm, fun hd => Curve.affineBitSum_computes hinv p hd hm,
   fun hd => Curve.liftOpen_computes hinv p hd hm, fun hd => Curve.onCurve_computes hinv p hd hm,
   fun hd => Curve.addU_computes hinv p hd hm⟩

/-- **F22b: the checks vanish on honest inputs** [K; hyp: `AddClosed`]. `edwards-prepare`'s 505
leading outputs (the masked recipient check, the bit checks) are zero on `PrepareIn` inputs;
`lift-open`'s four checks are zero for bits and curve mask points; `lift-point`'s opened
`Z = M_A + M_B + P` is a curve point on `LiftPointIn` inputs; `edwards-bit-table`'s 126 link checks are
zero when its window bases are linked (`EdwardsHinted.LinkedFrom`, `bitTable_sound`'s hypothesis;
for honest hints this is the group law, `proofs/` `bitTable_entries`). -/
theorem s11_checks_vanish (hA : Curve.AddClosed) (input : Nat → F) :
    (Curve.PL.PrepareIn input → ∀ i, i < 505 →
      (TlsMpc.EdwardsAffine.prepare.map (TlsMpc.FieldDag.Expr.eval input)).getD i 0 = 0) ∧
    (Curve.PL.IsBit (input 2) → Curve.PL.IsBit (input 3) →
      TlsMpc.Node.Local.Edwards.curveValue (input 4, input 5) = 0 →
      TlsMpc.Node.Local.Edwards.curveValue (input 6, input 7) = 0 → ∀ i, i < 4 →
      ((TlsMpc.EdwardsHinted.liftOpen ()).map (TlsMpc.FieldDag.Expr.eval input)).getD (1 + i) 0 = 0) ∧
    (Curve.PL.LiftPointIn input →
      TlsMpc.Node.Local.Edwards.onCurve (((TlsMpc.EdwardsHinted.liftPoint ()).map (TlsMpc.FieldDag.Expr.eval input)).getD 3 0,
        ((TlsMpc.EdwardsHinted.liftPoint ()).map (TlsMpc.FieldDag.Expr.eval input)).getD 4 0) = true) ∧
    (Curve.TableLinked input → ∀ i, i < 126 →
      ((TlsMpc.EdwardsHinted.bitTable ()).map (TlsMpc.FieldDag.Expr.eval input)).getD i 0 = 0) :=
  ⟨Curve.prepare_checks input, Curve.liftOpen_checks input, Curve.liftPoint_Z_onCurve hA input,
   Curve.bitTable_checks input⟩

/-- **F22a + F22b, `offsetPrepare` through `jointRun` without program hypotheses** [M; hyp:
`FieldInverse`, `CompleteAddition`, `AddClosed`, `RecipientOnCurve`]: `edwards-prepare` loaded as its
declaration's program (2031 masks), the honest inputs `PrepareIn`; the 505 checks are derived. Both
parties return `prepState f0 (P_A + P_B)`; the table handles hold the program's outputs 505 … 1530.
(The other restated runs, same composition: `Curve.agree_honest'`, `offsetStep_value'`,
`offsetStepFast_honest'`, `signatures_honest'`, `torsion_honest'`, `agreeAffine_honest'`,
`agreeHinted_honest'`, `tables_honest'` (link checks from `TableLinked`), `splitAgree_montU'`, in
`Flows/CurveRunJ.lean`.) Named `s11_offsetPrepare_honest'` on `s11-curve`; renamed on the merge
because `scripts/check_axioms.py` reads names between single quotes from Lean's output. -/
theorem s11_offsetPrepare_honest_derived (E : Env) (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hCA : Curve.CompleteAddition)
    (hAC : Curve.AddClosed) (hR : Curve.RecipientOnCurve)
    (hh : ∀ m, (E.hash m).length = 32) (pp : TlsMpc.FieldDag.V3.Program)
    (hP : E.programs Curve.prepareName = some pp) (hd : Curve.dPrepare.program = some pp) (hm2031 : pp.masks = 2031)
    (σA σB : Store) (I : Ideal) (f0 : Nat) (s : Curve.OffsetSlots) (u : FieldH) (uv : F)
    (hu : I.fields u.id = some uv) (hul : u.id < f0)
    (rA rB : F) (hrA : σA.elems s.r = [rA]) (hrB : σB.elems s.r = [rB])
    (bA bB : Nat → Bool) (hbA : σA.elems s.bits = (List.range 252).map fun i => TlsMpc.X25519.bitValue (bA i))
    (hbB : σB.elems s.bits = (List.range 252).map fun i => TlsMpc.X25519.bitValue (bB i))
    (mA mB : Nat → F) (hmA : σA.elems s.masks = (List.range 2031).map mA)
    (hmB : σB.elems s.masks = (List.range 2031).map mB) (hm : ∀ i, i < 2031 → mA i + mB i ≠ 0)
    (hin : Curve.PL.PrepareIn (fun i => (Curve.prepVals uv rA rB bA bB).getD i 0))
    (PA PB : TlsMpc.Node.Local.Edwards.Value)
    (hnA : (σA.bytes s.nonce).length = 32) (hsA : (σA.bytes s.share).length = 32)
    (hnB : (σB.bytes s.nonce).length = 32) (hsB : (σB.bytes s.share).length = 32)
    (hdA : TlsMpc.Node.Local.Edwards.decode (σA.bytes s.share) = some PA)
    (hdB : TlsMpc.Node.Local.Edwards.decode (σB.bytes s.share) = some PB)
    (hvA : TlsMpc.Node.Local.Edwards.isValid PA = true) (hvB : TlsMpc.Node.Local.Edwards.isValid PB = true)
    (hvS : TlsMpc.Node.Local.Edwards.isValid (TlsMpc.Node.Local.Edwards.add PA PB) = true)
    (hc : E.hash (commitFrame Curve.offsetTag .a (σA.bytes s.nonce) (σA.bytes s.share)) ≠
      E.hash (commitFrame Curve.offsetTag .b (σB.bytes s.nonce) (σB.bytes s.share))) :
    ∃ J, Run.JRet (jointRun E (Curve.offsetPrepare E.hash .a f0 s u) (Curve.offsetPrepare E.hash .b f0 s u) σA σB I)
        (Curve.prepState f0 (TlsMpc.Node.Local.Edwards.add PA PB)) (Curve.prepState f0 (TlsMpc.Node.Local.Edwards.add PA PB))
        J σA σB ∧
      (∀ i, i < 1026 → J.fields (Curve.prepOuts f0 + 505 + i) =
        some ((TlsMpc.EdwardsAffine.prepare.map
          (TlsMpc.FieldDag.Expr.eval (fun i => (Curve.prepVals uv rA rB bA bB).getD i 0))).getD (505 + i) 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  Curve.offsetPrepare_honest' E hinv hCA hAC hR hh pp hP hd hm2031 σA σB I f0 s u uv hu hul rA rB hrA hrB bA bB hbA hbB
    mA mB hmA hmB hm hin PA PB hnA hsA hnB hsB hdA hdB hvA hvB hvS hc

/-- **F25b: the batched inversion, the hints and the public table never fail on curve points** [K;
hyp: `FieldInverse`, `AddClosed`, `ExtClosed`]: `invAll` returns the inverses of nonzero elements
(its check passes), `toAffineAll` succeeds on nonzero `Z`; a party's hints succeed when `Z` and its
mask point are curve points; the public table of a curve point succeeds. -/
theorem s11_toAffineAll_live (hinv : TlsMpc.FieldDag.V3.FieldInverse) (hA : Curve.AddClosed) (hX : Curve.ExtClosed) :
    (∀ zs : List F, (∀ z ∈ zs, z ≠ 0) → TlsMpc.Node.Local.Edwards.invAll zs = some (zs.map inverse)) ∧
    (∀ es : List TlsMpc.Node.Local.Edwards.ExtV, (∀ e ∈ es, e.z ≠ 0) →
      (TlsMpc.Node.Local.Edwards.toAffineAll es).isSome = true) ∧
    (∀ (me : Party) (z mask : TlsMpc.Node.Local.Edwards.Value), TlsMpc.Node.Local.Edwards.curveValue z = 0 →
      TlsMpc.Node.Local.Edwards.curveValue mask = 0 → (TlsMpc.Node.Local.Edwards.hints me z mask).isSome = true) ∧
    (∀ p : TlsMpc.Node.Local.Edwards.Value, TlsMpc.Node.Local.Edwards.curveValue p = 0 →
      (TlsMpc.Node.Local.Edwards.publicTable p).isSome = true) :=
  ⟨Curve.LL.invAll_some hinv, Curve.LL.toAffineAll_isSome hinv, Curve.LL.hints_isSome hinv hA hX,
   Curve.LL.publicTable_isSome hinv hX⟩

/-- **F22 (part): the point exchange with `m` points each** [M]: every chunk decodes, the points and
the sums are valid, the commitments differ ⇒ both parties return the `m` sums `P_A,j + P_B,j`
(the K₀ exchange of `prepareSecond`). -/
theorem s11_pointExchange_many_honest (E : Env) (hh : ∀ m, (E.hash m).length = 32) (tag : Bytes)
    (σA σB : Store) (I : Ideal) (nA sA nB sB m : Nat) (PA PB : Nat → TlsMpc.Node.Local.Edwards.Value)
    (hnA : (σA.bytes nA).length = 32) (hsA : (σA.bytes sA).length = 32 * m)
    (hnB : (σB.bytes nB).length = 32) (hsB : (σB.bytes sB).length = 32 * m)
    (hdA : ∀ j, j < m → TlsMpc.Node.Local.Edwards.decode (((σA.bytes sA).drop (32 * j)).take 32) = some (PA j))
    (hdB : ∀ j, j < m → TlsMpc.Node.Local.Edwards.decode (((σB.bytes sB).drop (32 * j)).take 32) = some (PB j))
    (hvA : ∀ j, j < m → TlsMpc.Node.Local.Edwards.isValid (PA j) = true)
    (hvB : ∀ j, j < m → TlsMpc.Node.Local.Edwards.isValid (PB j) = true)
    (hvS : ∀ j, j < m → TlsMpc.Node.Local.Edwards.isValid (TlsMpc.Node.Local.Edwards.add (PA j) (PB j)) = true)
    (hc : E.hash (commitFrame tag .a (σA.bytes nA) (σA.bytes sA)) ≠
      E.hash (commitFrame tag .b (σB.bytes nB) (σB.bytes sB))) :
    Run.JRet (jointRun E (Curve.pointExchange E.hash .a tag nA sA m) (Curve.pointExchange E.hash .b tag nB sB m) σA σB I)
      ((List.range m).map fun j => TlsMpc.Node.Local.Edwards.add (PA j) (PB j))
      ((List.range m).map fun j => TlsMpc.Node.Local.Edwards.add (PA j) (PB j)) I σA σB :=
  Curve.pointExchange_many_honest E hh tag σA σB I nA sA nB sB m PA PB hnA hsA hnB hsB hdA hdB hvA hvB hvS hc

end FlowsS11

/-! ### 7d. GHASH key-power shares and TLS (stage S12; plan 7.1 P-GHASH, 8.1 T3/T4-TLS; numbered 7c
on the S12 branch, renumbered when the stages were joined on `scripts-stack`)

The S12 scripts (`TlsMpc/Node/Flows/{Ghash,Tls,TlsProofs}.lean`, the local arithmetic
`TlsMpc/Node/Local/Ghash.lean`, the backends `Flows/TlsBackend.lean`; S12_NOTES.md). Status letters
as above; **M** marks statements about the Lean model of the engines (`Engine/Model.lean`) or about
a kernel's output read through the script's layout. The kernels' circuits computing their Lean
definitions (`TlsBase.circuitOf`, `Ghash.GhashLoaded`) is T2's trust, as for the contact kernels. -/

section FlowsS12

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide

/-- **P-GHASH (a), one round of the doubling schedule** [M]: shares of H¹ … Hᵐ, extended by local
squares and the engines' odd powers (whose two values XOR to the product of the parties' inputs),
share H¹ … Hᵗ for m ≤ t ≤ 2m. No multiplication is evaluated; `GhashField.laws`. -/
theorem s12_ghash_shared_extend (a b : List (BitVec 128)) (h : BitVec 128) (m t : Nat) (oa ob : List (BitVec 128))
    (hs : Local.Ghash.Shared a b h m) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 2 * m)
    (hodd : ∀ i, i < t - m → (m + 1 + i) % 2 = 1 →
      oa.getD (i / 2) 0 ^^^ ob.getD (i / 2) 0 =
        Local.Ghash.mul (Local.Ghash.left a (m + 1 + i) ^^^ Local.Ghash.left b (m + 1 + i)) (a.getD 0 0 ^^^ b.getD 0 0)) :
    Local.Ghash.Shared (Local.Ghash.extend a t oa) (Local.Ghash.extend b t ob) h t :=
  Local.Ghash.shared_extend a b h m t oa ob hs hm hmt ht hodd

/-- **P-GHASH (a), the first share** [K]: A's mask and the `gcm-key-share` output opened to B share
H = `hashKeyOf K` (`gcmKeyShare_reshare`). -/
theorem s12_ghash_keyShare_shared (K m : List (BitVec 8)) (hK : K.length = 60) (hm : m.length = 16) :
    Local.Ghash.Shared [Local.Ghash.ofBytes m] [Local.Ghash.ofBytes (kernelOut HybridKernel.gcmKeyShare (K ++ m))]
      (HybridKernel.hashKeyOf K) 1 :=
  Ghash.keyShare_shared K m hK hm

/-- **P-GHASH (a), a round with the engines' values** [K]: A's masks and the `gcm-multiply` outputs
of the round (`Ghash.roundOpened`) keep the sharing (`gcmMultiply_reshare`). -/
theorem s12_ghash_round_shared (a b : List (BitVec 128)) (h : BitVec 128) (m t : Nat) (masks : List (List (BitVec 8)))
    (hs : Local.Ghash.Shared a b h m) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 2 * m)
    (hmask : ∀ x ∈ masks, x.length = 16) (hcount : masks.length = Local.Ghash.oddCount m t) :
    Local.Ghash.Shared (Local.Ghash.extend a t (masks.map Local.Ghash.ofBytes))
      (Local.Ghash.extend b t ((Ghash.roundOpened a b t masks).map Local.Ghash.ofBytes)) h t :=
  Ghash.round_shared a b h m t masks hs hm hmt ht hmask hcount

/-- **P-GHASH (b) and the halves of (c)** [M]: halves of shared shares with enough powers XOR to
GCM's GHASH of the header and ciphertext (`shared_halves_are_ghash_proved`). -/
theorem s12_ghash_halves_xor (traffic aad ct : List (BitVec 8)) (a b : List (BitVec 128)) (n : Nat)
    (hs : Local.Ghash.Shared a b (HybridKernel.hashKeyOf traffic) n) (hn : (Local.Ghash.blocks aad ct).length ≤ n) :
    Aes.addRoundKey Gcm.concrete.aes (Local.Ghash.toBytes (Local.Ghash.half a aad ct))
        (Local.Ghash.toBytes (Local.Ghash.half b aad ct)) =
      HybridKernel.ghashOf traffic aad ct :=
  Local.Ghash.halves_xor traffic aad ct a b n hs hn

/-- **P-GHASH (d), the key share hides H** [K]: for any two traffic keys, shifting A's mask by
H ⊕ H' (an involution) gives B the same opened value. The bijection form `proofs/` consumes. -/
theorem s12_ghash_keyShare_hides (K K' m : List (BitVec 8)) (hK : K.length = 60) (hK' : K'.length = 60)
    (hm : m.length = 16) :
    Local.Ghash.ofBytes (kernelOut HybridKernel.gcmKeyShare (K' ++ Local.Ghash.toBytes
        (Local.Ghash.ofBytes m ^^^ HybridKernel.hashKeyOf K ^^^ HybridKernel.hashKeyOf K'))) =
      Local.Ghash.ofBytes (kernelOut HybridKernel.gcmKeyShare (K ++ m)) :=
  (Ghash.keyShare_hides K K' m hK hK' hm).1

/-- **P-GHASH (d), a product's opening hides the product** [K]: whatever B supplied, exactly one of
A's masks gives B any given value. -/
theorem s12_ghash_multiply_hides (la lb ra rb : List (BitVec 8)) (h1 : la.length = 16) (h2 : lb.length = 16)
    (h3 : ra.length = 16) (h4 : rb.length = 16) (seen : BitVec 128) :
    ∃ mask : BitVec 128, ∀ m : List (BitVec 8), m.length = 16 →
      (Local.Ghash.ofBytes (kernelOut HybridKernel.gcmMultiply (la ++ lb ++ ra ++ rb ++ m)) = seen ↔
        Local.Ghash.ofBytes m = mask) :=
  Ghash.multiply_hides la lb ra rb h1 h2 h3 h4 seen

/-- **T3, GHASH shares, B honest** [M]: the adversary A's view of a key share is empty, against any
adversary (everything is opened to B). -/
theorem s12_ghash_keyShare_viewD_B (E : Env) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)
    (n : Nat) (traffic : BoolH) (maskSlot dst : Nat) :
    (withAdv E .b adv (Ghash.keyShareScript n traffic maskSlot dst) σ I vD).viewD = [] :=
  Ghash.keyShare_viewD_B E adv σ I vD n traffic maskSlot dst

/-- **T3, GHASH shares, B honest, a round** [M]: the adversary A's view is empty. -/
theorem s12_ghash_round_viewD_B (E : Env) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)
    (n c l r m dst : Nat) :
    (withAdv E .b adv (Ghash.roundScript n c l r m dst) σ I vD).viewD = [] :=
  Ghash.round_viewD_B E adv σ I vD n c l r m dst

/-- **T3, GHASH shares, A honest** [M]: the adversary B receives at most one value, labelled
ghashMaskedPower: `gcm-key-share` on the traffic block and A's mask (`H ⊕ mask`). -/
theorem s12_ghash_keyShare_disclosure_A (E : Env) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)
    (hE : Ghash.GhashLoaded E) (n : Nat) (traffic : BoolH) (maskSlot dst : Nat)
    (K m : List (BitVec 8)) (hK : K.length = 60) (hm : m.length = 16) (htn : traffic.id < n)
    (hk : I.bools traffic.id = some (bitsOf K)) (hσ : σ.bits maskSlot = bitsOf m) :
    (withAdv E .a adv (Ghash.keyShareScript n traffic maskSlot dst) σ I vD).viewD <+:
      [⟨Ghash.masked, .bits (bitsOf (kernelOut HybridKernel.gcmKeyShare (K ++ m)))⟩] :=
  Ghash.keyShare_disclosure_A E adv σ I vD hE n traffic maskSlot dst K m hK hm htn hk hσ

/-- **T4-TLS, the seal: `sealCtr_with_tag_is_seal` with its halves DISCHARGED** [K]: `tls-seal-ctr`'s
header ‖ ciphertext and `gcm-tag` on its pad and the two parties' halves of shares of H¹ … Hⁿ
(n covering the record) is `TlsRecord.sealCore`. Closes P-GHASH (c) for the Lean code. -/
theorem s12_tls_seal_is_record (kind size padding : Nat) (K seqB C : List (BitVec 8)) (hK : K.length = 60)
    (hs : seqB.length = 8) (hC : C.length = size) (a b : List (BitVec 128)) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (Tls.innerLength size padding) ≤ nPow) :
    let out := kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))
    let hc := out.take (5 + Tls.innerLength size padding)
    let pad := (out.drop (5 + Tls.innerLength size padding)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5))
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB C kind padding :=
  Tls.seal_is_record kind size padding K seqB C hK hs hC a b nPow hsh hn

/-- **T4-TLS, the tag check** [K]: with honest halves the private acceptance byte is 255 exactly
when the received tag is GCM's tag of the received header and ciphertext under the server key. -/
theorem s12_tls_check_accepts (K seqB hdr ct tag : List (BitVec 8)) (hK : K.length = 60) (hs : seqB.length = 8)
    (ht : tag.length = 16) (a b : List (BitVec 128)) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow) :
    kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes (Local.Ghash.half a hdr ct) ++
        (Local.Ghash.toBytes (Local.Ghash.half b hdr ct) ++ tag)))) =
      [if Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB) = tag
        then 255 else 0] :=
  Tls.check_accepts K seqB hdr ct tag hK hs ht a b nPow hsh hn

open TlsMpc.TypedOpenKernel in
open TlsMpc.HybridKernel (lookup) in
/-- **T4-TLS, the typed open** [K] (`typed_pair_refines`, `class_fields`): the opened bit is 0 or
255; on 0 the typed kernel's event and fields, on 255 `tls-frame`'s, are the class kernel's,
`fields (classSpec …)`. -/
theorem s12_tls_open_event_refines (cap : Nat) (typed frame : BVExpr.Assignment)
    (hp : (lookup (frameInputs cap) "parser").map (BVExpr.eval frame) =
      (lookup (typedInputs cap) "parser").map (BVExpr.eval typed))
    (hq : (lookup (frameInputs cap) "parsed").map (BVExpr.eval frame) = (typedParsed cap).map (BVExpr.eval typed)) :
    ((fieldValues (tlsOpenTyped cap) typed).getD 0 [] = [0] ∨ (fieldValues (tlsOpenTyped cap) typed).getD 0 [] = [255]) ∧
    ((fieldValues (tlsOpenTyped cap) typed).getD 0 [] = [0] →
      ((fieldValues (tlsOpenTyped cap) typed).drop 1).take 4 = fields (classSpec cap typed)) ∧
    ((fieldValues (tlsOpenTyped cap) typed).getD 0 [] = [255] →
      fieldValues (tlsFrame cap) frame = fields (classSpec cap typed)) :=
  Tls.open_event_refines cap typed frame hp hq

/-- **What the reveal kernel opens through `revealScript`** [K] (`tlsRevealMasked_value`). -/
theorem s12_tls_reveal_value (cap : Nat) (hcap : cap < 65536) (len content : List (BitVec 8)) (hl : len.length = 2)
    (hc : content.length = cap) :
    kernelOut (HybridKernel.tlsRevealMasked cap) (len ++ content) =
      len ++ (if Tls.lengthOf len ≤ cap then content.take (Tls.lengthOf len) ++ List.replicate (cap - Tls.lengthOf len) 0
        else List.replicate cap 0) :=
  Tls.reveal_value cap hcap len content hl hc

/-- **A revealed range below the length is the server's bytes** [K-fn]. -/
theorem s12_tls_range_value (content : List (BitVec 8)) (n lo hi : Nat) (hhi : hi ≤ n) (hn : n ≤ content.length) :
    (((content.take n ++ List.replicate (content.length - n) 0).drop lo).take (hi - lo)) =
      (content.drop lo).take (hi - lo) :=
  Tls.range_value content n lo hi hhi hn

/-- **The Finished check through `verifyScript`** [K] (`tlsVerifyFinished_spec`). -/
theorem s12_tls_verify_value (S hash message : List (BitVec 8)) (hS : S.length = 60) (hh : hash.length = 32)
    (hm : message.length = 36) :
    kernelOut HybridKernel.tlsVerifyFinished (S ++ (hash ++ message)) =
      [if TlsHandshake.finishedMessage Sha256.concrete (S.take 32) hash = message then 255 else 0] :=
  Tls.verify_value S hash message hS hh hm

/-- **The handshake record opening through `openHandshakeScript`** [K] (`tlsOpenHandshake_spec`). -/
theorem s12_tls_openHandshake_value (size : Nat) (S seqB record : List (BitVec 8)) (hS : S.length = 60)
    (hs : seqB.length = 8) (hr : record.length = size) :
    kernelOut (HybridKernel.tlsOpenHandshake size) (S ++ (seqB ++ record)) =
      TlsPublicHandshake.gate ByteAuth.concrete
        (TlsReceive.spec ((S.drop 32).take 16) ((S.drop 48).take 12) seqB record) :=
  Tls.openHandshake_value size S seqB record hS hs hr

/-- **The 64-record window keeps at most 64** [K-fn] (`tls_worker_v3.cpp:321-329`). -/
theorem s12_tls_window_bound (w : Tls.Window) (id : Nat) : (w.push id).1.length ≤ Tls.keptRecords :=
  Tls.Window.push_bound w id

/-- **The seal's first phase is well formed** [K]: the shell's `check` accepts every instruction of
`sealCtrScript` on every branch, given the traffic block and content live and `tls-seal-ctr`'s
signature. -/
theorem s12_tls_sealCtr_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic content : BoolH)
    (seq : List (BitVec 8)) (kind size padding : Nat) (cm : List Mark) (hf : Fresh c n) (htn : traffic.id < n)
    (hcn : content.id < n) (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩)
    (hc : c.bool? content = some ⟨cm, false⟩) (hcm : cm.length = 8 * size) (hs : seq.length = 8)
    (hsize : size + 1 + padding ≤ 16385)
    (hsig : sigs (Tls.sealCtrName kind size padding) =
      some ⟨8 * (68 + size), List.replicate (8 * (5 + Tls.innerLength size padding)) .pub ++ List.replicate 128 .never⟩) :
    WF sigs c (Tls.sealCtrScript n traffic content seq kind size padding) :=
  Tls.sealCtrScript_wf sigs c n traffic content seq kind size padding cm hf htn hcn ht hc hcm hs hsize hsig

end FlowsS12

/-! ### 7d (continued). S12 closed gaps: WF, the pipe, T4-TLS and P-GHASH through `jointRun`, value-level T3
(numbered 7c continued on the S12 branch, renumbered when merged into `scripts-stack`)

The second S12 pass (`TlsMpc/Node/Flows/{TlsWF,TlsBounded,TlsRun,TlsOpenRun,TlsGhashRun,TlsClassSeal,
TlsDerive,TlsT3}.lean`; S12_NOTES.md, "Second pass"). Closes PROOF_GAPS F13, F14, F15, F16, F18, F20.
Status letters as above (**M**: about the Lean model of the engines, `Engine/Model.lean`; the kernels'
circuits computing their Lean definitions, `TlsBase.circuitOf` / `Ghash.GhashLoaded`, is T2's trust). -/

section FlowsS12b

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide

/-- **WF, the open** [M] (F14): the shell's `check` accepts every instruction of `openScript` on every
branch (bit 0: the typed kernel's fields; bit 255: `tls-frame`; any other bit: abort), given the
parser state and traffic block live and the three kernels' signatures. -/
theorem s12_tls_open_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (parser traffic : BoolH)
    (seq tag recordPadded size : List (BitVec 8)) (cap halfSlot : Nat) (pm : List Mark) (hf : Fresh c n)
    (hpn : parser.id < n) (htn : traffic.id < n) (hp : c.bool? parser = some ⟨pm, false⟩) (hpm : pm.length = 88)
    (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩) (hs : seq.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2) (hcap : cap ≤ 65536)
    (hcheck : sigs Tls.checkName = some ⟨8 * 116, List.replicate 8 .never⟩)
    (htyped : sigs (Tls.typedName cap) = some ⟨8 * (82 + cap), Tls.typedMarks cap⟩)
    (hframe : sigs (Tls.frameName cap) = some ⟨8 * (11 + (cap - 17)), Tls.frameMarks cap⟩) :
    WF sigs c (Tls.openScript n parser traffic seq tag recordPadded size cap halfSlot) :=
  Tls.openScript_wf sigs c n parser traffic seq tag recordPadded size cap halfSlot pm hf hpn htn hp hpm ht hs htag hr hz
    hcap hcheck htyped hframe

/-- **WF, the class seal** [M] (F14). -/
theorem s12_tls_sealClass_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic content : BoolH)
    (seq : List (BitVec 8)) (size : Nat) (cm : List Mark) (hf : Fresh c n) (htn : traffic.id < n) (hcn : content.id < n)
    (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩) (hc : c.bool? content = some ⟨cm, false⟩)
    (hcm : cm.length = 8 * size) (hs : seq.length = 8) (hcap : Tls.capacity size ≤ 65536)
    (hsig : sigs (Tls.sealClassName (Tls.capacity size)) = some ⟨8 * (70 + Tls.capacity size),
      List.replicate (8 * (1 + 5 + Tls.capacity size + 1)) .pub ++ List.replicate 128 .never⟩) :
    WF sigs c (Tls.sealClassScript n traffic content seq size) :=
  Tls.sealClassScript_wf sigs c n traffic content seq size cm hf htn hcn ht hc hcm hs hcap hsig

/-- **WF, a doubling round** [M] (F14): every input `once`, each mask reaching one copy. -/
theorem s12_ghash_round_wf (sigs : Bytes → Option Sig) (ctx : Ctx) (n c leftSlot rightSlot maskSlot dst : Nat)
    (hf : Fresh ctx n) (hsig : sigs Ghash.multiplyName = some ⟨8 * 80, List.replicate 128 .toB⟩) :
    WF sigs ctx (Ghash.roundScript n c leftSlot rightSlot maskSlot dst) :=
  Ghash.roundScript_wf sigs ctx n c leftSlot rightSlot maskSlot dst hf hsig

/-- **WF, the server-byte reveal** [M] (F14). -/
theorem s12_tls_reveal_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (length content : BoolH) (cap : Nat)
    (lm cm : List Mark) (hf : Fresh c n) (hln : length.id < n) (hcn : content.id < n)
    (hl : c.bool? length = some ⟨lm, false⟩) (hc : c.bool? content = some ⟨cm, false⟩)
    (hlm : lm.length = 16) (hcm : cm.length = 8 * cap) (hcap : cap ≤ 65536)
    (hsig : sigs (Tls.revealName cap) = some ⟨8 * (2 + cap), List.replicate (16 + 8 * cap) .pub⟩) :
    WF sigs c (Tls.revealScript n length content cap) :=
  Tls.revealScript_wf sigs c n length content cap lm cm hf hln hcn hl hc hlm hcm hcap hsig

/-- **WF, the handshake** [M] (F14): `tls-derive` (the agreement word consumed and freed). The parser,
the handshake record, the Finished check, the client Finished and the agreement are
`Tls.parserScript_wf`, `openHandshakeScript_wf`, `verifyScript_wf`, `finishScript_wf`, `agreeScript_wf`. -/
theorem s12_tls_derive_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (agreement : BoolH) (helloHash : List (BitVec 8))
    (hf : Fresh c n) (han : agreement.id < n)
    (ha : c.bool? agreement = some ⟨List.replicate 255 .never, false⟩) (hh : helloHash.length = 32)
    (hsig : sigs Tls.deriveName = some ⟨511, List.replicate 1216 .never⟩) :
    WF sigs c (Tls.deriveScript n agreement helloHash) :=
  Tls.deriveScript_wf sigs c n agreement helloHash hf han ha hh hsig

/-- **WF, the client Finished** [M] (F14). -/
theorem s12_tls_finish_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (main clientHs : BoolH)
    (serverHash clientHash certificate : List (BitVec 8)) (hf : Fresh c n) (hmn : main.id < n) (hcn : clientHs.id < n)
    (hm : c.bool? main = some ⟨List.replicate 256 .never, false⟩)
    (hch : c.bool? clientHs = some ⟨List.replicate 480 .never, false⟩)
    (hsh : serverHash.length = 32) (hchl : clientHash.length = 32) (hcert : certificate.length ≤ 16384)
    (hsig : sigs (Tls.finishName certificate.length) = some ⟨8 * (156 + certificate.length),
      List.replicate 960 .never ++ List.replicate (8 * Tls.finishedLength certificate.length) .pub⟩) :
    WF sigs c (Tls.finishScript n main clientHs serverHash clientHash certificate) :=
  Tls.finishScript_wf sigs c n main clientHs serverHash clientHash certificate hf hmn hcn hm hch hsh hchl hcert hsig

/-- **The pipe, the open** [M] (F18): every instruction of `openScript` on every branch is
`Instr.Bounded`, so the batch encoding round-trips (`nextBatch_bounded`). All 17 S12 scripts:
`Tls.*_bounded`, `Ghash.keyShare_bounded`, `Ghash.round_bounded` (TlsBounded.lean). -/
theorem s12_tls_open_bounded (n : Nat) (parser traffic : BoolH) (seq tag recordPadded size : List (BitVec 8))
    (cap halfSlot : Nat) (hn : n + 16 < B64) (hp : parser.id < B64) (ht : traffic.id < B64) (hs : seq.length = 8)
    (htag : tag.length = 16) (hr : recordPadded.length < 4294967296) (hz : size.length = 2) (hcap : cap < 4294967296) :
    Every Instr.Bounded (Tls.openScript n parser traffic seq tag recordPadded size cap halfSlot) :=
  Tls.open_bounded n parser traffic seq tag recordPadded size cap halfSlot hn hp ht hs htag hr hz hcap

/-- **The pipe, a doubling round** [M] (F18). -/
theorem s12_ghash_round_bounded (n c leftSlot rightSlot maskSlot dst : Nat) (hn : n + 7 < B64) :
    Every Instr.Bounded (Ghash.roundScript n c leftSlot rightSlot maskSlot dst) :=
  Ghash.round_bounded n c leftSlot rightSlot maskSlot dst hn

/-- **T4-TLS for the seal, through `jointRun`** [M] (F13 (a)): two honest parties run the seal's first
phase; each then computes its OWN half from its own shares over the opened header and ciphertext; the
second phase returns to both a tag such that header ‖ ciphertext ‖ tag is `TlsRecord.sealCore` of the
key, IV, sequence, content, kind and padding (P-GHASH (a) for the shares). -/
theorem s12_tls_seal_honest (E : Env) (kind size padding : Nat)
    (hctr : E.circuits (Tls.sealCtrName kind size padding) =
      some (TlsBase.circuitOf (HybridKernel.tlsSealCtr kind size padding)))
    (htag : E.circuits Tls.tagName = some (TlsBase.circuitOf HybridKernel.gcmTag))
    (n m : Nat) (hm : n + 3 < m) (traffic content : BoolH) (K seqB C : List (BitVec 8)) (hK : K.length = 60)
    (hs : seqB.length = 8) (hC : C.length = size) (htn : traffic.id < n) (hcn : content.id < n)
    (σA σB : Store) (I : Ideal) (hIt : I.bools traffic.id = some (bitsOf K)) (hIc : I.bools content.id = some (bitsOf C))
    (halfSlot : Nat) (a b : List (BitVec 128)) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (Tls.innerLength size padding) ≤ nPow) :
    let hc := (kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))).take
      (5 + Tls.innerLength size padding)
    ∃ J, Run.JRet (jointRun E (Tls.sealCtrScript n traffic content seqB kind size padding)
        (Tls.sealCtrScript n traffic content seqB kind size padding) σA σB I) (hc, ⟨n + 3⟩) (hc, ⟨n + 3⟩) J σA σB ∧
      ∀ σA' σB' : Store,
        σA'.bits halfSlot = TlsBase.bitsOfW (Local.Ghash.half a (hc.take 5) (hc.drop 5)) →
        σB'.bits halfSlot = TlsBase.bitsOfW (Local.Ghash.half b (hc.take 5) (hc.drop 5)) →
        ∃ J' tag, Run.JRet (jointRun E (Tls.tagScript m ⟨n + 3⟩ halfSlot) (Tls.tagScript m ⟨n + 3⟩ halfSlot) σA' σB' J)
            tag tag J' σA' σB' ∧
          hc ++ tag = TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB C kind padding :=
  Tls.seal_honest E kind size padding hctr htag n m hm traffic content K seqB C hK hs hC htn hcn σA σB I hIt hIc
    halfSlot a b nPow hsh hn

/-- **The binding the vectors only tested** [K] (F13 (b)): the byte `openScript` binds to
`tls-open-typed`'s `accepted` input is `gcm-check`'s output on the two halves, and with honest halves
of shared key powers it is 255 exactly when the received tag is GCM's tag. -/
theorem s12_tls_open_binding_honest (cap : Nat) (P K seqB recordPadded size hdr ct tag : List (BitVec 8))
    (hP : P.length = 11) (hK : K.length = 60) (hs : seqB.length = 8) (hr : recordPadded.length = cap)
    (hz : size.length = 2) (ht : tag.length = 16) (a b : List (BitVec 128)) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow) :
    (HybridKernel.lookup (TypedOpenKernel.typedInputs cap) "accepted").map (BVExpr.eval (assignOf
      (Tls.typedInput P K seqB recordPadded size (kernelOut HybridKernel.gcmCheck
        (Tls.checkInput K seqB (Local.Ghash.half a hdr ct) (Local.Ghash.half b hdr ct) tag))))) =
      [if Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB) = tag
        then 255 else 0] :=
  Tls.open_binding_honest cap P K seqB recordPadded size hdr ct tag hP hK hs hr hz ht a b nPow hsh hn

/-- **T4-TLS for the open, through `jointRun`** [M] (F13 (b)): two honest parties' run of `openScript`
RETURNS the same opening to both, and whichever handshake bit was opened, the event and the values
behind the parser, length and content handles are exactly the four fields of the single class kernel
`tls-open-application-class CAP` (`classSpec`: the post-handshake parser on the record's parse). -/
theorem s12_tls_open_class (E : Env) (cap : Nat)
    (hcE : E.circuits Tls.checkName = some (TlsBase.circuitOf HybridKernel.gcmCheck))
    (htE : E.circuits (Tls.typedName cap) = some (TlsBase.circuitOf (TypedOpenKernel.tlsOpenTyped cap)))
    (hfE : E.circuits (Tls.frameName cap) = some (TlsBase.circuitOf (TypedOpenKernel.tlsFrame cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser traffic : BoolH) (hpn : parser.id < n) (htn : traffic.id < n)
    (P K seqB tag recordPadded size : List (BitVec 8)) (hP : P.length = 11) (hK : K.length = 60)
    (hs : seqB.length = 8) (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2)
    (halfSlot : Nat) (σA σB : Store) (I : Ideal) (hIp : I.bools parser.id = some (bitsOf P))
    (hIt : I.bools traffic.id = some (bitsOf K)) (xa xb : BitVec 128)
    (hA : σA.bits halfSlot = TlsBase.bitsOfW xa) (hB : σB.bits halfSlot = TlsBase.bitsOfW xb) :
    ∃ o J, Run.JRet (jointRun E (Tls.openScript n parser traffic seqB tag recordPadded size cap halfSlot)
        (Tls.openScript n parser traffic seqB tag recordPadded size cap halfSlot) σA σB I) o o J σA σB ∧
      ∃ vp vl vc, J.bools o.parser.id = some (bitsOf vp) ∧ J.bools o.length.id = some (bitsOf vl) ∧
        J.bools o.content.id = some (bitsOf vc) ∧
        [o.event, vp, vl, vc] = TypedOpenKernel.fields (TypedOpenKernel.classSpec cap (assignOf (Tls.typedInput P K seqB
          recordPadded size (kernelOut HybridKernel.gcmCheck (Tls.checkInput K seqB xa xb tag))))) :=
  Tls.open_class E cap hcE htE hfE n hcap parser traffic hpn htn P K seqB tag recordPadded size hP hK hs htag hr hz
    halfSlot σA σB I hIp hIt xa xb hA hB

/-- **A forged record, through `jointRun`** [M] (F13 (b)): with honest halves and a tag that is not
GCM's, the run returns the event `[0, 0]` after the bit 0. -/
theorem s12_tls_open_rejected_run (E : Env) (cap : Nat)
    (hcE : E.circuits Tls.checkName = some (TlsBase.circuitOf HybridKernel.gcmCheck))
    (htE : E.circuits (Tls.typedName cap) = some (TlsBase.circuitOf (TypedOpenKernel.tlsOpenTyped cap)))
    (hfE : E.circuits (Tls.frameName cap) = some (TlsBase.circuitOf (TypedOpenKernel.tlsFrame cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser traffic : BoolH) (hpn : parser.id < n) (htn : traffic.id < n)
    (P K seqB tag recordPadded size : List (BitVec 8)) (hP : P.length = 11) (hK : K.length = 60)
    (hs : seqB.length = 8) (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2)
    (halfSlot : Nat) (σA σB : Store) (I : Ideal) (hIp : I.bools parser.id = some (bitsOf P))
    (hIt : I.bools traffic.id = some (bitsOf K)) (hdr ct : List (BitVec 8)) (a b : List (BitVec 128)) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow)
    (hA : σA.bits halfSlot = TlsBase.bitsOfW (Local.Ghash.half a hdr ct))
    (hB : σB.bits halfSlot = TlsBase.bitsOfW (Local.Ghash.half b hdr ct))
    (hforged : Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB) ≠ tag) :
    ∃ o J, Run.JRet (jointRun E (Tls.openScript n parser traffic seqB tag recordPadded size cap halfSlot)
        (Tls.openScript n parser traffic seqB tag recordPadded size cap halfSlot) σA σB I) o o J σA σB ∧
      o.event = [0, 0] ∧
      (Tls.openOut cap P K seqB tag recordPadded size (Local.Ghash.half a hdr ct) (Local.Ghash.half b hdr ct)).take 1 = [0] :=
  Tls.open_rejected_run E cap hcE htE hfE n hcap parser traffic hpn htn P K seqB tag recordPadded size hP hK hs htag
    hr hz halfSlot σA σB I hIp hIt hdr ct a b nPow hsh hn hA hB hforged

/-- **P-GHASH (a) over a whole `ensure`, through `jointRun`** [M] (F20): after the first resharing and
any sequence of doubling rounds (and the local square), each a returning joint run of the scripts,
the two parties' share lists are XOR shares of H¹ … Hⁿ for the traffic block's GHASH key. -/
theorem s12_ghash_ensure_shared (E : Env) (hE : Ghash.GhashLoaded E) (K : List (BitVec 8)) (hK : K.length = 60)
    (a b : List (BitVec 128)) (h : Ghash.EnsureRuns E K a b) :
    Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) a.length :=
  Ghash.ensure_shared E hE K hK a b h

/-- **Value-level T3 for a round, A honest** [M] (F20): against any adversary B, B's view of a round is
at most one `ghashMaskedPower` release whose value is, copy by copy, `gcm-multiply` on A's inputs,
B's chosen inputs and A's fresh mask `j` (with `s12_ghash_multiply_hides`: a bijection of the mask). -/
theorem s12_ghash_round_disclosure_A (E : Env) (hE : Ghash.GhashLoaded E) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (n c leftSlot rightSlot maskSlot dst : Nat) (hc : 0 < c ∧ c ≤ 1024)
    (la mw : List (BitVec 128)) (ra : BitVec 128) (hla : la.length = c) (hmw : mw.length = c)
    (hL : σ.bits leftSlot = TlsBase.bitsOfWs la) (hR : σ.bits rightSlot = TlsBase.bitsOfW ra)
    (hM : σ.bits maskSlot = TlsBase.bitsOfWs mw) :
    ∃ (lb : List (List (BitVec 8))) (rb : List (BitVec 8)), (∀ x ∈ lb, x.length = 16) ∧ lb.length = c ∧ rb.length = 16 ∧
      (withAdv E .a adv (Ghash.roundScript n c leftSlot rightSlot maskSlot dst) σ I vD).viewD <+:
        [⟨Ghash.masked, .bits (bitsOf ((List.range c).map fun j => kernelOut HybridKernel.gcmMultiply
          (Local.Ghash.toBytes (la.getD j 0) ++ lb.getD j [] ++ Local.Ghash.toBytes ra ++ rb ++
            Local.Ghash.toBytes (mw.getD j 0))).flatten)⟩] :=
  Ghash.round_disclosure_A E hE adv σ I vD n c leftSlot rightSlot maskSlot dst hc la mw ra hla hmw hL hR hM

/-- **P-GHASH (e) for the seal** [K] (F20): a half that deviates by a nonzero δ makes the record the
parties produce NOT `TlsRecord.sealCore` (the server rejects it). -/
theorem s12_ghash_seal_deviation_rejected (kind size padding : Nat) (K seqB C : List (BitVec 8)) (hK : K.length = 60)
    (hs : seqB.length = 8) (hC : C.length = size) (a b : List (BitVec 128)) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (Tls.innerLength size padding) ≤ nPow) (δ : BitVec 128) (hδ : δ ≠ 0) :
    let out := kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))
    let hc := out.take (5 + Tls.innerLength size padding)
    let pad := (out.drop (5 + Tls.innerLength size padding)).take 16
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5)) ++
        Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5) ^^^ δ))) ≠
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB C kind padding :=
  Ghash.seal_deviation_rejected kind size padding K seqB C hK hs hC a b nPow hsh hn δ hδ

/-- **P-GHASH (e) for the open** [K] (F20): a half that deviates by a nonzero δ makes the tag check
refuse the GENUINE tag. -/
theorem s12_ghash_check_deviation (K seqB hdr ct : List (BitVec 8)) (hK : K.length = 60) (hs : seqB.length = 8)
    (a b : List (BitVec 128)) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow) (δ : BitVec 128) (hδ : δ ≠ 0) :
    kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes (Local.Ghash.half a hdr ct) ++
        (Local.Ghash.toBytes (Local.Ghash.half b hdr ct ^^^ δ) ++
          Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB))))) = [0] :=
  Ghash.check_deviation K seqB hdr ct hK hs a b nPow hsh hn δ hδ

/-- **The class seal's composition** [K] (F16): through `sealClassScript`'s layout the acceptance byte
is 255 and header ‖ ciphertext with the tag on its pad and honest halves is the exact-size record
`TlsRecord.sealCore … C 23 0`. -/
theorem s12_tls_sealClass_is_record (size : Nat) (K seqB C : List (BitVec 8)) (hK : K.length = 60)
    (hs : seqB.length = 8) (hC : C.length = size) (hb : Tls.capacity size + 17 < 65536) (a b : List (BitVec 128))
    (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (size + 1) ≤ nPow) :
    let out := kernelOut (RecordClassKernel.tlsSealClass (Tls.capacity size))
      (K ++ (seqB ++ (C ++ (List.replicate (Tls.capacity size - size) 0 ++ Tls.sizeBytes size))))
    let opened := out.take (1 + 5 + Tls.capacity size + 1)
    let hc := (opened.drop 1).take (5 + size + 1)
    let pad := (out.drop (1 + 5 + Tls.capacity size + 1)).take 16
    opened.take 1 = [255] ∧
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5)) ++
        Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5)))) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB C 23 0 :=
  Tls.sealClass_is_record size K seqB C hK hs hC hb a b nPow hsh hn

/-- **`deriveScript`'s value** [M] (F15): with the word input read through the shaped model circuit
(`Tls.shapedCircuit`, as S13's), two honest parties' run returns the handshake traffic blocks and the
main secret of the RFC 8446 schedule on the agreement's bytes and the hello hash. -/
theorem s12_tls_derive_honest (E : Env)
    (hE : E.circuits Tls.deriveName = some (Tls.shapedCircuit HybridKernel.tlsDerive (List.replicate 1216 .never)))
    (n : Nat) (agreement : BoolH) (han : agreement.id < n) (aw : Bits) (haw : aw.length = 255) (H : List (BitVec 8))
    (hH : H.length = 32) (σA σB : Store) (I : Ideal) (hIa : I.bools agreement.id = some aw) :
    ∃ J, Run.JRet (jointRun E (Tls.deriveScript n agreement H) (Tls.deriveScript n agreement H) σA σB I)
        ⟨⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩⟩ ⟨⟨n + 3⟩, ⟨n + 4⟩, ⟨n + 5⟩⟩ J σA σB ∧
      J.bools (n + 3) = some (bitsOf (KernelSpecs.TlsHandshake.trafficBlockValue
        (TlsKdf.handshakeSecrets Sha256.concrete (Tls.agreementBytes aw) H).client)) ∧
      J.bools (n + 4) = some (bitsOf (KernelSpecs.TlsHandshake.trafficBlockValue
        (TlsKdf.handshakeSecrets Sha256.concrete (Tls.agreementBytes aw) H).server)) ∧
      J.bools (n + 5) = some (bitsOf (TlsKdf.handshakeSecrets Sha256.concrete (Tls.agreementBytes aw) H).main) ∧
      J.bools agreement.id = none :=
  Tls.derive_honest E hE n agreement han aw haw H hH σA σB I hIa

/-- **Value-level T3, the seal's first phase** [M]: against any adversary, at most one `sealedRecord`
release: the header ‖ ciphertext of `tls-seal-ctr` (the pad stays private). -/
theorem s12_tls_sealCtr_disclosure (E : Env) (me : Party) (adv : Adversary) (kind size padding : Nat)
    (hE : E.circuits (Tls.sealCtrName kind size padding) =
      some (TlsBase.circuitOf (HybridKernel.tlsSealCtr kind size padding)))
    (n : Nat) (traffic content : BoolH) (K seqB C : List (BitVec 8)) (hK : K.length = 60) (hs : seqB.length = 8)
    (hC : C.length = size) (htn : traffic.id < n) (hcn : content.id < n) (σ : Store) (I : Ideal) (vD : List Release)
    (hIt : I.bools traffic.id = some (bitsOf K)) (hIc : I.bools content.id = some (bitsOf C)) :
    (withAdv E me adv (Tls.sealCtrScript n traffic content seqB kind size padding) σ I vD).viewD <+:
      [⟨Label.sealedRecord, .bits (bitsOf ((kernelOut (HybridKernel.tlsSealCtr kind size padding)
        (K ++ (seqB ++ C))).take (5 + Tls.innerLength size padding)))⟩] :=
  Tls.sealCtr_disclosure E me adv kind size padding hE n traffic content K seqB C hK hs hC htn hcn σ I vD hIt hIc

/-- **Value-level T3, the open, A honest** [M]: against any adversary B (whatever 16 bytes `hb` it
input as its half), at most two releases: the bit, which is 0 or 255, and the event, exactly the class
kernel's event (`classSpec`), whichever branch ran. A refused record: `Tls.open_disclosure_rejected`. -/
theorem s12_tls_open_disclosure_A (E : Env) (adv : Adversary) (cap : Nat)
    (hcE : E.circuits Tls.checkName = some (TlsBase.circuitOf HybridKernel.gcmCheck))
    (htE : E.circuits (Tls.typedName cap) = some (TlsBase.circuitOf (TypedOpenKernel.tlsOpenTyped cap)))
    (hfE : E.circuits (Tls.frameName cap) = some (TlsBase.circuitOf (TypedOpenKernel.tlsFrame cap)))
    (n : Nat) (hcap : 21 ≤ cap) (parser traffic : BoolH) (hpn : parser.id < n) (htn : traffic.id < n)
    (P K seqB tag recordPadded size : List (BitVec 8)) (hP : P.length = 11) (hK : K.length = 60)
    (hs : seqB.length = 8) (htag : tag.length = 16) (hr : recordPadded.length = cap) (hz : size.length = 2)
    (halfSlot : Nat) (σ : Store) (I : Ideal) (vD : List Release) (hIp : I.bools parser.id = some (bitsOf P))
    (hIt : I.bools traffic.id = some (bitsOf K)) (xa : BitVec 128) (hA : σ.bits halfSlot = TlsBase.bitsOfW xa) :
    ∃ hb : List (BitVec 8), (hb.length = 16 ∧
      ((kernelOut (TypedOpenKernel.tlsOpenTyped cap) (Tls.typedInput P K seqB recordPadded size
        (kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag))))))).take 1 = [0] ∨
       (kernelOut (TypedOpenKernel.tlsOpenTyped cap) (Tls.typedInput P K seqB recordPadded size
        (kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag))))))).take 1 = [255])) ∧
      (withAdv E .a adv (Tls.openScript n parser traffic seqB tag recordPadded size cap halfSlot) σ I vD).viewD <+:
        [⟨Label.recordKindBit, .bits (bitsOf ((kernelOut (TypedOpenKernel.tlsOpenTyped cap)
            (Tls.typedInput P K seqB recordPadded size
              (kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag))))))).take 1))⟩,
         ⟨Label.recordEvent, .bits (bitsOf ((TypedOpenKernel.classSpec cap (assignOf (Tls.typedInput P K seqB
            recordPadded size (kernelOut HybridKernel.gcmCheck
              (K ++ (seqB ++ (Local.Ghash.toBytes xa ++ (hb ++ tag)))))))).take 2))⟩] :=
  Tls.open_disclosure_A E adv cap hcE htE hfE n hcap parser traffic hpn htn P K seqB tag recordPadded size hP hK hs htag
    hr hz halfSlot σ I vD hIp hIt xa hA

end FlowsS12b

/-! ### 7e. Send (stage S13; plan 8.1 T3, T4-SEND, T7 through the scripts; numbered 7d on the S13
branch, renumbered when the stages were joined on `scripts-stack`)

The S13 scripts (`TlsMpc/Node/Flows/{Send,SendProofs}.lean`, the backend `Flows/SendBackend.lean`;
S13_NOTES.md). **M**: a kernel's output read through the script's layout; the kernels' circuits
computing their Lean definitions (`SendProofs.shapedCircuit`, `Contacts.kernelCircuit`) is T2's
trust. The four words of a seal (ephemeral public key, sender key, ephemeral and static agreements)
are S11's (E4). Compiled standalone in the S13 branch (scratch file with this text: standard axioms
only). -/

section FlowsS13

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide
open TlsMpc.Signal

/-- **T3 for the send scripts** [K]: every release of op 41 and op 61 is labelled counterWidths or
sealedEnvelope, ops 42 and 62 release nothing, the request's record phase releases under
sealedRecord only (on every branch, for every argument; with `viewD_kinds`, against any adversary). -/
theorem s13_send_reveal :
    (∀ n a, Reveals Send.sealKinds (Send.sealScript n a)) ∧
    (∀ n a, Reveals Send.sealKinds (Send.devicesScript n a)) ∧
    (∀ n cert state, Reveals [] (Send.requestScript n cert state)) ∧
    (∀ n state ats, Reveals [] (Send.requestDevicesScript n state ats)) ∧
    (∀ n traffic conv seq frame mask name,
      Reveals Send.requestSealKinds (Send.requestCtrScript n traffic conv seq frame mask name)) :=
  Registry.s13_flows_reveal

/-- **The status gate** [K]: after a seal's status other than 255 is opened, the script releases
nothing more (no envelope, no timestamp) and returns `none` with the state kept. -/
theorem s13_seal_refused_silent (n : Nat) (a : Send.SealArgs) (st : Bits) (h : st ≠ bitsOf [255]) :
    Silent (Send.afterStatus n a st) ∧ Send.afterStatus n a st =
      seqs [.freeBool ⟨n + 5⟩, .freeBool ⟨n + 6⟩, .freeBool ⟨n + 7⟩] (.done none) :=
  Send.seal_refused_silent n a st h

/-- **An accepted seal, as the script opens and keeps it** [M] (`SealSend.signalSeal_value`,
`sealValue_accepted` read through `sealScript`'s layout). -/
theorem s13_seal_accepted_value (cert cw pw ew iw classes : Nat) (official : Bool) (conv text : List (BitVec 8))
    (w : Bits) (hc : conv.length = Send.convBytes cert) (ht : text.length = Send.textBytes classes official)
    (hb : Send.SealBound cert cw pw ew iw classes official) (hcl : 1 ≤ classes) :
    let v := bitsOf conv ++ (bitsOf text ++ w)
    let a := Send.shapedAssign (Send.sealK cert cw pw ew iw classes official).inputs v
    let get := fun name => (HybridKernel.lookup (KernelSpecs.SealFixed.sealInputs cert classes official) name).map
      (BVExpr.eval a)
    let out := Send.shapedOut (Send.sealK cert cw pw ew iw classes official) v
    out.take 1 = [255] →
    let content := KernelSpecs.SealFixed.contentBytes classes official
    let shape : Serialization.Shape := ⟨cw, pw, false⟩
    let pqShape : SpqrMessage.Shape := ⟨ew, iw, 1, false⟩
    let staged := KernelSpecs.SealFixed.stagedOf ((conv.drop cert).take (182 + 80)) text
    let i := KernelSpecs.SealFixed.inputOf 0 staged text content
    let p := SpqrSend.canonical shape pqShape i
    SpqrSend.accepted shape pqShape i ∧
    ((out.drop (1 + cert)).take Send.recordBytes).length = Send.recordBytes ∧
    conv.take cert ++ (out.drop (1 + cert)).take Send.recordBytes = KernelSpecs.SealSend.advancedRecord cert conv staged p ∧
    (out.drop (1 + Send.convBytes cert)).take (8 + Send.sealEnvBytes cert classes official cw pw ew iw) =
      (text.drop (2 + content)).take 8 ++
        KernelSpecs.SealValue.Reference.sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic")
          (get "ephemeralAgreement") (get "staticAgreement") (conv.take cert) p.wire :=
  Send.seal_accepted_value cert cw pw ew iw classes official conv text w hc ht hb hcl

/-- **`signal-request-ctr` on the script's bundle** [M]: `RequestFrame.signalRequestCtr_built` with
`hframe`, `hmask` discharged by `requestCtrScript`'s layout (E2 for the send path). -/
theorem s13_requestCtr_value (cert : Nat) (env : List (BitVec 8)) (ts id : Nat) (mask frame : List (BitVec 8))
    (official : Bool) (offsets : List Nat)
    (hb : PublicRequest.build env ts id mask official = .ok (frame, offsets))
    (K seqB conv : List (BitVec 8)) (hK : K.length = 60) (hs : seqB.length = 8) (hc : conv.length = Send.convBytes cert) :
    let msg := PublicRequest.sendMessage env ts id official
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map
        (fun f => f.value.map (BVExpr.eval (assignOf (Send.requestIn K seqB conv frame mask)))) =
      KernelSpecs.sealedRequest K seqB
        (KernelSpecs.RequestFrame.buildHeader (PublicRequest.total msg) mask ++
          KernelSpecs.RequestFrame.maskFrom mask 0
            (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.requestValues cert conv) msg))
        (KernelSpecs.signalRequestSlots cert 0 0 0 0 conv).1 :=
  Send.requestCtr_value cert env ts id mask frame official offsets hb K seqB conv hK hs hc

/-- **`bundle-request-ctr` on the script's bundle** [M]: `RequestFrame.bundleRequestCtr_built` with
`hframe`, `hmask` discharged by the layout; `paired` is the script path's own pairing
(`Send.devicesName_paired`). -/
theorem s13_bundleRequestCtr_value (envs : List (List (BitVec 8))) (ts id : Nat) (mask frame : List (BitVec 8))
    (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (hb : PublicRequest.buildDevices envs ts id mask official = .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (hp : BundleKernel.pairs (offsets.drop 2) = some devices)
    (K seqB records : List (BitVec 8)) (hK : K.length = 60) (hs : seqB.length = 8)
    (hr : records.length = Send.recordBytes * devices.length) :
    let msg := PublicRequest.devicesMessage envs ts id official
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun f => f.value.map (BVExpr.eval (assignOf (Send.requestIn K seqB records frame mask)))) =
      KernelSpecs.sealedRequest K seqB
        (KernelSpecs.RequestFrame.assembleHeader (PublicRequest.total msg) mask ++
          KernelSpecs.RequestFrame.maskFrom mask 0
            (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.devicesValues records) msg))
        (KernelSpecs.bundleRequestValue records (offsets.getD 0 0) (offsets.getD 1 0) devices).1 :=
  Send.bundleRequestCtr_value envs ts id mask frame official payloadAt offsets hb devices hp K seqB records hK hs hr

/-- **The request's TLS record** [M] (P-GHASH (c) for the request sealer): header ‖ ciphertext of an
accepted request and `gcm-tag`'s tag over its pad and both parties' halves of shared key powers is
`TlsRecord.sealCore` of the plaintext. -/
theorem s13_request_record (K seqB P : List (BitVec 8)) (hK : K.length = 60) (a b : List (BitVec 128)) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (Send.innerOf P.length) ≤ nPow) :
    let o := KernelSpecs.sealedRequest K seqB P 255
    let hc := o.getD 1 [] ++ o.getD 2 []
    let pad := o.getD 3 []
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5))
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB P 23 0 :=
  Send.request_record K seqB P hK a b nPow hsh hn

/-- **T4-SEND / T7 on the script path, the headline** [M]: op 41, op 42 and the record seal with NO
worker-wiring hypothesis (`built`, `hframe`, `hmask` of `SealFrame.serverReceives_accepted` hold by
the scripts' construction: the frame is `frameFor` of the script's own openings, the kernels' inputs
are its concatenations). On an accepted send (status 255, request accepted 255): the reference send
step accepts; the kept state is the advanced record; the opened envelope is the reference
sealed-sender v1 envelope; what leaves for the server is the AES-GCM TLS record of the WebSocket frame
of `sendMessage` carrying that envelope with the contact's fields in their slots. -/
theorem s13_send_accepted (cert cw pw ew iw classes : Nat) (official : Bool) (certB record text : List (BitVec 8))
    (w : Bits) (hcB : certB.length = cert)
    (hr : record.length = Send.recordBytes) (ht : text.length = Send.textBytes classes official)
    (hb : Send.SealBound cert cw pw ew iw classes official) (hcl : 1 ≤ classes)
    (id : Nat) (mask frame : List (BitVec 8)) (offsets : List Nat) (K seqB : List (BitVec 8)) (hK : K.length = 60)
    (hs : seqB.length = 8)
    (a b : List (BitVec 128)) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) :
    let conv := certB ++ record
    let v := bitsOf conv ++ (bitsOf text ++ w)
    let sa := Send.shapedAssign (Send.sealK cert cw pw ew iw classes official).inputs v
    let get := fun name => (HybridKernel.lookup (KernelSpecs.SealFixed.sealInputs cert classes official) name).map
      (BVExpr.eval sa)
    let out := Send.shapedOut (Send.sealK cert cw pw ew iw classes official) v
    let te := (out.drop (1 + Send.convBytes cert)).take (8 + Send.sealEnvBytes cert classes official cw pw ew iw)
    let newRecord := (out.drop (1 + cert)).take Send.recordBytes
    let ctr := kernelOut (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0)
      (offsets.getD 2 0) (offsets.getD 3 0)) (Send.requestIn K seqB (certB ++ newRecord) frame mask)
    let hc := (ctr.drop 1).take (5 + Send.innerOf frame.length)
    let pad := (ctr.drop (1 + 5 + Send.innerOf frame.length)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5))
    out.take 1 = [255] →
    Send.frameFor (te.drop 8) (te.take 8) id mask official = .ok (frame, offsets) →
    ctr.take 1 = [255] →
    Local.Ghash.needed 5 (Send.innerOf frame.length) ≤ nPow →
    let content := KernelSpecs.SealFixed.contentBytes classes official
    let shape : Serialization.Shape := ⟨cw, pw, false⟩
    let pqShape : SpqrMessage.Shape := ⟨ew, iw, 1, false⟩
    let staged := KernelSpecs.SealFixed.stagedOf ((conv.drop cert).take (182 + 80)) text
    let i := KernelSpecs.SealFixed.inputOf 0 staged text content
    let p := SpqrSend.canonical shape pqShape i
    let envelope := KernelSpecs.SealValue.Reference.sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic")
      (get "ephemeralAgreement") (get "staticAgreement") certB p.wire
    let msg := PublicRequest.sendMessage envelope (Send.beNat (te.take 8)) id official
    SpqrSend.accepted shape pqShape i ∧
    certB ++ newRecord = KernelSpecs.SealSend.advancedRecord cert conv staged p ∧
    te.drop 8 = envelope ∧
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB
        (KernelSpecs.RequestFrame.buildHeader (PublicRequest.total msg) mask ++
          KernelSpecs.RequestFrame.maskFrom mask 0
            (KernelSpecs.RequestFrame.render (KernelSpecs.RequestFrame.requestValues cert (certB ++ newRecord)) msg))
        23 0 :=
  Send.send_accepted cert cw pw ew iw classes official certB record text w hcB hr ht hb hcl id mask frame offsets K seqB
    hK hs a b nPow hsh

/-- **Op 41 is well formed** [K]: every branch's instructions pass the shell's `check`, given the
handles live and the loaded signatures (`SealSigs`). -/
theorem s13_sealScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (a : Send.SealArgs)
    (cm sm dm tm em : List Mark) (hf : Fresh c n)
    (hcn : a.cert.id < n) (hsn : a.state.id < n) (hdn : a.sender.id < n) (htn : a.static.id < n)
    (hen : a.ephAgreement.id < n)
    (hes : a.ephAgreement.id ≠ a.state.id) (hec : a.ephAgreement.id ≠ a.cert.id)
    (hed : a.ephAgreement.id ≠ a.sender.id) (het : a.ephAgreement.id ≠ a.static.id)
    (hc : c.bool? a.cert = some ⟨cm, false⟩) (hs : c.bool? a.state = some ⟨sm, false⟩)
    (hd : c.bool? a.sender = some ⟨dm, false⟩) (ht : c.bool? a.static = some ⟨tm, false⟩)
    (he : c.bool? a.ephAgreement = some ⟨em, false⟩)
    (hcm : cm.length = 8 * a.certLen) (hsm : sm.length = 8 * Send.recordBytes) (hdm : dm.length = 255)
    (htm : tm.length = 255) (hem : em.length = 255) (hpk : a.ephPublic.length = 32)
    (hsig : Send.SealSigs sigs a.certLen) :
    WF sigs c (Send.sealScript n a) :=
  Send.sealScript_wf sigs c n a cm sm dm tm em hf hcn hsn hdn htn hen hes hec hed het hc hs hd ht he hcm hsm hdm htm
    hem hpk hsig

/-- **Op 42 is well formed** [K]. -/
theorem s13_requestScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (cert state : BoolH)
    (cm sm : List Mark) (hf : Fresh c n) (hcn : cert.id < n)
    (hc : c.bool? cert = some ⟨cm, false⟩) (hs : c.bool? state = some ⟨sm, false⟩)
    (hsm : 8 * Send.recordBytes ≤ sm.length) (hw : cm.length + 8 * Send.recordBytes ≤ maxWidth) :
    WF sigs c (Send.requestScript n cert state) :=
  Send.requestScript_wf sigs c n cert state cm sm hf hcn hc hs hsm hw

/-- **The request's record phase is well formed** [K]. -/
theorem s13_requestCtrScript_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic conv : BoolH)
    (seq frame mask : List (BitVec 8)) (name : Bytes) (C : Nat) (cm : List Mark) (hf : Fresh c n)
    (htn : traffic.id < n) (hcn : conv.id < n)
    (ht : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩) (hc : c.bool? conv = some ⟨cm, false⟩)
    (hcm : cm.length = 8 * C) (hs : seq.length = 8) (hm : mask.length = 4) (hsize : C + frame.length ≤ 65536)
    (hsig : sigs name = some ⟨8 * (68 + C + frame.length + 4),
      List.replicate (8 * (1 + 5 + Send.innerOf frame.length)) .pub ++ List.replicate 128 .never⟩) :
    WF sigs c (Send.requestCtrScript n traffic conv seq frame mask name) :=
  Send.requestCtrScript_wf sigs c n traffic conv seq frame mask name C cm hf htn hcn ht hc hcm hs hm hsize hsig

/-- **Op 41's wires fit the pipe** [K] (`Wire.Bounded`). -/
theorem s13_sealScript_bounded (n : Nat) (a : Send.SealArgs) (hn : n + 8 < B64)
    (hids : a.cert.id < B64 ∧ a.state.id < B64 ∧ a.sender.id < B64 ∧ a.static.id < B64 ∧ a.ephAgreement.id < B64)
    (hpk : a.ephPublic.length = 32) : Every Instr.Bounded (Send.sealScript n a) :=
  Registry.send_sealScript_bounded n a hn hids hpk

end FlowsS13

/-! ### 7e. Send, continued (stage S13 follow-up: F51, F52, F54 in part, F57, F58, F59)

`TlsMpc/Node/Flows/{SendDevices,SendRun,SendRecordRun,SendDevicesBounded}.lean` (S13_NOTES.md). **M**
as in 7e: the kernels' circuits computing their Lean definitions (`shapedCircuit` for kernels with
word inputs, `Contacts.kernelCircuit` for byte kernels) is T2's trust; the words of a seal are S11's
(E4). Compiled standalone in the S13 branch (scratch file with this text: standard axioms only). -/

section FlowsS13b

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide
open TlsMpc.Signal

/-- **F58: `bundleEnvBytes` is `bundle-seal`'s envelope length** [K], on every assignment, under the
kernel's own parameter bound. -/
theorem s13_bundleEnvBytes_eq (cert content : Nat) (oneTime : Bool) (cw pw ew iw : Nat) (a : BVExpr.Assignment)
    (hb : Send.BundleBound cert content cw pw ew iw) :
    ((ReceiveKernel.values (BundleKernel.bundleSeal cert oneTime content cw pw ew iw) a).getD 3 []).length =
      Send.bundleEnvBytes cert oneTime content cw pw ew iw :=
  Send.bundleEnvBytes_eq cert content oneTime cw pw ew iw a hb

/-- **`bundle-seal`'s conversation field** [K]: `cert + min 262 (182 + content) + 57` bytes. For an
official 89-byte text (content 79) this is `cert + 318`, one byte short of what `devicesScript`
slices: such a send to an unanswered device aborts before any status is opened (gap S13-10). -/
theorem s13_bundleOut_record_length (cert content : Nat) (oneTime : Bool) (cw pw ew iw : Nat)
    (a : BVExpr.Assignment) (hb : Send.BundleBound cert content cw pw ew iw) :
    ((ReceiveKernel.values (BundleKernel.bundleSeal cert oneTime content cw pw ew iw) a).getD 1 []).length =
      cert + min 262 (182 + content) + 57 :=
  Send.bundleOut_record_length cert content oneTime cw pw ew iw a hb

/-- **F52: op 61 + op 62 + the record seal on the script path** [M]. When the one opening of all
statuses is all 255 and the request's accepted byte is 255: every device's status is 255 and its
kept record the advanced one; the envelopes `splitEnvelopes` cuts out of the one opening of all
timestamps ‖ envelopes are, in device order, the reference envelopes (`sealV1` for kind 0,
`EstablishSeal.envelopeOf` for kinds 1, 2); op 62 reads the advanced records from the new state;
the bytes for the server are `TlsRecord.sealCore` of the frame of `devicesMessage` holding those
envelopes. No `built`, `hframe`, `hmask`, `paired` hypothesis. -/
theorem s13_devices_accepted (c : Send.DevCtx) (ds : List Send.DevSend) (hc : c.Ok) (hd : ∀ d ∈ ds, d.Ok c)
    (hne : ds ≠ []) (id : Nat) (mask frame : List (BitVec 8)) (payloadAt : Nat) (offsets : List Nat)
    (devices : List (Nat × Nat)) (K seqB : List (BitVec 8)) (hK : K.length = 60) (hs : seqB.length = 8)
    (a b : List Tls.W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) :
    let statuses := (ds.map (Send.DevSend.status c)).flatten
    let parts := Send.splitEnvelopes (ds.map (Send.DevSend.env c)) (ds.map (Send.DevSend.sealed c)).flatten
    let envelopes := parts.map (·.2)
    let timestamp := (parts.headD ([], [])).1
    let newState := (ds.map fun d => d.kept c ++ (if d.kind = 0 then [] else d.pending)).flatten
    let records := ((deviceSpans 0 (ds.map (·.kind))).map fun s =>
      (newState.drop s.1.1).take Send.recordBytes).flatten
    let ctr := kernelOut (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0)
      devices) (Send.requestIn K seqB records frame mask)
    let head := (ctr.drop 1).take (5 + Send.innerOf frame.length)
    let pad := (ctr.drop (1 + 5 + Send.innerOf frame.length)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half a (head.take 5) (head.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half b (head.take 5) (head.drop 5))
    statuses = List.replicate ds.length 255 →
    PublicRequest.buildDevices envelopes (Send.beNat timestamp) id mask c.official = .ok (frame, payloadAt, offsets) →
    BundleKernel.pairs (offsets.drop 2) = some devices →
    ctr.take 1 = [255] →
    Local.Ghash.needed 5 (Send.innerOf frame.length) ≤ nPow →
    let msg := PublicRequest.devicesMessage (ds.map (Send.DevSend.reference c)) (Send.beNat c.timestamp) id c.official
    (∀ d ∈ ds, d.status c = [255] ∧ d.kept c = d.advanced c) ∧
    envelopes = ds.map (Send.DevSend.reference c) ∧
    timestamp = c.timestamp ∧
    records = (ds.map (Send.DevSend.advanced c)).flatten ∧
    head ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) =
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB
        (KernelSpecs.RequestFrame.assembleHeader (PublicRequest.total msg) mask ++
          KernelSpecs.RequestFrame.maskFrom mask 0
            (KernelSpecs.RequestFrame.render
              (KernelSpecs.RequestFrame.devicesValues (ds.map (Send.DevSend.advanced c)).flatten) msg))
        23 0 :=
  Send.devices_accepted c ds hc hd hne id mask frame payloadAt offsets devices K seqB hK hs a b nPow hsh

/-- **F52: all or nothing** [K]: when some device's status is not 255, the opened statuses are not
all 255, and the rest of op 61 is silent: against any adversary nothing more is released to anyone,
no envelope of any device is opened, and the stored state is kept. -/
theorem s13_devices_refused_view (E : Env) (me : Party) (adv : Adversary) (c : Send.DevCtx) (ds : List Send.DevSend)
    (hc : c.Ok) (hd : ∀ d ∈ ds, d.Ok c) (hbad : ∃ d ∈ ds, d.status c ≠ [255])
    (n : Nat) (a : Send.DevicesArgs) (envs : List Nat) (σ : Store) (I : Ideal) (vD : List Release) :
    let st := bitsOf (ds.map (Send.DevSend.status c)).flatten
    st ≠ bitsOf (List.replicate ds.length 255) ∧
    Silent (Send.afterStatuses n ds.length a envs st) ∧
    (withAdv E me adv (Send.afterStatuses n ds.length a envs st) σ I vD).viewD = [] ∧
    (withAdv E me adv (Send.afterStatuses n ds.length a envs st) σ I vD).viewH = [] :=
  Send.devices_refused_view E me adv c ds hc hd hbad n a envs σ I vD

/-- **Public scripts, two honest parties** [K]: a script of plain instructions and openings run by
both parties in lockstep ends with `pubRun`'s result for both, its ideal state, and both views equal
to its releases. -/
theorem s13_jointRun_pub (E : Env) {α : Type} {s : Script α} (hs : Every (fun i => Send.pubInstr i = true) s)
    (σA σB : Store) (I : Ideal) :
    (jointRun E s s σA σB I).result = (Send.pubRun E s I).1.map (fun a => (a, a)) ∧
    (jointRun E s s σA σB I).ideal = (Send.pubRun E s I).2.1 ∧
    (jointRun E s s σA σB I).viewA = (Send.pubRun E s I).2.2 ∧
    (jointRun E s s σA σB I).viewB = (Send.pubRun E s I).2.2 :=
  Send.jointRun_pub E hs σA σB I

/-- **Public scripts, any adversary** [K]: the views are prefixes of `pubRun`'s releases and a result
is `pubRun`'s. -/
theorem s13_withAdv_pub (E : Env) (me : Party) (adv : Adversary) {α : Type} {s : Script α}
    (hs : Every (fun i => Send.pubInstr i = true) s) (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv s σ I vD).viewD <+: (Send.pubRun E s I).2.2 ∧
    (withAdv E me adv s σ I vD).viewH <+: (Send.pubRun E s I).2.2 ∧
    ∀ x, (withAdv E me adv s σ I vD).result = some x → (Send.pubRun E s I).1 = some x :=
  Send.withAdv_pub E me adv hs σ I vD

/-- **F57: op 41's view by value, against any adversary** [M]: a prefix of [flags, status] when the
status is not 255 (and the result, if any, is `none`), of [flags, status, timestamp ‖ envelope]
otherwise; the values: the widths kernel's output on certificate ‖ record, the seal kernel's slices
(`sealOut_values`: the envelope is `sealV1` of the reference message). -/
theorem s13_seal_view (E : Env) (me : Party) (adv : Adversary) (σ : Store) (vD : List Release)
    (n : Nat) (a : Send.SealArgs) (certB record : List (BitVec 8)) (db eb tb : Bits) (I : Ideal)
    (Cw : Circuit) (official : Bool) (classes : Nat)
    (h : Send.SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : Send.widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : Send.sealEnvBytes a.certLen classes official cw pw ew iw ≤ Send.maxEnvelope)
    (hS : E.circuits (Send.sealName official a.certLen classes cw pw ew iw) =
      some (Send.shapedCircuit (Send.sealK a.certLen cw pw ew iw classes official) mk)) :
    let flags := Cw.eval (bitsOf (certB ++ record))
    let out := Send.sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + Send.convBytes a.certLen)).take (8 + Send.sealEnvBytes a.certLen classes official cw pw ew iw)
    let o := withAdv E me adv (Send.sealScript n a) σ I vD
    (out.take 1 = [255] →
      o.viewD <+: [⟨Send.widthsLabel, .bits flags⟩, ⟨Send.envelopeLabel, .bits (bitsOf (out.take 1))⟩,
        ⟨Send.envelopeLabel, .bits (bitsOf te)⟩]) ∧
    (out.take 1 ≠ [255] →
      o.viewD <+: [⟨Send.widthsLabel, .bits flags⟩, ⟨Send.envelopeLabel, .bits (bitsOf (out.take 1))⟩] ∧
      ∀ x, o.result = some x → x = none) :=
  Send.seal_view E me adv σ vD n a certB record db eb tb I Cw official classes h cw pw ew iw mk hw henv hS

/-- **F51 for op 41** [M]: two honest parties end with the same result; on 255 the timestamp, the
envelope and the new state `n + 6` holding the kept record, both views [flags, status, timestamp ‖
envelope], every other handle below the counter untouched; otherwise `none`, views [flags, status],
the stored state's value kept. -/
theorem s13_seal_joint (E : Env) (σA σB : Store) (n : Nat) (a : Send.SealArgs) (certB record : List (BitVec 8))
    (db eb tb : Bits) (I : Ideal) (Cw : Circuit) (official : Bool) (classes : Nat)
    (h : Send.SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : Send.widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : Send.sealEnvBytes a.certLen classes official cw pw ew iw ≤ Send.maxEnvelope)
    (hS : E.circuits (Send.sealName official a.certLen classes cw pw ew iw) =
      some (Send.shapedCircuit (Send.sealK a.certLen cw pw ew iw classes official) mk)) :
    let flags := Cw.eval (bitsOf (certB ++ record))
    let out := Send.sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + Send.convBytes a.certLen)).take (8 + Send.sealEnvBytes a.certLen classes official cw pw ew iw)
    let sd : Send.Sealed := ⟨te.take 8, [te.drop 8], ⟨n + 6⟩⟩
    let o := jointRun E (Send.sealScript n a) (Send.sealScript n a) σA σB I
    (out.take 1 = [255] →
      o.result = some (some sd, some sd) ∧
      o.viewA = [⟨Send.widthsLabel, .bits flags⟩, ⟨Send.envelopeLabel, .bits (bitsOf (out.take 1))⟩,
        ⟨Send.envelopeLabel, .bits (bitsOf te)⟩] ∧ o.viewB = o.viewA ∧
      o.ideal.bools (n + 6) = some (bitsOf ((out.drop (1 + a.certLen)).take Send.recordBytes)) ∧
      ∀ x, x < n → x ≠ a.ephAgreement.id → x ≠ a.state.id → o.ideal.bools x = I.bools x) ∧
    (out.take 1 ≠ [255] →
      o.result = some (none, none) ∧
      o.viewA = [⟨Send.widthsLabel, .bits flags⟩, ⟨Send.envelopeLabel, .bits (bitsOf (out.take 1))⟩] ∧
      o.viewB = o.viewA ∧ o.ideal.bools a.state.id = some (bitsOf record)) :=
  Send.seal_joint E σA σB n a certB record db eb tb I Cw official classes h cw pw ew iw mk hw henv hS

/-- **F51: a whole single-device send through `jointRun`** [M]: op 41 (accepted), op 42 on op 41's new
state handle, the request's CTR phase, S12's tag phase; the same results at every phase for both
parties, and header ‖ ciphertext ‖ tag are exactly the bytes `s13_send_accepted` characterises
(`TlsRecord.sealCore` of the request frame carrying the reference sealed-sender envelope). -/
theorem s13_send_joint (E : Env) (σA σB σA' σB' : Store) (n : Nat) (a : Send.SealArgs) (certB record : List (BitVec 8))
    (db eb tb : Bits) (I : Ideal) (Cw : Circuit) (official : Bool) (classes : Nat)
    (h : Send.SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : Send.widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : Send.sealEnvBytes a.certLen classes official cw pw ew iw ≤ Send.maxEnvelope)
    (hS : E.circuits (Send.sealName official a.certLen classes cw pw ew iw) =
      some (Send.shapedCircuit (Send.sealK a.certLen cw pw ew iw classes official) mk))
    (traffic : BoolH) (K seqB : List (BitVec 8)) (hK : K.length = 60) (hs : seqB.length = 8)
    (htn : traffic.id < n) (hte : traffic.id ≠ a.ephAgreement.id) (hts : traffic.id ≠ a.state.id)
    (hKv : I.bools traffic.id = some (bitsOf K))
    (m p q : Nat) (hm : n + 8 ≤ m) (hp : m + 2 ≤ p) (hq : p + 6 ≤ q)
    (id : Nat) (mask frame : List (BitVec 8)) (offsets : List Nat) (marksR marksT : List Mark) (halfSlot : Nat)
    (hR : E.circuits (Send.requestNameOf a.certLen frame offsets) =
      some (kernelCircuit (HybridKernel.signalRequestCtr a.certLen frame.length (offsets.getD 0 0) (offsets.getD 1 0)
        (offsets.getD 2 0) (offsets.getD 3 0)) (68 + Send.convBytes a.certLen + frame.length + 4) marksR))
    (hT : E.circuits Tls.tagName = some (kernelCircuit HybridKernel.gcmTag 48 marksT))
    (ga gb : List Tls.W) :
    let out := Send.sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + Send.convBytes a.certLen)).take (8 + Send.sealEnvBytes a.certLen classes official cw pw ew iw)
    let newRecord := (out.drop (1 + a.certLen)).take Send.recordBytes
    let ctr := kernelOut (HybridKernel.signalRequestCtr a.certLen frame.length (offsets.getD 0 0) (offsets.getD 1 0)
      (offsets.getD 2 0) (offsets.getD 3 0)) (Send.requestIn K seqB (certB ++ newRecord) frame mask)
    let hc := (ctr.drop 1).take (5 + Send.innerOf frame.length)
    let pad := (ctr.drop (1 + 5 + Send.innerOf frame.length)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half ga (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half gb (hc.take 5) (hc.drop 5))
    out.take 1 = [255] →
    Send.frameFor (te.drop 8) (te.take 8) id mask official = .ok (frame, offsets) →
    ctr.take 1 = [255] →
    σA'.bits halfSlot = bitsOf hA → σB'.bits halfSlot = bitsOf hB →
    let o1 := jointRun E (Send.sealScript n a) (Send.sealScript n a) σA σB I
    let o2 := jointRun E (Send.requestScript m a.cert ⟨n + 6⟩) (Send.requestScript m a.cert ⟨n + 6⟩) σA σB o1.ideal
    let o3 := jointRun E
      (Send.requestCtrScript p traffic ⟨m + 1⟩ seqB frame mask (Send.requestNameOf a.certLen frame offsets))
      (Send.requestCtrScript p traffic ⟨m + 1⟩ seqB frame mask (Send.requestNameOf a.certLen frame offsets))
      σA σB o2.ideal
    let o4 := jointRun E (Tls.tagScript q ⟨p + 4⟩ halfSlot) (Tls.tagScript q ⟨p + 4⟩ halfSlot) σA' σB' o3.ideal
    ∃ (sd : Send.Sealed) (hc' tag : List (BitVec 8)),
      o1.result = some (some sd, some sd) ∧ sd.state = ⟨n + 6⟩ ∧ sd.envelopes = [te.drop 8] ∧
      o1.ideal.bools (n + 6) = some (bitsOf newRecord) ∧
      o2.result = some (⟨m + 1⟩, ⟨m + 1⟩) ∧
      o3.result = some ((hc', ⟨p + 4⟩), (hc', ⟨p + 4⟩)) ∧
      o4.result = some (tag, tag) ∧
      hc' ++ tag = hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) :=
  Send.send_joint E σA σB σA' σB' n a certB record db eb tb I Cw official classes h cw pw ew iw mk hw henv hS traffic
    K seqB hK hs htn hte hts hKv m p q hm hp hq id mask frame offsets marksR marksT halfSlot hR hT ga gb

/-- **F59: ORD-1 at script level** [M]: on the accepted path op 41 returns the new state handle
`n + 6` (defined by the seal kernel's run before the envelope's opening), and op 42 run on that
handle reads exactly the kept record: the request is built from the state op 41 produced. -/
theorem s13_send_state_order (E : Env) (σA σB : Store) (n : Nat) (a : Send.SealArgs) (certB record : List (BitVec 8))
    (db eb tb : Bits) (I : Ideal) (Cw : Circuit) (official : Bool) (classes : Nat)
    (h : Send.SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : Send.widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : Send.sealEnvBytes a.certLen classes official cw pw ew iw ≤ Send.maxEnvelope)
    (hS : E.circuits (Send.sealName official a.certLen classes cw pw ew iw) =
      some (Send.shapedCircuit (Send.sealK a.certLen cw pw ew iw classes official) mk))
    (m : Nat) (hm : n + 8 ≤ m) (σA' σB' : Store) :
    let out := Send.sealOutOf a certB record db eb tb official classes cw pw ew iw
    let newRecord := (out.drop (1 + a.certLen)).take Send.recordBytes
    let o := jointRun E (Send.sealScript n a) (Send.sealScript n a) σA σB I
    out.take 1 = [255] →
    (∃ sd : Send.Sealed, o.result = some (some sd, some sd) ∧ sd.state = ⟨n + 6⟩) ∧
    let o2 := jointRun E (Send.requestScript m a.cert ⟨n + 6⟩) (Send.requestScript m a.cert ⟨n + 6⟩) σA' σB' o.ideal
    o2.result = some (⟨m + 1⟩, ⟨m + 1⟩) ∧ o2.viewA = [] ∧
    o2.ideal.bools (m + 1) = some (bitsOf (certB ++ newRecord)) :=
  Send.send_state_order E σA σB n a certB record db eb tb I Cw official classes h cw pw ew iw mk hw henv hS m hm σA' σB'

/-- **F54 in part: op 62's wires fit the pipe** [K] (`Wire.Bounded`). -/
theorem s13_requestDevicesScript_bounded (n : Nat) (state : BoolH) (ats : List Nat) (hn : n + ats.length < B64)
    (hs : state.id < B64) (hat : ∀ x ∈ ats, 8 * (x + Send.recordBytes) < B64) :
    Every Instr.Bounded (Send.requestDevicesScript n state ats) :=
  Registry.requestDevicesScript_bounded n state ats hn hs hat

end FlowsS13b

/-! ### 7f. Receive a first message (stage S14; plan 8.1 T3, T4-RECV, T13; numbered 7d on the S14
branch, renumbered when the stages were joined on `scripts-stack`)

The S14 scripts (`TlsMpc/Node/Flows/Receive.lean`, proofs `Flows/ReceiveFlowProofs.lean`, the IO
glue `Flows/ReceiveBackend.lean`; S14_NOTES.md). **F** marks a statement at the function level: the
kernels' specifications (`ReceiveProofs.*_spec`) connected by the scripts' own wiring functions
(`Receive.staticIn` … `sessionInOf`), not yet through `jointRun`. -/

section FlowsS14

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Receive
open TlsMpc.Signal TlsMpc.Signal.ReceiveFirst TlsMpc.KernelSpecs.ReceiveAccept

/-- **T3, kinds, op 50** [K]: every release of `Receive.openFirst`, on every branch, from every
state, carries the label of `certificateLength`, `contentShape`, `prekeyShape`, `prekeyIds`, a
conversion's masked value, or one of the curve parameter's kinds; so in any run against any
adversary the adversary's view carries nothing else (`viewD_kinds`). -/
theorem s14_openFirst_reveals (cv : Curve) (loaded : Bytes → Bool) (fi : FirstIn) (env : BoolH) (size : Nat) :
    RevealsG (allFirst cv) (Receive.openFirst cv loaded fi env size) :=
  Receive.openFirst_reveals cv loaded fi env size

/-- **T3, kinds, op 51** [K]: the same for `Receive.session` (`signalShape`, `sessionStatus`,
`receivedText`, `accessKeyStatus`, masked field values, the curve's kinds). -/
theorem s14_session_reveals (cv : Curve) (loaded : Bytes → Bool) (a : Arrival) (sp : SessionPublic)
    (ss : SessionSecrets) : RevealsG (allSession cv) (Receive.session cv loaded a sp ss) :=
  Receive.session_reveals cv loaded a sp ss

/-- **Gating** [K]: once `receive-session`'s status opens to anything but 255, the script frees the
conversation and the plaintext and releases nothing more (`receive-text` is not run). -/
theorem s14_sessionRest_refused (loaded : Bytes → Bool) (cert ct : Nat) (se : List BoolH) (status : Bits)
    (h : Contacts.bytesOf status ≠ [255]) :
    sessionRest loaded cert ct se status = refuse [at! se 1, at! se 3] [] ∧ SilentG (sessionRest loaded cert ct se status) :=
  Receive.sessionRest_refused loaded cert ct se status h

/-- **The wiring, by definition** [F]: the session's `verified` input is
`receive-certificate-verified` on `receive-certificate`'s validity and signature (the hypothesis
`session_accept_certificate` takes about the controller holds for the scripts' wiring). -/
theorem s14_verified_wiring (i : Proofs.Pipeline.In) :
    (Proofs.Pipeline.sin i).verified =
      (certificateVerified ByteAuth.concrete
        ((certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete i.cert i.c (Proofs.Pipeline.certBytes i)
          (Proofs.Pipeline.contentValid i) (Proofs.Pipeline.senderIdentity i) i.signer i.now i.serverX i.serverY).getD 0 [])
        ((certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete i.cert i.c (Proofs.Pipeline.certBytes i)
          (Proofs.Pipeline.contentValid i) (Proofs.Pipeline.senderIdentity i) i.signer i.now i.serverX i.serverY).getD 3 [])
        i.serverValid i.rx i.ry).getD 0 [] :=
  Proofs.pipeline_verified_wiring i

/-- **T13 for the scripts' wiring** [F]: an accepted session (status 255) means the message MAC
verified under libsignal's keys, the sender certificate's identity is the decrypted static key, its
signer is the trusted one, it has not expired, the server key is a curve point and the signature's
`R` is the compression of the field engine's `[s]B − [h]A`. -/
theorem s14_accept_certificate (i : Proofs.Pipeline.In) (hjump : i.jump ≤ 16)
    (h : (Proofs.Pipeline.se i).getD 0 [] = [255]) :
    (certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete i.cert i.c (Proofs.Pipeline.certBytes i)
      (Proofs.Pipeline.contentValid i) (Proofs.Pipeline.senderIdentity i) i.signer i.now i.serverX i.serverY).getD 0 [] =
      [255] ∧
    Establish.part (Proofs.Pipeline.certBytes i)
      (if i.c.embedded then bodyAt i.cert + i.c.e164 + 48 else bodyAt i.cert + i.c.e164 + 46 + 2 + i.c.uuidSize + 1)
      i.c.signerSize = i.signer ∧
    i.serverValid = ByteAuth.concrete.const 1 :: List.replicate 31 (ByteAuth.concrete.const 0) ∧
    (Establish.part (Proofs.Pipeline.certBytes i) (bodyAt i.cert + i.c.body + 2) 64).take 32 =
      XEdDsa.compress ByteAuth.concrete i.rx i.ry := by
  obtain ⟨_, h1, _, h2, _, h3, _, h4⟩ := Proofs.pipeline_accept_certificate i hjump h
  exact ⟨h1, h2, h3, h4⟩

/-- **T4-RECV, the text** [F]: with the session's and `receive-text`'s statuses 255, the opened text
is exactly the body of the decrypted content (the session's plaintext, which
`pipeline_accept_outputs` says is libsignal's AES-256-CBC decryption under the message keys). -/
theorem s14_text (i : Proofs.Pipeline.In) (hcap : i.cap < 65536) (ht : (Proofs.Pipeline.tx i).getD 0 [] = [255]) :
    TlsMpc.KernelSpecs.ReceiveAcceptText.Accepted (((Proofs.Pipeline.se i).getD 3 []).drop 8) i.cap ∧
    (Proofs.Pipeline.tx i).getD 2 [] = (List.range i.cap).map (fun j =>
      if j < TlsMpc.KernelSpecs.ReceiveAcceptText.bodyLength (((Proofs.Pipeline.se i).getD 3 []).drop 8) then
        TlsMpc.KernelSpecs.ReceiveAcceptText.g (((Proofs.Pipeline.se i).getD 3 []).drop 8)
          (TlsMpc.KernelSpecs.ReceiveAcceptText.bodyStart (((Proofs.Pipeline.se i).getD 3 []).drop 8) + j)
      else 0) :=
  Proofs.pipeline_text i hcap ht

/-- **T4-RECV, the stored record** [F]: with `receive-access-key`'s status 255 the conversation it
outputs (whose bytes `cert .. cert + 319` the script stores) is the session's with the access key
derived from the message's profile key, for one of the 72 layouts. -/
theorem s14_record (i : Proofs.Pipeline.In) (hlen : i.ownCert + 294 ≤ ((Proofs.Pipeline.se i).getD 1 []).length)
    (hk : (Proofs.Pipeline.ak i).getD 0 [] = [255]) :
    ∃ g ∈ gaps, (Proofs.Pipeline.ak i).getD 1 [] = ((Proofs.Pipeline.se i).getD 1 []).take (i.ownCert + 278) ++
        TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.accessKeyOf
          (TlsMpc.KernelSpecs.ReceiveAcceptAccessKey.profileKey (((Proofs.Pipeline.se i).getD 3 []).drop 8) i.offset g) ++
        ((Proofs.Pipeline.se i).getD 1 []).drop (i.ownCert + 294) :=
  Proofs.pipeline_record i hlen hk

/-- **A refused session opens no text** [F]: unless the session's status is 255, every output of
`receive-text` on its plaintext is zero. -/
theorem s14_refused_text_zero (i : Proofs.Pipeline.In) (h : (Proofs.Pipeline.se i).getD 0 [] ≠ [255]) :
    ∀ field ∈ text ByteAuth.concrete i.cap ((Proofs.Pipeline.se i).getD 3 []), ∀ b ∈ field, b = 0 :=
  Proofs.pipeline_refused_text_zero i h

/-- **A refused envelope opens a zero certificate length** [F] (`unsealMessage_rejects`). -/
theorem s14_certificateLength_zero (i : Proofs.Pipeline.In) (h : (Proofs.Pipeline.um i).getD 0 [] = [0]) :
    ∀ b ∈ (Proofs.Pipeline.um i).getD 2 [], b = 0 :=
  Proofs.pipeline_certificateLength_zero i h

/-- **Provisional ids** [K]: distinct within a session, and never an application id (those are below
2^128 − 2^64), for fewer than 2^64 − 2 messages. -/
theorem s14_provisional_ids (j k : Nat) (hj : j + 2 < 2 ^ 64) (hk : k + 2 < 2 ^ 64) :
    (provisionalId j = provisionalId k → j = k) ∧ 2 ^ 128 - 2 ^ 64 ≤ provisionalId k :=
  ⟨provisionalId_inj j k (by omega) (by omega), provisionalId_high k hk⟩

end FlowsS14

/-! ### 7g. Device refresh (stage S15; plan 8.1 T3, T4-REFRESH, ORD-2; numbered 7d on the S15
branch, renumbered when the stages were joined on `scripts-stack`)

The S15 scripts (`TlsMpc/Node/Flows/Refresh.lean`, proofs `RefreshFlowProofs.lean`,
`RefreshSlotProofs.lean`, `RefreshKemProofs.lean`, `RefreshFirstProofs.lean`, `RefreshWF.lean`;
S15_NOTES.md). Status letters as above. S11's curve operations are a parameter (`Refresh.CurveOps`)
whose own `Reveals` is a hypothesis; the circuits computing their Lean kernels is T2's trust; the
KEM and session kernels' output widths (`KemWidths`, `SessionWidths`) are the pinned layouts.
Compiled standalone in this stage (the whole file exceeds the stage's 4 GB cap): standard axioms. -/

section FlowsS15

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide

/-- **T3 for the establishment** [M; hyp: S11's `Reveals`]: against any adversary, every release of a
refresh step carries the label of `sealedRecord`, `bundleShape`, `identityChanged`, `deviceStatus`,
`sealedBlob` or one of S11's kinds: the keys response body is opened only as its punctuation flags,
the first device's `changed` byte and each device's status. -/
theorem s15_refresh_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (cv : Refresh.CurveOps)
    (hcv : cv.Reveals) (acct : Refresh.Account) (t : Contacts.Table) (st : Refresh.RState)
    (id registration index count step start : Nat) (w : TlsMpc.Signal.BundleResponse.Widths) (slot : Nat) (σ : Store)
    (I : Ideal) (vD : List Release) :
    ∀ r ∈ (withAdv E me adv (Refresh.opEstablish cv acct t st id registration index count step start w slot).script
      σ I vD).viewD, ∃ k ∈ Refresh.refreshKinds cv.kinds, r.label = Label.ofKind k :=
  Refresh.refresh_viewD_kinds E me adv cv hcv acct t st id registration index count step start w slot σ I vD

/-- **T3, the other refresh scripts** [M]: each declares its kinds (`Registry.s15_flows_reveal`). -/
theorem s15_flows_reveal_restated :
    (∀ n body size, Reveals Refresh.shapeKinds (Refresh.shapeScript n body size)) ∧
    (∀ t st, Reveals [] (Refresh.opDrop t st).script) ∧ (∀ t st id, Reveals [] (Refresh.opCommit t st id).script) :=
  ⟨Registry.s15_flows_reveal.2.2.1, Registry.s15_flows_reveal.2.2.2.2.2.2.2.2.1,
    Registry.s15_flows_reveal.2.2.2.2.2.2.2.2.2⟩

/-- **ORD-2 on the table** [K]: `opCommit` is the only refresh operation that changes a contact's
entry, and only to the content the scratch's seal sealed, when the scratch is complete and sealed
for that contact. -/
theorem s15_ord2_commit (t : Contacts.Table) (st : Refresh.RState) (id : Nat) (r : Unit)
    (h : ((Refresh.opCommit t st id).commit r).1.entries ≠ t.entries) :
    ∃ e content size kinds, t.find? id = some e ∧ st.contact = some id ∧ st.sealed = some (content, size, kinds) ∧
      st.ready = true ∧
      ((Refresh.opCommit t st id).commit r).1 = t.put id (Refresh.committed e content size kinds st.changed) :=
  Refresh.opCommit_entry t st id r h

/-- **ORD-2: a dropped scratch leaves the table unchanged** [K]. -/
theorem s15_ord2_drop (t : Contacts.Table) (st : Refresh.RState) (r : Unit) :
    ((Refresh.opDrop t st).commit r) = (t, {}) := Refresh.opDrop_table t st r

/-- **ORD-2: the establishment changes no entry** [K] (likewise fetch, take, shape, scratch seal:
`opFetch_entries`, `opTake_entries`, `opShape_entries`, `opScratchSeal_entries`). -/
theorem s15_ord2_establish (cv : Refresh.CurveOps) (acct : Refresh.Account) (t : Contacts.Table)
    (st : Refresh.RState) (id registration index count step start : Nat) (w : TlsMpc.Signal.BundleResponse.Widths)
    (slot : Nat) (r : Refresh.Status × Refresh.RState) :
    ((Refresh.opEstablish cv acct t st id registration index count step start w slot).commit r).1.entries = t.entries :=
  Refresh.opEstablish_entries cv acct t st id registration index count step start w slot r

/-- **The splice and the digit counts from one source** [M]: from the held body, `bundle-slot`'s
input is the cut with the item spliced by `BundleSlots.splice w` followed by `widthsOf w` of the
SAME `w` (the `inconsistent_width_*` combination cannot be formed). -/
theorem s15_slot_one_source (E : Env) (n : Nat) (body : BoolH) (X : B8) (start : Nat)
    (w : TlsMpc.Signal.BundleResponse.Widths) (first last : Bool) (I : Ideal) (hb : I.bools body.id = some (bitsOf X))
    (hbn : body.id < n) (hp : Refresh.placedOk X.length start w first last = true) :
    ∃ I', runPlain E (Refresh.slotInput n body X.length start w first last) I = some I' ∧
      I'.bools (n + 4) = some (bitsOf (Refresh.slotBytes X start w first last ++ Refresh.widthsOf w)) ∧
      ∀ j, j < n → I'.bools j = I.bools j :=
  Refresh.slotInput_value E n body X start w first last I hb hbn hp

/-- **T4, the parse** [K]: the kernel the script feeds outputs `BundleResponse.device` on the body
the server sent (`bundleSlot_device`). -/
theorem s15_parse_device (X : B8) (start : Nat) (w : TlsMpc.Signal.BundleResponse.Widths) (first last : Bool)
    (hp : Refresh.placedOk X.length start w first last = true) :
    let out := TlsMpc.Signal.BundleResponse.device TlsMpc.ByteAuth.concrete X.length start w X
    TlsMpc.ReceiveKernel.values (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0))
        (Refresh.slotAssign X start w first last) =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) :=
  Refresh.parse_device X start w first last hp

/-- **T4, the parse, any counts: device or refused** [K] (`bundleSlot_parses_or_refuses`). -/
theorem s15_parse_or_refuse (X : B8) (start : Nat) (w : TlsMpc.Signal.BundleResponse.Widths) (first last : Bool)
    (hp : Refresh.placedOk X.length start w first last = true) :
    ((TlsMpc.Signal.BundleResponse.device TlsMpc.ByteAuth.concrete X.length start w X).getD 0 [] = [255] ∧
      (∀ w', (TlsMpc.Signal.BundleResponse.device TlsMpc.ByteAuth.concrete X.length start w' X).getD 0 [] = [255] →
        w' = w) ∧
      let out := TlsMpc.Signal.BundleResponse.device TlsMpc.ByteAuth.concrete X.length start w X
      TlsMpc.ReceiveKernel.values (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0))
          (Refresh.slotAssign X start w first last) =
        [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
          out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
        (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []])) ∨
    (∀ field ∈ TlsMpc.ReceiveKernel.values (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0))
        (Refresh.slotAssign X start w first last), ∀ byte ∈ field, byte = 0) :=
  Refresh.parse_parses_or_refuses X start w first last hp

/-- **T4, the encapsulation** [K; hyp: `KemWidths`]: every name binding of `kernels_compose` holds
for the script's wiring, so the script's encapsulation is `pipeline`. -/
theorem s15_kem_pipeline (K eA eB : B8) (hW : Refresh.KemWidths) (hK : K.length = 1568) (hA : eA.length = 32)
    (hB : eB.length = 32) : Refresh.kemFlow K eA eB = (TlsMpc.KernelSpecs.KemCompose.pipeline true K eA eB).flatten :=
  Refresh.kemFlow_pipeline K eA eB hW hK hA hB

/-- **T4, the encapsulation, valid key** [K; hyp: `KemWidths`]: status 255, the reference ciphertext
and secret. -/
theorem s15_kem_accept (K eA eB : B8) (hW : Refresh.KemWidths) (hK : K.length = 1568) (hA : eA.length = 32)
    (hB : eB.length = 32) (hvalid : TlsMpc.KernelSpecs.KemCompose.KeyValid K)
    (hs : (TlsMpc.KernelSpecs.KemCompose.specEnc true K eA eB).success = 255) :
    Refresh.kemFlow K eA eB = [255] ++ (TlsMpc.KernelSpecs.KemCompose.specEnc true K eA eB).bytes.take 1568 ++
      (TlsMpc.KernelSpecs.KemCompose.specEnc true K eA eB).bytes.drop 1568 :=
  Refresh.kemFlow_accept K eA eB hW hK hA hB hvalid hs

/-- **T4, the encapsulation, invalid key: nothing released** [K; hyp: `KemWidths`]. -/
theorem s15_kem_invalid (K eA eB : B8) (hW : Refresh.KemWidths) (hK : K.length = 1568) (hA : eA.length = 32)
    (hB : eB.length = 32) (h : ¬ TlsMpc.KernelSpecs.KemCompose.KeyValid K) : ∀ b ∈ Refresh.kemFlow K eA eB, b = 0 :=
  Refresh.kemFlow_invalid K eA eB hW hK hA hB h

/-- **T4, the first message: `wired` for the script** [K; hyp: `SessionWidths`, the send binds the
handed records]: the scratch hands the send `establish-session`'s outputs 1 and 2, so
`firstMessage_envelope` / `openedEnvelopes_first` apply. -/
theorem s15_first_wired (cert content : Nat) (s : TlsMpc.KernelSpecs.EstablishDevices.DeviceSession)
    (d : TlsMpc.KernelSpecs.EstablishDevices.DeviceSeal) (hW : Refresh.SessionWidths cert d.withOneTime)
    (established : (s.outputs cert d.withOneTime).getD 0 [] = [255])
    (hconv : d.input cert content "conversation" = Refresh.keptConversation (s.outputs cert d.withOneTime).flatten cert)
    (hpend : d.input cert content "pending" = Refresh.keptPending (s.outputs cert d.withOneTime).flatten cert)
    (opened : (d.outputs cert content).getD 0 [] = [255]) :
    TlsMpc.KernelSpecs.EstablishDevices.wired cert content (s, d) :=
  Refresh.first_wired cert content s d hW established hconv hpend opened

/-- **A drop keeps the table's invariant** [M] (`opDrop_inv`). -/
theorem s15_drop_inv (sigs : Bytes → Option Sig) (c : Ctx) (t : Contacts.Table) (st : Refresh.RState)
    (hT : t.Inv c) (hR : st.Inv c t) :
    WFP sigs (fun c' r => ((Refresh.opDrop t st).commit r).1.Inv c' ∧ ((Refresh.opDrop t st).commit r).2.Inv c' t) c
      (Refresh.opDrop t st).script :=
  Refresh.opDrop_inv sigs c t st hT hR

end FlowsS15

/-! ### 7h. The joins: S11's curve flows as the parameters of S12–S15 (`scripts-stack`)

`TlsMpc/Node/Flows/Join.lean` (scripts and proofs) and `Flows/JoinBackend.lean` (IO glue, no
theorems); STACK_NOTES.md has the join table. The parameters the branches left open are
instantiated with S11's flows and S10's conversions; each composed script declares the union of
its parts' kinds, and S15's hypothesis `CurveOps.Reveals` is DISCHARGED for the joined
operations. **M** as above. -/

section FlowsJoin

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows

/-- **S12's key agreement, joined** [M]: the agreement script (`Curve.splitAgree`, zero check,
`Convert.fieldToWord`) releases only P-SPLIT's and P-F2W's kinds. -/
theorem join_splitAgreeWord_reveals (f0 tSlot maskSlot n0 f1 : Nat) (m : Conv.WordMask) :
    Reveals Join.keyAgreementKinds (Join.splitAgreeWord f0 tSlot maskSlot n0 f1 m) :=
  Join.splitAgreeWord_reveals f0 tSlot maskSlot n0 f1 m

/-- **S13's ephemeral pair, joined** [M]: the offset step and field to word release only P-OFFSET's
and P-F2W's kinds. -/
theorem join_ephemeralWord_reveals (f0 maskSlot n0 f1 : Nat) (st : Curve.OffsetState) (τ : Nat)
    (m : Conv.WordMask) :
    Reveals Join.ephemeralKinds (Join.ephemeralWord f0 maskSlot n0 f1 st τ m) :=
  Join.ephemeralWord_reveals f0 maskSlot n0 f1 st τ m

/-- **S14's curve parameter, joined** [M]: S11's ladder agreements on P-BITS swap bits declare
their kinds from every state; with S14's program-based signature and base check, ops 50 and 51
release only registered kinds (S14's `openFirst_reveals`, `session_reveals` instantiated). -/
theorem join_receive_reveals (sl : Join.AgreeSlots) (pm : Receive.ProgramMasks) (loaded : Bytes → Bool) :
    (∀ fi env size, Receive.RevealsG (Receive.firstKinds ++ .maskedDenominator :: Join.receiveAgreeKinds)
      (Receive.openFirst (Join.receiveCurve sl pm) loaded fi env size)) ∧
    (∀ a sp ss, Receive.RevealsG (Receive.sessionKinds ++ .maskedDenominator :: Join.receiveAgreeKinds)
      (Receive.session (Join.receiveCurve sl pm) loaded a sp ss)) ∧
    (∀ k ∈ Receive.firstKinds ++ Receive.sessionKinds ++ .maskedDenominator :: Join.receiveAgreeKinds,
      k ∈ Label.kinds) :=
  Join.receive_joined_reveals sl pm loaded

/-- **S15's `CurveOps.Reveals`, discharged** [M]. -/
theorem join_refreshOps_reveals (rc : Join.RefreshCurve) : (Join.refreshOps rc).Reveals :=
  Join.refreshOps_reveals rc

/-- **T3 for the joined establishment, no hypothesis on the curve** [M]. -/
theorem join_refresh_reveals (rc : Join.RefreshCurve) (acct : Refresh.Account) (t : Contacts.Table)
    (st : Refresh.RState) (id registration index count step start : Nat)
    (w : TlsMpc.Signal.BundleResponse.Widths) (slot : Nat) :
    Reveals (Refresh.refreshKinds Join.refreshCurveKinds)
      (Refresh.opEstablish (Join.refreshOps rc) acct t st id registration index count step start w slot).script ∧
    ∀ k ∈ Refresh.refreshKinds Join.refreshCurveKinds, k ∈ Label.kinds :=
  Join.refresh_joined_reveals rc acct t st id registration index count step start w slot

open TlsMpc.KernelSpecs.EstablishDevices (DeviceSession DeviceSeal wired) in
/-- **S15's `first_wired` bindings from S13's `bundle-seal` layout** [K]: for the bundle S13's
`devicesScript` builds, `wired` holds given only that the certificate bytes are the session's
certificate input (`hcert`) and the pending block is the session's (`hpend`). -/
theorem join_first_wired (cert content : Nat) (s : DeviceSession) (oneTime : Bool) (cw pw ew iw : Nat)
    (certBytes pending address text : Contacts.B8) (w : Bits)
    (hW : Refresh.SessionWidths cert oneTime)
    (established : (s.outputs cert oneTime).getD 0 [] = [255])
    (hcert : certBytes = s.input cert oneTime "certificate")
    (hpend : pending = (s.outputs cert oneTime).getD 2 [])
    (hc : (certBytes ++ ((s.outputs cert oneTime).getD 1 []).drop cert).length = Send.convBytes cert)
    (hp : pending.length = TlsMpc.EstablishKernel.pendingBytes) (ha : address.length = 17)
    (ht : text.length = content + 10) (d : DeviceSeal)
    (hd : d = ⟨oneTime, cw, pw, ew, iw, Send.shapedAssign (TlsMpc.BundleKernel.sealInputs cert content)
      (Contacts.bitsOf (certBytes ++ ((s.outputs cert oneTime).getD 1 []).drop cert) ++
        (Contacts.bitsOf pending ++ (Contacts.bitsOf address ++ (Contacts.bitsOf text ++ w))))⟩)
    (opened : (d.outputs cert content).getD 0 [] = [255]) :
    wired cert content (s, d) :=
  Join.join_first_wired cert content s oneTime cw pw ew iw certBytes pending address text w hW established
    hcert hpend hc hp ha ht d hd opened

/-- **Every kind the joined scripts release is a registered label.** -/
theorem join_kinds_registered :
    ∀ k ∈ Join.keyAgreementKinds ++ Curve.splitKinds ++ Join.ephemeralKinds ++ Random.jointKinds ++
      Join.receiveAgreeKinds ++ Join.refreshCurveKinds, k ∈ Label.kinds :=
  Join.join_kinds_registered

end FlowsJoin

/-! ### 7i. J1 (no slot of fresh randomness read twice) and the controller-side script runner

`TlsMpc/Node/Flows/JoinOnce.lean`: every field-element input of the joined receive and refresh
flows reads a store slot TAKEN from the state's supply (`Receive.St.slots`, `Gen.takeSlot`), so on
every run no slot of fresh mask contributions is read twice (two openings `z·m`, `z'·m` with one
mask `m` would reveal `z / z'`; before J1's fix op 50's two agreements shared one slot).
`TlsMpc/Node/Flows/Runner.lean`: the runner's pure core `drive` (what the controller sends as
op 93, batch by batch) against the model's honest party. **M** as above; the runner's IO loop is
`drive`'s steps (unverified glue, like the backends). -/

section FlowsRunner

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows

/-- **J1, op 50 joined** [M]: whatever the replies, the slots a run of the joined `openFirst` reads
are slots of the supply it started with, none twice (its two agreements and `xeddsa-check`). -/
theorem j1_openFirst_reads_once (sl : Join.AgreeSlots) (pm : Receive.ProgramMasks) (loaded : Bytes → Bool)
    (fi : Receive.FirstIn) (env : BoolH) (size : Nat) (st : Receive.St) (h : (JoinOnce.supply st).Nodup) :
    ∀ rs, (JoinOnce.readsAlong (Receive.openFirst (Join.receiveCurve sl pm) loaded fi env size st) rs).Nodup ∧
      ∀ x ∈ JoinOnce.readsAlong (Receive.openFirst (Join.receiveCurve sl pm) loaded fi env size st) rs,
        x ∈ JoinOnce.supply st :=
  JoinOnce.openFirst_reads_once sl pm loaded fi env size st h

/-- **J1, op 51 joined** [M]: the same for the session (`xeddsa-recover`, `receive-torsion`, the six
or seven agreements). -/
theorem j1_session_reads_once (sl : Join.AgreeSlots) (pm : Receive.ProgramMasks) (loaded : Bytes → Bool)
    (a : Receive.Arrival) (sp : Receive.SessionPublic) (ss : Receive.SessionSecrets) (st : Receive.St)
    (h : (JoinOnce.supply st).Nodup) :
    ∀ rs, (JoinOnce.readsAlong (Receive.session (Join.receiveCurve sl pm) loaded a sp ss st) rs).Nodup ∧
      ∀ x ∈ JoinOnce.readsAlong (Receive.session (Join.receiveCurve sl pm) loaded a sp ss st) rs,
        x ∈ JoinOnce.supply st :=
  JoinOnce.session_reads_once sl pm loaded a sp ss st h

/-- **J1, the joined agreements** [M]: they take their quotient-mask slot from the supply and read it
once (from every state whose supply and reads have no slot twice). -/
theorem j1_receiveAgree_once (U : List Nat) (sl : Join.AgreeSlots) (jobs : List Receive.Job) :
    JoinOnce.OnceG U (Join.receiveAgree sl jobs) :=
  JoinOnce.receiveAgree_once U sl jobs

/-- **J1, S15's joined curve operations** [M]: `lift`, `check`, `agree` each read only slots of
their own supply, none twice. -/
theorem j1_refreshOps_reads_once (rc : Join.RefreshCurve) (c : Counters) :
    ((rc.liftSlots.map Prod.fst).Nodup → ∀ p rs,
      (JoinOnce.readsAlong ((Join.refreshOps rc).lift c p) rs).Nodup ∧
        ∀ x ∈ JoinOnce.readsAlong ((Join.refreshOps rc).lift c p) rs, x ∈ rc.liftSlots.map Prod.fst) ∧
    ((rc.checkSlots.map Prod.fst).Nodup → ∀ x y ec pq rs,
      (JoinOnce.readsAlong ((Join.refreshOps rc).check c x y ec pq) rs).Nodup ∧
        ∀ s ∈ JoinOnce.readsAlong ((Join.refreshOps rc).check c x y ec pq) rs, s ∈ rc.checkSlots.map Prod.fst) ∧
    ((rc.agreeSlots.map Prod.fst).Nodup → ∀ ip sp o rs,
      (JoinOnce.readsAlong ((Join.refreshOps rc).agree c ip sp o) rs).Nodup ∧
        ∀ s ∈ JoinOnce.readsAlong ((Join.refreshOps rc).agree c ip sp o) rs, s ∈ rc.agreeSlots.map Prod.fst) :=
  JoinOnce.refreshOps_reads_once rc c

/-- **J1's sibling in the S15 join** [M]: the three calls' mask pools cut from one share no mask. -/
theorem j1_refresh_pools_disjoint (p : Conv.MaskPool) (hd : p.Distinct) :
    let s := Join.splitPool p
    (s.1.words ++ s.2.1.words ++ s.2.2.1.words ++ s.2.2.2.words).Nodup ∧
      (s.1.bits ++ s.2.1.bits ++ s.2.2.1.bits ++ s.2.2.2.bits).Nodup :=
  Join.split_disjoint p hd

/-- **The controller sends exactly the batches the model says** [M]: if the honest party's model run
of `s` returns `a`, the runner's pure core fed the values the model released to it (as the worker's
reply items) sends batches whose instructions are the model run's trace, in order, and returns `a`
with the model's final store. -/
theorem runner_drive_model (E : Env) (me : Party) (adv : Adversary) {α : Type} (fuel : Nat) (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) (a : α)
    (hr : (withAdv E me adv s σ I vD).result = some a) (hl : (withAdv E me adv s σ I vD).trace.length < fuel) :
    (Runner.drive E.hash me fuel s σ ((withAdv E me adv s σ I vD).viewH.map (·.datum))).2 =
        (some a, (withAdv E me adv s σ I vD).store) ∧
      (Runner.drive E.hash me fuel s σ ((withAdv E me adv s σ I vD).viewH.map (·.datum))).1.flatten.map InstrP.skel =
        (withAdv E me adv s σ I vD).trace :=
  Runner.drive_model E me adv fuel s σ I vD a hr hl

/-- **The runner sends only bounded wires** [M] (so every batch round-trips through the encoding). -/
theorem runner_drive_bounded (hash : Bytes → Bytes) (me : Party) {α : Type} (fuel : Nat) (s : Script α)
    (σ : Store) (ds : List Datum) (hs : Every Instr.Bounded s) :
    ∀ b ∈ (Runner.drive hash me fuel s σ ds).1, ∀ w ∈ b, w.Bounded :=
  Runner.drive_bounded hash me fuel s σ ds hs

/-- **The batches depend on the store only through `fill`** [M]. -/
theorem runner_nextBatch_fill_only (hash : Bytes → Bytes) (me : Party) {α : Type} (σ₁ σ₂ : Store)
    (h : ∀ i, fill hash me σ₁ i = fill hash me σ₂ i) (s : Script α) :
    nextBatch hash me σ₁ s = nextBatch hash me σ₂ s :=
  Runner.nextBatch_fill_only hash me σ₁ σ₂ h s

end FlowsRunner

/-! ### 7j. The contact set made selectable: J8, J11, J12, J13, F32

`TlsMpc/Node/Flows/Account.lean` (ops 47, 46 as scripts; the account state keeps the identity's
swap-bit handles and the sender key word), `Flows/UpgradeAuth.lean` (op 32 on the script account
state), `Flows/Join.lean` + `Flows/JoinIdentity.lean` (J8: the identity scalar's swap bits as field
handles in the joined agreements, spared by every run), `Flows/ContactsPrepare.lean` (F32: op 66's
contact-table glue; J12: the sender key), `Flows/Select.lean` (the contact set switches as one),
`Flows/Runner.lean` (J13: slots released). **M** as above; the kernels' values through `Signal`'s
specifications (the upgrade kernels, T2 for their circuits as `Contacts.Loaded`'s). -/

section FlowsContactSet

open TlsMpc.Node TlsMpc.Node.Engine TlsMpc.Node.Flows

/-- **Op 47 releases nothing** [M]. -/
theorem s16_credentials_reveals (a : Account.State) (slot : Nat) :
    Reveals [] (Account.credentialsStep a slot).1 :=
  Account.credentialsStep_reveals a slot

/-- **Op 46 (TEST) releases only the conversions' masked bits** [M]. -/
theorem s16_admit_reveals (a : Account.State) (n f : Nat) (pool : Conv.MaskPool) (hinted : Bool)
    (scalarSlot certSlot certLen : Nat) :
    Reveals Account.openKinds55 (Account.admitStep a n f pool hinted scalarSlot certSlot certLen) :=
  Account.admitStep_reveals a n f pool hinted scalarSlot certSlot certLen

/-- **Op 32 releases only the joint nonce's commitment and opening** [M]: the credentials and the
request are never opened. -/
theorem s16_upgrade_reveals (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot n : Nat)
    (cr : UpgradeAuth.Creds) :
    Reveals Random.jointKinds (UpgradeAuth.authenticated hash me nonceSlot valueSlot n cr) :=
  UpgradeAuth.authenticated_reveals hash me nonceSlot valueSlot n cr

/-- **Op 32 is well formed** [M] from a context holding the credential handles with their marks. -/
theorem s16_upgrade_wf (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (nonceSlot valueSlot n : Nat)
    (cr : UpgradeAuth.Creds) (c : Ctx) (outM : List Mark) (hf : Contacts.Fresh c n)
    (hp : ∀ p ∈ cr.parts, p.id < n ∧ c.bool? p = some UpgradeAuth.credInfo)
    (hsig : sigs cr.name = some ⟨8 * (Account.credentialBytes * cr.parts.length + 16), outM⟩)
    (hout : outM.length ≤ maxWidth) : WF sigs c (UpgradeAuth.authenticated hash me nonceSlot valueSlot n cr) :=
  UpgradeAuth.authenticated_wf sigs hash me nonceSlot valueSlot n cr c outM hf hp hsig hout

/-- **The shared upgrade kernel on the bundle op 32 builds** is the relay's request on the XOR of
the credential shares and the nonce (`signalUpgradeShared_spec`) [K]. -/
theorem s16_request_shared_value (a b nonce : Contacts.B8) (ha : a.length = 16 + UpgradeAuth.passwordBytes)
    (hb : b.length = 16 + UpgradeAuth.passwordBytes) (hn : nonce.length = 16) :
    Contacts.kernelOut (HybridKernel.signalUpgradeShared UpgradeAuth.passwordBytes) (a ++ b ++ nonce) =
      Signal.RelayUpgrade.request ByteAuth.concrete UpgradeAuth.passwordBytes (List.zipWith (· ^^^ ·) a b ++ nonce) :=
  UpgradeAuth.requestShared_value a b nonce ha hb hn

/-- **The plain upgrade kernel** (credentials combined, op 55) [K]. -/
theorem s16_request_plain_value (cred nonce : Contacts.B8) (hc : cred.length = 16 + UpgradeAuth.passwordBytes)
    (hn : nonce.length = 16) :
    Contacts.kernelOut (HybridKernel.signalUpgrade UpgradeAuth.passwordBytes) (cred ++ nonce) =
      Signal.RelayUpgrade.request ByteAuth.concrete UpgradeAuth.passwordBytes (cred ++ nonce) :=
  UpgradeAuth.requestPlain_value cred nonce hc hn

/-- **J8** [M]: a job whose scalar has swap-bit handles runs nothing and makes nothing. -/
theorem j8_jobBits_swaps (sl : Join.AgreeSlots) (j : Receive.Job) (hs : List FieldH) (h : sl.swaps j.scalar = some hs)
    (st : Receive.St) : Join.jobBits sl j st = .done ((hs, []), st) :=
  Join.jobBits_swaps sl j hs h st

/-- **J8: the joined agreements spare the identity's swap-bit handles** [M]: along every branch no
instruction frees them or consumes them as a program mask (handles allocated before the run, none a
pool mask's). -/
theorem j8_receiveAgree_spares (sl : Join.AgreeSlots) (jobs : List Receive.Job) (st : Receive.St) (S : List FieldH)
    (hbelow : ∀ h ∈ S, h.id < st.table.ctr.field) (hpool : ∀ m ∈ st.pool.words, m.field ∉ S) :
    Every (JoinIdentity.Spares S) (Join.receiveAgree sl jobs st) :=
  JoinIdentity.receiveAgree_spares sl jobs st S hbelow hpool

/-- **J8 for S15's agreement step** [M]. -/
theorem j8_agreeG_spares (sl : Join.AgreeSlots) (ip sp : BoolH) (o : Option BoolH) (st : Receive.St) (S : List FieldH)
    (hbelow : ∀ h ∈ S, h.id < st.table.ctr.field) (hpool : ∀ m ∈ st.pool.words, m.field ∉ S) :
    Every (JoinIdentity.Spares S) (Join.agreeG sl ip sp o st) :=
  JoinIdentity.agreeG_spares sl ip sp o st S hbelow hpool

/-- **J12 and J8: the sender key's agreement spares them** [M]. -/
theorem j12_senderPublic_spares (sl : Join.AgreeSlots) (st : Receive.St) (S : List FieldH)
    (hbelow : ∀ h ∈ S, h.id < st.table.ctr.field) (hpool : ∀ m ∈ st.pool.words, m.field ∉ S) :
    Every (JoinIdentity.Spares S) (ContactsPrepare.senderPublicG sl st) :=
  JoinIdentity.senderPublicG_spares sl st S hbelow hpool

/-- **J12: the sender key releases only the joined agreements' kinds** [M]. -/
theorem j12_senderPublic_reveals (sl : Join.AgreeSlots) :
    Receive.RevealsG Join.receiveAgreeKinds (ContactsPrepare.senderPublicG sl) :=
  ContactsPrepare.senderPublicG_reveals sl

/-- **F32: one contact's preparation releases only P-W2F's, P-OFFSET's and the agreements' kinds**
[M], all registered. -/
theorem f32_prepare_reveals (hash : Bytes → Bytes) (me : Party) (cert : BoolH) (certLen : Nat) (sl : Join.AgreeSlots)
    (os : Curve.OffsetSlots) (state : BoolH) :
    Receive.RevealsG ContactsPrepare.prepareKinds (ContactsPrepare.prepareOneG hash me cert certLen sl os state) ∧
      ∀ k ∈ ContactsPrepare.prepareKinds, k ∈ Label.kinds :=
  ⟨ContactsPrepare.prepareOneG_reveals hash me cert certLen sl os state, ContactsPrepare.prepareKinds_registered⟩

/-- **F32: the status byte means "prepared"** [M]. -/
theorem f32_prepareStatus_iff (t : Contacts.Table) (cache : ContactsPrepare.Cache) (id : Nat) :
    ContactsPrepare.statusByte t cache id = 255 ↔ ∃ p, ContactsPrepare.prepared? t cache id = some p :=
  ContactsPrepare.prepareStatus_iff t cache id

/-- **F32: after the commit the contact is prepared with its run's results, no other contact
changes** [M]. -/
theorem f32_commit (t : Contacts.Table) (cache : ContactsPrepare.Cache) (id : Nat) (p : ContactsPrepare.Prepared)
    (e : Contacts.Entry) (he : t.find? id = some e) :
    ContactsPrepare.prepared? (ContactsPrepare.commit t cache id p).1 (ContactsPrepare.commit t cache id p).2 id = some p ∧
      ∀ id', id' ≠ id → ContactsPrepare.prepared? (ContactsPrepare.commit t cache id p).1
        (ContactsPrepare.commit t cache id p).2 id' = ContactsPrepare.prepared? t cache id' :=
  ⟨ContactsPrepare.commit_prepared t cache id p e he, fun id' h => ContactsPrepare.commit_other t cache id id' p h⟩

/-- **F32: the commit keeps the contact table's invariant** [M], given what the run leaves. -/
theorem f32_commit_inv {c c' : Ctx} (t t' : Contacts.Table) (cache : ContactsPrepare.Cache) (id : Nat)
    (p : ContactsPrepare.Prepared) (e : Contacts.Entry)
    (hI : t.Inv c) (he : t.find? id = some e) (hent : t'.entries = t.entries) (hn : t.next ≤ t'.next)
    (hf : Contacts.Fresh c' t'.next)
    (hold : ∀ q ∈ t.entries, ∀ g ∈ q.2.handles, c'.bool? g = c.bool? g)
    (hnew : t.next ≤ p.static.id) (hbelow : p.static.id < t'.next) (hlive : (c'.bool? p.static).isSome = true) :
    (ContactsPrepare.commit t' cache id p).1.Inv c' :=
  ContactsPrepare.commit_inv t t' cache id p e hI he hent hn hf hold hnew hbelow hlive

/-- **The contact set is selectable, and only whole** (with `tls` and `masks`). -/
theorem select_contactSet :
    (Select.check (Select.contactSet ++ ["tls", "masks"])).toBool = true ∧
      ∀ g ∈ Select.contactSet ++ ["tls", "masks"],
        (Select.check ((Select.contactSet ++ ["tls", "masks"]).erase g)).toBool = false :=
  ⟨Select.check_contactSet, Select.check_contactSet_partial⟩

/-- **J13: a released slot reads as the base store** (so a script naming it fails the payload check)
and the runner's `fresh` never hands out a released slot. -/
theorem j13_release (m : Runner.Slots) (base : Store) (ns : List Nat) (s : Nat) (hs : s ∈ ns)
    (l : Runner.Ledger) (hl : l.Inv) :
    (((m.release ns).over base).bits s = base.bits s ∧ ((m.release ns).over base).elems s = base.elems s ∧
      ((m.release ns).over base).bytes s = base.bytes s) ∧
    (l.fresh.1 ∉ l.released ∧ l.fresh.2.Inv) ∧ (l.release ns).Inv :=
  ⟨Runner.release_reads_base m base ns s hs, Runner.Ledger.fresh_not_released l hl, Runner.Ledger.release_inv l ns hl⟩

end FlowsContactSet

/-! ### 7-labels. Labels, the reveal registry and the engine's batching (stages S9, S6; numbered 7b
on the main line, renamed when the main line was merged into `scripts-stack`, whose 7b is S10)

`TlsMpc/Node/Engine/Labels.lean` (the release labels are the reveal kinds' codes),
`Engine/Reveal.lean` (`Reveals ks s`: every release instruction of `s` carries the label of a
declared kind; the open rule in the reveal list's vocabulary; the Lean sender's wires are bounded),
`Flows/Registry.lean` (every script flow's declared kinds are registered) and the batch builder of
`Engine.lean` (decision D8). **Trust:** statements about the model, as section 7a. -/

section LabelsRegistry
open TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts
open TlsMpc.Node (RevealKind)

/-! #### The labels -/

/-- **A label names its kind:** `Label.ofKind` is injective. -/
theorem engine_label_ofKind_inj {a b : RevealKind} : Label.ofKind a = Label.ofKind b ↔ a = b :=
  TlsMpc.Node.Engine.Label.ofKind_inj

/-- **The registry's labels are pairwise distinct** (no two share a code). -/
theorem engine_label_all_distinct : (Label.all.map (·.code)).Nodup :=
  TlsMpc.Node.Engine.Label.all_distinct

/-- **No registered label has code 0** (which `check` refuses). -/
theorem engine_label_all_nonzero : ∀ l ∈ Label.all, l.code ≠ 0 :=
  TlsMpc.Node.Engine.Label.all_nonzero

/-! #### The open rule in the reveal list's vocabulary -/

/-- **The adversary's view in the reveal list's vocabulary.** In any run of a script that declares
the kinds `ks`, against any adversary, from any store and engine state, every release the adversary
received is labelled `Label.ofKind k` for a declared kind `k`. -/
theorem engine_viewD_kinds (E : Env) (me : Party) (adv : Adversary) {α : Type} (ks : List RevealKind)
    (s : Script α) (hs : Reveals ks s) (σ : Store) (I : Ideal) (vD : List Release) :
    ∀ r ∈ (withAdv E me adv s σ I vD).viewD, ∃ k ∈ ks, r.label = Label.ofKind k :=
  TlsMpc.Node.Engine.viewD_kinds E me adv ks s hs σ I vD

/-- **The honest party's view in the reveal list's vocabulary** (the same, for what it received). -/
theorem engine_viewH_kinds (E : Env) (me : Party) (adv : Adversary) {α : Type} (ks : List RevealKind)
    (s : Script α) (hs : Reveals ks s) (σ : Store) (I : Ideal) (vD : List Release) :
    ∀ r ∈ (withAdv E me adv s σ I vD).viewH, ∃ k ∈ ks, r.label = Label.ofKind k :=
  TlsMpc.Node.Engine.viewH_kinds E me adv ks s hs σ I vD

/-! #### The registry: every script flow declares registered kinds -/

/-- **The registry check:** every kind a script flow declares is one of the label registry's kinds. -/
theorem registry_declared_registered : ∀ p ∈ Registry.declared, ∀ k ∈ p.2, k ∈ Label.kinds :=
  TlsMpc.Node.Flows.Registry.declared_registered

/-- **Every script flow declares its kinds** (on every branch, for every argument). -/
theorem registry_script_flows_reveal :
    (∀ hash me nonce value, Reveals Random.jointKinds (Random.joint hash me nonce value)) ∧
    (∀ hash me nonce value, Reveals Random.jointKinds (Upgrade.publicUpgrade hash me nonce value)) ∧
    (∀ n slot, Reveals keyKinds (keyScript n slot)) ∧
    (∀ n key state size version, Reveals sealKinds (sealScript n key state size version)) ∧
    (∀ n key version check ct, Reveals openKinds (openScript n key version check ct)) ∧
    (∀ hash me nonceSlot valueSlot used n key state size,
      Reveals writeKinds (writeScript hash me nonceSlot valueSlot used n key state size)) ∧
    (∀ t id slot, Reveals keyKinds (opKey t id slot).script) ∧
    (∀ t id version, Reveals sealKinds (opSeal t id version).script) ∧
    (∀ t id kinds version check ct, Reveals openKinds (opOpen t id kinds version check ct).script) ∧
    (∀ t id, Reveals [] (opEvict t id).script) ∧
    (∀ t fromId toId, Reveals [] (opAssign t fromId toId).script) ∧
    (∀ t id hash me nonceSlot valueSlot used,
      Reveals writeKinds (opWrite t id hash me nonceSlot valueSlot used).script) ∧
    (∀ a slot, Reveals keyKinds (Account.keyStep a slot).1) ∧
    (∀ a n version, Reveals sealKinds (Account.opSeal a n version).1) ∧
    (∀ a version, Reveals sealKinds (Account.sealStep a version).1) :=
  TlsMpc.Node.Flows.Registry.script_flows_reveal

/-- **Registered labels only:** in any run of a script that declares registered kinds, against any
adversary, every release the adversary receives carries a label of `Label.all`. -/
theorem registry_viewD_registered (E : Env) (me : Party) (adv : Adversary) {α : Type} (ks : List RevealKind)
    (s : Script α) (hs : Reveals ks s) (hk : ∀ k ∈ ks, k ∈ Label.kinds) (σ : Store) (I : Ideal)
    (vD : List Release) : ∀ r ∈ (withAdv E me adv s σ I vD).viewD, r.label ∈ Label.all :=
  TlsMpc.Node.Flows.Registry.viewD_registered E me adv ks s hs hk σ I vD

/-! #### Each flow's releases carry its declared kinds (no hypothesis) -/

/-- **T3 for `Random.joint` in the reveal list's vocabulary:** only the commitment and opening kinds. -/
theorem flows_joint_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (nonce value : Nat) :
    ∀ r ∈ (withAdv E me adv (Random.joint E.hash me nonce value) σ I vD).viewD,
      ∃ k ∈ Random.jointKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Random.joint_viewD_kinds E me adv σ I vD nonce value

/-- **T3 for the upgrade in the reveal list's vocabulary:** only `Random.joint`'s kinds. -/
theorem flows_publicUpgrade_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (nonce value : Nat) :
    ∀ r ∈ (withAdv E me adv (Upgrade.publicUpgrade E.hash me nonce value) σ I vD).viewD,
      ∃ k ∈ Random.jointKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Upgrade.publicUpgrade_viewD_kinds E me adv σ I vD nonce value

/-- **T3 for `Contacts.seal` in the reveal list's vocabulary:** only `ofKind .sealedBlob`. -/
theorem flows_seal_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (n : Nat) (key state : BoolH) (size : Nat) (version : B8) :
    ∀ r ∈ (withAdv E me adv (sealScript n key state size version) σ I vD).viewD,
      ∃ k ∈ sealKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Contacts.seal_viewD_kinds E me adv σ I vD n key state size version

/-- **T3 for `Contacts.open` in the reveal list's vocabulary:** only `ofKind .blobAccepted`. -/
theorem flows_open_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (n : Nat) (key : BoolH) (version check ct : B8) :
    ∀ r ∈ (withAdv E me adv (openScript n key version check ct) σ I vD).viewD,
      ∃ k ∈ openKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Contacts.open_viewD_kinds E me adv σ I vD n key version check ct

/-- **T3 for `Contacts.key` in the reveal list's vocabulary:** no kind (the view is empty). -/
theorem flows_key_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (n slot : Nat) :
    ∀ r ∈ (withAdv E me adv (keyScript n slot) σ I vD).viewD, ∃ k ∈ keyKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Contacts.key_viewD_kinds E me adv σ I vD n slot

/-- **T3 for a state write in the reveal list's vocabulary:** only the commitment, opening and
sealed-blob kinds. -/
theorem flows_write_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release)
    (nonceSlot valueSlot : Nat) (used : List B8) (n : Nat) (key state : BoolH) (size : Nat) :
    ∀ r ∈ (withAdv E me adv (writeScript E.hash me nonceSlot valueSlot used n key state size) σ I vD).viewD,
      ∃ k ∈ writeKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Contacts.write_viewD_kinds E me adv σ I vD nonceSlot valueSlot used n key state size

/-- **T3 for op 38 on the table in the reveal list's vocabulary:** only `ofKind .sealedBlob`. -/
theorem flows_opSeal_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (t : Table) (id : Nat) (version : B8) :
    ∀ r ∈ (withAdv E me adv (opSeal t id version).script σ I vD).viewD, ∃ k ∈ sealKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Contacts.opSeal_viewD_kinds E me adv σ I vD t id version

/-- **T3 for ops 37 and 63 on the table in the reveal list's vocabulary:** only
`ofKind .blobAccepted`. -/
theorem flows_opOpen_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (t : Table) (id : Nat) (kinds : List Nat) (version check ct : B8) :
    ∀ r ∈ (withAdv E me adv (opOpen t id kinds version check ct).script σ I vD).viewD,
      ∃ k ∈ openKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Contacts.opOpen_viewD_kinds E me adv σ I vD t id kinds version check ct

/-- **T3 for op 54 in the reveal list's vocabulary** (both credential cases, any state): only
`ofKind .sealedBlob`. -/
theorem flows_account_opSeal_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (a : Account.State) (n : Nat) (version : B8) :
    ∀ r ∈ (withAdv E me adv (Account.opSeal a n version).1 σ I vD).viewD,
      ∃ k ∈ sealKinds, r.label = Label.ofKind k :=
  TlsMpc.Node.Flows.Account.opSeal_viewD_kinds E me adv σ I vD a n version

/-! #### The batches the Lean sender builds -/

/-- **The batches an honest party sends are admitted** (decision D8 refuses none): if the script is
well formed in the carried context and its batch is sent, `checkBatch` accepts its skeletons. -/
theorem engine_nextBatch_admitted (sigs : Bytes → Option Sig) (hash : Bytes → Bytes) (me : Party) (σ : Store)
    {α : Type} (s : Script α) : ∀ (c : Ctx) (i₀ : Nat), WF sigs c s →
    (∀ r, (nextBatch hash me σ s).rest ≠ .aborted r) →
    ∃ c' shs, checkBatchFrom sigs c i₀ ((nextBatch hash me σ s).wires.map InstrP.skel) = .ok (c', shs) :=
  TlsMpc.Node.Engine.nextBatch_admitted sigs hash me σ s

/-- **Decision D8 for the batch builder:** in a batch `nextBatch` builds, no instruction but the
last ends a batch. -/
theorem engine_nextBatch_ends {α : Type} (hash : Bytes → Bytes) (me : Party) (σ : Store) (s : Script α) :
    ∀ w ∈ (nextBatch hash me σ s).wires.dropLast, w.endsBatch = false :=
  TlsMpc.Node.Engine.nextBatch_ends hash me σ s

/-- **Filling keeps the bound:** the payloads `fill` puts in have the lengths the skeleton declares,
all below 2^64. -/
theorem engine_fill_bounded (hash : Bytes → Bytes) (me : Party) (σ : Store) (i : Instr) (w : Wire)
    (h : fill hash me σ i = some w) (hb : i.Bounded) : w.Bounded :=
  TlsMpc.Node.Engine.fill_bounded hash me σ i w h hb

/-- **The wires of a batch the Lean sender builds are bounded** when the script's instructions are
(on every branch), so the batch encoding round-trips. -/
theorem engine_nextBatch_bounded {α : Type} (hash : Bytes → Bytes) (me : Party) (σ : Store) (s : Script α)
    (hs : Every Instr.Bounded s) : ∀ w ∈ (nextBatch hash me σ s).wires, w.Bounded :=
  TlsMpc.Node.Engine.nextBatch_bounded hash me σ s hs

end LabelsRegistry

/-! ## 8. NOT YET PROVED

Comments, not theorems. Each line names the statement (REORGANIZATION_PLAN.md section 7 / 8.1)
and the stage or proof track that delivers it. When one is proved, its restatement moves into
the matching section above in the same commit.

### Lowering and artifacts
* **T2** — open marks and printers. DONE for the flat kernels in the emitter batch (section 1b,
  effective once the emitters are rebuilt; the printed bytes do not change): for every kernel
  `lowerKernel` lowers (all four kernel emitters now share `TlsMpc/FlatKernelLayout.lean`), the
  printed layout's rows and open marks are the kernel's declared fields and marks
  (`layout_parse`, `layout_openCode`), parsing the printed `.flat` gives back `Flat`
  (`flat_printWith_render`, `flat_parse_render`), and the flat is `lowerExpr` of the joined
  outputs (`kernel_loaded`, `flat_lowerExpr_loaded`). Still open: `selection` (which named output
  bit is which bit of the joined value; with it, "the loaded file computes the kernel's `_spec`"
  per named field); that the C++/Rust loaders parse as `parseFlat`/`parseLayout` do; the V3
  field-program printer (`EmitWordMask`; scheduled with S9/S10). → **P3** (rest), **S9/S10**.

### Kernels compute their specification
* Kernel-level specs: now proved for every kernel this item used to list (section 2c). Closed in
  section 2d: `bundle-item` on the whole body (`bundleItem_whole`, from the locality lemma
  `bundleDevice_local`), the meaning of the `signal-widths` flags (`signalWidths_value`), the UUID,
  base64 and padded decimal slot encoders against independent references (RFC 4122 string form,
  RFC 4648, decimal digits) with round trips (`slotUuid_*`, `slotBase64_*`, `slotDecimal_*`).
  Also closed: `bundle-slot` against `device` on the body the server sent (section 2d:
  `bundleSlot_device`, `bundleSlot_eq_bundleItem`, `deviceSlots_splice`, `spliced_layout`,
  `slotValid_pad`; wrong digit counts refuse: `device_unique`, `bundleSlot_wrong_counts`,
  `bundleSlot_parses_or_refuses`, `bundleSlot_any_widths`). The caveat `inconsistent_width_accepts`
  (a body whose number has a leading zero, spliced with one digit count but declared with another
  in `widths`, was accepted where `device` refuses) is fixed in the emitter batch, effective after
  the re-lowering together with the C++ worker's new filler byte: the splice pads with the byte 0
  instead of `0`, `bundleSlot_inconsistent_width_refused`, and `bundleSlot_any_widths` now holds
  for every item whose fields do not start with a NUL byte (`bundleSlot_zero_padding_ambiguous`:
  with `0` padding no kernel change alone could have fixed it). Still trusted: that the C++ worker
  binds `head`/`before`/`item`/`after`/`end` as stated and pads with the filler 0, and that the
  template is what Signal-Server writes.
  → no stage assigned; candidate for **P5**.
* ML-KEM: Kyber-1024 (round 3, rank 4; libsignal key type 8). The `kem-*` kernels equal the
  repository's reference `MlKem.encapsulate` on valid keys and are zero on invalid keys (proved,
  section 2e). Still open: the reference being Kyber-1024 rests on test vectors against libcrux;
  the 2⁻¹⁰⁵ sampling-failure probability is a calculation; the worker's name binding between the
  `kem-*` kernels is a hypothesis. → no stage assigned.
* **T7** — what the server receives: (a) `signal-request-ctr`, `bundle-request-ctr`,
  `bundle-fetch-ctr` seal the frame with each slot replaced by the WebSocket-masked field and
  nothing else changed — now proved at kernel level up to the frame (section 2c:
  `*RequestCtr_spec`, `bundleFetchCtr_spec`, `insertSlots_inside_zero`), and now composed with the
  frames the controller builds (section 2d: `signalRequestCtr_built`, `bundleFetchCtr_built`,
  `bundleRequestCtr_built`: the opened ciphertext encrypts exactly the masked frame of the request
  with the secret fields in their slots; trusted: the C++ worker passes the controller's frame,
  mask and offsets unchanged); (b) `signal-seal-official`/`-built`
  compute `SealedSenderV1` encryption of the message produced by `ChainSend`/`SpqrSend` from the
  stored state — the kernel is now proved to compute that composition on concrete values
  (`signalSealBuilt_spec`), its value is sealed sender v1 of the reference send step's message
  (section 2c: `sealCore_value`, `boundSeal_value`, `signalSeal_value`, `sealValue_accepted`), and
  composed with (a) for an accepted send (section 2d: `serverReceives_accepted`). On refusal the
  kernel preserves the ratchet state, not the whole record: the stored record still takes the built
  text's kind byte and first 80 content bytes (`stagedOf`, `TlsMpc/HybridKernels.lean` line 446).
  Still open: `Reference.sealV1` is a transcription of libsignal's sealed-sender v1, not
  machine-linked to libsignal; the send step is checked against the repository's own
  `SpqrSend.canonical`, not against the Signal/SPQR specifications; the X25519 agreements (inputs
  here) and that the controller passes the opened envelope, frame and mask unchanged are not
  proved. The device-refresh path is now covered too: `bundle-seal` by value
  (`establishSeal_*`, `establishFirst_*`, section 2c) and `bundle-request-ctr` over several opened
  envelopes (`establishDevices_*`, `establishRequest_serverReceives_refresh*`, section 2d), with the
  same transcription and wiring caveats. → **P5**.

### Gating and what each opening reveals
* **T13** — receive gating, accept direction: now proved for the kernels on concrete values
  (section 3a: `receive-session` status 255 iff the MAC verified and the other checks passed, with
  the certificate checks under the controller's wiring; `receive-text` zero unless the session
  accepted; the `_rejects` lemmas; what `receive-text` and `receive-access-key` open). The DEFECT
  recorded here (`receive-text` accepted a body longer than its DataMessage) is fixed in the
  emitter batch, effective after the re-lowering: `receiveAcceptText_overlongBody_refused`, and
  `receive-text` accepts exactly what the reference protobuf reading accepts for length prefixes of
  at most two bytes (`receiveAcceptText_accepted_iff_reference`,
  `receiveAcceptText_text_status_iff_reference`, `receiveAcceptText_text_accepted_reference`;
  NEEDS_REVIEW.md 3f). Still open: prefixes of three or more bytes (refused by the kernel, accepted
  by a protobuf decoder: a completeness gap, not a leak); the converse for a genuine
  sender's envelope (that it is accepted); Prop forms for the multi-byte counters,
  `canonicalRange`, `Unpad.decode` and the layout masks (stated today as byte computations); an
  accept-direction value theorem for `contentShape`'s flags and for `receive-content`; and the
  field engine (the curve computations whose outputs `rx`, `ry` and the agreements are inputs
  here). → **P6**. S14 (section 7f): the controller's wiring is now the scripts' own (`Receive.*In`,
  `s14_verified_wiring`), so T13 holds for it without the wiring hypothesis (`s14_accept_certificate`,
  function level); open: the same through `jointRun` (S14_NOTES.md, F22).
* **T3** — disclosure per flow: the released values in any trace of a flow are exactly the
  listed `Reveal` kinds on the listed handles. The list exists since S6 (`TlsMpc/Node/Reveal.lean`,
  section 7-reveal: every `Opened` value is made there, each kind's docstring names its bounding
  theorems or "none yet"); behind each flow is still a C++ worker operation. → **S9–S16** (one per
  flow).

### The controller
* **T1 (all streams)** — DONE, about the loop the session runs (section 4g:
  `receivePolicy_t1_all`, `receivePolicy_loop_sub`, `receivePolicy_run_fuel`,
  `receivePolicy_view_replies`; PROOF_GAPS C1, C2 closed 2026-11-12), and from the first byte of a
  fresh connection (`{ PublicReceive.start accept with lenient, openBody }`, the HTTP head then
  frames) against `ReceiveSpec.classify`: `receivePolicy_t1_start` (PROOF_GAPS D1 closed 2026-11-12;
  steps between records must also keep the upgrade parser's state, `ReceiveStart.KeepsHead`).
  Assumed: `Faithful` (the engines' `revealRange` returns exactly the bytes asked for; a theorem for
  the S12 script backend on its branch, an assumption for the legacy operation 43). It is the
  precondition of `Reveal.serverBytes` (`Flow.Tls.revealRange`). → **P1** (D8).
* **T8** — request templates: for `build`/`buildDevices`/`buildFetch`/`assemble` the structural
  part is now proved (section 2d, about the controller's own builders in
  `TlsMpc/Node/Policy/Request.lean`): the frame is the WebSocket header and the message masked, slots
  are zero runs inside the payload, non-overlapping, at the returned offsets (`requestBuild_ok`,
  `requestInsertSlots_offsets`), and the messages are the reference protobuf/JSON requests in
  RFC 6455 client frames, `reply`, `keepalive`, `ping` and `clientFrame` included (section 4d,
  `t8_*`). Still open: the id `reply` answers is shown to be the one `varintAt` reads only under a
  hypothesis (`scan`'s loop invariant is not proved); `replies` (pong/close echoes) is covered
  by section 4c only. → **P2**.
* **T11** — application results: at `deliverJob`'s level DONE (section 5b:
  `t11_deliverJob_results`, `t11_resultsTail_spec`: when it returns, the reported results are the
  ones whose digest both controllers exchanged). Still open: the `DaemonLine.jobResult` / final
  report level (argued: results are written in one place, `serve` resets them per job), and that
  each result is `Recovery.onSend`/`onFetch` of revealed statuses or a fixed reason. PROOF_GAPS I2.
  → **P4** (rest).
* Parsers vs RFC 6455 / HTTP: the frame parser's extents and refusals, the control queue, the
  TLS record splitter and the upgrade's accept value now have references (section 4c). Still
  open: `TlsChatResponse` (the chat-response parser) has no reference yet; nor has the upgrade
  response parser; and frame-parser acceptance (a well-formed frame keeps validity 255) is not
  proved, so the composition frame parser → control queue is stated on the queue's inputs.
  → no stage assigned.

### State and ordering
* **T6 / ORD-1**, **ORD-2** — DONE for the deployed definitions (section 5b, **C-gen**:
  `ord1_*`, `ord2_*`; PROOF_GAPS C3 closed 2026-11-12: the definitions are the deployed functions;
  the remaining trust is A8, the free theorem of a generic definition, and the operations doing what
  their events name, `Session/Events.lean` header). Still open: ORD-1 for the S13 send scripts and
  ORD-2 after S15 (device refresh as scripts; PROOF_GAPS F59, I4). → **S13**, **S15**.
* **T10** — database writes: every blob = nonce ‖ sealed blob with the nonce fresh joint
  randomness unused in the session; versions increase by one per acknowledged write (the version
  half for the store functions: section 5b, `versions_*`). → **S9**.
* **T14** — stock used once: DONE for the journal/use model (section 5c, `stock_*`, **M**); the
  engine instruction and the C ABI are specified, not built (PROOF_GAPS C5). → **X1** (rest).
* **T15** — connection rotation reveals nothing about ids: the planner's action sequence is
  independent of the payloads (section 5c, `rotation_*`, **M**); not yet used by the session.
  → **X2** (rest).

### Conversions and helper protocols (T5)
* **P-RAND** (joint randomness): (a), (b) under `IdealCommit`, (c), disclosure and commit before
  open are proved in the model (section 7a). Still open: that the running code is the script (S9
  wiring). → **S9**.
* **P-CHAL**: (a), (b), (c) and `commit_open_sound` proved in the model (section 7b). Open: that the
  running code is the script (the S10 scripts are not yet called by the controller; S11–S16).
* **P-CUT** (section 7b). Proved: (a) at the protocol level (honest candidates pass, the mask and
  pair values); (b) `Reveals` of the whole `generate` (labels), the cut phase's disclosure with
  values, the cut disjoint from the kept candidates; (c) the core lemma (cut and bucket releases and
  word-mask flags unchanged under the cancelling shift; the shift a bijection reaching any target
  reference); (d) protocol and run level (`cutPhase_sound`); (e) protocol level exactly (pass ⟺
  val(ref) + val(member) < 2p and the errors cancel, for a canonical reference), the counting
  model's mixed-bucket rule, and the run level (`bucketPhase_sound`); (f) the flags' meaning; (g)
  `bitBlock_unique` with `FieldInverse`; (h) the pool and the frees. Proved since (section 7b
  continued, S10 follow-up): (a) for a whole honest run through `jointRun`, every parameter set
  with 0 < M and bits ≤ N, so the deployed profiles (`s10_pcut_a_run`); (c) composed with the model:
  two runs against the same adversary agree under the bucket-cancelling change of the honest
  candidates (`s10_pcut_c_agree`), plan 7.0's form `s10_generate_hides` with the re-randomisation a
  bijection (`s10_reRand_bijection`), the bit-block flag under the move (`s10_moveRef`: a bit block's
  reference is moved inside [32, p)); (f), (g) at run level (`s10_pcut_fg_run`,
  `s10_mask_consistent`); a WF theorem for `generate` (`s10_generate_wf`, `s10_profile_sizes`); the
  counting model's hypotheses for any run that returns (`s10_generate_sound`, `s10_bucket_uniform`)
  and the two challenge permutations as one arrangement (`s10_arrangement`). OPEN: (b) a value-level
  disclosure of the whole run as ONE prefix statement (the releases are characterised phase by
  phase inside `s10_pcut_c_agree`'s proof: `Twin.cut_same`, `bucket_same`, `flags_same`,
  `bitZ_same`); the PROBABILITY part of the correspondence with `proofs/` `CutAndChoose`: that the
  arrangement is uniform when the two permutations are (a K!-to-one counting fact), and that the
  permutations are uniform and independent of the bad set (`IdealCommit` for the seeds, SHA-256 as
  a random oracle in `permOf`); what `generate_hides` does not say: it is about the honest party's
  candidates for FIXED challenge randomness, and a bit block's reference below 32 (probability
  32/p) is revealed by the abort of its own run.
* **P-PAIR / P-B2F**, **P-W2F**, **P-F2W**: (a), (b), T3, (c) proved (section 7b; W2F and F2W (a)
  through `jointRun`; B2F (a) per bit and, for the whole bundle through `jointRun`,
  `s10_pb2f_honest`). Open: WF theorems for `wordToField`, `fieldToWord`, `bitsToField`, `Account.openStep` (`sharedBits`:
  `s10_sharedBits_wf`).
* **P-BITS**: (a) with `FieldInverse` (the converse of `fieldBits_bitCheck_bit`), (b), (c) at the
  protocol level; at run level `s10_pbits_run` (any adversary: every input of both parties is a bit
  and the outputs are the field XORs) and `s10_pbits_honest` (`jointRun`).
* **P-INV** (masked inversion `D`/`Z` nodes), **P-FIELDPROG** (what a program releases). → **S9**,
  **S11**.
* **P-SPLIT**, **P-OFFSET**, **P-HINT** (section 7c, stage S11). Proved: P-SPLIT (a) through
  `jointRun` for the agreement (`s11_splitAgree_honest`, `s11_addU_montU`; the group law itself is
  `proofs/` R7), (b) the gate (`Curve.splitAgree_gate`, checks = `curveValue`), (c) the kinds
  (`Curve.splitKinds`), (d) `s11_local_formulas`; P-OFFSET (a) the recoding lemma about the flow's
  own `recode` (`s11_recode64`, `s11_step_tableSum`) and the step's program inputs
  (`s11_stepIns_window`: exactly `offsetSum_recoded`'s hypothesis; there is no C++ `step`), (b) the
  key the script returns (`s11_ephemeralKey`), (c), (d) gates (`Curve.offsetPrepare_gate`,
  `Curve.pointExchange_gate`); P-HINT (a) (`s11_lift_order`), (b) soundness with `FieldInverse` and
  completeness under H-QR/Euler as named hypotheses (`s11_prepareStatus_iff`). Since the S11
  follow-up: `_wf` for every curve script and op 66 as a staged flow (`s11_wf_split_offset`,
  `s11_wf_hinted`, `s11_prepareContacts_wf`); `splitBegin` through `jointRun`
  (`s11_splitBegin_honest`) and the split agreement's value with the denominator discharged
  (`s11_splitAgree_montU`, `CompleteAddition` ← `proofs/` `edwards_complete`); the model form of
  `commit_open_sound` for the point exchanges (`s11_pointExchange_sound`) and their value-level
  disclosure (`s11_pointExchange_disclosure`: a prefix of [our commitment, our opening]); `sqrt` and the lift's
  roots never fail (`s11_liveness`). Since the second follow-up (F22): the block-level lemma for
  n masked quotients (`s11_quotientMany_honest`) and honest runs through `jointRun` of `agree`
  (the handles hold `X25519.spec`: `s11_agree_honest`), `offsetPrepare`, `offsetStep`,
  `offsetStepFast` (`s11_offset_honest`), `tables`, `agreeAffine`, `signatures`, `torsion`
  (`s11_hinted_honest`), `lift`, `agreeHinted` (`s11_lift_agreeHinted_honest`), under the named
  program hypotheses `Curve.ComputesD` / `Curve.Live` (discharged for translated artifacts by
  `FieldDagV3.eval_compileAll`, `eval_ofArtifact_some` given nonzero honest denominators) and
  nonzero mask sums. Since the third follow-up (F22a, F22b, F25b): those program hypotheses are
  DISCHARGED (`s11_decl_live`: a compiled program is live where its source divisions are nonzero;
  `s11_programs_live`, `s11_maskfree_computes`: every curve program the flows run, from the loader's
  facts and per-program input conditions, under the named group facts `AddClosed`, `ExtClosed`,
  `RecipientOnCurve`, `CompleteAddition`, theorems of `proofs/`), the runs restated without them
  (`Curve.*_honest'`, headline `s11_offsetPrepare_honest_derived`), the checks derived on honest inputs
  for `offsetPrepare` and `lift` and the lift's `Z` on the curve (`s11_checks_vanish`); the batched
  inversion, the hints and the public table never fail on curve points (`s11_toAffineAll_live`);
  the point exchange with m points (`s11_pointExchange_many_honest`). OPEN: the bit table's link
  checks from honest hints (reduced to `EdwardsHinted.LinkedFrom`, the group law for the hints'
  multiples: `proofs/` `bitTable_entries`); the input conditions from the state the earlier flows
  leave (e.g. the offset table's entries are curve points); honest runs of `prepareSecond` and
  `prepareContacts` as a staged flow (checked executably:
  `node_worker/tests/s11_vectors.txt`, every `check … ok`); value-level disclosure (T3 with values)
  for the curve flows other than the point exchanges and the quotient round
  (`s11_quotientMany_disclosure`: [z_j·m_j, flags] for the masks the engines hold): the opened
  checks, `w`, `Z` and the programs' own `D` openings are proved only at the level of kinds; P-HINT (c), (d) composed with the runs (`entries_sound`,
  `curve_hinted_Z_uniform` are about the program); that the local step's mask points are uniform
  on the curve group (`randomPoint`, the map (r, t) ↦ r·B + t·T₈; `proofs/`
  `curve_hinted_Z_uniform` assumes it); `decode (encode P) = some P` on curve points (liveness of
  decoding; tested against curve25519-dalek, not proved). → **S11 follow-up**.
* **P-GHASH**: (a) for the doubling schedule (`s12_ghash_shared_extend`, the kernels' resharing
  `s12_ghash_keyShare_shared`, `s12_ghash_round_shared`), (b) (`s12_ghash_halves_xor`), (c) for the
  Lean code (`s12_tls_seal_is_record`, `s12_tls_check_accepts`), (d) (`s12_ghash_keyShare_hides`,
  `s12_ghash_multiply_hides`, the views `s12_ghash_keyShare_viewD_B`, `s12_ghash_round_viewD_B`,
  `s12_ghash_keyShare_disclosure_A`) proved in section 7d (S12). Second S12 pass (section 7d
  continued): (a) over a whole `ensure` through `jointRun` (`s12_ghash_ensure_shared`: the key share,
  the local square and the doubling rounds, each a returning joint run of the scripts), (d) for a
  round with A honest at value level against any adversary (`s12_ghash_round_disclosure_A`), (e) for
  the scripts (`s12_ghash_seal_deviation_rejected`, `s12_ghash_check_deviation`), `roundScript`'s WF
  (`s12_ghash_round_wf`). Open: that the controller-side runner (`Flows/Runner.lean`, section 7i:
  its pure core is proved against the model) executes `TlsBackend.ensure` as written (`EnsureRuns`
  is the model of its steps; the IO glue is unverified, F17).
* `commit_open_sound`: proved for every S10 commit-then-open site (all are `Random.joint`; section
  7b, `s10_commit_open_sound`). The S11 point exchanges (`Curve.pointExchange`, same frame
  `tag ‖ party ‖ nonce ‖ value`): the gate only (`Curve.pointExchange_gate`); the model statement
  as `Random.commit_open_sound` is OPEN (S11 follow-up).
* **P-INV** as a flow (section 7b): T3 against any adversary (only z·m and the zero flag), (a)
  through `jointRun`, the mask's uniformity, (c). The masks are fresh field randomness of both
  parties (never cut-and-choose word masks: a program mask must be marked never).

### Flows and channels
* **T4-x** — composition per flow (CONTACT, UPGRADE, TLS, SEND, RECV, REFRESH, CEREMONY): under
  the ideal model with both parties honest, the flow's result equals its specification.
  → **S9** (CONTACT), **S12** (TLS), **S13** (SEND), **S14** (RECV), **S15** (REFRESH), **S16**
  (UPGRADE, CEREMONY). TLS (S12, section 7d): at the function level (each kernel's output read
  through the script's layout: `s12_tls_seal_is_record`, `s12_tls_check_accepts`,
  `s12_tls_open_event_refines`, `s12_tls_reveal_value`, `s12_tls_verify_value`,
  `s12_tls_openHandshake_value`); since the second S12 pass through `jointRun` for the seal
  (`s12_tls_seal_honest`, the class seal's composition `s12_tls_sealClass_is_record`), the open
  (`s12_tls_open_class`, `s12_tls_open_rejected_run`, the binding `s12_tls_open_binding_honest`) and
  the derive step (`s12_tls_derive_honest`, the agreement word read through `Tls.shapedCircuit`; the
  word itself is S11's, `TlsBackend.KeyAgreement`); value-level T3 against any adversary for the seal
  and the open (`s12_tls_sealCtr_disclosure`, `Tls.tag_disclosure_A`, `s12_tls_open_disclosure_A`,
  `Tls.open_disclosure_rejected`). Open for TLS: the handshake record / Finished / client Finished /
  reveal / update scripts are at the function level (their WF is proved), T3 with B honest for the
  open and the tag (symmetric scripts; not written), and the IO glue `TlsBackend` (F17). SEND (S13, section 7e): at
  the function level, composed with the kernel theorems and WITHOUT the worker-wiring hypotheses
  (`s13_send_accepted`, `s13_requestCtr_value`, `s13_bundleRequestCtr_value`, `s13_request_record`,
  `s13_seal_accepted_value`); T3 (`s13_send_reveal`, `s13_seal_refused_silent`); WF of ops 41, 42 and
  the request's record phase. Section 7e (S13 follow-up): T4-SEND through `jointRun` for one device
  (`s13_seal_joint`, `s13_send_joint`: op 41, op 42, the CTR phase and the tag, both parties the
  same results, the bytes those of `s13_send_accepted`); the devices path's composed headline
  (`s13_devices_accepted`, no wiring hypothesis) and all-or-nothing (`s13_devices_refused_view`);
  the `bundle-seal` slicing (`s13_bundleEnvBytes_eq`, `s13_bundleOut_record_length`); op 41's view
  by value against any adversary (`s13_seal_view`). Open (S13_NOTES.md, gaps S13-1 … S13-13): the
  devices path through `jointRun`; `Table.Inv` for the send's table commit; WF of ops 61 and 62
  and `Wire.Bounded` of op 61 (op 62's: `s13_requestDevicesScript_bounded`); `wired` (S15's); the
  four words are S11's (E4); an official 89-byte text cannot be sent to an unanswered device (the
  run aborts: `s13_bundleOut_record_length`).
* **T6 / ORD-1** restated over the Lean flow: the script-level facts are proved
  (`s13_send_state_order`: the accepted op 41 returns the new state handle, defined by the seal
  kernel's run before the envelope is opened; op 42 on that handle reads exactly the kept record;
  `s13_seal_joint`: on refusal the stored state's value is kept). The session-level ORD-1 theorem
  (P4: the session's Seal/StoreAck/Send events) is unchanged since the backend keeps the legacy
  results and call order; its restatement over the Lean flow waits for the controller switch.
* **T4-RECV** (S14, section 7f): at the
  function level (`s14_accept_certificate`, `s14_text`, `s14_record`); open: through `jointRun`
  (needs S10's conversions' and S11's agreements' run-level specifications and the receive kernels
  as model circuits with word inputs), the whole flows' WF, a value-level T3 for every release of a
  run (S14_NOTES.md, F22-F27).
* **T4-REFRESH** (S15, section 7g):
  the parse in the model (`s15_slot_one_source`, `s15_parse_device`, `s15_parse_or_refuse`), the
  encapsulation's wiring at the function level (`s15_kem_pipeline`, `s15_kem_accept`,
  `s15_kem_invalid`, hyp. `KemWidths`), the first message's `wired` (`s15_first_wired`, hyp.
  `SessionWidths` and the send's binding). Open: the KEM block and the session step through
  `runPlain`/`jointRun`, the signature verification (S11's `check`), the agreements (S11's
  `agree`), WF of the fetch, establishment and scratch-seal scripts (tested by the vectors), and
  `opCommit`'s preservation of `Table.Inv` (S15_NOTES.md, gaps).
* **ORD-2** — a refresh's scratch becomes the contact's state only by `opCommit`
  (`s15_ord2_commit`, `s15_ord2_establish`, `s15_ord2_drop`: S15, section 7g, script level); that
  the controllers call it only after both saw the nodes acknowledge the sealed scratch is the
  session-level ORD-2 (P4, `Session/RefreshProofs.lean` on the main line), unchanged by the switch.
* **The joins** (section 7h, `scripts-stack`): the S12–S15 curve parameters instantiated with S11's
  flows; proved: the composed kinds, S15's `CurveOps.Reveals` (discharged), S15's `first_wired`
  bindings from S13's `bundle-seal` layout. Open: the joined flows through `jointRun` (values: S11's
  `agree`/`offsetStep` honest runs are themselves open); the handle-content facts `hcert`/`hpend`
  of `join_first_wired`; the IO glue (`JoinBackend`, `RefreshBackend`, `Select`, unverified, as
  every backend); `_wf` of the joined scripts (their id blocks are counted, not proved). J1 (one
  mask slot for op 50's two agreements) is RESOLVED: section 7i (`j1_openFirst_reads_once`,
  `j1_session_reads_once`, `j1_refreshOps_reads_once`). J8 (the identity scalar's swap bits are
  field handles, not coins) is RESOLVED: section 7j (`j8_jobBits_swaps`, `j8_receiveAgree_spares`).
* **The contact set** (section 7j): ops 47, 46, 32 as scripts (`s16_*`), op 66's glue (`f32_*`),
  the sender key (`j12_*`), slot release (`j13_release`), the selection (`select_contactSet`).
  Open: the joined scripts' `_wf` (op 66's glue: `f32_commit_inv` assumes what the run leaves);
  `prepareOneG`, `senderPublicG` through `jointRun` (values: S11's `offsetPrepare` and `agree`
  honest runs, the view kernel's `signalConversationView_spec`); op 32's request through
  `jointRun` (the function-level values `s16_request_*` are proved); the hinted op 66 path (J3).
* **The script runner** (section 7i): its pure core against the model (`runner_drive_model`,
  `runner_drive_bounded`, `runner_nextBatch_fill_only`). Open: the IO loop is `drive`'s steps by
  construction, not by a theorem (an IO function); the fake-pair test
  (`node_worker/tests/lean/RunnerTest.lean`) runs it against the model's shells.
* **T9** — peer messages are public: by type since S5 (`Messages.checkPublic`, section 7-channels;
  `peerMsg_reply_kind`). Open: `PeerMsg.flow` only from `Reveal.lean` (S9: no flow sends an
  own-secret opening to the peer through the controller before the scripts).
* **`Contacts.Loaded E`** (`TlsMpc/Node/Flows/ContactsBase.lean`), the trust behind every
  contact/account entry of section 7a that takes `hE : Loaded E`: the environment's circuit named
  `contact-key` is `kernelCircuit HybridKernel.contactKey 64 keyMarks` (480 output bits, never
  opened), and for every size N from 1 to 16384 `contact-seal N` is
  `kernelCircuit (HybridKernel.contactSeal N) (68 + N) (sealMarks N)` (8N + 128 public bits) and
  `contact-open N` is `kernelCircuit (HybridKernel.contactOpen N) (84 + N) (openMarks N)` (8 public
  bits, then 8N never opened). That is, the pinned circuits the worker loads under those names
  compute their Lean kernels with these open marks: the T2 correspondence for these three kernels.
  Partly discharged by the emitter batch: for a circuit `lowerKernel` produced from the kernel,
  the file the engine loads parses back to that circuit and its layout to the kernel's fields and
  open marks (`kernel_loaded`, `layout_openCode`), and the circuit computes `lowerExpr` of the
  joined outputs. What `Loaded` still assumes: that the cache entry under that name is the
  emitter's output for that kernel (cache/manifest integrity), that the engine's loader parses as
  `parseFlat`/`parseLayout`, and `selection`. → **P3** (rest). Not covered by `Loaded`: the
  `xor-bit` circuit that `Account.opSeal` runs on two credential shares.
* **T12** — skeleton determinism of scripts: proved for the model (section 7a,
  `engine_T12_skeleton_determinism`); T4-UPGRADE for honest parties likewise (`upgrade_honest`).

### Affected by the Mathlib decision (owner, 2026-11-12)
Mathlib may be used by proof-only modules in a separate library that no executable imports. The
Edwards group law (H-GROUP) was a hypothesis; discharged later the same day, see below. This
changes the following items:
* **H-QR** (2 is a non-square mod p; Euler's criterion for p = 2²⁵⁵ − 19) becomes a theorem, so
  **P-HINT(b)** ((r, b) ↦ q·r²·2ᵇ covers F∖{0} four-to-one) loses that hypothesis. → **S11**,
  Mathlib library.
* **Hiding as real probability.** Plan section 7.0 states hiding as a bijection on the honest
  party's randomness; with Mathlib each such statement also gets its distributional form ("the
  adversary's view has the same distribution for any two secrets when ρ is uniform"), derived
  from the bijection. Affected: **P-RAND(b)**, **P-CUT(c)**, **P-PAIR/P-B2F(b)**, **P-W2F(b)**,
  **P-F2W(b)**, **P-BITS(c)**, **P-INV(c)**, **P-GHASH(d)**, **P-HINT(c)**, **T15**, and the
  existing bijection statements restated above: `ceremony_masked_hides`, `ghash_share_hides`,
  `maskedAgreement_mask_hides`, `offsetAgreement_public_key_independent`. `idealCommit` stays a
  hypothesis (a cryptographic assumption, not a Mathlib fact).
* **The cut-and-choose counting bound** (formerly **P7**, optional and "not done"): the
  probability that a bad mask survives the cut and the buckets, against
  `check_parameters_128.py`'s 2⁻¹²⁸ target. → now in scope, Mathlib library; pairs with
  **P-CUT(d)–(f)**.
* **Done in `proofs/` (2026-11-12; index `proofs/TlsMpcProofs/SecurityMathlib.lean`, axioms in
  `proofs/SECURITY_MATHLIB_AXIOMS.txt`):**
  - H-QR and the square-root programs: `sqrtMinusOne_eq_power`, `candidate_fourth_iff`,
    `candidate_sq`, `recipient_check_zero_iff`, `recipient_x_mul_self`, `lift_select`,
    `liftOpen_square_iff`, `lift_fiber_card` (2 preimages per (r, b), not 4), `lift_opened_uniform`,
    `xeddsa_recover_valid_iff`, `xeddsa_recover_x_mul_self`. P-HINT(b) for the script remains (S11).
  - Distributional hiding for `ghash_share_hides`, `ceremony_masked_hides` (same expression, not
    linked by import), P-RAND(b), P-B2F(b), P-W2F(b), P-F2W(b), P-INV(c),
    `maskedAgreement_mask_hides`, P-HINT(c), and `offsetAgreement_public_key_independent`
    (`offset_public_key_independent`, `offset_public_key_uniform`; scalars in ZMod ℓ, H-GROUP as
    "finite commutative group of order ℓ"); several messages: `offset_public_keys_independent`,
    `offset_public_keys_uniform` (k keys jointly uniform on G^k).
  - The deployed offset sampling (P-OFFSET(b), `proofs/TlsMpcProofs/OffsetSampling.lean`):
    τ = (mine XOR peer) mod 2²⁵² is exactly uniform on [0, 2²⁵²) (`deployedOffset_uniform`); keys
    for any two initial scalars within (ℓ − 2²⁵²)/2²⁵² on every event (`deployed_key_close`),
    within (ℓ − 2²⁵²)/ℓ of uniform on G (`deployed_key_close_uniform`); ℓ prime (`prime_order`,
    Pocklington); (ℓ − 2²⁵²)/2²⁵² < 2⁻¹²⁷ (`order_gap_lt`), so `ed25519_key_close`,
    `ed25519_key_close_uniform` (2⁻¹²⁷) and `ed25519_keys_close` (k messages, k·2⁻¹²⁷).
    Hypotheses: `idealCommit`; `P ≠ 0`, `ℓ·P = 0` for the recipient point. The digit recoding is
    now the flow's own `Curve.recode` (section 7c, `s11_recode64`, `s11_stepIns_window`); open:
    the `proofs/` statement that `TlsMpcProofs.Ed25519.recode` equals `Curve.recode` (same equations,
    `Curve.recode_zero` / `recode_succ`; by induction) once `proofs/` imports the S11 modules.
  - Receive: `Unpad.decode` is PKCS#7 unpadding (`unpad_decode_padded`, `unpad_decode_unpadded`,
    `unpad_decode_accepts_iff`). Open: value forms of `varintValue` (widths 2–5) and
    `canonicalRange` (ReceiveFirst's import closure is not compiled into proofs/).
  - Cut-and-choose, for the model: `cut_and_bucket_probability`, `cut_bound_le_bound_one`,
    `*_bound_all_t`, `*_undetected_lt` (every bad set < 2⁻¹²⁸ for 2¹⁹/8, 256/14, 512/13,
    1024/12). The model's hypotheses are theorems about the Lean script `Masks.generate` since S10
    (`s10_generate_sound`: bad set fixed before the challenges, (d), (e), (f); `s10_arrangement`:
    the two challenge permutations are one arrangement of the model's shape); that this
    arrangement is uniform, and the legacy C++ generators, are not covered.
  - H-GROUP (section 7): the group law, the main-package formulas in it, base point of order
    exactly ℓ, the offset and masked-point theorems instantiated
    (`curve_deployed_key_close_uniform`, `base_deployed_key_close_uniform`,
    `curve_hinted_Z_uniform`, `curve_maskedAgreement_mask_hides`), `x25519_spec_scalar_mult`.
  - H-GROUP, chains and Montgomery side (sections 7c–7e): `x25519_u_zero`,
    `x25519_spec_scalar_mult_all`, `x25519_clampedScalar_rfc`, `window_table`, `bitTable_entries`,
    `offsetSum_scalar_mult` (with `recode_offset`), `bitSum_is_x25519`,
    `prepareHinted_initial_point`, `xeddsa_doubleScalar`, `montQ_square_iff`,
    `liftPoint_valid_point`, `liftPoint_invalid_point`. Open: `#E = 8ℓ`, X25519 on the twist.
* Not affected: everything in sections 1–7 above is proved without Mathlib and stays so; the
  executables' import closure must stay Mathlib-free.
-/

end TlsMpc.Security

/-! ## 9. Machine checks

`scripts/check_axioms.py` parses the lines below. Allowed: `propext`, `Classical.choice`,
`Quot.sound` (and `Lean.ofReduceBool` only if a `bv_decide` proof needs it). -/

#print axioms TlsMpc.Security.s13_send_reveal
#print axioms TlsMpc.Security.s13_seal_refused_silent
#print axioms TlsMpc.Security.s13_seal_accepted_value
#print axioms TlsMpc.Security.s13_requestCtr_value
#print axioms TlsMpc.Security.s13_bundleRequestCtr_value
#print axioms TlsMpc.Security.s13_request_record
#print axioms TlsMpc.Security.s13_send_accepted
#print axioms TlsMpc.Security.s13_sealScript_wf
#print axioms TlsMpc.Security.s13_requestScript_wf
#print axioms TlsMpc.Security.s13_requestCtrScript_wf
#print axioms TlsMpc.Security.s13_sealScript_bounded
#print axioms TlsMpc.Security.s13_bundleEnvBytes_eq
#print axioms TlsMpc.Security.s13_bundleOut_record_length
#print axioms TlsMpc.Security.s13_devices_accepted
#print axioms TlsMpc.Security.s13_devices_refused_view
#print axioms TlsMpc.Security.s13_jointRun_pub
#print axioms TlsMpc.Security.s13_withAdv_pub
#print axioms TlsMpc.Security.s13_seal_view
#print axioms TlsMpc.Security.s13_seal_joint
#print axioms TlsMpc.Security.s13_send_joint
#print axioms TlsMpc.Security.s13_send_state_order
#print axioms TlsMpc.Security.s13_requestDevicesScript_bounded
#print axioms TlsMpc.Security.lower_sound
#print axioms TlsMpc.Security.lower_correct
#print axioms TlsMpc.Security.lowerExpr_correct
#print axioms TlsMpc.Security.flat_printWith_render
#print axioms TlsMpc.Security.flat_parse_render
#print axioms TlsMpc.Security.flat_lowerExpr_loaded
#print axioms TlsMpc.Security.layoutText_unchanged
#print axioms TlsMpc.Security.layout_parse
#print axioms TlsMpc.Security.layout_openCode
#print axioms TlsMpc.Security.kernel_loaded
#print axioms TlsMpc.Security.flat_run_eq_eval
#print axioms TlsMpc.Security.joinExpr_correct
#print axioms TlsMpc.Security.kernel_compiled_correct
#print axioms TlsMpc.Security.boolDag_compile_correct
#print axioms TlsMpc.Security.fieldDag_compile_correct
#print axioms TlsMpc.Security.fieldDag_compileAll_correct
#print axioms TlsMpc.Security.aes_encryptCore_compiled
#print axioms TlsMpc.Security.aesSbox_packed_correct
#print axioms TlsMpc.Security.sha256_hash_refines
#print axioms TlsMpc.Security.sha256_hmac_refines
#print axioms TlsMpc.Security.tls_handshakeSecretsFast_correct
#print axioms TlsMpc.Security.tls_applicationSecretsFast_correct
#print axioms TlsMpc.Security.tls_expandLabelFast_correct
#print axioms TlsMpc.Security.gcm_sealCore_compiled
#print axioms TlsMpc.Security.tlsRecord_sealCore_compiled
#print axioms TlsMpc.Security.tlsReceive_openCore_correct
#print axioms TlsMpc.Security.tls_verifyHash_value
#print axioms TlsMpc.Security.xeddsa_recover_correct
#print axioms TlsMpc.Security.xeddsa_check_correct
#print axioms TlsMpc.Security.receive_torsion_correct
#print axioms TlsMpc.Security.x25519Fast_compiled_correct
#print axioms TlsMpc.Security.x25519_compiled_compute_correct
#print axioms TlsMpc.Security.edwards_offsetSum_eval
#print axioms TlsMpc.Security.edwardsHinted_entries_sound
#print axioms TlsMpc.Security.edwardsHinted_compiled_correct
#print axioms TlsMpc.Security.pqxdh_deriveCore_specification
#print axioms TlsMpc.Security.symmetric_deriveFast_correct
#print axioms TlsMpc.Security.dhRatchet_materialFast_correct
#print axioms TlsMpc.Security.spqrChain_materialFast_correct
#print axioms TlsMpc.Security.establish_keys_specification
#print axioms TlsMpc.Security.xeddsa_reduce_bytes_spec
#print axioms TlsMpc.Security.messageMac_verifyMask_value
#print axioms TlsMpc.Security.xeddsa_scalarMask_spec
#print axioms TlsMpc.Security.relayUpgrade_request_compiled
#print axioms TlsMpc.Security.tlsUpdate_spec
#print axioms TlsMpc.Security.tlsSealCtr_spec
#print axioms TlsMpc.Security.gcmTag_spec
#print axioms TlsMpc.Security.gcmCheck_spec
#print axioms TlsMpc.Security.gcmKeyShare_spec
#print axioms TlsMpc.Security.gcmMultiply_spec
#print axioms TlsMpc.Security.contactKey_spec
#print axioms TlsMpc.Security.contactSeal_spec
#print axioms TlsMpc.Security.contactOpen_spec
#print axioms TlsMpc.Security.recordClass_open_padded
#print axioms TlsMpc.Security.recordClass_sealCiphertext_padded
#print axioms TlsMpc.Security.typedOpen_class_fields
#print axioms TlsMpc.Security.typedOpen_frame_fields
#print axioms TlsMpc.Security.typedOpen_typed_pair_refines
#print axioms TlsMpc.Security.kemHash_spec
#print axioms TlsMpc.Security.kemNtt_spec
#print axioms TlsMpc.Security.kemMatrix_spec
#print axioms TlsMpc.Security.kemU_spec
#print axioms TlsMpc.Security.kemV_spec
#print axioms TlsMpc.Security.kemFinish_spec
#print axioms TlsMpc.Security.kemSample_spec
#print axioms TlsMpc.Security.receive_envelopePoint_spec
#print axioms TlsMpc.Security.receive_unsealStatic_spec
#print axioms TlsMpc.Security.receive_unsealMessage_spec
#print axioms TlsMpc.Security.receive_contentShape_spec
#print axioms TlsMpc.Security.receive_content_spec
#print axioms TlsMpc.Security.receive_certificate_spec
#print axioms TlsMpc.Security.receive_certificateVerified_spec
#print axioms TlsMpc.Security.receive_prekeyShape_spec
#print axioms TlsMpc.Security.receive_prekeyOpen_spec
#print axioms TlsMpc.Security.receive_signalShape_spec
#print axioms TlsMpc.Security.receive_session_spec
#print axioms TlsMpc.Security.receive_text_spec
#print axioms TlsMpc.Security.receive_accessKey_spec
#print axioms TlsMpc.Security.receive_keys_specification
#print axioms TlsMpc.Security.establishChallenges_spec
#print axioms TlsMpc.Security.establishVerified_spec
#print axioms TlsMpc.Security.establishSession_spec
#print axioms TlsMpc.Security.establishSeal_spec
#print axioms TlsMpc.Security.bundleShape_spec
#print axioms TlsMpc.Security.bundleRebind_spec
#print axioms TlsMpc.Security.bundleSeal_spec
#print axioms TlsMpc.Security.bundleDevice_spec
#print axioms TlsMpc.Security.bundleBind_spec
#print axioms TlsMpc.Security.ceremonySecrets_spec
#print axioms TlsMpc.Security.registerPlaintext_spec
#print axioms TlsMpc.Security.signalRequestCtr_spec
#print axioms TlsMpc.Security.signalRequestCtr_rejects
#print axioms TlsMpc.Security.bundleFetchCtr_spec
#print axioms TlsMpc.Security.bundleFetchCtr_rejects
#print axioms TlsMpc.Security.bundleRequestCtr_spec
#print axioms TlsMpc.Security.bundleRequestCtr_rejects
#print axioms TlsMpc.Security.insertSlots_inside_zero
#print axioms TlsMpc.Security.signalSealBuilt_spec
#print axioms TlsMpc.Security.sealCore_value
#print axioms TlsMpc.Security.boundSeal_value
#print axioms TlsMpc.Security.signalSeal_value
#print axioms TlsMpc.Security.sealValue_accepted
#print axioms TlsMpc.Security.signalSealBuilt_rejects
#print axioms TlsMpc.Security.tlsDerive_spec
#print axioms TlsMpc.Security.tlsVerifyFinished_spec
#print axioms TlsMpc.Security.tlsFinish_spec
#print axioms TlsMpc.Security.tlsOpenHandshake_spec
#print axioms TlsMpc.Security.tlsOpenHandshake_application_zero
#print axioms TlsMpc.Security.tlsRevealMasked_value
#print axioms TlsMpc.Security.signalUpgrade_spec
#print axioms TlsMpc.Security.signalUpgradeShared_spec
#print axioms TlsMpc.Security.signalConversationView_spec
#print axioms TlsMpc.Security.signalWidths_spec
#print axioms TlsMpc.Security.tlsParserInitial_spec
#print axioms TlsMpc.Security.wsInitial_spec
#print axioms TlsMpc.Security.establishPoints_spec
#print axioms TlsMpc.Security.bundleItem_spec
#print axioms TlsMpc.Security.bundleItem_rejects
#print axioms TlsMpc.Security.requestBuild_ok
#print axioms TlsMpc.Security.requestInsertSlots_offsets
#print axioms TlsMpc.Security.signalRequestCtr_built
#print axioms TlsMpc.Security.bundleFetchCtr_built
#print axioms TlsMpc.Security.bundleRequestCtr_built
#print axioms TlsMpc.Security.serverReceives_accepted
#print axioms TlsMpc.Security.establishSeal_preKeyMessage_value
#print axioms TlsMpc.Security.establishSeal_sealedSender_value
#print axioms TlsMpc.Security.establishSeal_sealMessage_value
#print axioms TlsMpc.Security.establishSeal_bundleSeal_value
#print axioms TlsMpc.Security.establishSeal_bundleSeal_accepted
#print axioms TlsMpc.Security.establishSeal_varint5_decode
#print axioms TlsMpc.Security.establishSeal_varint_decode
#print axioms TlsMpc.Security.establishFirst_keys_value
#print axioms TlsMpc.Security.establishFirst_firstMessage_envelope
#print axioms TlsMpc.Security.establishDevices_openedEnvelopes_reference
#print axioms TlsMpc.Security.establishDevices_openedEnvelopes_first
#print axioms TlsMpc.Security.establishRequest_serverReceives_refresh
#print axioms TlsMpc.Security.establishRequest_serverReceives_refresh_first
#print axioms TlsMpc.Security.bundleDevice_local
#print axioms TlsMpc.Security.bundleItem_whole
#print axioms TlsMpc.Security.bundleSlot_whole
#print axioms TlsMpc.Security.slotValid_pad
#print axioms TlsMpc.Security.deviceSlots_splice
#print axioms TlsMpc.Security.spliced_layout
#print axioms TlsMpc.Security.bundleSlot_device
#print axioms TlsMpc.Security.bundleSlot_eq_bundleItem
#print axioms TlsMpc.Security.device_unique
#print axioms TlsMpc.Security.bundleSlot_wrong_counts
#print axioms TlsMpc.Security.bundleSlot_parses_or_refuses
#print axioms TlsMpc.Security.bundleSlot_any_widths
#print axioms TlsMpc.Security.bundleSlot_slotValid_width
#print axioms TlsMpc.Security.bundleSlot_inconsistent_width_refused
#print axioms TlsMpc.Security.bundleSlot_zero_padding_ambiguous
#print axioms TlsMpc.Security.receiveAccept_session_status_iff
#print axioms TlsMpc.Security.receiveAccept_session_accept_outputs
#print axioms TlsMpc.Security.receiveAccept_session_status_cases
#print axioms TlsMpc.Security.receiveAccept_session_accept_certificate
#print axioms TlsMpc.Security.receiveAccept_text_zero_unless_accepted
#print axioms TlsMpc.Security.receiveAccept_receiveText_gated
#print axioms TlsMpc.Security.receiveAccept_certificateVerified_iff
#print axioms TlsMpc.Security.receiveAccept_certificate_valid
#print axioms TlsMpc.Security.receiveAccept_unsealStatic_valid_iff
#print axioms TlsMpc.Security.receiveAccept_unsealStatic_outputs
#print axioms TlsMpc.Security.receiveAccept_unsealMessage_valid_iff
#print axioms TlsMpc.Security.receiveAccept_unsealMessage_outputs
#print axioms TlsMpc.Security.receiveAccept_prekeyOpen_valid_iff
#print axioms TlsMpc.Security.receiveAccept_prekeyOpen_outputs
#print axioms TlsMpc.Security.receiveAccept_contentShape_rejects
#print axioms TlsMpc.Security.receiveAccept_prekeyShape_rejects
#print axioms TlsMpc.Security.receiveAccept_signalShape_rejects
#print axioms TlsMpc.Security.receiveAccept_atMost_value
#print axioms TlsMpc.Security.receiveAccept_opened_unsealStatic
#print axioms TlsMpc.Security.receiveAccept_opened_unsealMessage
#print axioms TlsMpc.Security.receiveAccept_opened_contentShape
#print axioms TlsMpc.Security.receiveAccept_opened_content
#print axioms TlsMpc.Security.receiveAccept_opened_certificate
#print axioms TlsMpc.Security.receiveAccept_opened_certificateVerified
#print axioms TlsMpc.Security.receiveAccept_opened_prekeyShape
#print axioms TlsMpc.Security.receiveAccept_opened_prekeyOpen
#print axioms TlsMpc.Security.receiveAccept_opened_signalShape
#print axioms TlsMpc.Security.receiveAccept_opened_session
#print axioms TlsMpc.Security.receiveAccept_opened_text
#print axioms TlsMpc.Security.receiveAccept_opened_accessKey
#print axioms TlsMpc.Security.receiveAccept_opened_envelopePoint
#print axioms TlsMpc.Security.receiveAcceptText_text_eq
#print axioms TlsMpc.Security.receiveAcceptText_text_status
#print axioms TlsMpc.Security.receiveAcceptText_text_rejects
#print axioms TlsMpc.Security.receiveAcceptText_text_accepted
#print axioms TlsMpc.Security.receiveAcceptText_text_of_reference
#print axioms TlsMpc.Security.receiveAcceptText_text_reference
#print axioms TlsMpc.Security.receiveAcceptText_overlongBody_refused
#print axioms TlsMpc.Security.receiveAcceptText_overlongBody_reference
#print axioms TlsMpc.Security.receiveAcceptText_accepted_iff_reference
#print axioms TlsMpc.Security.receiveAcceptText_text_status_iff_reference
#print axioms TlsMpc.Security.receiveAcceptText_text_accepted_reference
#print axioms TlsMpc.Security.receiveAccessKey_gap_unique
#print axioms TlsMpc.Security.receiveAccessKey_withAccessKey_status
#print axioms TlsMpc.Security.receiveAccessKey_withAccessKey_accepted
#print axioms TlsMpc.Security.receiveAccessKey_withAccessKey_rejected
#print axioms TlsMpc.Security.widthFlags_value
#print axioms TlsMpc.Security.signalWidths_value
#print axioms TlsMpc.Security.slotUuid_eq
#print axioms TlsMpc.Security.slotUuid_parse
#print axioms TlsMpc.Security.slotBase64_eq
#print axioms TlsMpc.Security.slotBase64_decode
#print axioms TlsMpc.Security.slotDecimal_value
#print axioms TlsMpc.Security.slotDecimal_parse
#print axioms TlsMpc.Security.chainSend_sealCore_concrete_correct
#print axioms TlsMpc.Security.spqrSend_sealCore_concrete_correct
#print axioms TlsMpc.Security.typedOpen_gated
#print axioms TlsMpc.Security.typedOpen_rejected_parse
#print axioms TlsMpc.Security.typedOpen_rejected_independent
#print axioms TlsMpc.Security.typedOpen_gating
#print axioms TlsMpc.Security.typedOpen_handshakeBit_cases
#print axioms TlsMpc.Security.typedOpen_rejected_parse_length
#print axioms TlsMpc.Security.tlsOpenApplication_event_private
#print axioms TlsMpc.Security.postHandshake_application_event_independent
#print axioms TlsMpc.Security.postHandshake_process_event_independent
#print axioms TlsMpc.Security.postHandshake_reject_unauthenticated
#print axioms TlsMpc.Security.postHandshake_reject_failed
#print axioms TlsMpc.Security.publicHandshake_gate_value
#print axioms TlsMpc.Security.publicHandshake_application_not_released
#print axioms TlsMpc.Security.providerGate_gate_value
#print axioms TlsMpc.Security.tlsReceive_bad_header_zero
#print axioms TlsMpc.Security.tlsReceive_bad_tag_zero
#print axioms TlsMpc.Security.receive_released_zero
#print axioms TlsMpc.Security.receive_unsealStatic_rejects
#print axioms TlsMpc.Security.receive_unsealMessage_rejects
#print axioms TlsMpc.Security.receive_content_rejects
#print axioms TlsMpc.Security.receive_prekeyOpen_rejects
#print axioms TlsMpc.Security.receive_session_rejects
#print axioms TlsMpc.Security.bundle_rebind_rejects
#print axioms TlsMpc.Security.bundle_bind_rejects
#print axioms TlsMpc.Security.establish_rejects
#print axioms TlsMpc.Security.mlkem_finish_rejects
#print axioms TlsMpc.Security.mlkem_finish_accepts
#print axioms TlsMpc.Security.contactOpen_rejected
#print axioms TlsMpc.Security.contactOpen_accepted_iff
#print axioms TlsMpc.Security.openResult_finish_reject_auth
#print axioms TlsMpc.Security.openResult_finish_reject_padding
#print axioms TlsMpc.Security.bundle_structural_value
#print axioms TlsMpc.Security.bundle_shape_length
#print axioms TlsMpc.Security.bundleItem_shape_padded
#print axioms TlsMpc.Security.ceremony_masked_hides
#print axioms TlsMpc.Security.preKeyValidation_finish_spec
#print axioms TlsMpc.Security.controller_fast_eq
#print axioms TlsMpc.Security.passOver_frame_step_room
#print axioms TlsMpc.Security.passOver_frameRoom_one
#print axioms TlsMpc.Security.passOver_frameBulk_succ
#print axioms TlsMpc.Security.passOver_control_idle
#print axioms TlsMpc.Security.passOver_response_step_room
#print axioms TlsMpc.Security.passOver_responseRoom_one
#print axioms TlsMpc.Security.passOver_responseBulk_succ
#print axioms TlsMpc.Security.passOne_bulk
#print axioms TlsMpc.Security.passRun_bulk
#print axioms TlsMpc.Security.passRun_add
#print axioms TlsMpc.Security.word64_fast_eq
#print axioms TlsMpc.Security.varint_decodeCore_spec
#print axioms TlsMpc.Security.notification_buildPublic_spec
#print axioms TlsMpc.Security.notification_buildPublicOfficial_spec
#print axioms TlsMpc.Security.notification_buildPublic_short
#print axioms TlsMpc.Security.notification_firstFit_spec
#print axioms TlsMpc.Security.bundle_layout_sound
#print axioms TlsMpc.Security.wsFrame_frame_extent
#print axioms TlsMpc.Security.wsFrame_frames_extent
#print axioms TlsMpc.Security.wsFrame_controller_run
#print axioms TlsMpc.Security.wsFrame_runByte_active
#print axioms TlsMpc.Security.wsFrame_reject_second
#print axioms TlsMpc.Security.wsFrame_reject_sticky
#print axioms TlsMpc.Security.wsFrame_reject_noncanonical
#print axioms TlsMpc.Security.wsFrame_reject_capacity16
#print axioms TlsMpc.Security.wsControl_control_frame
#print axioms TlsMpc.Security.wsControl_run_stateBytes
#print axioms TlsMpc.Security.wsControl_encode_frame
#print axioms TlsMpc.Security.wsControl_replies_fresh_masks
#print axioms TlsMpc.Security.wsControl_replies_missing_mask
#print axioms TlsMpc.Security.tlsRecord_receive_one
#print axioms TlsMpc.Security.tlsRecord_records_sound
#print axioms TlsMpc.Security.tlsRecord_records_complete
#print axioms TlsMpc.Security.tlsRecord_records_overflow
#print axioms TlsMpc.Security.wsAccept_accept_spec
#print axioms TlsMpc.Security.wsAccept_rfc6455_accept
#print axioms TlsMpc.Security.wsAccept_sha1_abc
#print axioms TlsMpc.Security.clock_agreed_within
#print axioms TlsMpc.Security.clock_agree_symm
#print axioms TlsMpc.Security.t8_sendMessage_reference
#print axioms TlsMpc.Security.t8_fetchMessage_reference
#print axioms TlsMpc.Security.t8_devicesMessage_reference
#print axioms TlsMpc.Security.t8_build_reference
#print axioms TlsMpc.Security.t8_buildFetch_reference
#print axioms TlsMpc.Security.t8_buildDevices_reference
#print axioms TlsMpc.Security.t8_decode_clientFrame
#print axioms TlsMpc.Security.t8_clientFrame_reference
#print axioms TlsMpc.Security.t8_ping_decode
#print axioms TlsMpc.Security.t8_close_reference
#print axioms TlsMpc.Security.t8_close_decode
#print axioms TlsMpc.Security.t8_keepalive_reference
#print axioms TlsMpc.Security.t8_keepalive_decode
#print axioms TlsMpc.Security.t8_reply_reference
#print axioms TlsMpc.Security.t8_reply_decode
#print axioms TlsMpc.Security.t8_build_public
#print axioms TlsMpc.Security.t8_buildFetch_public
#print axioms TlsMpc.Security.t8_buildDevices_public
#print axioms TlsMpc.Security.t8_build_two_contacts
#print axioms TlsMpc.Security.t8_build_layout
#print axioms TlsMpc.Security.t8_buildFetch_layout
#print axioms TlsMpc.Security.t8_buildDevices_layout
#print axioms TlsMpc.Security.t8_signalRequestCtr_reference
#print axioms TlsMpc.Security.t8_bundleFetchCtr_reference
#print axioms TlsMpc.Security.t8_bundleRequestCtr_reference
#print axioms TlsMpc.Security.kemc_pipeline_valid_accept
#print axioms TlsMpc.Security.kemc_pipeline_valid_reject
#print axioms TlsMpc.Security.kemc_pipeline_invalid
#print axioms TlsMpc.Security.kemc_kernels_compose
#print axioms TlsMpc.Security.engine_T12_skeleton_determinism
#print axioms TlsMpc.Security.engine_trace_eq_skeletons
#print axioms TlsMpc.Security.engine_view_labels_H
#print axioms TlsMpc.Security.engine_view_labels_D
#print axioms TlsMpc.Security.engine_honest_replay
#print axioms TlsMpc.Security.engine_decodeBatch_encodeBatch
#print axioms TlsMpc.Security.engine_skeletonBytes_inj
#print axioms TlsMpc.Security.engine_check_label
#print axioms TlsMpc.Security.engine_check_program
#print axioms TlsMpc.Security.engine_check_program_openable
#print axioms TlsMpc.Security.engine_idealStep_program
#print axioms TlsMpc.Security.engine_runProgram_lengths
#print axioms TlsMpc.Security.fieldDagV3_parse_render
#print axioms TlsMpc.Security.fieldDagV3_render_parse
#print axioms TlsMpc.Security.fieldDagV3_eval_ofArtifact
#print axioms TlsMpc.Security.fieldDagV3_eval_ofArtifact_some
#print axioms TlsMpc.Security.fieldDagV3_eval_compileAll
#print axioms TlsMpc.Security.fieldDagV3_ofArtifact_masksOk
#print axioms TlsMpc.Security.fieldDagV3_parse_masksOk
#print axioms TlsMpc.Security.fieldDagV3_masksOk_once
#print axioms TlsMpc.Security.fieldDagV3_masked_div
#print axioms TlsMpc.Security.fieldDagV3_opening_zero_iff
#print axioms TlsMpc.Security.fieldDagV3_opening_bijective
#print axioms TlsMpc.Security.fieldDagV3_ofArtifact_declares
#print axioms TlsMpc.Security.fieldDagV3_quotient_checks
#print axioms TlsMpc.Security.fieldDagV3_quotient_spec
#print axioms TlsMpc.Security.fieldProgramsV3_decl_checks
#print axioms TlsMpc.Security.fieldProgramsV3_decl_values
#print axioms TlsMpc.Security.fieldProgramsV3_bitCheck
#print axioms TlsMpc.Security.prand_a_honest
#print axioms TlsMpc.Security.prand_disclosure
#print axioms TlsMpc.Security.prand_commit_before_open
#print axioms TlsMpc.Security.prand_c_copy_aborts
#print axioms TlsMpc.Security.prand_b_ideal
#print axioms TlsMpc.Security.upgrade_honest
#print axioms TlsMpc.Security.contacts_keyScript_wf
#print axioms TlsMpc.Security.contacts_sealScript_wf
#print axioms TlsMpc.Security.contacts_openScript_wf
#print axioms TlsMpc.Security.contacts_key_disclosure
#print axioms TlsMpc.Security.contacts_seal_disclosure
#print axioms TlsMpc.Security.contacts_open_disclosure
#print axioms TlsMpc.Security.contacts_open_released_byte
#print axioms TlsMpc.Security.contactsTable_opKey_disclosure
#print axioms TlsMpc.Security.contactsTable_opSeal_disclosure
#print axioms TlsMpc.Security.contactsTable_opOpen_disclosure
#print axioms TlsMpc.Security.contactsTable_opEvict_disclosure
#print axioms TlsMpc.Security.contactsTable_opAssign_disclosure
#print axioms TlsMpc.Security.contactsTable_opEvict_wf
#print axioms TlsMpc.Security.account_accountKey_disclosure
#print axioms TlsMpc.Security.account_accountSeal_disclosure
#print axioms TlsMpc.Security.account_opSeal_disclosure_stored
#print axioms TlsMpc.Security.account_opSeal_disclosure_shares
#print axioms TlsMpc.Security.contacts_key_honest
#print axioms TlsMpc.Security.contacts_seal_honest
#print axioms TlsMpc.Security.contacts_open_honest
#print axioms TlsMpc.Security.contacts_open_after_seal
#print axioms TlsMpc.Security.contacts_key_seal_open
#print axioms TlsMpc.Security.account_accountKey_honest
#print axioms TlsMpc.Security.contactsWrite_write_fresh
#print axioms TlsMpc.Security.contactsWrite_used_nodup
#print axioms TlsMpc.Security.engine_withAdv_bind
#print axioms TlsMpc.Security.engine_jointRun_bind
#print axioms TlsMpc.Security.engine_skeletonBytes_ne_unusable
#print axioms TlsMpc.Security.engine_unusable_rejected_by_both
#print axioms TlsMpc.Security.engine_shellPair_unusable
#print axioms TlsMpc.Security.engine_counters_blocksB_disjoint
#print axioms TlsMpc.Security.contactsWrite_write_disclosure
#print axioms TlsMpc.Security.contactsWrite_write_honest
#print axioms TlsMpc.Security.contactsWrite_writeScript_wfp
#print axioms TlsMpc.Security.contactsTable_inv_empty
#print axioms TlsMpc.Security.contactsTable_opKey_inv
#print axioms TlsMpc.Security.contactsTable_opSeal_inv
#print axioms TlsMpc.Security.contactsTable_opOpen_inv
#print axioms TlsMpc.Security.contactsTable_opEvict_inv
#print axioms TlsMpc.Security.contactsTable_opAssign_inv
#print axioms TlsMpc.Security.contactsWrite_opWrite_inv
#print axioms TlsMpc.Security.contactsWrite_opWrite_disclosure
#print axioms TlsMpc.Security.account_sealStep_eq
#print axioms TlsMpc.Security.engine_label_ofKind_inj
#print axioms TlsMpc.Security.engine_label_all_distinct
#print axioms TlsMpc.Security.engine_label_all_nonzero
#print axioms TlsMpc.Security.engine_viewD_kinds
#print axioms TlsMpc.Security.engine_viewH_kinds
#print axioms TlsMpc.Security.registry_declared_registered
#print axioms TlsMpc.Security.registry_script_flows_reveal
#print axioms TlsMpc.Security.registry_viewD_registered
#print axioms TlsMpc.Security.flows_joint_viewD_kinds
#print axioms TlsMpc.Security.flows_publicUpgrade_viewD_kinds
#print axioms TlsMpc.Security.flows_seal_viewD_kinds
#print axioms TlsMpc.Security.flows_open_viewD_kinds
#print axioms TlsMpc.Security.flows_key_viewD_kinds
#print axioms TlsMpc.Security.flows_write_viewD_kinds
#print axioms TlsMpc.Security.flows_opSeal_viewD_kinds
#print axioms TlsMpc.Security.flows_opOpen_viewD_kinds
#print axioms TlsMpc.Security.flows_account_opSeal_viewD_kinds
#print axioms TlsMpc.Security.engine_nextBatch_admitted
#print axioms TlsMpc.Security.engine_nextBatch_ends
#print axioms TlsMpc.Security.engine_fill_bounded
#print axioms TlsMpc.Security.engine_nextBatch_bounded
#print axioms TlsMpc.Security.contact_round_trip
#print axioms TlsMpc.Security.chainSend_selectState_accept
#print axioms TlsMpc.Security.chainSend_selectState_reject
#print axioms TlsMpc.Security.chainSend_acceptedMask_value
#print axioms TlsMpc.Security.spqrSend_acceptedMask_value
#print axioms TlsMpc.Security.spqrSend_prepare_concrete_correct
#print axioms TlsMpc.Security.chainSend_reject_preserves_state
#print axioms TlsMpc.Security.tlsPolicy_application_reservation
#print axioms TlsMpc.Security.tlsPolicy_consecutive_application_distinct
#print axioms TlsMpc.Security.tlsPolicy_update_uses_old_epoch
#print axioms TlsMpc.Security.tlsPolicy_pending_blocks_application
#print axioms TlsMpc.Security.tlsPolicy_aborted_blocks
#print axioms TlsMpc.Security.tlsPolicy_receive_reservation
#print axioms TlsMpc.Security.wordMask_modAddCircuit_val
#print axioms TlsMpc.Security.wordMask_intoField_val
#print axioms TlsMpc.Security.wordMask_modAdd_val
#print axioms TlsMpc.Security.wordMask_belowP_eval
#print axioms TlsMpc.Security.wordMask_atLeast32_eval
#print axioms TlsMpc.Security.wordMask_into_field_roundtrip
#print axioms TlsMpc.Security.wordMask_from_field_roundtrip
#print axioms TlsMpc.Security.swapBits_eval
#print axioms TlsMpc.Security.swapBits_shares
#print axioms TlsMpc.Security.fieldBits_bitCheck_bit
#print axioms TlsMpc.Security.fieldBits_bitXor_bits
#print axioms TlsMpc.Security.fieldBits_recompose_eval
#print axioms TlsMpc.Security.fieldBits_maskPair_eval
#print axioms TlsMpc.Security.edwards_onCurve_eval
#print axioms TlsMpc.Security.edwards_addU_eval
#print axioms TlsMpc.Security.x25519Fast_spec_eq_quotient
#print axioms TlsMpc.Security.edwardsHinted_prepareTable_sound
#print axioms TlsMpc.Security.gcmKeyShare_reshare
#print axioms TlsMpc.Security.gcmMultiply_reshare
#print axioms TlsMpc.Security.sealCtr_with_tag_is_seal
#print axioms TlsMpc.Security.gcm_shared_halves_are_ghash
#print axioms TlsMpc.Security.gcm_scheduled_halves_are_ghash
#print axioms TlsMpc.Security.ghash_share_hides
#print axioms TlsMpc.Security.ghash_localTag_shares
#print axioms TlsMpc.Security.ghash_accept_unique_pad
#print axioms TlsMpc.Security.ghash_genuine_rejected
#print axioms TlsMpc.Security.ghash_honest_accepts
#print axioms TlsMpc.Security.ghash_halves_are_ghash
#print axioms TlsMpc.Security.ghash_powers_additive
#print axioms TlsMpc.Security.ghash_square_additive
#print axioms TlsMpc.Security.maskedAgreement_correct
#print axioms TlsMpc.Security.maskedAgreement_mask_hides
#print axioms TlsMpc.Security.maskedAgreement_guess_attack
#print axioms TlsMpc.Security.offsetAgreement_public_key_correct
#print axioms TlsMpc.Security.offsetAgreement_correct
#print axioms TlsMpc.Security.offsetAgreement_table_sum_correct
#print axioms TlsMpc.Security.offsetAgreement_public_key_independent
#print axioms TlsMpc.Security.offsetAgreement_candidate_needs_initial
#print axioms TlsMpc.Security.tlsClient_accepted_session_authenticated

#print axioms TlsMpc.Security.s10_pchal_permutation
#print axioms TlsMpc.Security.s10_pchal_honest
#print axioms TlsMpc.Security.s10_pchal_seed_injective
#print axioms TlsMpc.Security.s10_commit_open_sound
#print axioms TlsMpc.Security.s10_modAdd_exact
#print axioms TlsMpc.Security.s10_pcut_d_cut
#print axioms TlsMpc.Security.s10_pcut_d_run
#print axioms TlsMpc.Security.s10_pcut_b_cut
#print axioms TlsMpc.Security.s10_pcut_b_disjoint
#print axioms TlsMpc.Security.s10_pcut_e_bucket
#print axioms TlsMpc.Security.s10_pcut_e_mixed
#print axioms TlsMpc.Security.s10_pcut_e_run
#print axioms TlsMpc.Security.s10_pcut_f_flags
#print axioms TlsMpc.Security.s10_pcut_g_bitblock
#print axioms TlsMpc.Security.s10_pcut_a_mask
#print axioms TlsMpc.Security.s10_pcut_c_core
#print axioms TlsMpc.Security.s10_pcut_h_takes
#print axioms TlsMpc.Security.s10_pw2f_honest
#print axioms TlsMpc.Security.s10_pw2f_disclosure
#print axioms TlsMpc.Security.s10_pw2f_hides
#print axioms TlsMpc.Security.s10_pf2w_honest
#print axioms TlsMpc.Security.s10_pf2w_disclosure
#print axioms TlsMpc.Security.s10_pf2w_hides
#print axioms TlsMpc.Security.s10_pb2f
#print axioms TlsMpc.Security.s10_pb2f_disclosure
#print axioms TlsMpc.Security.s10_pbits_checks
#print axioms TlsMpc.Security.s10_pbits_xor
#print axioms TlsMpc.Security.s10_pinv_disclosure
#print axioms TlsMpc.Security.s10_pinv_honest
#print axioms TlsMpc.Security.s10_account_open_kinds
#print axioms TlsMpc.Security.s10_swapBits_spec
#print axioms TlsMpc.Security.s10_flows_reveal
#print axioms TlsMpc.Security.s10_challenge_wf
#print axioms TlsMpc.Security.s10_quotient_wf
#print axioms TlsMpc.Security.s10_pb2f_honest
#print axioms TlsMpc.Security.s10_pbits_run
#print axioms TlsMpc.Security.s10_pbits_honest
#print axioms TlsMpc.Security.s10_pcut_c_agree
#print axioms TlsMpc.Security.s10_generate_hides
#print axioms TlsMpc.Security.s10_reRand_bijection
#print axioms TlsMpc.Security.s10_moveRef
#print axioms TlsMpc.Security.s10_moveRef_reach
#print axioms TlsMpc.Security.s10_pcut_fg_run
#print axioms TlsMpc.Security.s10_mask_consistent
#print axioms TlsMpc.Security.s10_pcut_a_run
#print axioms TlsMpc.Security.s10_generate_wf
#print axioms TlsMpc.Security.s10_profile_sizes
#print axioms TlsMpc.Security.s10_sharedBits_wf
#print axioms TlsMpc.Security.s10_generate_sound
#print axioms TlsMpc.Security.s10_bucket_uniform
#print axioms TlsMpc.Security.s10_arrangement
#print axioms TlsMpc.Security.s11_local_formulas
#print axioms TlsMpc.Security.s11_recoverPublic
#print axioms TlsMpc.Security.s11_sqrt_sq
#print axioms TlsMpc.Security.s11_recode64
#print axioms TlsMpc.Security.s11_step_tableSum
#print axioms TlsMpc.Security.s11_stepIns_window
#print axioms TlsMpc.Security.s11_ephemeralKey
#print axioms TlsMpc.Security.s11_lift_order
#print axioms TlsMpc.Security.s11_lift_valid_sound
#print axioms TlsMpc.Security.s11_prepareStatus_iff
#print axioms TlsMpc.Security.s11_addU_montU
#print axioms TlsMpc.Security.s11_splitAgree_honest
#print axioms TlsMpc.Security.s11_prepareContacts_kinds
#print axioms TlsMpc.Security.s11_flows_reveal
#print axioms TlsMpc.Security.s12_ghash_shared_extend
#print axioms TlsMpc.Security.s12_ghash_keyShare_shared
#print axioms TlsMpc.Security.s12_ghash_round_shared
#print axioms TlsMpc.Security.s12_ghash_halves_xor
#print axioms TlsMpc.Security.s12_ghash_keyShare_hides
#print axioms TlsMpc.Security.s12_ghash_multiply_hides
#print axioms TlsMpc.Security.s12_ghash_keyShare_viewD_B
#print axioms TlsMpc.Security.s12_ghash_round_viewD_B
#print axioms TlsMpc.Security.s12_ghash_keyShare_disclosure_A
#print axioms TlsMpc.Security.s12_tls_seal_is_record
#print axioms TlsMpc.Security.s12_tls_check_accepts
#print axioms TlsMpc.Security.s12_tls_open_event_refines
#print axioms TlsMpc.Security.s12_tls_reveal_value
#print axioms TlsMpc.Security.s12_tls_range_value
#print axioms TlsMpc.Security.s12_tls_verify_value
#print axioms TlsMpc.Security.s12_tls_openHandshake_value
#print axioms TlsMpc.Security.s12_tls_window_bound
#print axioms TlsMpc.Security.s12_tls_sealCtr_wf
#print axioms TlsMpc.Security.s14_openFirst_reveals
#print axioms TlsMpc.Security.s14_session_reveals
#print axioms TlsMpc.Security.s14_sessionRest_refused
#print axioms TlsMpc.Security.s14_verified_wiring
#print axioms TlsMpc.Security.s14_accept_certificate
#print axioms TlsMpc.Security.s14_text
#print axioms TlsMpc.Security.s14_record
#print axioms TlsMpc.Security.s14_refused_text_zero
#print axioms TlsMpc.Security.s14_certificateLength_zero
#print axioms TlsMpc.Security.s14_provisional_ids
#print axioms TlsMpc.Security.s15_refresh_viewD_kinds
#print axioms TlsMpc.Security.s15_flows_reveal_restated
#print axioms TlsMpc.Security.s15_ord2_commit
#print axioms TlsMpc.Security.s15_ord2_drop
#print axioms TlsMpc.Security.s15_ord2_establish
#print axioms TlsMpc.Security.s15_slot_one_source
#print axioms TlsMpc.Security.s15_parse_device
#print axioms TlsMpc.Security.s15_parse_or_refuse
#print axioms TlsMpc.Security.s15_kem_pipeline
#print axioms TlsMpc.Security.s15_kem_accept
#print axioms TlsMpc.Security.s15_kem_invalid
#print axioms TlsMpc.Security.s15_first_wired
#print axioms TlsMpc.Security.s15_drop_inv
#print axioms TlsMpc.Security.s11_wf_split_offset
#print axioms TlsMpc.Security.s11_wf_hinted
#print axioms TlsMpc.Security.s11_prepareContacts_wf
#print axioms TlsMpc.Security.s11_splitBegin_honest
#print axioms TlsMpc.Security.s11_splitAgree_montU
#print axioms TlsMpc.Security.s11_pointExchange_sound
#print axioms TlsMpc.Security.s11_liveness
#print axioms TlsMpc.Security.s11_pointExchange_disclosure
#print axioms TlsMpc.Security.join_splitAgreeWord_reveals
#print axioms TlsMpc.Security.join_ephemeralWord_reveals
#print axioms TlsMpc.Security.join_receive_reveals
#print axioms TlsMpc.Security.join_refreshOps_reveals
#print axioms TlsMpc.Security.join_refresh_reveals
#print axioms TlsMpc.Security.join_first_wired
#print axioms TlsMpc.Security.join_kinds_registered
#print axioms TlsMpc.Security.j1_openFirst_reads_once
#print axioms TlsMpc.Security.j1_session_reads_once
#print axioms TlsMpc.Security.j1_receiveAgree_once
#print axioms TlsMpc.Security.j1_refreshOps_reads_once
#print axioms TlsMpc.Security.j1_refresh_pools_disjoint
#print axioms TlsMpc.Security.runner_drive_model
#print axioms TlsMpc.Security.s16_credentials_reveals
#print axioms TlsMpc.Security.s16_admit_reveals
#print axioms TlsMpc.Security.s16_upgrade_reveals
#print axioms TlsMpc.Security.s16_upgrade_wf
#print axioms TlsMpc.Security.s16_request_shared_value
#print axioms TlsMpc.Security.s16_request_plain_value
#print axioms TlsMpc.Security.j8_jobBits_swaps
#print axioms TlsMpc.Security.j8_receiveAgree_spares
#print axioms TlsMpc.Security.j8_agreeG_spares
#print axioms TlsMpc.Security.j12_senderPublic_spares
#print axioms TlsMpc.Security.j12_senderPublic_reveals
#print axioms TlsMpc.Security.f32_prepare_reveals
#print axioms TlsMpc.Security.f32_prepareStatus_iff
#print axioms TlsMpc.Security.f32_commit
#print axioms TlsMpc.Security.f32_commit_inv
#print axioms TlsMpc.Security.select_contactSet
#print axioms TlsMpc.Security.j13_release
#print axioms TlsMpc.Security.runner_drive_bounded
#print axioms TlsMpc.Security.runner_nextBatch_fill_only
#print axioms TlsMpc.Security.s11_quotientMany_honest
#print axioms TlsMpc.Security.s11_agree_honest
#print axioms TlsMpc.Security.s11_offset_honest
#print axioms TlsMpc.Security.s11_hinted_honest
#print axioms TlsMpc.Security.s11_lift_agreeHinted_honest
#print axioms TlsMpc.Security.s11_quotientMany_disclosure
#print axioms TlsMpc.Security.s11_decl_live
#print axioms TlsMpc.Security.s11_programs_live
#print axioms TlsMpc.Security.s11_maskfree_computes
#print axioms TlsMpc.Security.s11_checks_vanish
#print axioms TlsMpc.Security.s11_offsetPrepare_honest_derived
#print axioms TlsMpc.Security.s11_toAffineAll_live
#print axioms TlsMpc.Security.s11_pointExchange_many_honest
#print axioms TlsMpc.Security.s12_tls_open_wf
#print axioms TlsMpc.Security.s12_tls_sealClass_wf
#print axioms TlsMpc.Security.s12_ghash_round_wf
#print axioms TlsMpc.Security.s12_tls_reveal_wf
#print axioms TlsMpc.Security.s12_tls_derive_wf
#print axioms TlsMpc.Security.s12_tls_finish_wf
#print axioms TlsMpc.Security.s12_tls_open_bounded
#print axioms TlsMpc.Security.s12_ghash_round_bounded
#print axioms TlsMpc.Security.s12_tls_seal_honest
#print axioms TlsMpc.Security.s12_tls_open_binding_honest
#print axioms TlsMpc.Security.s12_tls_open_class
#print axioms TlsMpc.Security.s12_tls_open_rejected_run
#print axioms TlsMpc.Security.s12_ghash_ensure_shared
#print axioms TlsMpc.Security.s12_ghash_round_disclosure_A
#print axioms TlsMpc.Security.s12_ghash_seal_deviation_rejected
#print axioms TlsMpc.Security.s12_ghash_check_deviation
#print axioms TlsMpc.Security.s12_tls_sealClass_is_record
#print axioms TlsMpc.Security.s12_tls_derive_honest
#print axioms TlsMpc.Security.s12_tls_sealCtr_disclosure
#print axioms TlsMpc.Security.s12_tls_open_disclosure_A

/-! The five `bv_decide` uses of the repository (SECURITY_MAP C.6) sit in these public theorems
(two private helpers each in `TlsWebSocketActivity` and `TlsPrivateSeal`, and one tactic call
inside `TlsPrivateSeal.seal_status`). Their axioms answer whether `bv_decide` needs
`Lean.ofReduceBool` here. -/

#print axioms TlsMpc.TlsWebSocketActivity.activity_valid
#print axioms TlsMpc.TlsPrivateSeal.build_correct
#print axioms TlsMpc.TlsPrivateSeal.seal_status
#print axioms TlsMpc.Security.wsFrameAccept_frame_accept
#print axioms TlsMpc.Security.wsFrameAccept_frame_exact
#print axioms TlsMpc.Security.wsFrameAccept_frames_accept
#print axioms TlsMpc.Security.wsFrameAccept_closeCode_value
#print axioms TlsMpc.Security.wsFrameAccept_utf8_drun
#print axioms TlsMpc.Security.wsFrameAccept_reject_close_one
#print axioms TlsMpc.Security.wsFrameAccept_reject_message_full
#print axioms TlsMpc.Security.wsFrameAccept_reject_reason
#print axioms TlsMpc.Security.wsFrameAccept_reject_close_code
#print axioms TlsMpc.Security.wsFrameAccept_reject_reason_code
#print axioms TlsMpc.Security.wsFrameAccept_reject_reason_unfinished
#print axioms TlsMpc.Security.wsControlFrame_control_queue
#print axioms TlsMpc.Security.wsControlFrame_control_queue_pong
#print axioms TlsMpc.Security.wsControlFrame_control_queue_empty
#print axioms TlsMpc.Security.wsReplies_control_reply
#print axioms TlsMpc.Security.chatResponse_body_field
#print axioms TlsMpc.Security.chatResponse_body_field_close
#print axioms TlsMpc.Security.chatResponse_respRun_active
#print axioms TlsMpc.Security.chatResponse_body_field_runByte
#print axioms TlsMpc.Security.chatResponse_reject_body_length
#print axioms TlsMpc.Security.chatResponse_reject_end_in_field
#print axioms TlsMpc.Security.receivePolicy_go_skip
#print axioms TlsMpc.Security.receivePolicy_recordLoop_skip
#print axioms TlsMpc.Security.receivePolicy_request_body_unrevealed
#print axioms TlsMpc.Security.receivePolicy_response_body_unrevealed
#print axioms TlsMpc.Security.receivePolicy_scanBody_tooLong
#print axioms TlsMpc.Security.receivePolicy_scan_wrapper_tooLong
#print axioms TlsMpc.Security.receivePolicy_replyScanBody_tooLong
#print axioms TlsMpc.Security.receivePolicy_replyScan_wrapper_tooLong
#print axioms TlsMpc.Security.receivePolicy_envelope_payload_unrevealed
#print axioms TlsMpc.Security.receivePolicy_request_envelope_safe
#print axioms TlsMpc.Security.receivePolicy_envRun_safe
#print axioms TlsMpc.Security.receivePolicy_payloadByte_request_envelope
#print axioms TlsMpc.Security.receivePolicy_payloadByte_request_skip
#print axioms TlsMpc.Security.receivePolicy_payloadByte_request_more
#print axioms TlsMpc.Security.receivePolicy_payloadByte_reply_skip
#print axioms TlsMpc.Security.receivePolicy_payloadByte_reply_more
#print axioms TlsMpc.Security.receivePolicy_frameByte_frame
#print axioms TlsMpc.Security.peerMsg_reply_kind
#print axioms TlsMpc.Security.revealKind_codes_distinct
#print axioms TlsMpc.Security.revealKind_mem_all
#print axioms TlsMpc.Security.revealKind_code_ne_zero
#print axioms TlsMpc.Security.receivePolicy_t1_all
#print axioms TlsMpc.Security.receivePolicy_loop_sub
#print axioms TlsMpc.Security.receivePolicy_run_fuel
#print axioms TlsMpc.Security.receivePolicy_view_replies
#print axioms TlsMpc.Security.receivePolicy_keeps_afterRecord
#print axioms TlsMpc.Security.receivePolicy_t1_frames
#print axioms TlsMpc.Security.receivePolicy_run_safe
#print axioms TlsMpc.Security.receivePolicy_sim_step
#print axioms TlsMpc.Security.receivePolicy_sim_pass
#print axioms TlsMpc.Security.receivePolicy_envelope_noErr
#print axioms TlsMpc.Security.receivePolicy_rshape_run_c
#print axioms TlsMpc.Security.receivePolicy_qshape_run_c
#print axioms TlsMpc.Security.receivePolicy_classifyFrames_stream
#print axioms TlsMpc.Security.receivePolicy_classify_stream
#print axioms TlsMpc.Security.receivePolicy_message_prefix
#print axioms TlsMpc.Security.receivePolicy_reply_run_safe
#print axioms TlsMpc.Security.receivePolicy_request_run_safe
#print axioms TlsMpc.Security.receivePolicy_frameByte_reject
#print axioms TlsMpc.Security.receivePolicy_upgrade_run_safe
#print axioms TlsMpc.Security.receivePolicy_frameByte_terminator
#print axioms TlsMpc.Security.receivePolicy_t1_start
#print axioms TlsMpc.Security.receivePolicy_t1_start_model
#print axioms TlsMpc.Security.receivePolicy_frameByte_head
#print axioms TlsMpc.Security.receivePolicy_payloadByte_head
#print axioms TlsMpc.Security.receivePolicy_headStep
#print axioms TlsMpc.Security.receivePolicy_keepsHead_afterRecord
#print axioms TlsMpc.Security.ord1_sendSoft_agreed
#print axioms TlsMpc.Security.ord1_sendMessage_acked
#print axioms TlsMpc.Security.ord1_deliverJob_sendsAgreed
#print axioms TlsMpc.Security.ord1_loop_sendsAcked
#print axioms TlsMpc.Security.ord1_serve_sendsAgreed
#print axioms TlsMpc.Security.ord2_commitScratch_agreed
#print axioms TlsMpc.Security.ord2_commitScratch_outcome
#print axioms TlsMpc.Security.ord2_deliverJob_commitsAgreed
#print axioms TlsMpc.Security.ord2_loop_commitsAgreed
#print axioms TlsMpc.Security.ord2_serve_commitsAgreed
#print axioms TlsMpc.Security.t11_deliverJob_results
#print axioms TlsMpc.Security.t11_resultsTail_spec
#print axioms TlsMpc.Security.versions_storeSoft
#print axioms TlsMpc.Security.versions_storeAdvanced
#print axioms TlsMpc.Security.versions_versionIn_bumpIn
#print axioms TlsMpc.Security.stock_T14
#print axioms TlsMpc.Security.stock_T14_boot
#print axioms TlsMpc.Security.stock_agreeIndex_never_back
#print axioms TlsMpc.Security.stock_waste_bound
#print axioms TlsMpc.Security.stock_stockUses_nodup
#print axioms TlsMpc.Security.rotation_t15_erase
#print axioms TlsMpc.Security.rotation_plan_sends_perm
#print axioms TlsMpc.Security.rotation_plan_pool_bound
#print axioms TlsMpc.Security.rotation_plan_generations

/-! Which restated entries depend (transitively, through any proof or definition) on a constant
proved by `bv_decide`. Prints one line per such entry; the script records them. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let isBvDecide (n : Name) : Bool :=
    let s := n.toString
    let last := match n with | .str _ l => l | _ => ""
    ((s.splitOn "TlsWebSocketActivity").length > 1 || (s.splitOn "TlsPrivateSeal").length > 1) &&
      (last == "or_zero" || last == "or_ones" || last == "seal_status")
  -- every restated entry of this file
  let roots := env.constants.map₂.foldl (init := (#[] : Array Name)) fun acc n _ =>
    if (`TlsMpc.Security).isPrefixOf n && !n.isInternal then acc.push n else acc
  -- the dependency graph below the roots
  let mut edges : Std.HashMap Name (Array Name) := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if edges.contains n then continue
    let used := match env.find? n with
      | some ci => ci.getUsedConstantsAsSet.toArray
      | none => #[]
    edges := edges.insert n used
    for u in used do
      unless edges.contains u do stack := stack.push u
  -- reverse reachability from the bv_decide constants
  let mut reverse : Std.HashMap Name (Array Name) := {}
  for (n, used) in edges.toList do
    for u in used do
      reverse := reverse.insert u ((reverse.getD u #[]).push n)
  let targets := edges.toList.filterMap fun (n, _) => if isBvDecide n then some n else none
  let mut reaches : NameSet := {}
  let mut work := targets.toArray
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if reaches.contains n then continue
    reaches := reaches.insert n
    for p in reverse.getD n #[] do
      unless reaches.contains p do work := work.push p
  for t in targets do
    logInfo m!"bv_decide constant reached: {t}"
  let dependent := (roots.filter reaches.contains).qsort (·.toString < ·.toString)
  for r in dependent do
    logInfo m!"depends on bv_decide: {r}"
  logInfo m!"entries depending on bv_decide: {dependent.size} of {roots.size}"
