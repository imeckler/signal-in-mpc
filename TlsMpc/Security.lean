import TlsMpc.FlatLowering
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
import TlsMpc.KernelSpecs.KemCompose
import TlsMpc.Node.Engine.Model
import TlsMpc.Node.Flows.Random
import TlsMpc.Node.Flows.Upgrade
import TlsMpc.Node.Flows.Contacts
import TlsMpc.Node.Flows.ContactsTable
import TlsMpc.Node.Flows.Account
import TlsMpc.Node.Flows.ContactsWrite
import TlsMpc.Node.Flows.MasksRun
import TlsMpc.Node.Flows.Registry
import TlsMpc.Node.Messages
import TlsMpc.KernelSpecs.ParseWebSocketAccept
import TlsMpc.KernelSpecs.ParseWebSocketControlFrame
import TlsMpc.KernelSpecs.ParseWebSocketReplies
import TlsMpc.KernelSpecs.ParseChatResponse
import TlsMpc.Node.Policy.ReceiveProofs
import TlsMpc.Node.Policy.ReceiveEnvelope
import TlsMpc.Node.Policy.ReceiveInvariant
import TlsMpc.Node.Types
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

## What every entry silently relies on (trusted, not proved)

* The circuit printers (`Flat.print`, `EmitWordMask.render`/`renderField`), the layout text with
  its open/private marks, and the choice of which flat outputs form which named field
  (SECURITY_MAP C.1). A kernel theorem is about the Lean term; the file the worker loads reaches
  it only through these printers.
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
term. The printers that turn the gate list into text are NOT covered (see the header). -/

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
`end` as stated and passes the splice and `widths` from the same digit counts. Caveat
`inconsistent_width_accepts` (section 8). -/

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.BundleSlotWhole Std.Tactic.BVDecide TlsMpc.Signal in
open TlsMpc.Signal.Establish (part) in
open TlsMpc.Signal.BundleResponse (Widths Piece literals fieldOf item header firstItem size numberBits numberValid
  numberBytes digitValid pushDigit) in
/-- **A slot of `m` bytes holding `m − n` zeros and then `n` characters, checked with the declared
width `n`, is accepted exactly when `numberValid` accepts the `n` characters.** -/
theorem slotValid_pad (limit : Nat) (cs : List Byte) (m : Nat) (h1 : 1 ≤ cs.length) (hnm : cs.length ≤ m)
    (hm : m < 256) :
    BundleSlots.slotValid ByteAuth.concrete limit (BitVec.ofNat 8 cs.length) (List.replicate (m - cs.length) 48 ++ cs) =
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
        (pre ++ applyRuns 48 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post).length
        pre.length (w.oneTime != 0) (widthBytes w)
        (pre ++ applyRuns 48 (BundleSlots.runs (item w) (item (BundleSlots.slots (w.oneTime != 0)))) I ++ post) =
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
          BundleSlots.spliced w (part X start (size (item w))) 48 ++
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
          BundleSlots.spliced w (part X start (size (item w))) 48 ++
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
          BundleSlots.spliced w' (part X start (size (item w'))) 48 ++
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
          BundleSlots.spliced w' (part X start (size (item w'))) 48 ++
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
/-- **`bundle-slot` on an item the server wrote, whatever the `widths` input.** If `device`
accepts the item at `start` of `X` with digit counts `w` and the runtime splices it with `w`,
then for ANY five bytes as `widths` the kernel either gives exactly `device`'s outputs (those of
`bundle-item`) or releases nothing at all. -/
theorem bundleSlot_any_widths (first last : Bool) (w : Widths) (ok : w.ok = true) (assign : BVExpr.Assignment)
    (X : List Byte) (start : Nat) (placed : BundleItemWhole.Placed X.length first last start (size (item w)))
    (inputs : let get := fun name =>
        (lookup (BundleSlotKernel.slotInputs first last (w.oneTime != 0)) name).map (BVExpr.eval assign)
      get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" =
        part X 0 firstItem ++ (if first then [] else part X (start - 1) 1) ++
          BundleSlots.spliced w (part X start (size (item w))) 48 ++
          (if last then [] else part X (start + size (item w)) 1) ++ part X (X.length - 2) 2)
    (accepted : (BundleResponse.device ByteAuth.concrete X.length start w X).getD 0 [] = [255]) :
    (let out := BundleResponse.device ByteAuth.concrete X.length start w X;
      values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign =
        [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
          out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
        (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []])) ∨
    (∀ field ∈ values (BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) assign, ∀ byte ∈ field, byte = 0) :=
  TlsMpc.KernelSpecs.BundleSlotWhole.bundleSlot_any_widths first last w ok assign X start placed inputs accepted

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
lets out) are printed by unproved code (T2, section 8). -/

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
text and access-key kernels on concrete values), **K-fn** where stated. One DEFECT is recorded
as a counterexample pair: `receive-text` accepts a body longer than its DataMessage
(`receiveAcceptText_overlongBody_*`; NEEDS_REVIEW.md 3f). -/

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
/-- **DEFECT (counterexample, with `receiveAcceptText_overlongBody_reference`): `receive-text`
accepts a body longer than its DataMessage.** On this plaintext the kernel opens status 255 and the
5-byte text `abcde`, while the reference parse of the same content refuses it (NEEDS_REVIEW.md 3f).
A statement of what the kernel does today, not a property to keep. -/
theorem receiveAcceptText_overlongBody_accepted :
    text ByteAuth.concrete 10 overlongBodyPlain =
      [[255], [0, 5], [0x61, 0x62, 0x63, 0x64, 0x65, 0, 0, 0, 0, 0], [255, 0, 0]] :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.overlongBody_accepted

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.ReceiveAcceptText TlsMpc.KernelSpecs.ReceiveAccept Std.Tactic.BVDecide TlsMpc.Signal TlsMpc.Signal.ReceiveFirst in
/-- **DEFECT, the other half:** the reference parse refuses the plaintext that `receive-text`
accepts in `receiveAcceptText_overlongBody_accepted` (NEEDS_REVIEW.md 3f). -/
theorem receiveAcceptText_overlongBody_reference : referenceBody (overlongBodyPlain.drop 8) = none :=
  TlsMpc.KernelSpecs.ReceiveAcceptText.overlongBody_reference
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
every stream is not (section 8; checked by `ReceiveTest`). End-to-end runs of the loop
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
ordering (ORD-1: store acknowledged before send; ORD-2) and the database nonce rule (T10) are
NOT proved (section 8). -/

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
ciphertext (hypothesis `halves`). **K**, but `halves` is discharged only for a modelled schedule
(`gcm_scheduled_halves_are_ghash`), not for the C++ `gcm_shares.h` (P-GHASH(c), section 8).
SECURITY_MAP C.3. -/
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

end FlowsS10

/-! ### 7c. Local arithmetic and the curve flows (stage S11; plan 7.1 P-SPLIT, P-OFFSET, P-HINT)

Status per entry: **M** (ideal model of `Engine/Model.lean`) or **K** (values, independent of the
model); hypotheses named `[hyp: …]`. `FieldInverse` (Fermat for p) is FieldDagV3's named
hypothesis (discharged in `proofs/`: `FieldBridge.toZMod_inverse`). H-QR (`Curve.TwoNonSquare`)
and Euler's criterion (`Curve.EulerCriterion`) are named hypotheses here, discharged in `proofs/`
by `two_not_square` and `euler_criterion` (with `Local.Field.pow_eq`). H-GROUP is not assumed by any
entry here: the entries state the main-package values the `proofs/` group-law theorems
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

end FlowsS11

/-! ## 8. NOT YET PROVED

Comments, not theorems. Each line names the statement (REORGANIZATION_PLAN.md section 7 / 8.1)
and the stage or proof track that delivers it. When one is proved, its restatement moves into
the matching section above in the same commit.

### Lowering and artifacts
* **T2** — open marks and printers: for every kernel name the inventory can emit, the printed
  layout's rows and open flags equal the kernel's declared fields and marks; parsing the printed
  `.flat` gives back `Flat`; the V3 field-program printer likewise. Also: a composed theorem
  "the loaded flat file computes the kernel spec" (`lowerExpr_correct` + `joinExpr_correct` +
  `_spec`). → **P3** (touches the emitters; one re-lowering, alone).

### Kernels compute their specification
* Kernel-level specs: now proved for every kernel this item used to list (section 2c). Closed in
  section 2d: `bundle-item` on the whole body (`bundleItem_whole`, from the locality lemma
  `bundleDevice_local`), the meaning of the `signal-widths` flags (`signalWidths_value`), the UUID,
  base64 and padded decimal slot encoders against independent references (RFC 4122 string form,
  RFC 4648, decimal digits) with round trips (`slotUuid_*`, `slotBase64_*`, `slotDecimal_*`).
  Also closed: `bundle-slot` against `device` on the body the server sent (section 2d:
  `bundleSlot_device`, `bundleSlot_eq_bundleItem`, `deviceSlots_splice`, `spliced_layout`,
  `slotValid_pad`; wrong digit counts refuse: `device_unique`, `bundleSlot_wrong_counts`,
  `bundleSlot_parses_or_refuses`, `bundleSlot_any_widths`). Still open for `bundle-slot`: the
  caveat `inconsistent_width_accepts` (`TlsMpc/KernelSpecs/BundleSlotWhole.lean`): a body whose
  number has a leading zero, spliced with one digit count but declared with another in `widths`,
  is accepted where `device` refuses (the released value is still that number's value); still
  trusted: that the C++ worker binds `head`/`before`/`item`/`after`/`end` as stated and passes the
  splice and `widths` from the same counts, and that the template is what Signal-Server writes.
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
  accepted; the `_rejects` lemmas; what `receive-text` and `receive-access-key` open). One DEFECT
  recorded: `receive-text` accepts a body longer than its DataMessage
  (`receiveAcceptText_overlongBody_*`, NEEDS_REVIEW.md 3f). Still open: the converse for a genuine
  sender's envelope (that it is accepted); Prop forms for the multi-byte counters,
  `canonicalRange`, `Unpad.decode` and the layout masks (stated today as byte computations); an
  accept-direction value theorem for `contentShape`'s flags and for `receive-content`; and the
  field engine (the curve computations whose outputs `rx`, `ry` and the agreements are inputs
  here). → **P6**.
* **T3** — disclosure per flow: the released values in any trace of a flow are exactly the
  listed `Reveal` kinds on the listed handles. The list exists since S6 (`TlsMpc/Node/Reveal.lean`,
  section 7-reveal: every `Opened` value is made there, each kind's docstring names its bounding
  theorems or "none yet"); behind each flow is still a C++ worker operation. → **S9–S16** (one per
  flow).

### The controller
* **T1 (all streams)** — server-byte reveal policy: for every byte stream and every
  non-throwing run of `budget`/`mayReveal`/`step`/`stepPassed`/`stepSkipped`, the revealed
  positions are disjoint from the reference classifier's hidden set (request bodies, response
  bodies unless `openBody`, envelope payloads, …). Delivered envelopes are proved at the
  controller-step level for every byte string (section 4f: `receivePolicy_request_envelope_safe`,
  `receivePolicy_envRun_safe`, with the pass-over across records, a request's and a response's
  body, and fail-closed varints). T1 for all streams is still OPEN: the streaming form of the
  reference classifier, the frame-layer simulation, `scan`/`replyScan` for every field order, the
  loop-level run theorem, the capacity-counter invariant; the upgrade layer is outside T1. Checked
  meanwhile by `ReceiveTest` (`policy-check`). It is the precondition of `Reveal.serverBytes`
  (`Flow.Tls.revealRange`). → **P1**.
* **T8** — request templates: for `build`/`buildDevices`/`buildFetch`/`assemble` the structural
  part is now proved (section 2d, about the controller's own builders in
  `TlsMpc/Node/Policy/Request.lean`): the frame is the WebSocket header and the message masked, slots
  are zero runs inside the payload, non-overlapping, at the returned offsets (`requestBuild_ok`,
  `requestInsertSlots_offsets`), and the messages are the reference protobuf/JSON requests in
  RFC 6455 client frames, `reply`, `keepalive`, `ping` and `clientFrame` included (section 4d,
  `t8_*`). Still open: the id `reply` answers is shown to be the one `varintAt` reads only under a
  hypothesis (`scan`'s loop invariant is not proved); `replies` (pong/close echoes) is covered
  by section 4c only. → **P2**.
* **T11** — application results: every `jobResult` line carries exactly the entries both
  controllers agreed on; each result is `Recovery.onSend`/`onFetch` of revealed statuses or a
  fixed reason. → **P4**.
* Parsers vs RFC 6455 / HTTP: the frame parser's extents and refusals, the control queue, the
  TLS record splitter and the upgrade's accept value now have references (section 4c). Still
  open: `TlsChatResponse` (the chat-response parser) has no reference yet; nor has the upgrade
  response parser; and frame-parser acceptance (a well-formed frame keeps validity 255) is not
  proved, so the composition frame parser → control queue is stated on the queue's inputs.
  → no stage assigned.

### State and ordering
* **T6 / ORD-1** — send ordering: every Send(c) is preceded by a StoreAck(c) after the last
  Seal(c); no two Sends carry the same sealed envelope. → **P4** (after S7; restated after S13).
* **ORD-2** — a refresh's scratch becomes state only after both parties saw the nodes
  acknowledge it. → **P4**, **S15**.
* **T10** — database writes: every blob = nonce ‖ sealed blob with the nonce fresh joint
  randomness unused in the session; versions increase by one per acknowledged write. → **S9**.
* **T14** — stock used once. → **X1** (after S16).
* **T15** — connection rotation reveals nothing about ids. → **X2**.

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
  `bitBlock_unique` with `FieldInverse`; (h) the pool and the frees. OPEN: (a) for a whole honest
  `generate` run in the model (checked executably for the test parameters: the vectors'
  `check mask … ok`); (b) a value-level disclosure for the bucket, flag and bit-block phases and
  the whole run; (c) the composition with the model (the adversary's whole view of `generate` as a
  function of these releases and the challenges), and the bit-block flags (the ≥ 32 condition of
  the shifted reference); (f), (g) at run level; a WF theorem for `generate` (every batch of the
  test instance is admitted: the vectors' `verdict ok`). → **S10 follow-up**.
* **P-PAIR / P-B2F**, **P-W2F**, **P-F2W**: (a), (b), T3, (c) proved (section 7b; W2F and F2W (a)
  through `jointRun`, B2F (a) per bit). Open: B2F (a) through `jointRun` for the whole bundle; WF
  theorems for the conversion scripts.
* **P-BITS**: (a) with `FieldInverse` (the converse of `fieldBits_bitCheck_bit`), (b), (c) at the
  protocol level. Open: the run-level statement through the program instructions.
* **P-INV** (masked inversion `D`/`Z` nodes), **P-FIELDPROG** (what a program releases). → **S9**,
  **S11**.
* **P-GHASH** (incl. (c): `sealCtr_with_tag_is_seal`'s `halves` discharged for the running
  code). → **S12**.
* **P-SPLIT**, **P-OFFSET**, **P-HINT** (section 7c, stage S11). Proved: P-SPLIT (a) through
  `jointRun` for the agreement (`s11_splitAgree_honest`, `s11_addU_montU`; the group law itself is
  `proofs/` R7), (b) the gate (`Curve.splitAgree_gate`, checks = `curveValue`), (c) the kinds
  (`Curve.splitKinds`), (d) `s11_local_formulas`; P-OFFSET (a) the recoding lemma about the flow's
  own `recode` (`s11_recode64`, `s11_step_tableSum`) and the step's program inputs
  (`s11_stepIns_window`: exactly `offsetSum_recoded`'s hypothesis; there is no C++ `step`), (b) the
  key the script returns (`s11_ephemeralKey`), (c), (d) gates (`Curve.offsetPrepare_gate`,
  `Curve.pointExchange_gate`); P-HINT (a) (`s11_lift_order`), (b) soundness with `FieldInverse` and
  completeness under H-QR/Euler as named hypotheses (`s11_prepareStatus_iff`). OPEN: honest runs
  through `jointRun` of `agree`, `offsetPrepare`, `offsetStep(Fast)`, `lift`, `tables`,
  `agreeHinted`, `agreeAffine`, `signatures`, `torsion`, `prepareContacts` (checked executably:
  `node_worker/tests/s11_vectors.txt`, every `check … ok`); value-level disclosure (T3 with values)
  for the curve flows beyond the kinds; `_wf` theorems for the curve scripts (every batch of the
  vector instances admitted: `verdict ok`); P-HINT (d) composed with the runs (`entries_sound` is
  about the program); that the local step's mask points are uniform on the curve group
  (`randomPoint`, the map (r, t) ↦ r·B + t·T₈; `proofs/` `curve_hinted_Z_uniform` assumes it).
  → **S11 follow-up**.
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
  (UPGRADE, CEREMONY).
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
  Open. → **P3** (with T2). Not covered by `Loaded`: the `xor-bit` circuit that `Account.opSeal`
  runs on two credential shares.
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
    1024/12). P-CUT(d)–(f), i.e. that the C++ generators implement the model, remain (S10).
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

#print axioms TlsMpc.Security.lower_sound
#print axioms TlsMpc.Security.lower_correct
#print axioms TlsMpc.Security.lowerExpr_correct
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
#print axioms TlsMpc.Security.receiveAcceptText_overlongBody_accepted
#print axioms TlsMpc.Security.receiveAcceptText_overlongBody_reference
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
