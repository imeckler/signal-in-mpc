import TlsMpc.FlatLowering
import TlsMpc.ByteCircuit
import TlsMpc.BoolDag
import TlsMpc.FieldDag
import TlsMpc.FieldDagMulti
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

* **H-GROUP**: the Edwards/Montgomery formulas used by the curve programs are the group law. No
  entry proves it; entries about curve formulas say "formulas only". Stays a hypothesis even
  under the Mathlib decision below.
* **H-QR**: 2 is a non-square mod p (used by the hinted lift; no entry here needs it yet).
  **To become a theorem** in the planned Mathlib-backed proof library (owner's decision of
  2026-11-12: Mathlib for proof-only modules in a separate library no executable imports).
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
not proved to be the group law (H-GROUP). SECURITY_MAP C.2. -/
theorem xeddsa_recover_correct (artifact : MultiArtifact) (compiled : compileAll recover = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) =
      TlsMpc.Signal.XEdDsaField.run TlsMpc.X25519.concrete true input :=
  TlsMpc.EstablishField.recover_correct artifact compiled input

open TlsMpc.EstablishField TlsMpc.FieldDag in
/-- **The `xeddsa-check` field program computes `XEdDsaField.signedRun`.** **K**. Formulas
only (H-GROUP). SECURITY_MAP C.2. -/
theorem xeddsa_check_correct (artifact : MultiArtifact) (compiled : compileAll check = some artifact) (input : Nat → F) :
    artifact.outputs.map (result (concrete input) artifact.nodes) =
      TlsMpc.Signal.XEdDsaField.signedRun TlsMpc.X25519.concrete input :=
  TlsMpc.EstablishField.check_correct artifact compiled input

open TlsMpc.ReceiveField TlsMpc.FieldDag in
/-- **The `receive-torsion` field program computes `torsionRun`.** **K**. Formulas only
(H-GROUP). Not listed in SECURITY_MAP C.2; found while building this file. -/
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
agreement, `edwards_points.h`). Formulas only (H-GROUP). Not listed in SECURITY_MAP C.2; found
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
computed tag, else 0** (accept direction included). **K-fn**: no theorem connects it to
`receive-session`'s status (T13, section 8). SECURITY_MAP C.2, C.3. -/
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
/-- **`receive-certificate-verified`** = `ReceiveFirst.certificateVerified`. **K**. That status
255 implies the signature verified is NOT proved (T13, section 8). -/
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
/-- **`receive-session`** = `ReceiveFirst.session` (first four outputs). **K**. That status 255
implies the message MAC verified is NOT proved (T13, section 8). -/
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
/-- **`receive-text`** = `ReceiveFirst.text`. **K**. No `_rejects` lemma (section 8, T13). -/
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
/-- **`bundle-seal`** = `Establish.sealMessage` (rearranged). **K**. `Establish.sealMessage`
itself has only `_map` lemmas, no value theorem (T7, section 8). -/
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
**K** (wire). No value theorem for `boundSeal` itself (T7(b), section 8). SECURITY_MAP C.2. -/
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
slot encoders (TlsMpc/KernelSpecs/{RequestFrame, BundleItemWhole, WidthFlags, SlotEncoders,
SlotBase64, SlotDecimal}.lean)

The request builders `PublicRequest.build`/`buildFetch`/`buildDevices` live in the controller's
executable root, which this file does not import (section 4). The entries below are about
`RequestFrame.Mirror.*`, restated character for character with the byte operations as a
parameter; `TlsMpc/KernelSpecs/RequestFrameBridge.lean` (checked on its own, not imported here)
proves `PublicRequest.build = Mirror.build PublicReceive.fast`, `PublicRequest.buildFetch =
Mirror.buildFetch` and `PublicRequest.buildDevices = Mirror.buildDevices PublicReceive.fast`. Those
entries are **C** (the builders) composed with **K** (the kernels). -/

open TlsMpc.KernelSpecs.RequestFrame TlsMpc.KernelSpecs.RequestFrame.Mirror in
/-- **Every frame `build` returns has the 8-byte WebSocket header** `[130, 254, size / 256, size] ‖
mask` (payload of 126..65535 bytes), followed by the built payload (text masked, slots zero); the
offsets are those the slot pieces set. So `signal-request-ctr`'s fixed payload start 8 is right for
every frame the controller builds for it. **C** (mirror + bridge). T8. -/
theorem requestBuild_ok (ops : ByteAuth.Ops (BitVec 8)) (envelope : List (BitVec 8)) (timestamp id : Nat)
    (mask frame : List (BitVec 8)) (official : Bool) (offsets : List Nat)
    (built : build ops envelope timestamp id mask official = .ok (frame, offsets)) :
    let msg := sendMessage ops envelope timestamp id official
    126 ≤ total msg ∧ total msg < 65536 ∧ mask.length = 4 ∧ (buildHeader (total msg) mask).length = 8 ∧
      frame = buildHeader (total msg) mask ++ body mask 0 msg ∧ offsets = (offsetsFold #[0, 0, 0, 0] 8 msg).toList :=
  TlsMpc.KernelSpecs.RequestFrame.build_ok ops envelope timestamp id mask frame official offsets built

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.RequestFrame TlsMpc.KernelSpecs.RequestFrame.Mirror in
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

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.RequestFrame TlsMpc.KernelSpecs.RequestFrame.Mirror Std.Tactic.BVDecide
  TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`signal-request-ctr` on a frame `build` returned seals exactly the WebSocket frame of the
request with the contact's UUID, base64 access key and space-padded device and registration ids in
place of its four slots** (masked with the frame's mask), released under `valid`. **K** + **C**.
T7(a), T8. -/
theorem signalRequestCtr_built (ops : ByteAuth.Ops (BitVec 8)) (envelope : List (BitVec 8)) (timestamp id : Nat)
    (mask frame : List (BitVec 8)) (official : Bool) (offsets : List Nat)
    (built : build ops envelope timestamp id mask official = .ok (frame, offsets))
    (cert : Nat) (assign : BVExpr.Assignment)
    (hframe : (lookup (signalRequestInputs cert frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (signalRequestInputs cert frame.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (signalRequestInputs cert frame.length) name).map (BVExpr.eval assign)
    let msg := sendMessage ops envelope timestamp id official
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (buildHeader (total msg) mask ++ maskFrom mask 0 (render (requestValues cert (get "conversation")) msg))
        (signalRequestSlots cert 0 0 0 0 (get "conversation")).1 :=
  TlsMpc.KernelSpecs.RequestFrame.signalRequestCtr_built ops envelope timestamp id mask frame official offsets built
    cert assign hframe hmask

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.RequestFrame TlsMpc.KernelSpecs.RequestFrame.Mirror Std.Tactic.BVDecide
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

open TlsMpc.KernelSpecs TlsMpc.KernelSpecs.RequestFrame TlsMpc.KernelSpecs.RequestFrame.Mirror Std.Tactic.BVDecide
  TlsMpc.Signal in
open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-request-ctr` on a frame `buildDevices` returned seals exactly the frame of
`PUT /v1/messages/{uuid}` with the UUID, access key and every device's padded ids in place**, the
kernel named with the device offsets paired as `find` pairs them. **K** + **C**. T7(a), T8. -/
theorem bundleRequestCtr_built (ops : ByteAuth.Ops (BitVec 8)) (envelopes : List (List (BitVec 8))) (timestamp id : Nat)
    (mask frame : List (BitVec 8)) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices ops envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let msg := devicesMessage ops envelopes timestamp id official
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total msg) mask ++ maskFrom mask 0 (render (devicesValues (get "records")) msg))
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 :=
  TlsMpc.KernelSpecs.RequestFrame.bundleRequestCtr_built ops envelopes timestamp id mask frame official payloadAt
    offsets built devices paired assign hframe hmask

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
spliced into the slot layout.** **K**. That `deviceSlots` on the spliced item equals `device` on
the original is NOT proved (section 8). -/
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
MAC verified) is NOT proved (T13, section 8). SECURITY_MAP C.3. -/
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

/-! ## 4. The controller: parsers, the reveal policy, templates, results (SECURITY_MAP C.4)

Code that `public_service_controller` executes. The parsers (WebSocket upgrade, frame, control,
chat response) are proved only symbolic = concrete; nothing relates them to RFC 6455 or HTTP.
The reveal policy (`PublicReceive.scan`, `budget`, `mayReveal`, …), the request templates
(`PublicRequest.*`), `Recovery`, `Circuits` and `CeremonyRequests` have NO theorem (T1, T8, T11
in section 8). -/

/-! **Pending restatement (C): `PublicReceive.fast_eq : fast = ByteAuth.concrete`** — the
controller's fast byte operations equal the reference ones, so every parser the controller runs
with `fast` is the proved concrete parser (SECURITY_MAP C.4; the controller file's only theorems
are this one and its helpers `fastConst_eq`, `fastNot_eq`, `fastMask_eq`). It lives in the
controller's executable root `handshake_backend/EmpHybridWork/PublicServiceController.lean`,
which stage S2 is moving to `TlsMpc/Node/Policy/Receive.lean`. This file does not import an
executable root; restate it here (`theorem controller_fast_eq : PublicReceive.fast =
ByteAuth.concrete := …fast_eq`) in the S2 commit, from its new module. -/

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
Formulas only (H-GROUP). -/
theorem edwards_onCurve_eval (input : Nat → F) :
    onCurve.eval input =
      ofNat 121666 * (input 1 * input 1 - input 0 * input 0 - ofNat 1) +
        ofNat 121665 * (input 0 * input 0 * (input 1 * input 1)) :=
  TlsMpc.EdwardsShare.onCurve_eval input

open TlsMpc.EdwardsShare TlsMpc.FieldDag in
/-- **The `edwards-add-u` program computes the numerator and denominator of the Montgomery u of
a sum.** **K** (`split_ecdh.h`). Formulas only (H-GROUP). -/
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

No per-flow or per-channel theorem exists yet (T3, T4-x, T9–T12, section 8). The one statement
at the level of a flow is a structural fact about the TLS client. -/

open TlsMpc.TlsClient in
/-- **Any TLS `Session` value records that the server certificate and the server Finished were
verified.** **C**, weak: a structure projection (the flags are fields that construction must
supply), not a statement about what the handshake checked. SECURITY_MAP C.4. -/
theorem tlsClient_accepted_session_authenticated {S : Type} (session : Session S) :
    session.serverCertificateVerified = true ∧ session.serverFinishedVerified = true :=
  TlsMpc.TlsClient.accepted_session_authenticated session

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
  Still open: `bundle-slot`: `deviceSlots` on the spliced item = `device` on the original item,
  and `BundleSlots.splice` producing the slot layout (`bundleSlot_whole` links the kernel only to
  the whole SPLICED body). → no stage assigned; candidate for **P5**.
* ML-KEM: the `kem-*` kernels composed into `MlKem.encapsulate`. → no stage assigned.
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
  (`signalSealBuilt_spec`); open: a value theorem for `boundSeal` and for `prepare` against the
  Signal/SPQR definitions. → **P5**.

### Gating and what each opening reveals
* **T13** — receive gating, accept direction: `receive-session` status 255 ⇒ the message MAC
  verified and the sender certificate verified under the trusted server key; `receive-text`
  outputs are zero unless the session status is 255 (the missing `_rejects` lemmas for
  receive-text, -certificate, -certificate-verified, -access-key and the three -shape kernels).
  → **P6**.
* **T3** — disclosure per flow: the released values in any trace of a flow are exactly the
  listed `Reveal` kinds on the listed handles. → **S9–S16** (one per flow).

### The controller
* **T1** — server-byte reveal policy: for every byte stream and every non-throwing run of
  `budget`/`mayReveal`/`step`/`stepPassed`/`stepSkipped`, the revealed positions are disjoint
  from the reference classifier's hidden set (request bodies, response bodies unless `openBody`,
  envelope payloads, …). → **P1**.
* **T8** — request templates: for `build`/`buildDevices`/`buildFetch`/`assemble` the structural
  part is now proved (section 2d, about the restated `Mirror` builders, equal to the controller's
  by `RequestFrameBridge.lean`): the frame is the WebSocket header and the message masked, slots
  are zero runs inside the payload, non-overlapping, at the returned offsets (`requestBuild_ok`,
  `requestInsertSlots_offsets`). Still open: that the message is the stated protobuf/JSON
  (`render` of the pieces, against a protobuf encoder); `reply`, `keepalive`, `ping`,
  `clientFrame`. → **P2**.
* **T11** — application results: every `jobResult` line carries exactly the entries both
  controllers agreed on; each result is `Recovery.onSend`/`onFetch` of revealed statuses or a
  fixed reason. → **P4**.
* Parsers vs RFC 6455 / HTTP (today only symbolic = concrete). → no stage assigned.

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
* **P-RAND** (joint randomness: honest result, bijection under `idealCommit`, copied commitment
  aborts). → **S9**.
* **P-CHAL** (challenge permutation: agreement, is a permutation, injective seed). → **S10**.
* **P-CUT** (cut-and-choose word masks: correctness, disclosure, hiding, detection, bit blocks,
  single use). → **S10**.
* **P-PAIR / P-B2F**, **P-W2F**, **P-F2W** (conversions: value, bijection, single use). → **S10**.
* **P-BITS** (shared scalars as field bits; needs the converse of `fieldBits_bitCheck_bit`).
  → **S10**.
* **P-INV** (masked inversion `D`/`Z` nodes), **P-FIELDPROG** (what a program releases). → **S9**,
  **S11**.
* **P-GHASH** (incl. (c): `sealCtr_with_tag_is_seal`'s `halves` discharged for the running
  code). → **S12**.
* **P-SPLIT** (split ECDH), **P-OFFSET** (offset agreement about `step`, incl. the digit
  recoding lemma), **P-HINT** (lift and tables, under H-QR). → **S11**.
* `commit_open_sound` (one commitment for all commit-then-open sites). → **S9–S11**.

### Flows and channels
* **T4-x** — composition per flow (CONTACT, UPGRADE, TLS, SEND, RECV, REFRESH, CEREMONY): under
  the ideal model with both parties honest, the flow's result equals its specification.
  → **S9** (CONTACT), **S12** (TLS), **S13** (SEND), **S14** (RECV), **S15** (REFRESH), **S16**
  (UPGRADE, CEREMONY).
* **T9** — peer messages are public (by types; `PeerMsg.flow` only from `Reveal.lean`). → **S5**.
* **T12** — skeleton determinism of scripts. → **S9**.

### Affected by the Mathlib decision (owner, 2026-11-12)
Mathlib may be used by proof-only modules in a separate library that no executable imports. The
Edwards group law (H-GROUP) stays a hypothesis. This changes the following items:
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
#print axioms TlsMpc.Security.bundleDevice_local
#print axioms TlsMpc.Security.bundleItem_whole
#print axioms TlsMpc.Security.bundleSlot_whole
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
#print axioms TlsMpc.Security.word64_fast_eq
#print axioms TlsMpc.Security.varint_decodeCore_spec
#print axioms TlsMpc.Security.notification_buildPublic_spec
#print axioms TlsMpc.Security.notification_buildPublicOfficial_spec
#print axioms TlsMpc.Security.notification_buildPublic_short
#print axioms TlsMpc.Security.notification_firstFit_spec
#print axioms TlsMpc.Security.bundle_layout_sound
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

/-! The five `bv_decide` uses of the repository (SECURITY_MAP C.6) sit in these public theorems
(two private helpers each in `TlsWebSocketActivity` and `TlsPrivateSeal`, and one tactic call
inside `TlsPrivateSeal.seal_status`). Their axioms answer whether `bv_decide` needs
`Lean.ofReduceBool` here. -/

#print axioms TlsMpc.TlsWebSocketActivity.activity_valid
#print axioms TlsMpc.TlsPrivateSeal.build_correct
#print axioms TlsMpc.TlsPrivateSeal.seal_status

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
