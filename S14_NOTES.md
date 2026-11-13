# Stage S14: receive a first message — notes

Branch `s14-receive` (from `s12-tls`, which carries S10 and S12). REORGANIZATION_PLAN.md 8.1 (T3,
T4-RECV, T13) and 10.2 S14.

## What moved from C++ to Lean

| C++ (read-only, unchanged) | Lean | File |
|---|---|---|
| `service_kernels.h` `envelope_take` (260-264), op 48 | `Receive.takeScript` (a slice of S12's revealed bytes appended to the held envelope) | `TlsMpc/Node/Flows/Receive.lean` |
| `envelope_drop` (265), op 49 | `Receive.dropScript` | |
| `envelope_open` (274-333), op 50, steps 1-12 | `Receive.openFirst` → `firstContent` → `firstCertificate` → `firstPrekey` | |
| `envelope_session` (338-408), op 51, steps 13-17 | `Receive.session` → `sessionRest` | |
| `Arrival` (104-105) | `Receive.Arrival` (`Held BoolH` + the three field handles + public widths) | |
| `ReceivePrograms` (106-113) | `Receive.programSignature`, `programBaseCheck` (`program` instruction, V3) | |
| `server(...)` (118-127) | `ReceiveBackend.serverPoint` (local: `XEdDsaField.run X25519.concrete true`) | `Flows/ReceiveBackend.lean` |
| `shaped`, `flag`, `width` (131-142) | the `loaded` predicate, `flagAt`, `widthAt`, `prekeyWidths`, `certShapeOf`, `signerOf`, `signalValues`, `textBody` | `Flows/Receive.lean` |
| the controller's provisional ids (`PublicServiceController.lean` 634-664) | `Receive.provisionalId` (+ `provisionalId_inj`, `provisionalId_high`) | |

The IO glue `ReceiveBackend.scriptApi` has exactly the legacy functions' types once its context is
given (`ReceiveBackend.Api`; `legacyApi w` builds the same record from `Flow.Receive.*`, so the
types are checked by the compiler): switching the controller changes no call site.

### Deviations from the C++ (both parties change together)
* **One opening per kernel output group**: the four prekey fields in one opening (`prekeyIds`), the
  text's length ‖ text ‖ layout in one (`receivedText`) — after its status, which is opened alone
  first. (The C++ opens 4 and 4 times.)
* **Refusals free every handle** (the C++ drops its `Wires` by RAII); the scripts free each input as
  soon as no later stage needs it.
* **Kernel availability**: a kernel the worker did not load refuses the message (the C++ `shaped`)
  through the runner's `loaded` predicate; the scripts never run an unloaded kernel.
* **Our identity key, address, request id, signer, time, server key words**: public bits
  (`boolPublic`), as the C++ `k.constant`. **The Kyber shared secret** (OWN, both hold it): party
  A's private input (`inputA`), not a public constant, so no `Secret` is exposed in Lean; a party
  that inputs a wrong secret only makes the MAC check fail.
* **The access key input** is 16 zero bytes as in the C++; **the request id** is `2^63` as the
  legacy flow passes it.
* **Program masks**: fresh field contributions of both parties (Inversion's discipline), per program
  instance, from `Channels.random`.
* **The hinted mode's reuse** of the sender's lifted point between op 50 and op 51
  (`Arrival::sender_curve`) is not kept: S11's `agree` may lift again (one more lift per message).
* `SIGNAL_RECEIVE_JUMP` is a parameter (`SessionPublic.jump`, the agreed setting), not read by the
  worker.

## The parameters (to join with S11 and the runner)

S11 (`Flows/Curve.lean`) supplies a `Receive.Curve` per message:

```lean
inductive Scalar where
  | identity            -- our identity key (S11's shared account scalar)
  | own (slot : Nat)    -- an OWN scalar both parties hold: this party's 32 bytes in byte slot `slot`
  | fresh (slot : Nat)  -- a new scalar nobody knows: this party's 32 random bytes; same slot = same scalar
inductive Point where
  | handle (h : FieldH) -- a private u-coordinate in the field engine
  | base                -- u = 9
structure Job where
  scalar : Scalar
  point : Point
structure Curve where
  agree : List Job → Gen (List BoolH)
  signature : FieldH → FieldH → List FieldH → Gen (FieldH × FieldH)
  baseCheck : FieldH → Gen (FieldH × FieldH × FieldH)
  kinds : List RevealKind
  agree_reveals : ∀ jobs st, Reveals kinds (agree jobs st)
  signature_reveals : ∀ x y bits st, Reveals kinds (signature x y bits st)
  baseCheck_reveals : ∀ b st, Reveals kinds (baseCheck b st)
```

`Gen = StateT Receive.St Script`, `St = { table : Contacts.Table, pool : Conv.MaskPool }`: handle
ids from the contact table's counters (`Gen.allocB`, `Gen.allocF`), masks from the pool.
Specification S14 relies on:
* `agree jobs`: in the same field rounds, per job a FRESH 255-bit Boolean handle (marks never, not
  once) holding X25519(scalar, point) (clamped scalar, RFC 7748) as the little-endian value below p
  (P-F2W); inputs not freed; releases only under `kinds` (P-SPLIT/P-HINT kinds: `curveChecks`,
  `maskedDenominator`, `maskedFieldValue`, `scalarBitChecks`, …). The receive jobs: `[identity ·
  ephemeral]`, `[identity · sender]` (op 50); `sessionJobs` (op 51): dh1 = signed · sender, dh2 =
  identity · base, dh3 = signed · base, receiving = signed · ratchet, sending = fresh · ratchet,
  ratchet public = fresh · 9, dh4 = one-time · base (when named) — `service_kernels.h` line 367.
* `signature sx sy bits`: `[s]B − [h]A` (`xeddsa-check` on sx, sy and the 510 field bits flip ‖ h ‖
  s), fresh secret field handles; S11's hinted mode: the signature sum over the server table.
* `baseCheck b`: (valid, torsionX, torsionY) of the base key (`xeddsa-recover` then
  `receive-torsion`; hinted: `fast().torsion`), fresh secret field handles.
* `Curve.withPrograms agree kinds hagree pm` builds `signature` and `baseCheck` from the three V3
  programs through the `program` instruction (S14's code): S11 then supplies only `agree`.

The runner (`ReceiveBackend.Runner`): `run` (op 93 batches, the agreement per batch), the session
state `IO.Ref St`, `stashBits/Bytes/Elems` (store slots, decision D1), `random` (`Channels.random`),
`loaded` (the manifest's kernel names), `programMasks` (the loaded V3 programs' mask counts). S12's
`TlsBackend.revealed` gives `take` the received buffer's revealed bytes.

## The KEM boundary

Unchanged: Kyber-1024 decapsulation runs OUTSIDE the engines, in the local tool, with the key on its
standard input (`Channels.kemDecapsulate`, `Session/Receive.lean` `decapsulate`); `session` takes
its result as a `Secret Bytes`, as the legacy op 51 does, and enters it as party A's private input.

## What is proved, and what is not

Restated in `TlsMpc/Security.lean` section 7d (10 entries; compiled standalone from the same text:
standard axioms only — `propext`, `Classical.choice`, `Quot.sound`; the whole Security.lean was not
compiled on the branch, 4 GB cap).
* T3, kinds: `openFirst_reveals`, `session_reveals`, `take_reveals`, `drop_reveals`
  (`Registry.s14_flows_reveal`; the receive kinds 50-57 are registered labels).
* Gating: `sessionRest_refused` (a non-255 session status: the rest frees and opens nothing; the
  text kernel is not even run); every refusal is `refuse` (frees, silent: `refuse_silent`); the
  text's length/body/layout are opened only after its status opened 255 (by the script's
  structure), the record kept only after the access key's status opened 255.
* The wiring: the scripts build every stage's inputs with polymorphic functions (`staticIn` …
  `sessionInOf`, `heldOf`) that the byte-level pipeline of `Flows/ReceiveFlowProofs.lean` uses too;
  `pipeline_verified_wiring` (`rfl`): the session's `verified` is `receive-certificate-verified` on
  `receive-certificate`'s validity and signature — the hypothesis the kernel theorems took.
* T13: `pipeline_accept_certificate` (from `session_accept_certificate` with that hypothesis
  discharged by the wiring). T4-RECV: `pipeline_accept_outputs` (`session_accept_outputs`: the
  plaintext is libsignal's CBC decryption, the conversation record), `pipeline_text`
  (`text_status`, `text_accepted`: the opened text is the decrypted content's body),
  `pipeline_record` (`withAccessKey_status`, `withAccessKey_accepted`). Refusals:
  `pipeline_refused_text_zero`, `pipeline_certificateLength_zero`, `pipeline_contentShape_zero`,
  `pipeline_prekeyShape_zero`, `pipeline_prekeyIds_zero`, `pipeline_signalShape_zero`.
* `stageInstrs_bounded` (`Wire.Bounded` for every kernel stage); `dropScript_frees_wf`;
  `provisionalId_inj`, `provisionalId_high`.
* `receive-text`'s acceptance is used through theorem names only (`text_status`, `text_accepted`,
  `text_zero_unless_accepted`), never by unfolding `text` (another branch changes it).

## Rounds per received message vs the C++

A round = one batch with a data reply (an agreement plus a message delay); `k` = S11's rounds for one
`agree` call.
* op 50: 4 word→field (2 each: open, re-compare) + 2 field→word (2 each) + bits→field (1) + the
  certificate length, content shape, prekey shape, prekey ids (1 each) + 2·k = 17 + 2k (the
  `xeddsa-check` openings ride in a batch without a reply). The C++: the same conversions and
  openings except the ids (4 openings) = 20 + its agreements.
* op 51: 3 field→word (6) + signal shape, session status, text status, text, access-key status (5)
  + k = 11 + k (the programs' openings ride along). The C++: 6 + 1 + 1 + 4 + 1 = 13 + its agreements.
* op 48: 0 (no reply: a slice and a concat), op 49: 0.
Each batch costs one agreement more than the C++ (plan R1). Measured in the vectors: the stand-in
run of an accepted message (stand-in agreements, no rounds) plus a refused one is 43 rounds in all,
including the stand-in pool and buffers.

## Tests

* Lean vectors: `node_worker/tests/lean/S14Vectors.lean` → `node_worker/tests/s14_vectors.txt`
  (`lake env lean --run`, light). STAND-IN TABLES (clearly labelled in the file): the receive
  kernels are fixed-output stand-ins with the kernels' input widths and marks, the three programs
  stand-in programs of the right shapes (one `D` row), S11's agreements party A's inputs, the pool
  party A's consistent masks. An accepted first message (take ×2, openFirst, session) and a second
  envelope refused at the certificate length: 43 rounds, every batch admitted by `checkBatch`;
  `check parameters/opened/text/record/refused ok`.
* Stand-in two-party test: `cargo test --offline --no-default-features --test s14_pair` (2 tests):
  every reply of the two shells equals the Lean model's. All node_worker tests pass (13 suites).
* Loader: `receive_kernel_expected` / `receive_kernels_check` (a receive kernel with another layout,
  e.g. the session's status kept private, or an unknown one, or a missing
  `receive-certificate-verified`, fails closed); placeholder pins for `xeddsa-check`,
  `xeddsa-recover`, `receive-torsion` (fail closed until the V3 re-export); unit test
  `s14_receive_kernels_fail_closed`.
* Real engines, NOT RUN: `node_worker/tests/e2e_s14.py` — `layouts MANIFEST` (light, once the receive
  kernels are produced: every `receive-*` layout against the scripts' closed forms) and `flow`
  (heavy; refuses until the runner, S11 and the re-export exist).

## C++ that becomes deletable, and when

After (1) the controller-side runner sends Lean batches (op 93), (2) S11's `Curve` (agreements,
hinted variants) is merged, (3) the V3 re-export's pins of `xeddsa-check`, `xeddsa-recover`,
`receive-torsion` are in `loader.rs`, (4) the controller selects `ReceiveBackend.scriptApi`, and
`e2e_s14.py` passes in both modes:
* `service_kernels.h`: `Arrival`, `ReceivePrograms` (102-114), `server`, `server_*` members
  (115-127), `public_word` (128-129, if S13/S15 do not use it), `shaped`/`flag`/`width` (131-142,
  likewise), `envelope` member, `envelope_take`, `envelope_drop`, `envelope_open`,
  `envelope_session` (258-408).
* `tls_worker_v3.cpp`: ops 48-51.
* `tls_kernels.h` `take_range`: after S15 moves `bundle_take` too.
* The V2 `xeddsa-recover.flat`, `xeddsa-check.flat`, `receive-torsion.flat` and their SHA defines: with
  S11's switch to `program.rs`.

## New gaps (PROOF_GAPS.md style; to add under F — F22-F34 are S11's)

| # | Gap | Status |
|---|---|---|
| F35 | S14: T13 / T4-RECV are at the function level (the kernels' specifications connected by the scripts' own wiring functions), not through `jointRun`: that the model run of `openFirst` / `session` computes the pipeline needs S10's conversions' and S11's agreements' run-level specifications, and the receive kernels as model circuits with `.word` inputs and `bits` outputs (as F15). | open |
| F36 | S14: value-level T3 only per stage at function level (`pipeline_*_zero`: each opened shape / id is zero when its stage's validity is not 255) and by labels for a whole run (`openFirst_reveals`, `session_reveals`); no theorem that every release of a run against any adversary is a kernel's opened field on some input. | open |
| F37 | S14: WF proved only for the frees (`dropScript_frees_wf`); `takeScript`, `openFirst`, `session` pass `checkBatch` on every batch of the vectors (stand-in tables), no theorem. | tested / open |
| F38 | S14: the output widths the scripts slice by (`Receive.*Out`) are closed forms checked against the kernels by `loader.rs` `receive_kernels_check` at start and by `e2e_s14.py layouts` (not run), not by a Lean theorem about the kernels' `outputs`. | tested / pending |
| F39 | S14: `Flows/ReceiveBackend.lean` is unverified IO glue; `Runner` and S11's `Curve` have written specifications only; nothing selects it. The KEM decapsulation stays a local tool (`Channels.kemDecapsulate`). | open (engineering) |
| F40 | S14: the vectors and `s14_pair.rs` use STAND-IN kernel tables, programs, agreements and pool (an accepted message needs a genuine envelope); `e2e_s14.py` not run; the receive programs' pins are placeholders. | tested / pending |
| F41 | S14: `Reveal.prekeyIds`, `sessionStatus`, `receivedText` are still made by legacy-style wrappers in the IO glue (`Reveal.*`); their bounding theorems are now the S14 ones (section 7d) plus the kernel ones. `certificateLength`, `contentShape`, `prekeyShape`, `signalShape`, `accessKeyStatus` have labels (released inside the scripts) but no `Reveal` function (nothing hands them to the controller). | note |

Lines of PROOF_GAPS.md this stage closes (in part):
* **E2** (worker wiring hypotheses), for the receive flow: the session's `verified` binding is no
  longer a hypothesis — `pipeline_verified_wiring`, `pipeline_accept_certificate`
  (`s14_verified_wiring`, `s14_accept_certificate`); every other receive kernel's inputs are the
  scripts' wiring functions (`staticIn` … `accessKeyIn`). Residue: through `jointRun` (F35).
* **E8** (receive, accept direction), the composed part: an accepted message's text is the
  decrypted body and the record is the access-keyed conversation, for the scripts' wiring
  (`pipeline_text`, `pipeline_record`, `pipeline_accept_outputs`). The converse for a genuine
  envelope and the Prop forms of the layout masks remain open as E8 says.
* **G (receive kinds)**: `prekeyIds`, `sessionStatus`, `receivedText` gain script-level bounds
  (section 7d); no new G line.

## Checks

* Every module compiled with `lake env lean -o` one at a time (guarded 4 GB): `Engine/Labels`,
  `Flows/Receive`, `Flows/ReceiveBackend`, `Flows/ReceiveFlowProofs`, `Flows/Registry`. Security.lean's
  section 7d compiled standalone (same text): standard axioms only. `scripts/check_axioms.py` NOT run
  (Security.lean as a whole exceeds the 4 GB cap; as S10, S12).
* `scripts/lint_node.py`: 0 findings.
* `Labels.kinds` / `all` grew (kinds 50-57): every module importing `Engine/Labels.lean` needs a
  rebuild after the merge (as S12's F21).

## Merge notes: files touched

* New Lean: `TlsMpc/Node/Flows/{Receive,ReceiveFlowProofs,ReceiveBackend}.lean`.
* Changed Lean: `TlsMpc/Node/Engine/Labels.lean` (labels of kinds 50-57; `kinds`, `all`,
  `all_codes`), `TlsMpc/Node/Flows/Registry.lean` (imports `Flows.Receive`; S14 entries in
  `declared`; `s14_flows_reveal`), `TlsMpc/Security.lean` (imports `Flows.ReceiveFlowProofs`;
  section 7d; section 8's T13 and T4 items; `#print axioms` lines), `REORGANIZATION_PLAN.md` (S14
  status).
* Not touched: `TlsMpc/Node/Types.lean` (no new kind: all receive kinds existed), `Reveal.lean`, the
  controller, `Main/Session/Flow/*Legacy/Channels/Messages/Policy`, the S10/S12 flow files, every
  module an emitter imports (`ReceiveFirst`, `ReceiveKernels`, `ReceiveProofs`, the KernelSpecs
  only imported), the C++.
* Rust: `node_worker/src/loader.rs` (`Kernels::names`, `receive_kernel_expected`,
  `receive_kernels_check`, three placeholder program pins, a test); new
  `node_worker/tests/{s14_pair.rs,s14_vectors.txt,e2e_s14.py,lean/S14Vectors.lean}`.
* With S11: `Receive.Curve` above (its `agree` is S11's; `Curve.withPrograms` for the non-hinted
  path); `Flows/Receive.lean` imports neither `Flows/Curve` nor `Local/{Field,Edwards}`.
* After the V3 re-export: paste the pins of `xeddsa-check`, `xeddsa-recover`, `receive-torsion` into
  loader.rs (replacing `PIN_FROM_REEXPORT`).
