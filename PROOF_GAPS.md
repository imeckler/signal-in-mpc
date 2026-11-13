# Proof gaps: everything that is assumed, tested-only, or proved about a model

Started 2026-11-12 at the owner's request ("make sure you're recording all these proof gaps.
we're going to close them later"). One list, so nothing reported by a proof engineer is lost.
`TlsMpc/Security.lean` section 8 is the in-Lean list of open items and names the theorems;
this file is the plain-language index, grouped by what it would take to close each gap.
Kernel defects (as opposed to missing proofs) are in `NEEDS_REVIEW.md` section 3f.

Status words: **open** (nothing proved), **model** (proved about a model or twin of the code,
not the code that runs), **conditional** (proved under a stated hypothesis), **tested** (checked
by tests or vectors only), **assumed** (a cryptographic or engineering assumption we do not plan
to prove soon).

When a gap is closed: move its line to the "Closed" section at the end with the theorem name
and commit, do not delete it.

## A. The trusted base (assumed; not planned to be proved)

| # | Gap | Status |
|---|---|---|
| A1 | The two engines (EMP authenticated garbling, MP-SPDZ field arithmetic) compute what they are asked, reveal nothing else, abort on cheating. `Engine/Model.lean` `idealStep` is the definition of "ideal". | assumed |
| A2 | The engine C ABI glue (`engine_abi.cpp`, `legacy_abi.cpp`) and, until S10–S16 land, the C++ sequencing behind `legacy_dispatch`. | assumed; shrinks as flows move to scripts |
| A3 | Underlying cryptography: OT, garbling, AES, SHA-256; the statistical parameters. | assumed |
| A4 | SHA-256 commitments are hiding and binding (`idealCommit`): used by joint randomness, the offset agreement, cut-and-choose. Peer's value fixed per message; an adaptive peer across messages is not covered. | assumed |
| A5 | The Lean compiler and runtime; the I/O code in `TlsMpc/Node/Channels.lean`. | assumed |
| A6 | The five database nodes (`secret-shared-db`), a separate Rust project. | outside this repository |
| A7 | No end-to-end theorem: there are theorems per kernel, per flow and per channel and one reveal list, but no single statement "the server plus one corrupted node learn nothing about the contact list beyond the reveal list", with a simulator. | open |

## B. Rust code that implements a Lean definition

| # | Gap | Status |
|---|---|---|
| B1 | `node_worker/src/handles.rs` `check` is a line-by-line transcription of Lean's `Engine.check`; equality is tested on Lean-generated vectors (137 batches), not proved. Idea: extract and prove equal. | tested |
| B2 | `interp.rs` decode/encode/skeleton, `program.rs` (V3 parser and evaluator), `loader.rs` pins and manifest agreement, `agree.rs`: tested against Lean vectors and real engines. | tested |
| B3 | The Rust and C++ loaders parse circuit and layout files the way Lean's `parseFlat` / `parseLayout` do (what remains of T2 after the emitter batch; `selection` is also trusted). | assumed |
| B4 | `node_stock`: the Rust store agrees with the Lean journal/use model on 312 generated schedules. | tested |
| B5 | `node_daemon` (scheduler, peer link, replay cache) and the rest of `node_worker` (sockets, SOCKS, control link). | tested |
| B6 | Real-engine tests not yet run: `program` (opcode 22) flows (need exported V3 files); `openBoolTo` (the test manifest has no such output). | open (testing) |

## C. Theorems about a model instead of the code that runs

| # | Gap | Status |
|---|---|---|
| C1 | Reveal policy `t1_all` is about `recordLoop`/`streamRun`, a pure transcription of the session's record loop (`Session/Common.lean` `record`, in `SessionM`). Differences: the real loop gets bytes from the engines' `revealRange` (assumes nothing is revealed beyond the record's end); completed envelopes go to `c.envelope` before being cleared; no fuel. | model |
| C2 | Between records the session applies `replies`, `requests := []`, `expect`; the last two keep the policy's view by `rfl`; the lemma that `replies` keeps it timed out and is not proved. | open (small) |
| C3 | Ordering (ORD-1, ORD-2, T11): proved about monad-generic twins shown equal to the deployed definitions (`*_deployed`); carrying a property from the model monad to `SessionM` relies on parametricity, which Lean does not state. Fix specified in `Session/Events.lean`: make each twin the definition. One piece of work with C1. | model |
| C4 | Cut-and-choose counting bound (`proofs/`): proved for a model (one uniform permutation, detection rules). That `dyn_word_mask.h` / `dabit_generator.h` implement it — P-CUT (d), (e), and the composition of the two challenge permutations — is S10's job. | model |
| C5 | Stock T14: about the journal/use model; the engine instruction `stockUse` and the C ABI export/import are specified, not built. Restoring disk AND boot memory together defeats both barriers (`full_rollback_reuse`): deployment must forbid whole-machine snapshots or add the peer cross-check. | model; one known limit |
| C6 | Envelope walk `envelope_payload_unrevealed` is about `envWalk`; linked to the controller's steps by `ReceiveInvariant` (`env_reveal`, `env_pass`). Covered by `t1_all` now; listed for completeness. | closed by `t1_all` (model, see C1) |

## D. The reveal policy and parsers (what the nodes see of server bytes)

| # | Gap | Status |
|---|---|---|
| D1 | Start of a connection: `t1_all` starts after the upgrade; the HTTP head is proved separately (`upgrade_run_safe`); not joined (missing: the head bytes leave the frame parser at a boundary; `payloadByte` keeping `upgraded`/`terminator` in general). | open |
| D2 | The one-byte allowance: the byte right after the first malformed byte can be revealed. By design (removing it costs a round trip per response field). | accepted |
| D3 | WebSocket frame parser: "accepted only if well-formed" as one whole-frame theorem (each malformation has its rejecting step); `drun 0 r = some 0 → Utf8 r` (only the converse is proved). | open |
| D4 | Chat-response parser (`TlsChatResponse`): general decoding of id, status, message, headers and `finish`'s checks are pinned by three kernel-checked vectors only; a general fail-closed statement for malformed responses (two cases proved). | tested / open |
| D5 | TLS record splitter applies the 2^14+256 limit to plaintext handshake records (RFC says 2^14); `receiveHello` checks it. | minor |
| D6 | Request builders: the 200 reply theorem is conditional on the id found by `scan` being in range (loop invariant not proved); `replies` (pong/close echoes) not covered in `RequestProofs` (covered per frame in `ParseWebSocketControl*`). | conditional |
| D7 | Hardening not done because proofs unfold these definitions: `varint` emits a malformed value at ≥ 2^70; `clientFrame` writes a one-byte length unchecked; builders accept an empty envelope; slot ranges exceed the server's types. | open (hardening) |

## E. Kernels (what the circuits compute)

| # | Gap | Status |
|---|---|---|
| E1 | Most kernel specs are stated against the kernel's own composition on concrete values, not an independent standard. Exceptions: TLS handshake kernels (RFC transcriptions), seal kernels (sealed-sender reference), request sealers, KEM. | by design; note |
| E2 | Worker wiring hypotheses in the end-to-end theorems: the worker passes frame, mask, offsets and envelopes unchanged (`built`, `hframe`, `hmask`, `paired`); wires each device's establishment outputs into its seal (`wired`); binds the kem kernels' named outputs to inputs; binds head/before/item/after/end for bundle-slot. Goes away as those flows become scripts. | conditional |
| E3 | Sealed sender reference `sealV1` / `sealV1Typed` and the PreKey message framing are transcriptions of libsignal, not machine-linked to it. The ratchet step is checked against the repository's own `SpqrSend.canonical`. | assumed (transcription) |
| E4 | The X25519 agreements and KEM secret/ciphertext are inputs to the send theorems, not proved values. | open |
| E5 | Kyber-1024: kernels equal the repository's reference `MlKem.encapsulate` (proved); that reference is Kyber-1024 rests on test vectors against libcrux; the 2^-105 sampling-failure probability is a calculation. | tested |
| E6 | `receive-text`: length prefixes of three or more bytes are refused where a protobuf decoder accepts (completeness, not a leak). Fix for the over-long body is in the emitter batch (takes effect after re-lowering). | open (completeness) |
| E7 | `bundle-slot`: theorems assume no field of the item starts with a NUL byte (no JSON text does); the response template is what Signal-Server writes. | conditional |
| E8 | Receive, accept direction: the converse for a genuine sender's envelope (needs AES-CTR involution, matching varints, DH agreement between the sides); Prop forms for multi-byte counters (`varintValue` widths 2–5), `canonicalRange`, the `prekeyMask`/`signalMask` layout masks (ReceiveFirst's import closure is too large to compile into `proofs/`); accept-direction value theorems for `contentShape`'s flags and `receive-content`. | open |
| E9 | `signal-widths`, slot encoders, request frames: done. `reply`, `keepalive`, `ping` frames: done (D6 for the caveat). | closed, listed for the record |
| E10 | A refused send overwrites the stored text slot (ratchet state preserved, record not byte-identical). Statements say "preserves the ratchet state". | accepted; note |

## F. Engine scripts and flows

| # | Gap | Status |
|---|---|---|
| F1 | `Contacts.Loaded`: the circuits named `contact-key` / `contact-seal N` / `contact-open N` compute their Lean kernels. Partly discharged by the emitter batch's `lowerKernel_loaded`; remainder is B3. | conditional |
| F2 | `FieldInverse` (Fermat for p) is a named hypothesis in the main package (`masked_div`, `opening_bijective`, `eval_ofArtifact`, …); `proofs/` can discharge it with `toZMod_inverse`. | conditional (easy) |
| F3 | `decodeBatch_encodeBatch` needs batch length < 2^64; not shown for the sender. | open (small) |
| F4 | The model does not enforce marks, `once`, or handle freshness; theorems transfer because they are about accepted results or are prefix-closed (argued in `Model.lean`'s header). | argued |
| F5 | Legacy flows are still C++ operations behind `Flows/*Legacy.lean`: their reveals are bounded by kernel theorems, not by script theorems, until each moves (S9 switch, S10–S16). Script versions exist for ops 33, 36–38, 40, 45, 52–54, 63 but the controller does not use them yet. | open (engineering) |
| F6 | No `RevealKind` yet for `program` openings; chosen when a flow uses them (S10). | open (small) |
| F7 | S10 P-CUT: closed (see Closed). Scope notes that remain: `generate_hides` is for fixed challenge randomness of the honest party; a bit block's reference below 32 (probability 32/P) is not hidden — its run aborts at the flags; no one-statement value disclosure (P-CUT (b)) for the whole run. | closed, with scope notes |
| F8 | S10 well-formedness: `generate_wf`, `generate_wf_profile`, `profile_sizes`, `sharedBits_wf` proved. Still missing: `_wf` for `wordToField`, `fieldToWord`, `bitsToField`, `Account.openStep` (their test-instance batches pass `checkBatch`). | partly closed |
| F9 | closed (see Closed). | closed |
| F10 | S10: `check_axioms.py` not run on the branch (a rebuild exceeded the 4 GB cap); its Security.lean section was compiled separately with standard axioms only. Run after the merge. | pending check |
| F11 | S10: field programs `field-bit-check`, `field-bit-xor`, `field-recompose` carry a placeholder pin until the V3 re-export (fail closed); the real-engine fixture `e2e_s10.py` has not been run. | pending |
| F12 | S10 and the Mathlib counting model: `generate_sound` (in any returning run the bad set is fixed by the adversary's replies before the challenges; (d), (e), (f) hold), `arrangement_perm` / `arrangement_cut` / `arrangement_slot` (the two challenge permutations compose into the model's single arrangement, a permutation), `bucket_uniform`. Still argued only: that the arrangement is uniform when π₁, π₂ are (a K!-to-one map); that π₁, π₂ are uniform and independent of the bad set (`IdealCommit`, SHA-256 as a random oracle, the 2⁻⁶⁴⁰ abort term). | partly closed |

S12 (branch `s12-tls`, not merged; GHASH shares and TLS as scripts):

| # | Gap | Status |
|---|---|---|
| F13 | T4-TLS is at function level only, not through `jointRun`. The binding of `gcm-check`'s output to `tls-open-typed`'s `accepted` input relies on the concat order: tested, not proved. | open |
| F14 | WF not proved for `roundScript`, `sealClassScript`, `openScript`, `revealScript`, `parserScript` or the handshake scripts (vectors pass for seal, open, GHASH; the handshake scripts are untested). WF proved for 7 scripts. | tested / open |
| F15 | `tls-derive` has a `.word` input, so there is no model circuit for it and no value statement for `deriveScript`. | open |
| F16 | The class seal's composition is not stated through the script. | open |
| F17 | `Flows/TlsBackend.lean` is unverified IO glue; `Runner` and `KeyAgreement` have written specifications only (the key agreement is S11's `Curve.agree`). | open (engineering) |
| F18 | `Wire.Bounded` not shown for the S12 scripts. | open (small) |
| F19 | S12's pair test uses table stand-ins for circuits; `e2e_s12.py` not run; the handshake fixture not moved (needs the controller-side runner and S11). | tested / pending |
| F20 | P-GHASH (e) not restated for the scripts; (a) over a whole `ensure` through `jointRun` not proved; value-level T3 for `roundScript` with A honest not proved. P-GHASH (c) IS closed for the Lean code: `seal_is_record`, `check_accepts`. | open |
| F21 | Security.lean not compiled as a whole on the S10/S12 branches (4 GB cap during the re-lowering); every module importing `Labels` needs a rebuild after the merges. | pending check |

S11 (branch `s11-curve`, not merged; local arithmetic and curve flows as scripts):

| # | Gap | Status |
|---|---|---|
| F22 | Honest runs through `jointRun` proved only for `splitAgree`; for `splitBegin`, `agree`, `offsetPrepare`, `offsetStep(Fast)`, `lift`, `tables`, `agreeHinted`, `agreeAffine`, `signatures`, `torsion`, `prepareContacts` they are checked by Lean model vectors (51 value checks) only. | tested |
| F23 | No `_wf` theorem for any S11 script (every batch of the vectors is admitted). | tested |
| F24 | Value-level T3 for the curve flows (only the kinds each flow releases under are proved). | open |
| F25 | Model form of `commit_open_sound` for `pointExchange` (the gate only is proved). | open |
| F26 | `randomPoint` (r·B + t·T₈) is uniform on the curve group, as `curve_hinted_Z_uniform` assumes. | assumed |
| F27 | P-HINT (c), (d) composed with the runs. | open |
| F28 | `den ≠ 0` (complete addition on curve points) assumed in `addU_montU`; proved in `proofs/`. | conditional |
| F29 | Local arithmetic agrees with a reference library only on vectors (curve25519-dalek; no libsodium binding offline): encode/decode, validity, lift. | tested |
| F30 | `shapeOf` mask counts are read from compilations (a wrong count fails closed). | tested |
| F31 | `e2e_s11.py` not run; S11's field-program pins are placeholders until the V3 re-export. | pending |
| F32 | Op 66's contact-table glue (view kernel, word/field conversions, `sender_public`) is not scripted; left for the flow-API switch. | closed on `scripts-stack` (STACK_NOTES section 8): `Flows/ContactsPrepare.lean` (`prepareStatus_iff`, `commit_prepared`, `commit_other`, `commit_inv`, `prepareOneG_reveals`, `senderPublicG`); non-hinted path; WF and values through `jointRun` open (stack J15, J16) |
| F33 | Local functions return `none` on an impossible zero Z or a `sqrt` failure: liveness rests on facts proved in `proofs/`. | conditional |
| F34 | `proofs/` should state `Ed25519.recode = Curve.recode` once it imports the S11 modules (same equations; by induction). | open (small) |

S14 (branch `s14-receive`, not merged; receiving a first message as scripts):

| # | Gap | Status |
|---|---|---|
| F35 | T13 and T4-RECV for the script pipeline are at function level, not through `jointRun`. | open |
| F36 | Value-level T3 for every release of a whole receive run against any adversary (kinds are proved: `openFirst_reveals`, `session_reveals`; refusals open zeros: `pipeline_refused_*_zero`). | open |
| F37 | WF for `takeScript`, `openFirst`, `session` (the vectors admit every batch). | tested |
| F38 | The receive kernels' output widths are not proved against the kernels in Lean; the Rust loader checks them at start (fails closed). | tested |
| F39 | `Flows/ReceiveBackend.lean` is unverified IO glue; `Curve` (S11) and `Runner` are parameters with written signatures. | open (engineering) |
| F40 | S14's vectors use labelled stand-in tables (an accepted message at test size is impossible: it needs a genuine envelope); `e2e_s14.py` not run; placeholder pins for the three receive programs. | tested / pending |
| F41 | The `Reveal` wrappers for the receive results are applied in the backend glue, not by the scripts (see S14_NOTES.md). | note |

Closed in part by S14: E2 for the receive flow — the wiring of `verified` from
`receive-certificate-verified` is proved for the script (`pipeline_verified_wiring`,
`pipeline_accept_certificate`, no wiring hypothesis left); E8's composed part
(`pipeline_accept_outputs`, `pipeline_text`, `pipeline_record`).

S15 (branch `s15-refresh`, not merged; device refresh as scripts):

| # | Gap | Status |
|---|---|---|
| F42 | The KEM composition for the script (`kemFlow_pipeline`, `kemFlow_accept`, `kemFlow_invalid`) and the session step are at function level, not carried through the model's `run` (the slot parse IS: `parse_fields`). | open |
| F43 | Width hypotheses `KemWidths` and `SessionWidths` (the kernels' output widths) are assumed in Lean; the Rust loader checks layouts at start. | conditional |
| F44 | WF not proved for `fetchScript`, the establishment scripts, `scratchSealScript`; `Table.Inv` not proved preserved by `opCommit` (proved: `shapeScript_wfp`, `takeScript_wfp`, `RState.Inv.empty`, `opDrop_inv`). | tested / open |
| F45 | Joins: S11's `CurveOps` (`lift`, `check`, `agree`, with its `Reveals` as a hypothesis) and S13's send (must bind `bundle-seal`'s `conversation`/`pending` to the handed records) are parameters; `first_wired` assumes that binding. | conditional |
| F46 | No `RefreshBackend.lean` with the legacy `Flow.Refresh.*` signatures: callers cannot switch yet (mapping written in S15_NOTES.md). | open (engineering) |
| F47 | Value-level T3 for a whole refresh run (kinds proved: `opEstablish_reveals`, `refresh_viewD_kinds`). | open |
| F48 | S15's vectors use labelled stand-in circuits (Kyber and the bundle parser have no test-size parameters); `e2e_s15.py` not run. | tested / pending |
| F49 | After merging the emitter batch (slot filler NUL), `Refresh.slotFiller` must change from `'0'` to `0` (one line; proofs use kernel theorems by name). | merge task |
| F50 | Security.lean not built as a whole on the branch (4 GB cap). | pending check |

Closed in part by S15: E2 — the 21 KEM name-binding hypotheses of `kernels_compose` are proved
for the script's wiring (`kemFlow_pipeline`), the bundle-slot head/before/item/after/end bindings
(`slotInput_value`, `slot_inputs`, `parse_fields`), and the script's part of `wired`
(`first_wired`, `stored_record`). E7 — the splice and the declared digit counts come from one
value, so the inconsistent-width combination cannot be formed (`slotInput_value`). I4 — ORD-2 at
script level: `opCommit_entry` (the only operation that changes an entry), `opDrop_table`.

S13 (branch `s13-send`, not merged; send as scripts):

| # | Gap | Status |
|---|---|---|
| F51 | T4 for send (`send_accepted`) is at function level, not through `jointRun`. | open |
| F52 | No composed headline for op 61 (several devices); the `bundle-seal` output slicing is unproved. | open |
| F53 | `shapedCircuit` (the model circuit for kernels with 255-bit word inputs) extends the T2 trust (F1 / B3). | assumed |
| F54 | WF and `Wire.Bounded` for ops 61 and 62 (tested by vectors; proved for op 41, the request scripts and the request record seal). | tested |
| F55 | `Flows/SendBackend.lean` is unverified IO glue; S11's `Curve` half (`ephemeral`, `staticAgreement`, `senderPublic`) is a parameter; `Reveal.ephemeralPublic` to be added by S11; the runner's handle counters must be joined with `Contacts.Table.ctr`. | open (engineering) |
| F56 | S13's pair test uses stand-in circuits; `e2e_s13.py` and the harness not run. | tested / pending |
| F57 | The refusal statement (`seal_refused_silent`) is structural (what the script does), not a full statement about the adversary's view. | open |
| F58 | `bundleEnvBytes` is not proved equal to the kernel's envelope length. | open (small) |
| F59 | ORD-1 not restated for the script path; Security.lean not compiled as a whole on the branch. | pending |

Closed by S13: E2 for the send path — `built`, `hframe`, `hmask` are not hypotheses of
`send_accepted` (the kernels' inputs are the script's own concatenations); `hframe`, `hmask`,
`paired` gone for `bundle-request-ctr` (`bundleRequestCtr_value`, `devicesName_paired`). What
stays in E2: `wired` (S15, partly closed there) and the kernels' width assumptions. E4 narrowed:
the agreements are still inputs, now with a written join specification. A behaviour difference
from the C++: with several devices, envelopes are opened only once EVERY status is 255 (the C++
opened device k's envelope before checking device k+1).

Partly closed by S12: C1's caveat "the engine reveals nothing beyond the record's end" is proved
for the script backend (`reveal_value`, `range_value`); it stays assumed for legacy op 43. G1
`handshakeShare`: the random half is P-RAND, the key-share half is S11's P-SPLIT.

## G. The reveal list (`TlsMpc/Node/Reveal.lean`): kinds with no bounding theorem

| # | Kind | Status |
|---|---|---|
| G1 | `handshakeShare` (client key share and hello random) | open |
| G2 | `assignStatus` (a provisional contact took its id; one bit) | open |
| G3 | `prepareStatus` (per-contact status byte). The statement needed exists: the lift is valid exactly when the coordinate is on the curve (`montQ_square_iff`, `liftPoint_valid_point` in `proofs/`). Attach it. | open (easy) |
| G4 | `jointRandom` for the legacy op 33 (the script version has P-RAND) | closes when the script replaces the op |
| G5 | `serverBytes` is bounded by T1 (section D, C1). | see D, C1 |

## H. The curve and probability (`proofs/`, Mathlib)

| # | Gap | Status |
|---|---|---|
| H1 | Group order `#E = 8ℓ` (point counting). So: not shown that every point killed by ℓ is a multiple of the base point; the cofactor claim of `edwards-torsion-hinted`. | open (hard) |
| H2 | A recipient's point is nonzero and killed by ℓ: hypothesis of the instantiated offset theorems (proved for the base point). | conditional |
| H3 | X25519 for inputs on the quadratic twist (the complete-addition construction does not apply: a = −2 is not a square). | open |
| H4 | The C++ `step` / `step_inputs` / `Local/Edwards` implement the Lean `recode` and programs (the Lean rule copies the C++ line for line). Closes in S11. | open until S11 |
| H5 | Offset agreement: two aborts not modelled (`mine = peer`, probability 2^-256; τ = 0, 2^-252); P-OFFSET about the C++ `step`. | open (small) |
| H6 | P-HINT (b) for the script (S11). | open until S11 |
| H7 | Rotation: the shuffle is uniform assuming SHA-256 keyed by the seed is a PRF (stated, not used in proofs). | assumed |

## I. Session-level and reporting

| # | Gap | Status |
|---|---|---|
| I1 | Non-recovery send path checks only this party's database acknowledgement before sending; "the send is a joint computation, so it cannot leave if the other party failed" is an argument, not a theorem. | argued |
| I2 | T11 at the `DaemonLine.jobResult` / final-report level (results are written in one place; `serve` resets them per job): argued. T11's second half (each entry comes from `Recovery.onSend` / `onFetch`): not done. | argued / open |
| I3 | `bumpIn_absent`: a contact missing from the version list would make every store write the same version (the nodes refuse the repeat; the send fails, no key reuse). Deployed paths always add contacts first; harden. | open (hardening) |
| I4 | ORD-2 to be rechecked after S15 (device refresh moves to scripts). | pending |
| I5 | Settings agreement, typed messages, `Secret`, flow-calls, session-state: enforced by types and the lint (`scripts/lint_node.py`), not by theorems. | by construction / lint |

## J. Specifications that are transcriptions or derived from source reading

| # | Gap | Status |
|---|---|---|
| J1 | Signal-Server request formats, the WebSocket protobuf, routes: reference encoders written from the Signal-Server sources on disk (paths cited in `Policy/RequestSpec.lean`). | assumed (transcription) |
| J2 | RFC transcriptions: TLS key schedule and record layer, WebSocket framing and accept, SHA-1, base64, UUID text, UTF-8, close codes. Test vectors from the RFCs are proved where they exist. | assumed (transcription) |
| J3 | The official-client reference in `CLIENT_FINGERPRINT.md` is derived from source, not a capture (see `NETWORKING_FINDINGS.md` for what only a capture can settle). Not a proof matter; listed so it is not forgotten. | open (measurement) |

## Closed

(Move lines here with theorem name and commit when a gap is closed.)

| # | What was closed | Theorems | Where |
|---|---|---|---|
| F7 | P-CUT (c): the adversary's whole view of mask generation is unchanged under re-randomising the honest party's candidates while the output masks move to any target (the 7.0 bijection form); the bit-block flag under a shift. P-CUT (f), (g) at run level against any adversary. P-CUT (a) for a whole honest run, deployed profiles. | `generate_agree`, `generate_hides`, `reRand_inverse`, `reRand_lt`, `moveRef_32`; `finishPhase_sound`, `mask_consistent`; `generate_honest`, `generate_honest_profile` | branch `s10-conversions` (commits a642a82 … 4dbd7b3), not yet merged |
| F9 | P-BITS at run level; P-B2F (a) for a whole bundle through `jointRun`. | `sharedBits_sound`, `sharedBits_honest`, `b2f_honest` | branch `s10-conversions` (50055a8, 5c66a85), not yet merged |
| H4 | There is no C++ step any more: the offset flow uses the Lean `Curve.recode`, and `Local/Edwards` uses the programs' own formulas. | `recode64_value`, `stepIns_window`, `step_tableSum`; `add_eq`, `toAffine_eq`, `montU_eq` | branch `s11-curve`, not yet merged (residue: F34) |
| H5 (part) | P-OFFSET about the step is closed; the two unmodelled aborts remain open. | `ephemeralKey_spec`, `stepIns_window` | branch `s11-curve` |
| H6, G3 | P-HINT (b) for the script and the `prepareStatus` reveal: the status is 255 exactly when the coordinate's curve polynomial is a nonzero square. Conditional on H-QR and Euler's criterion as named hypotheses, both theorems in `proofs/`. | `lift_valid_sound`, `lift_valid_complete`, `prepareStatus_iff` | branch `s11-curve` |
| (S12) | P-GHASH (c): the "halves" hypothesis of the record seal. | `seal_is_record`, `check_accepts` | branch `s12-tls`, not yet merged |
| (P1) | T1 for all streams after the upgrade (about the model loop; see C1, D1 for what remains). | `ReceiveLoop.t1_all` | main tree, uncommitted pending the merge |
