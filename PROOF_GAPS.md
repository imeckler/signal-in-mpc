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
| A8 | Instantiation of a monad-generic definition (what remains of C1 and C3): the session's ordering functions (`storeSoftG` … `serveG`) and its record loop (`RecordLoop.run`) are each ONE definition, deployed at `SessionM` with the real operations and proved about at a pure model monad for every operations record. That the definition, run at `SessionM`, makes the calls its model instance makes when every call is answered alike is the free theorem of its type (it uses only `pure`, `bind`, `throw`/`tryCatch`, `get`/`set`, `read`, `for`/`while`); Lean does not state free theorems and cannot observe `IO`. Trusted with the compiler (A5). Also trusted there: the real operations do what their events name (`Session/Events.lean`, header, items 1 and 3; item 2 is checked by `lint_node.py` `ordering-sites`). | assumed |

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
| C1 | closed (see Closed): T1 is about the loop the session runs (`RecordLoop.run`); the instantiation step is A8, the engines' reveal assumption is D8. | closed |
| C2 | closed (see Closed). | closed |
| C3 | closed (see Closed): the ordering theorems are about the deployed definitions; the instantiation step is A8. | closed |
| C4 | Cut-and-choose counting bound (`proofs/`): proved for a model (one uniform permutation, detection rules). That `dyn_word_mask.h` / `dabit_generator.h` implement it — P-CUT (d), (e), and the composition of the two challenge permutations — is S10's job. | model |
| C5 | Stock T14: about the journal/use model; the engine instruction `stockUse` and the C ABI export/import are specified, not built. Restoring disk AND boot memory together defeats both barriers (`full_rollback_reuse`): deployment must forbid whole-machine snapshots or add the peer cross-check. | model; one known limit |
| C6 | Envelope walk `envelope_payload_unrevealed` is about `envWalk`; linked to the controller's steps by `ReceiveInvariant` (`env_reveal`, `env_pass`). Covered by `t1_all` now (about the deployed loop since C1 closed); listed for completeness. | closed by `t1_all` |

## D. The reveal policy and parsers (what the nodes see of server bytes)

| # | Gap | Status |
|---|---|---|
| D1 | closed (see Closed): T1 from the first byte of a fresh connection, against `ReceiveSpec.classify` (`ReceiveStart.t1_start`). | closed |
| D2 | The one-byte allowance: the byte right after the first malformed byte can be revealed. By design (removing it costs a round trip per response field). | accepted |
| D3 | WebSocket frame parser: "accepted only if well-formed" as one whole-frame theorem (each malformation has its rejecting step); `drun 0 r = some 0 → Utf8 r` (only the converse is proved). | open |
| D4 | Chat-response parser (`TlsChatResponse`): general decoding of id, status, message, headers and `finish`'s checks are pinned by three kernel-checked vectors only; a general fail-closed statement for malformed responses (two cases proved). | tested / open |
| D5 | TLS record splitter applies the 2^14+256 limit to plaintext handshake records (RFC says 2^14); `receiveHello` checks it. | minor |
| D6 | Request builders: the 200 reply theorem is conditional on the id found by `scan` being in range (loop invariant not proved); `replies` (pong/close echoes) not covered in `RequestProofs` (covered per frame in `ParseWebSocketControl*`). | conditional |
| D7 | Hardening not done because proofs unfold these definitions: `varint` emits a malformed value at ≥ 2^70; `clientFrame` writes a one-byte length unchecked; builders accept an empty envelope; slot ranges exceed the server's types. | open (hardening) |
| D8 | `t1_all` assumes `ReceiveLoop.Faithful` of the engines: the length probe returns the record's length, `revealRange offset count` returns that length and exactly `(record.drop offset).take count`, revealing those positions and no others, and the other record operations reveal nothing. A theorem for the S12 script backend (`reveal_value`, `range_value`, branch `s12-tls`, not merged); an assumption on the engines (A1) for the legacy operation 43 the controller uses today. | assumed (legacy) |
| D9 | Behaviour note (C1's refactor): the record loop now has fuel, the record's length plus one steps (`RecordLoop.run`), which never runs out when the engines report the same length at every reveal (`loop_fuel`, `run_fuel`). If an engine reported a longer record at a later reveal than at its length probe, the loop now fails ("the record's length changed while it was read") where the old `while` loop read on. | accepted (fails closed) |

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
| F13 | closed (see Closed): `seal_honest`, `open_binding`, `open_binding_honest`, `open_class`, `open_rejected_run`. | closed |
| F13a | The handshake record, Finished, client Finished, reveal, range and update scripts have WF and function-level values only, no `jointRun` theorem (`derive_honest` is done). | open (small) |
| F14 | closed (see Closed): WF for every S12 script on every branch. | closed |
| F14a | The S12 WF theorems take each kernel's signature as explicit marks (`typedMarks`, `frameMarks`, …); that these equal `circuitOf`'s `kernelMarks` is not proved (the Rust loader's `tls_script_kernels_check` compares them at start). | conditional |
| F15 | closed: `derive_out`, `derive_honest` (via a `shapedCircuit` for the word input). | closed |
| F16 | closed: `sealClass_kernelOut`, `sealClass_is_record`. | closed |
| F17 | `Flows/TlsBackend.lean` is unverified IO glue; `Runner` and `KeyAgreement` have written specifications only (the key agreement is S11's `Curve.agree`). | open (engineering) |
| F18 | closed: `Instr.Bounded` on every branch of all 17 S12 scripts (`Flows/TlsBounded.lean`). | closed |
| F19 | S12's pair test uses table stand-ins for circuits; `e2e_s12.py` not run; the handshake fixture not moved (needs the controller-side runner and S11). | tested / pending |
| F20 | closed (see Closed): `ensure_shared`, `round_disclosure_A`, `tag_deviation`, `seal_deviation_rejected`, `check_deviation`. Value-level T3 for a whole seal and open against any adversary with A honest: `sealCtr_disclosure`, `tag_disclosure_A`, `open_disclosure_A`, `open_disclosure_rejected`. | closed |
| F20a | Value-level T3 with B honest for the open and the tag is not written (the scripts are symmetric; only the A-honest case is). | open (small) |
| F21 | Security.lean not compiled as a whole on the S10/S12 branches (4 GB cap during the re-lowering); every module importing `Labels` needs a rebuild after the merges. | pending check |

S11 (branch `s11-curve`, not merged; local arithmetic and curve flows as scripts):

| # | Gap | Status |
|---|---|---|
| F22 | Honest runs through `jointRun`: now proved for every curve flow except `prepareSecond` and `prepareContacts` (`quotientMany_honest`, `agree_honest`, `offsetPrepare_honest`, `offsetStep_honest` / `offsetStep_value`, `offsetStepFast_honest`, `lift_honest`, `tables_honest`, `agreeHinted_honest`, `agreeAffine_honest`, `signatures_honest`, `torsion_honest`, plus the earlier split ones). Remaining: an m-point `pointExchange_honest`, then `prepareSecond_honest`, then `prepareContacts` through `Staged.jointRun` (the local step needs F25b). | mostly closed |
| F22a | closed (see Closed): the per-program hypotheses are discharged; the honest runs are restated without them (`*_honest'`), conditional on the named group-law hypotheses `AddClosed`, `ExtClosed`, `RecipientOnCurve`, `CompleteAddition` (each a theorem in `proofs/`). | closed (conditional) |
| F22b | Closed for `offsetPrepare` and `lift` (`prepare_checks`, `liftOpen_checks`, `liftPoint_Z_onCurve`). For `tables`, reduced to F22c. | mostly closed |
| F22c | The bit table's link predicate (`TableLinked`, `EdwardsHinted.LinkedFrom`) from the honest hints: the group law for the hints' multiples (`proofs/` `bitTable_entries`, `doublings_multiples`) is not composed with `bitTable_checks`. | conditional |
| F22d | The `*_honest'` input conditions (`PL.*In`: table entries, hints and mask points are curve points; bits are bits) are hypotheses on the programs' input values; deriving them from the state the earlier flows and local steps leave is not written. | conditional |
| F23 | closed (see Closed). | closed |
| F24 | Value-level T3 for the curve flows: done for the point exchange (`pointExchange_disclosure`: the adversary sees at most our commitment then our opening, with values). Also done for the masked quotient round (`quotientMany_disclosure`: the view is a prefix of the masked denominators and the zero flags), which is the last step of `agree`, `offsetStepFast`, `agreeHinted`, `agreeAffine`. The opened checks, w, Z and the programs' own `D` openings are still proved only at the level of kinds. | partly closed |
| F25 | closed (see Closed). | closed |
| F25a | `decode (encode P) = some P` on curve points is tested only (also affects the liveness of `decode` and `liftU`). | tested |
| F25b | closed (conditional): `invAll_some`, `toAffineAll_isSome`, `hints_isSome`, `publicTable_isSome`. | closed (conditional) |
| F25c | The V3 program signatures in `WFB.CurveProgs` (hypotheses of the S11 `_wf` theorems) are read off the compiled programs, not proved. | conditional |
| F25d | `lift-point` declares its validity bit public, so the shell would accept opening it in ANY flow that lifts; only `prepareFirst` does. By design (it reveals only whether the coordinate is on the curve: `prepareStatus_iff`); noted so a new flow does not open it by accident. | note |
| F26 | `randomPoint` (r·B + t·T₈) is uniform on the curve group, as `curve_hinted_Z_uniform` assumes. | assumed |
| F27 | P-HINT (c), (d) composed with the runs. Note from the third S11 pass: the opened w is uniform by FIBER COUNTING (`lift_fiber_card`), not by a bijection of (r, b), so it does not fit `hiding_of_bijection` directly — it needs a counting form of the hiding lemma; Z needs associativity and inverses on curve points as named hypotheses. | open |
| F28 | closed under the named hypothesis `CompleteAddition`, which `proofs/` discharges with `edwards_complete` (`addU_den_ne_zero`, `splitAgree_montU`). | closed (conditional) |
| F29 | Local arithmetic agrees with a reference library only on vectors (curve25519-dalek; no libsodium binding offline): encode/decode, validity, lift. | tested |
| F30 | `shapeOf` mask counts are read from compilations (a wrong count fails closed). | tested |
| F31 | `e2e_s11.py` not run; S11's field-program pins are placeholders until the V3 re-export. | pending |
| F32 | Op 66's contact-table glue (view kernel, word/field conversions, `sender_public`) is not scripted; left for the flow-API switch. | open |
| F33 | closed for the square root and the lift's root (`sqrt_complete`, `root_isSome`, `roots_isSome`, under `FieldInverse`, `EulerCriterion`, `TwoNonSquare`, all theorems in `proofs/`). The zero-Z case is F25b. | closed (conditional) |
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
| F51 | Closed for one device (see Closed): `send_joint`. Still open: the multi-device path through `jointRun`, and `Table.Inv` for the send's table commit (F59b). | partly closed |
| F52 | closed (see Closed): `devices_accepted`, `gate_iff`, `devices_refused_view`. Still open: the first-message-after-refresh corollary (S15's binding, J6). | closed |
| F59a | `send_joint` takes the T2 model circuits as hypotheses and assumes each stashed tag half equals `bitsOf (toBytes (half …))` (that equality is S12's). | conditional |
| F59b | `Table.Inv` is not proved for the send's table commit (no `Contacts.Step` / WFP for ops 41 and 61). | open |
| F59c | Op 61 has no envelope-size check (op 41 has `maxEnvelope`), so it has no `Wire.Bounded` proof. | open (small) |
| F59d | Functional defect, not a gap in a proof: an official 89-byte text to a contact with an unanswered device aborts (`bundleOut_record_length`; NEEDS_REVIEW 3f item 7). Fails closed. | open (functional) |
| F53 | `shapedCircuit` (the model circuit for kernels with 255-bit word inputs) extends the T2 trust (F1 / B3). | assumed |
| F54 | WF and `Wire.Bounded` for ops 61 and 62 (tested by vectors; proved for op 41, the request scripts and the request record seal). | tested |
| F55 | `Flows/SendBackend.lean` is unverified IO glue; S11's `Curve` half (`ephemeral`, `staticAgreement`, `senderPublic`) is a parameter; `Reveal.ephemeralPublic` to be added by S11; the runner's handle counters must be joined with `Contacts.Table.ctr`. | open (engineering) |
| F56 | S13's pair test uses stand-in circuits; `e2e_s13.py` and the harness not run. | tested / pending |
| F57 | closed for op 41 (`seal_view`, `seal_view_flags`: against any adversary the view is a prefix of [flags, status] on refusal, or [flags, status, timestamp‖envelope] on acceptance, with values from the kernel theorems) and for op 61's gate (`devices_refused_view`). | closed |
| F58 | closed: `bundleEnvBytes_eq`. | closed |
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

The joined stack (branch `scripts-stack`, six script branches plus the main line; not merged back).
Closed there: F10, F21, F50, F59's build part (Security.lean compiles as a whole on the stack: 636
restated theorems, standard axioms), F49 (slot filler is NUL). Narrowed: F45 (`CurveOps.Reveals`
discharged; S13's binding derived: `join_first_wired`), F55, F17, F39 (curve parameters
instantiated in `Flows/Join.lean`). New gaps from the joins:

| # | Gap | Status |
|---|---|---|
| J1 | FIXED on `scripts-stack` (df5d354). The defect: op 50's two agreements read one store slot of masks, so the openings `z₁·m`, `z₂·m` revealed `z₁/z₂`. Fix: `Receive.St` carries a supply of fresh slots, consumed one per use. Proved for every run: `openFirst_reads_once`, `session_reads_once`, `refreshOps_reads_once` (every field-element slot read comes from the starting supply and none is read twice). A sibling liveness defect in S15's `refreshOps` (lift, check and agree shared one mask pool; step 0 always aborted) was fixed too (`split_disjoint`). | closed on the stack |
| J2 | closed on the stack: `Runner.field` supplies field ids, element slots, the mask pool and per-call slots. | closed on the stack |
| J8 | The joined agreements take the identity scalar as a coins slot, but op 55 leaves its swap bits as field handles (`Account.Opened.swaps`); receive and refresh cannot run until `Scalar.identity` maps to them. | open (design) |
| J9 | `Main.session` still calls `Worker.start`; to select script flows it must call `Flow.Worker.startWith … config.agreed …`, and the manifest's kernel names and V3 mask counts must be passed for receive. | open (main line) |
| J10 | The runner's IO loop equals its pure core `drive` by construction, not by theorem (`drive_model`: the pure core's batches are exactly the model's trace; `drive_bounded`; `nextBatch_fill_only`). | note |
| J11 | `account` cannot be selected (op 32 reads credentials from the legacy worker); contacts / send / receive / refresh must switch together with `account` and `curve` (no handle sharing with the legacy library). Today only `random` can run in a real session; `masks`, `tls`, `upgrade` wait for the V3 re-export; `curve` waits for op 66's table glue (F32). | open |
| J12 | The script `Account.State` has no sender-key word (needed by the send's `senderPublic` and the refresh's `Refresh.Account`). | open (engineering) |
| J13 | The runner's store never frees a slot. | open (small) |
| J14 | The runner test (20 checks against a fake worker running the model) covers joint randomness, the upgrade, the contact operations and a refused receive; NOT masks with a conversion, record seal/open, send, an accepted receive, refresh (their stand-in tables live inline in the per-stage vector files). | tested, partial |
| J3 | Only the non-hinted path is joined. | open |
| J4 | closed on the stack: the lint's `flow-calls` allowlist now includes `Flows/*Backend.lean`, `Runner.lean`, `Select.lean` (they use the same `Reveal.*` makers as the legacy flows). | closed on the stack |
| J5 | The joined key agreement also opens the field-to-word masked value, which S12's written `KeyAgreement` spec does not list (the reveal kinds are proved and registered; the spec wording is behind). | note |
| J6 | `join_first_wired` still assumes `hcert` / `hpend`: the bytes in the handles S13 concatenates are the session's certificate input and pending block (a fact across scripts, not proved through `jointRun`). | conditional |
| J7 | The joins' values are not proved through `jointRun`; S15's id blocks are counted, not proved (no WF); the per-contact offset states the send needs depend on op 66's contact-table glue (F32). | open |

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
| I2 | T11 at the `DaemonLine.jobResult` / final-report level (results are written in one place; `serve` resets them per job): argued. T11's second half (each entry comes from `Recovery.onSend` / `onFetch`): not done. (T11 at `deliverJob`'s level is proved about the deployed definition and restated in Security.lean 5b: `t11_deliverJob_results`, `t11_resultsTail_spec`.) | argued / open |
| I3 | `bumpIn_absent`: a contact missing from the version list would make every store write the same version (the nodes refuse the repeat; the send fails, no key reuse). Deployed paths always add contacts first; harden. | open (hardening) |
| I4 | ORD-2 to be rechecked after S15 (device refresh moves to scripts). | pending |
| I5 | Settings agreement, typed messages, `Secret`, flow-calls, session-state: enforced by types and the lint (`scripts/lint_node.py`), not by theorems. | by construction / lint |
| I6 | Session end and send-session keepalive under the libsignal profile (2026-11-12, `Session/Common.lean` `closeWebSocket`, `keepAlive`, `keepAliveSoft`): the Close frame is proved RFC 6455's Close 1000 (`CloseProofs.close_reference`, `close_decode`; Security.lean 4d `t8_close_*`), the ping as before (`ping_reference`). Not proved: that the Close is sent only at an orderly end and on every connection, that nothing is answered or opened after it (the server's records are polled and dropped unopened), the 31 s idle rule and the per-connection ping count (`Pool.nextPing`); the worker sealing the public buffer unchanged (E2's kind of hypothesis). Checked by the fingerprint stage (`close.websocket`, `keepalive.ping_payloads`, `tls.client_records`) and the harness. | tested |

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
| F23 | Well-formedness of every S11 script, and of `prepareContacts` as a staged flow. | `splitBegin_wf` … `sharedBits_wf`, `prepareContacts_wf` (`s11_wf_split_offset`, `s11_wf_hinted`, `s11_prepareContacts_wf`) | branch `s11-curve` (e5a5ff6 … 07501a9) |
| F25 | Commit-then-open soundness of the point exchange in the model; copying our commitment aborts. | `pointExchange_sound`, `pointExchange_copy_aborts` | branch `s11-curve` (1c5ce9a) |
| H4 | There is no C++ step any more: the offset flow uses the Lean `Curve.recode`, and `Local/Edwards` uses the programs' own formulas. | `recode64_value`, `stepIns_window`, `step_tableSum`; `add_eq`, `toAffine_eq`, `montU_eq` | branch `s11-curve`, not yet merged (residue: F34) |
| H5 (part) | P-OFFSET about the step is closed; the two unmodelled aborts remain open. | `ephemeralKey_spec`, `stepIns_window` | branch `s11-curve` |
| H6, G3 | P-HINT (b) for the script and the `prepareStatus` reveal: the status is 255 exactly when the coordinate's curve polynomial is a nonzero square. Conditional on H-QR and Euler's criterion as named hypotheses, both theorems in `proofs/`. | `lift_valid_sound`, `lift_valid_complete`, `prepareStatus_iff` | branch `s11-curve` |
| F13, F14, F15, F16, F18, F20 | S12 second pass: the record seal and open through whole two-party runs (the jointly produced record is `TlsRecord.sealCore`; the acceptance byte is 255 exactly when the tag is GCM's; the gcm-check → tls-open-typed binding); WF and boundedness for every S12 script; GHASH share derivation over a whole `ensure`; a deviating tag half is rejected; the class seal; the derive kernel's value. | `seal_honest`, `open_binding_honest`, `open_class`, `open_rejected_run`, `ensure_shared`, `round_disclosure_A`, `seal_deviation_rejected`, `sealClass_is_record`, `derive_honest`, the `*_wf` and `*_bounded` families | branch `s12-tls` (ad385f0 … a0564a2), not yet merged |
| F51 (one device), F52, F57, F58, F59 (script level) | S13 second pass: multi-device send end to end with no wiring hypothesis and all-or-nothing opening; single-device send through whole two-party runs; the adversary's view of a send; state before request at script level. | `devices_accepted`, `gate_iff`, `devices_refused_view`, `send_joint`, `seal_view`, `bundleEnvBytes_eq`, `send_state_order` | branch `s13-send` (ab1561b … 0f05a5d), not yet merged |
| F22a, F25b, F22b (part) | S11 third pass: compiled curve programs compute their functions and do not abort on stated inputs; honest runs restated without per-program hypotheses; checks vanish on honest inputs (offset prepare, lift); batched inversion cannot fail. | `compileAll_good`, `Decl.live`, the `*_honest'` family, `prepare_checks`, `liftOpen_checks`, `liftPoint_Z_onCurve`, `toAffineAll_isSome` | branch `s11-curve` (2cbd872 … da1eee8), not yet merged |
| (S12) | P-GHASH (c): the "halves" hypothesis of the record seal. | `seal_is_record`, `check_accepts` | branch `s12-tls`, not yet merged |
| (P1) | T1 for all streams after the upgrade (about the model loop then; since C1, about the deployed loop; D1 closed since, below). | `ReceiveLoop.t1_model` (formerly `t1_all`) | main tree, uncommitted pending the merge |
| D1 | T1 from the first byte of a fresh connection: from the start states the session uses (`{ PublicReceive.start accept with lenient, openBody }`: `Session/Pool.lean` `readUpgrade` and `openCircuits`, `Send.lean`, `Receive.lean`, `Ceremony.lean`), over every stream (the upgrade response's head up to CR LF CR LF, then frames) cut into records in any way (a record may end inside the head, or hold the head's end and the first frames), every position the session's record loop (`RecordLoop.run`, via `loop_sub`) reveals is allowed by `ReceiveSpec.classify` (head included) or is its first `error`. Two-phase relation `HeadSim` / `SimAll` against `classifyStream`'s `.head k` / `.frames st`; the completing byte is the last of its run (budget `4 - k`) and gives `Sim` at `Stream.init`. Lemma (i): the upgrade parser's activity byte is not 255 until it completes (true at `start`, kept by `upgradeByte`), so the frame parser gets inactive bytes and stays at its start state (`frameIdle`, `frameRefuses`, `frameByte_head`); lemma (ii): `payloadByte` on a non-data, non-final byte keeps the view and the upgrade parser's state (`payloadByte_head`). Hypotheses: `Faithful` (D8); the steps between records keep the view **and the upgrade parser's state** (`KeepsHead`, stronger than `Keeps`; the session's steps satisfy it: `keepsHead_afterRecord`, `keepsHead_replies`, `keepsHead_expect`); A8 as for C1. No leak found at the head/frame boundary. | `ReceiveStart.t1_start`, `t1_start_model`, `loopStart_good`, `sessionStart_good`, `headStep`, `headWindow`, `frameByte_head`, `payloadByte_head`, `upgradeByte`; Security.lean 4g `receivePolicy_t1_start`, `receivePolicy_t1_start_model`, `receivePolicy_frameByte_head`, `receivePolicy_payloadByte_head`, `receivePolicy_headStep`, `receivePolicy_keepsHead_afterRecord` | main tree, 2026-11-12, uncommitted |
| C1 | T1 is about the record loop the session runs. The session's `record` (`Session/Common.lean`) IS `RecordLoop.run` (`Policy/RecordLoop.lean`, monad-generic: the engines' length probe and `revealRange`, the passed-over bytes, the bookkeeping of a revealed run and the envelope callback are parameters) at the session's operations; the theorem is about `RecordLoop.run` at every operations record of a pure monad that satisfies `Faithful` (D8), over every stream, every cut into records, with any view-keeping steps between records. The three differences: bytes from the reveal parameter (hypothesis `Faithful.reveal`); envelopes to the callback before `envelopes := []` (may fail, reveals nothing, the state passed on is the model's: `loop_sub`); fuel `length + 1` never runs out (`loop_fuel`, `run_fuel`; D9). Remaining: A8, D8. | `ReceiveLoop.t1_all`, `t1_session`, `loop_sub`, `loop_fuel`, `run_fuel`, `sessionGo_good`, `stepRun_window`; Security.lean 4g `receivePolicy_t1_all`, `receivePolicy_loop_sub`, `receivePolicy_run_fuel` | main tree, 2026-11-12, uncommitted |
| C2 | Between records: `replies` keeps the policy's view (restructured: `replies` returns `{ s with control := _ }` on every success, by three binds, no unfolding of its `mapM`); so do `requests := []`, `expect` and the prekey fetch's fields; the session's step after a record (`replies` with any masks, then `requests := []`) keeps it, and keeping it is closed under composition. `t1_all` takes any such steps between records. | `ReceiveLoop.replies_state`, `view_replies`, `keeps_afterRecord`, `keeps_expect`, `view_fetch`, `keepsView_bind`; Security.lean 4g `receivePolicy_view_replies`, `receivePolicy_keeps_afterRecord` | main tree, 2026-11-12, uncommitted |
| C3 | Ordering (ORD-1, ORD-2, T11, versions) is about the deployed definitions: every session function on those paths is defined once over any monad (`storeSoftG`, `commitScratchG`, `Send.sendSoftG`, `sendMessageG`, `refreshContactG`, `refreshSoftG`, `loopG`, `deliverJobG`, `Serve.serveG`, …; effects the fields of `StoreOps`, `SendOps`, `RefreshOps`, `LoopOps`, `DeliverOps`, `ServeOps`), and the deployed function is that definition at `SessionM` and the real record (`abbrev f := fG realOps`); the twins and `*_deployed` are gone. The theorems quantify over the model's operations records. The call sites of `Flow.Send.request` / `requestDevices` / `Flow.Refresh.scratchCommit` are checked by `lint_node.py` `ordering-sites`. Remaining: A8. | `sendSoft_agreed`, `sendMessage_acked`, `deliverJob_sendsAgreed'`, `loop_sendsAcked`, `serve_sendsAgreed`, `commitScratch_agreed`, `commitScratch_outcome`, `deliverJob_commitsAgreed`, `loop_commitsAgreed`, `serve_commitsAgreed`, `deliverJob_results`, `resultsTail_spec`, `storeSoft_versions`, `storeAdvanced_versions`, `versionIn_bumpIn`; Security.lean 5b | main tree, 2026-11-12, uncommitted |
