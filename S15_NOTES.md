# Stage S15: device refresh — notes

Branch `s15-refresh` (from `s12-tls`: the engine `program` instruction, V3 field programs, S10, S12).
REORGANIZATION_PLAN.md 8.1 (T3, T4-REFRESH, ORD-2) and 10.2 S15.

## What moved from C++ to Lean

| C++ (read-only, unchanged) | Lean | File |
|---|---|---|
| `service_kernels.h` `bundle_fetch` (op 56) and its sealer `bundle-fetch-ctr` inside the TLS record seal | `Refresh.fetchScript`, `opFetch` (the record seal's first phase; the tag is `Tls.tagScript`) | `Flows/Refresh.lean` |
| `bundle_take` (op 57) | `takeScript`, `opTake` | |
| `bundle_drop` (op 58) | `opDrop` (frees the body and the whole scratch) | |
| `bundle_shape` (op 59) | `shapeScript`, `opShape` (`none` when the size class has no circuit) | |
| `bundle_establish` (op 60), steps 0–8 | `opEstablish` → `step0` (`parseScript`: `bundle-slot` with the splice and the counts from ONE `Widths`, `establish-points`; S11 `lift`; `challengeScript`; S11 `check`; `verifyScript`: `establish-verified`, `bundle-rebind`, `changed` opened for device 0), `step1` (S11 `agree`), `step2` / `stepRow` / `step7` (the KEM: `kemHashInstrs`, `kemRowInstrs`, `kemFinishInstrs`, one block of 34 ids), `step8` (`sessionScript`: `establish-session`, status opened) | |
| `Establishing` (between steps), `bundle`, the scratch | `RState`, `Progress`, `Device`, `Parsed`, `Lifted` (public, Lean side, beside `Contacts.Table`, same counter) | |
| `scratch_seal` (op 64), `entries` | `scratchSealScript` (the content handle is KEPT: it is exactly what the commit installs), `opScratchSeal` | |
| `scratch_commit` (op 65) | `opCommit` (`committed`: the sealed content becomes the entry's state; with `changed`, the derived caches go) | |

### Deviations from the C++ (both parties change together; the legacy library keeps its own)
* **The cut and the splice are one `pick`** from `body ‖ [filler]` (`slotInput`): the positions
  (`cutPositions`) come from `BundleSlots.splice w`, and the `widths` input is `widthsOf w` of the
  same `w`; the C++ received the runs and the counts as two arguments (op 60's tail) and trusted
  the controllers to compute both from one `w`.
* **Placement is checked exactly** (`placedOk` = `BundleItemWhole.Placed`): the C++ checked
  `first ↔ start = head` and the fit but not `last ↔ start + size + 2 = total`; a valid response
  satisfies both.
* **The scratch's sealed content is kept and installed** by the commit (C++: `entries` recomputed
  at commit time from the same devices). The stored bytes are the same (record ‖ pending per
  device).
* **The scratch keeps each device's whole `conversation`** (certificate ‖ record); the stored content
  slices the record out at seal time (`contentParts`), as the C++ stored `device.record`.
* **The fetch's request is sealed by the script** (`bundle-fetch-ctr` then `Tls.tagScript`), not by
  a `PrivateBuffer` with a sealer: `TlsBackend` (S12) has no service-sealer buffers.

## Parameters (to join with S11 and S13)

### S11: `Refresh.CurveOps` (from `Flows/Curve.lean`)
```lean
structure CurveOps where
  liftIds : Nat × Nat          -- Boolean, field ids each call uses (caller allocates the block)
  checkIds : Nat × Nat
  agreeIds : Nat × Nat
  lift : Counters → BoolH → Script (BoolH × BoolH × BoolH)
  check : Counters → BoolH → BoolH → BoolH → BoolH → Script (BoolH × BoolH × BoolH × BoolH)
  agree : Counters → BoolH → BoolH → Option BoolH → Script (List BoolH)
  kinds : List RevealKind
```
Specification S15 relies on (C++ `bundle_establish` steps 0–1, `service_kernels.h:799-853`):
* `lift c point`: `point` = `establish-points`' `identityPoint` (255 bits, never); word to field,
  `xeddsa-recover` (or the hinted lift), field to word: returns FRESH 255-bit handles `(valid, x, y)`
  (marks never, not once) from the block at `c`; frees nothing it was given.
* `check c x y ec pq`: `ec`, `pq` = the two 510-bit halves of `establish-challenges`' output
  (flip ‖ challenge ‖ scalar); bits to field, `xeddsa-check` (or the hinted signature sums), field to
  word: returns fresh `(ecRx, ecRy, pqRx, pqRy)` words. The script frees `ec`, `pq` after it.
* `agree c identityPoint signedPoint oneTimePoint?`: two fresh shared scalars (base, ratchet) and the
  account's identity scalar; returns fresh words `[dh1, dh2, dh3, ratchetAgreement, basePublic,
  ratchetPublic]` and `dh4` last when a one-time point is given (the order of
  `EstablishKernel.sessionInputs`; the script refuses another length). The points stay the
  script's (freed at step 8).
* every call releases only under `kinds` (S11's) — the hypothesis `CurveOps.Reveals` of
  `opEstablish_reveals`; WF with the post-condition "fresh 255-bit handles from its block, nothing
  else changed" is S11's to state (not assumed by a theorem here: the WF of the establishment is a
  gap, tested by the vectors).

### S9/S16: `Refresh.Account`
`⟨certificate : BoolH (cert bytes, never), cert : Nat, senderPublic : BoolH (a word)⟩`: the account's
sender certificate and identity public key handles (C++ `a.certificate`, `a.sender_public`).

### S13: the send (`Flow.Send.sealDevices` / `requestDevices`)
After `opCommit`, the contact's state is record ‖ pending per device (kinds 1/2), as the C++ stored
it; the send builds each device's `bundle-seal` input `conversation` = account certificate ‖ record
and `pending`. The theorem `first_wired` needs of the send exactly: its `bundle-seal`'s
`conversation` and `pending` inputs are the bytes of the handles it is given (`keptConversation`,
`keptPending` of the session's output); `stored_record` shows certificate ‖ stored record IS the
session's conversation output (for an accepted session), so a send from the committed state meets
it when it prefixes the same certificate handle. `requestDevices` (`bundle-request-ctr`) reads the
devices' records from the same state.

### The IO layer (not in this branch)
`Flow.Refresh.*` keep their signatures; behind them, with S12's `Runner`: `fetch` registers a
request (frame, mask, offsets, contact) under a fresh buffer id and the application backend's
`sealApplication` seals it with `fetchScript` + `Tls.tagScript` (`TlsBackend.sealPhases`); `take
h o c` → `opTake` on the buffer's content handle; `drop` → `opDrop`; `shape` → `opShape` (wrapped
by `Reveal.bundleShape`); `establish … step …` → `opEstablish` (the status as
`Reveal.deviceStatus [s]`; the entropy slot from `Channels.random 32`); `scratchSeal id nonce` →
`opScratchSeal` (`Reveal.sealedBlob`); `scratchCommit id` → `opCommit`. A `RefreshBackend.lean`
like `TlsBackend.lean` was not written (gap F47 below): the table's and the runner's counters must
be one before it can be.

## What is proved, and what is not

Restated in `TlsMpc/Security.lean` section 7d (13 entries, compiled standalone: `propext`,
`Classical.choice`, `Quot.sound` only; see "Checks").
* **T3** — `opEstablish_reveals` / `refresh_viewD_kinds` (against any adversary, with S11's
  `Reveals` as hypothesis), `fetch_reveals`, `take_reveals`, `shape_reveals`, `parse_reveals`,
  `challenge_reveals`, `verify_reveals`, `session_reveals`, `scratchSeal_reveals`, `quiet_kemBlock`
  (the encapsulation releases nothing), `op*_reveals`; `Registry.s15_flows_reveal`. The keys
  response body reaches a release only through `bundleShape`, `identityChanged`, `deviceStatus`.
* **T4-REFRESH, the parse** (in the model): `slotInput_value` (the one-source property: the input
  bundle is the cut with the item spliced by `BundleSlots.splice w` and `widthsOf w`),
  `slot_inputs` (the hypotheses `inputs`, `widths` of `bundleSlot_device` discharged),
  `parse_device`, `parse_parses_or_refuses`, `parse_fields` (`runPlain` through the run).
* **T4-REFRESH, the encapsulation**: `kemFlow_pipeline` — all 21 name bindings of
  `KemCompose.kernels_compose` PROVED for the script's wiring (its offsets and input orders,
  `kemFlow`; field-name comparisons included, `row_name_ne`); `kemFlow_accept`
  (`pipeline_valid_accept`), `kemFlow_invalid` (`pipeline_invalid`). Hypothesis `KemWidths` (the
  kernels' output widths). Function level: `kemBlock` → `kemFlow` in the model is a gap.
* **T4-REFRESH, the first message**: `kept_outputs`, `first_wired` (PROVES `EstablishDevices.wired`
  for what the script hands the send, given the send binds them), `first_envelopes`
  (`openedEnvelopes_first`), `stored_record`. Hypothesis `SessionWidths`.
* **ORD-2 (script level)**: `opCommit_entry` (the only entry change, to the sealed content, only
  when ready and sealed for that contact), `opDrop_table` (a drop leaves the table), `opFetch_entries`,
  `opTake_entries`, `opShape_entries`, `opEstablish_entries`, `opScratchSeal_entries`. With these, the
  session-level ORD-2 (`Session/RefreshProofs.lean`, `refreshCommits`: `Guarded CommitsAgreed`,
  main line) keeps holding when `Flow.Refresh` switches: its premise is that every operation but
  `commitScratch` commits no scratch, which is `*_entries`.
* **WF / invariant**: `shapeScript_wfp`, `takeScript_wfp`; `RState.Inv`, `RState.Inv.empty`,
  `opDrop_inv` (a drop keeps `Table.Inv`). `Wire.Bounded`: `Registry.takeScript_bounded`,
  `shapeScript_bounded`.

## C++ that becomes deletable, and when

After (1) the runner and the IO layer above, (2) S11's `CurveOps` and S13's send scripts, (3) the
controller calls the script `Flow.Refresh.*` and the fixtures pass (`e2e_s15.py` both modes,
`--multi-device`, `--recovery devices,refresh-retry,identity,bundle-fault`):
* `service_kernels.h` lines 631–925: `bundle` and `Establishing`, `bundle_fetch`, `bundle_take`,
  `bundle_drop`, `bundle_shape`, `bundle_establish`, `scratch_seal`, `scratch_commit`; `entries` once
  S13's send no longer needs it; `ephemeral` goes with S13.
* `tls_worker_v3.cpp`: ops 56–60, 64, 65 (their dispatch and argument parsing, including op 60's
  `runs` tail).
* `RefreshLegacy.establishTail` (the splice sent to the worker) and the legacy wrappers of
  `Reveal.bundleShape` / `deviceStatus` (S16).
Kept: `take_range` (S14's receive), the `PrivateBuffer` sealer path for other services (S13, S16).

## Performance (rounds per device vs the C++)

A round = one batch (an agreement; plus a message delay when it has a data reply). Per device,
outside S11's parts: 9 operations (as the C++'s 9 op-60 calls), each one batch, two data replies
(device 0's `changed`, the status) — the C++ had the same openings inside the same calls. Added: one
agreement per batch, about 9 message delays per device (a few ms at 1 ms link delay) against the
measured ~10 s per extra device in malicious mode (dominated by the twelve KEM kernels and S11's
field work, unchanged). S11's lift/check/agree cost what the C++'s conversions and programs cost
(S11_NOTES). The fetch: one round (header ‖ ciphertext with the accepted byte) plus the tag's,
as a TLS seal. The shape: one round. Scratch seal: one round; commit: no data reply.

## Tests

* Lean vectors: `node_worker/tests/lean/S15Vectors.lean` → `node_worker/tests/s15_vectors.txt`
  (`lake env lean --run`, light; 34 rounds): a two-device refresh (no one-time prekey, then one
  with), fetch, two takes, shape, 18 establishment steps with a STAND-IN `CurveOps`, scratch seal,
  commit, take, drop. LABELLED STAND-IN circuits with the kernels' real signatures (Kyber-1024 and
  the bundle parser have no test-size parameters); every batch admitted by `checkBatch` (this
  exercises the establishment's WF on the instance); `check fetch/shape/ready/sealed/commit/drop ok`.
* Stand-in pair test: `cargo test --offline --no-default-features --test s15_pair` (2 tests): every
  reply of the two shells equals Lean's model. All node_worker tests pass.
* Loader: `REFRESH_SCRIPT_KERNELS`, `refresh_script_kernels_check` (fails closed: a missing kernel, or
  `bundle-rebind` / a KEM stage with an openable private output); unit test
  `s15_refresh_kernels_fail_closed`.
* Real engines, NOT RUN: `node_worker/tests/e2e_s15.py` (`shape` mode: fetch, takes, shape with the
  real `bundle-fetch-ctr` and `bundle-shape`, the shape's flags compared byte for byte;
  `python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s15.py NODE_WORKER`;
  `refresh` mode needs S11, the runner and a captured two-device response from the LOCAL server).

## Checks

* `#print axioms` of the 13 section-7d entries (standalone file with the same text) and of 15 proof
  theorems: `propext`, `Classical.choice`, `Quot.sound` only. `scripts/check_axioms.py` (all of
  Security.lean) NOT run: over the stage's 4 GB cap (as S10, S12).
* `scripts/lint_node.py`: 0 findings.
* No `sorry`, `native_decide`, `bv_decide`, new axiom, `partial def`, `unsafe`, `opaque`, `extern`.

## PROOF_GAPS.md bookkeeping

Closed or narrowed (by theorem):
* **E2** (worker wiring hypotheses), in part: "binds the kem kernels' named outputs to inputs" —
  CLOSED for the script's wiring at the function level (`kemFlow_pipeline`: every hypothesis of
  `kernels_compose`); "binds head/before/item/after/end for bundle-slot" — CLOSED in the model
  (`slotInput_value`, `slot_inputs`, `parse_device`, `parse_fields`); "wires each device's
  establishment outputs into its seal (`wired`)" — CLOSED for the script's part (`first_wired`,
  `kept_outputs`, `stored_record`), the send's binding of the handed records remains (S13). The
  fetch's frame/mask/offsets pass unchanged into `bundle-fetch-ctr` by construction
  (`fetchScript`), not yet a theorem.
* **E7** (`bundle-slot` conditional), in part: the runtime splice and the declared counts can no
  longer disagree (`slotInput_value`; the `inconsistent_width_*` premise cannot be formed); the
  template/NUL-free-field assumption remains as stated.
* **I4** (ORD-2 after S15): the script-level facts the session-level theorems rely on are proved
  (`opCommit_entry`, `opDrop_table`, `op*_entries`); rerun `Session/RefreshProofs.lean` after the
  switch (it states the RefreshOps interface, unchanged).

New gaps (F style; numbers F42–F50 provisional, renumber at merge if S13 took them):

| # | Gap | Status |
|---|---|---|
| F42 | S15: T4 of the encapsulation is at the function level (`kemFlow`, the script's offsets); `runPlain` through `kemBlock` to `kemFlow` not proved (the parse's IS, `parse_fields`); the session step likewise (word inputs: no `circuitOf`). | open |
| F43 | S15: `KemWidths`, `SessionWidths` (output widths of the KEM and session kernels) are hypotheses: no length lemmas for the stages; the loader checks the pinned layouts at start (`refresh_script_kernels_check`, fails closed). | tested |
| F44 | S15: WF proved for `shapeScript`, `takeScript`, `opDrop`; not for `fetchScript`, the establishment steps (S11's parameters' WF is S11's), `scratchSealScript`, `opCommit` (the vectors admit every batch). `opCommit`'s preservation of `Table.Inv` not proved. | tested / open |
| F45 | S15: S11's `CurveOps` (lift, check, agree) is a parameter; T4 of the signature verification and the agreements through the script is S11's; `CurveOps.Reveals` a hypothesis. | open (join) |
| F46 | S15: `first_wired` needs the send (S13) to bind `bundle-seal`'s `conversation`/`pending` to the handles it is given (and to prefix the account's certificate for a send from the committed state). | conditional (join) |
| F47 | S15: no `RefreshBackend.lean` (IO glue with the legacy signatures); the mapping is written above; nothing selects the scripts. | open (engineering) |
| F48 | S15: value-level T3 for the whole establishment (which bytes `changed` and the status are, through the model) not stated; kinds are proved against any adversary. | open |
| F49 | S15: vectors use labelled stand-in circuits; `e2e_s15.py` not run (`shape` mode needs the two kernels lowered; `refresh` mode needs S11, the runner, a captured response). | tested / pending |
| F50 | S15: Security.lean not compiled as a whole on the branch; section 7d compiled standalone. `Labels.kinds`/`all` grew (60–62): rebuild every importer after the merge (only `Registry` uses them). | pending check |

## Merge notes: files touched

* New Lean: `TlsMpc/Node/Flows/{Refresh,RefreshFlowProofs,RefreshSlotProofs,RefreshKemProofs,RefreshFirstProofs,RefreshWF}.lean`.
* Changed Lean: `TlsMpc/Node/Engine/Labels.lean` (labels `bundleShape`, `identityChanged`,
  `deviceStatus`; `kinds`, `all`, `all_codes`), `TlsMpc/Node/Flows/Registry.lean` (imports
  `RefreshFlowProofs`; S15 `declared`; `s15_flows_reveal`; `takeScript_bounded`,
  `shapeScript_bounded`), `TlsMpc/Security.lean` (imports; section 7d; section 8 items; prints),
  `REORGANIZATION_PLAN.md` (S15 status). S11 and S13 also extend `Labels.kinds`/`all`: merge the
  lists (codes are distinct by `RevealKind.codes_distinct`).
* **The slot filler**: this branch's `BundleSlotWhole.bundleSlot_device` uses `'0'` (48);
  the main line's uses NUL (0). After merging main, change `Refresh.slotFiller` to `0` (one line);
  every theorem here uses the kernel theorems by name (`bundleSlot_device`,
  `bundleSlot_parses_or_refuses`, `spliced_eq`, `applyRuns_merge`, `fits_item`, `spliced_layout`)
  and `slotFiller` symbolically. (The copied build directory held main's NUL oleans for
  `Signal/BundleSlots`, `BundleSlotKernels`, `BundleItemWhole`, `BundleSlotWhole`; they were rebuilt
  from this branch's sources.)
* Not touched: `Types.lean` (no new kind), `Reveal.lean`, the controller,
  `Main/Session/Flow/*Legacy/Channels/Messages/Policy`, the S10/S12 flow files, every module an
  emitter imports (kernels only imported), the C++.
* Rust: `node_worker/src/loader.rs` (`REFRESH_SCRIPT_KERNELS`, `refresh_script_kernels_check`, a
  test); new `node_worker/tests/{s15_pair.rs,s15_vectors.txt,e2e_s15.py,lean/S15Vectors.lean}`.
