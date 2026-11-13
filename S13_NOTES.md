# Stage S13: Send — notes

Branch `s13-send` (on `s12-tls`, which carries S10 and S12). REORGANIZATION_PLAN.md 8.1 (T3,
T4-SEND, T7) and 10.2 S13.

## What moved from C++ to Lean

| C++ (read-only, unchanged) | Lean | File |
|---|---|---|
| `service_kernels.h` `seal_open(id, text)` (526-572): widths opening, kernel by name, status gate, timestamp and envelope, `keep` | `Send.sealScript` (op 41) | `TlsMpc/Node/Flows/Send.lean` |
| `seal_devices` (931-968) | `Send.devicesScript` (op 61) | |
| `request(id, …)` (579-586) | `Send.requestScript` (op 42) | |
| `request_devices` (971-981) | `Send.requestDevicesScript` (op 62) | |
| `tls_kernels.h` `seal_application`'s sealer path (200-207) for these requests | `Send.requestCtrScript`, then S12's `Tls.tagScript` (`TlsBackend.sealPhases`) | |
| `tls_worker_v3.cpp` ops 41, 42, 61, 62 (dispatch, reply formats) | `SendBackend.«seal»`, `sealDevices`, `request`, `requestDevices`, `sendApplicationBackend` | `Flows/SendBackend.lean` |
| `ephemeral` (662-671), `prepare(c)`, `of(c).sender_public` | parameters (`SendBackend.Curve`, S11) | |

`SendBackend` returns the legacy results (`Opened .sealedEnvelope (Option (Nat × List Bytes))`,
`TlsWorker.BufferHandle`), so `Flow.Send.*` callers do not change; the legacy `Worker` argument is
replaced by the runner context, as in S12. Nothing selects the backend yet.

### Deviations from the C++ (both parties change together; the legacy library keeps its own)
* **One opening per group**: the four width fields in one opening; timestamp ‖ envelope in one.
* **Op 61**: one opening for all devices' width flags, one for all statuses, one for all timestamps
  ‖ envelopes; the envelopes are opened only after EVERY status is 255 (the C++ opened device k's
  envelope before device k+1's status, so a later refusal left an opened envelope that was never sent).
* **The request's sealer** is its own phase: accepted ‖ header ‖ ciphertext in one opening, abort
  unless accepted is 255 (the C++ opened accepted, then header and ciphertext).
* **Kernel names Lean refuses**: the C++ returned `{0}` when `shaped(name)` threw; the widths read
  from 0/255 flags are always within `find`'s ranges (`Send.widthsOf_le`: at most 10), so this cannot
  happen; the certificate (≤ 1024) and the text class are checked at entry (abort, as the C++'s
  `need`). Request names are checked against `find`'s ranges at op 42/62 (the C++ failed at seal time).
* **The envelope's length** is computed by Lean from the public parameters (`sealEnvBytes` /
  `bundleEnvBytes`: the kernels' value functions on the all-zero inputs; for the seal kernel proved
  equal to the kernel's own output length, `sealOut_lengths`); a computed length above 64 KiB aborts
  (`maxEnvelope`, for `Wire.Bounded`).
* **A refused send** frees the new record and keeps the old state handle; an accepted one frees the
  old state (the table points at the new one). Requests own a copy of the conversation and free it
  when sealed (drop after seal).

## The parameters (to join with S11; `SendBackend.Curve`)

```lean
structure Curve where
  ephemeral : ContactId → M (Opened .ephemeralPublic Bytes × BoolH)
  staticAgreement : ContactId → M (Option BoolH)
  senderPublic : M BoolH
```

* `ephemeral id` (S11 `Curve.offset.step`, `service_kernels.h` `ephemeral`): a fresh ephemeral pair by
  the offset agreement with a joint public offset (commit-then-open; P-OFFSET): the 32-byte public key,
  opened under kind `ephemeralPublic` (S11 adds `Reveal.ephemeralPublic`), and a FRESH Boolean handle
  of 255 private bits, not once, `X25519(e, recipient)` little-endian below p (P-F2W `fieldToWord`).
  The send script consumes and frees it. No other release than P-OFFSET's kinds. One call per message
  (op 41) or per device (op 61).
* `staticAgreement id` (`prepare(c)`, S11 `prepareContacts`, op 66): the contact's static agreement
  word, a live handle of 255 private bits (not once) kept in the contact's derived caches
  (`Contacts.Entry.derived`), or `none` when the contact's key is not a point of the curve (`c.ready`
  false): the send is refused with `none` (the C++'s `{0}`), nothing run.
* `senderPublic`: the account's sender key as a 255-bit word handle (live, not once).
* The runner: `TlsBackend.Runner` (S12). Handle ids come from `Runner.allocB`; the contact table's
  `Table.ctr` must be the same session counters when the two are joined.
* The account's certificate handle and length: `Account.State.certificate` (S9/S10).

Join: `SendBackend.«seal» runner curve refs id built`, etc.; `sendApplicationBackend runner ka refs`
replaces `TlsBackend.scriptApplicationBackend` (it delegates everything but request buffers).

## What is proved, and what is not

Restated in `TlsMpc/Security.lean` section 7d (11 entries, compiled standalone with the same text:
`propext`, `Classical.choice`, `Quot.sound` only; `seal_refused_silent`: `propext` only).

* **T3**: `Reveals` for every script (`Registry.s13_flows_reveal`: ops 41, 61 under `counterWidths`,
  `sealedEnvelope`; ops 42, 62 nothing; the record phase `sealedRecord`), against any adversary
  (`seal_viewD_kinds`, `devices_viewD_kinds`, `request_viewD`, `requestDevices_viewD`,
  `requestCtr_viewD_kinds`). The gate: `seal_refused_silent` (after a status other than 255 nothing is
  released, the state is kept).
* **T4-SEND / T7 at the function level** (each kernel's output read through the script's layout, as
  S12): `seal_out`, `sealOut_lengths`, `seal_accepted_value` (the opened envelope is `sealV1` of the
  reference `SpqrSend.canonical` message, the kept state `advancedRecord`), `requestCtr_value`,
  `bundleRequestCtr_value`, `bundleSeal_get`, `request_record` (header ‖ ciphertext ‖ tag is
  `TlsRecord.sealCore`), and the headline **`send_accepted`**: op 41, op 42 and the record seal; on an
  accepted send what leaves for the server is the TLS record sealing the request frame that carries
  the reference sealed-sender envelope for the reference ratchet step, and the stored state is the
  advanced one; on refusal nothing is sent (the scripts stop before any request) and only the widths
  and the status are opened.
* **E2 for the send path**: `send_accepted` has no `built`, `hframe`, `hmask`: the kernels' inputs are
  the scripts' own concatenations (`request_get`, `seal_get`) and the frame is `Send.frameFor` of the
  script's own opened envelope and timestamp. For devices, `bundleRequestCtr_value` discharges
  `hframe`, `hmask`, and `paired` is the script path's own pairing (`devicesName_paired`).
* **WF**: `sealScript_wf` (op 41, every branch, under `SealSigs`), `requestScript_wf` (op 42),
  `requestCtrScript_wf`. **Wire.Bounded**: `Registry.send_sealScript_bounded`,
  `requestScript_bounded`, `requestCtrScript_bounded`.
* Not proved: see the gaps below.

## C++ that becomes deletable, and when

After (1) the controller-side runner sends Lean batches (op 93), (2) S11's `Curve.offset.step`,
`prepareContacts` and the sender key are merged and passed as `SendBackend.Curve`, (3) the controller
selects `SendBackend` and `sendApplicationBackend` (and the fixtures pass: `e2e_s13.py` both modes,
the harness Q/F/D):
* `service_kernels.h`: `seal_open` (all three overloads; the input-indexed one is the TEST private-text
  path), `request` (both), `seal_devices`, `request_devices`, `ephemeral`, the send part of `prepare`
  (with S11).
* `tls_worker_v3.cpp`: the dispatch of ops 41, 42, 61, 62.
* `tls_kernels.h`: `PrivateBuffer::sealer` / `extra` and the sealer path of `seal_application`
  (lines 200-207) once `bundle_fetch` (op 56, S15) also moves; until then it stays for
  `bundle-fetch-ctr`.

## Performance (rounds per send vs the C++)

A round = one batch with a data reply (an agreement plus a message delay; plan 5.2). S11's ephemeral
pair (offset commit/open, the offset step, field to word) is the same in both and not counted.
* Op 41: 3 rounds (width flags; status; timestamp ‖ envelope) vs the C++'s 7 openings (4 width fields,
  status, timestamp, envelope) inside one operation.
* Op 61 with m devices: 3 rounds whatever m vs 7m openings.
* Ops 42, 62: no round (one batch without reply; can ride the next batch), as the C++ (a buffer).
* The request's record: 2 rounds (accepted ‖ header ‖ ciphertext; tag) plus S12's GHASH rounds when
  more key powers are needed, vs 4 openings (accepted, header, ciphertext, tag).
* The Lean side adds the agreement per batch, and `sealEnvBytes` (one evaluation of the seal's value
  function on zeros per send: concrete AES/SHA in Lean; measure, or cache per parameter tuple).

## Tests

* Lean vectors: `node_worker/tests/lean/S13Vectors.lean` → `node_worker/tests/s13_vectors.txt`
  (`lake env lean --run`, light, ~3 s): flow `s13-send` (op 41 with an 8-byte certificate and a
  class-1 built text, op 42, the record phase on `frameFor`'s frame) and flow `s13-devices` (op 61 with
  two records, op 62, the record phase with `bundle-request-ctr` on `buildDevices`' frame). 16 rounds,
  every batch admitted by `checkBatch`; `check seal/request/devices/devices-request ok` (the opened
  envelopes equal `sealV1` of the reference step, the kept states the advanced records, the opened
  request records the CTR encryption of the filled frames). Stand-in circuits: `signal-widths` itself,
  the seal and request kernels' specifications. One finding while writing them: the kernel reads the
  ephemeral public key as a 255-bit word (its top bit dropped), as the C++'s `public_bits(255)`.
* Stand-in pair test: `cargo test --offline --no-default-features --test s13_pair` (2 tests): every
  reply of the two shells equals the Lean model's, a fresh pair per flow. All node_worker tests pass
  (lib 42, every integration test).
* Loader: `send_script_kernels_check(kernels, cert)` fails closed (missing `signal-widths CERT`, no
  seal kernel, no request sealer, or any send kernel with another layout) with the unit test
  `s13_send_kernels_fail_closed`.
* Real engines, NOT RUN: `node_worker/tests/e2e_s13.py`
  (`python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s13.py <node-worker>`;
  needs the vectors' four kernels lowered into the cache: `signal-widths 8`,
  `signal-seal-built 8 1 1 1 1 1`, and the `signal-request-ctr …` / `bundle-request-ctr …` named in the
  vectors' `sig` lines).

## Checks

* `#print axioms` of the 11 section-7d entries (scratch file with the same text): standard axioms
  only. `scripts/check_axioms.py` (all of Security.lean) NOT run: `KernelSpecs/SlotEncoders.olean` is
  not built in this worktree and rebuilding Security.lean's closure exceeds this stage's 4 GB cap.
* `scripts/lint_node.py`: 0 findings.
* No `sorry`, `native_decide`, axiom, `partial def`, `unsafe`, `opaque`, `extern`, Mathlib; no
  `bv_decide` added.

## Gap bookkeeping (PROOF_GAPS.md)

Closed or narrowed by S13:
* **E2 (send path)**: closed for the script path. `built`, `hframe`, `hmask` are not hypotheses of
  `Send.send_accepted` (Security `s13_send_accepted`); `hframe`, `hmask` discharged and `paired` the
  script's own for `bundle-request-ctr` (`Send.bundleRequestCtr_value`, `Send.devicesName_paired`).
  What `built` trusted (the C++ worker passes the opened envelope and the controller's frame unchanged)
  is replaced by Lean values passed between Lean functions (`Reveal.sealedEnvelope` of the script's
  opening, `frameFor`). Still in E2: `wired` (S15: the stored pending block is what the refresh's
  `establish-session` produced), the kem kernels and bundle-slot bindings (S14/S15).
* **E3**: unchanged (`sealV1` is a transcription); the script path now reaches it with no wiring step.
* **E4**: narrowed: the agreements are still inputs, now with a written specification for the join
  (`SendBackend.Curve`), and `send_accepted` states the envelope in terms of the words the script
  feeds.
* **F5** (legacy flows): ops 41, 42, 61, 62 have script versions (not used by the controller yet).

New gaps (to add under F):

| # | Gap | Status |
|---|---|---|
| S13-1 | T4-SEND is at the function level (kernel outputs read through the script's layout); not through `jointRun`. That the scripts' concat/slice order produces exactly the bundles the theorems use (`requestIn`, `bitsOf conv ++ (bitsOf text ++ words)`) is by the scripts' text, checked by the vectors, not a run-level theorem. | open |
| S13-2 | Op 61 has no composed headline: per device `bundleSeal_get` (+ `EstablishDevices.openedEnvelopes_reference`) and `seal_accepted_value` for kind 0, the request `bundleRequestCtr_value`; the slicing of `bundle-seal`'s outputs (status 1, conversation `cert + 319`, envelope `bundleEnvBytes`) is not proved (the kind-0 analogue `sealOut_lengths` is). | open |
| S13-3 | `shapedCircuit`: the model circuit of a kernel with `.word` inputs (255 bits read as one variable, `BitVec.ofBoolListLE`) is the T2 trust extended to word inputs (the lowered circuit's word wire order). | assumed (T2) |
| S13-4 | WF and `Wire.Bounded` not proved for `devicesScript` (op 61) and `requestDevicesScript` (op 62); the vectors' batches all pass `checkBatch`. | tested |
| S13-5 | `Flows/SendBackend.lean` is unverified IO glue; `Runner` and `Curve` are parameters with written specifications only; the counters of the runner and of `Contacts.Table` must be joined; nothing selects the backend. | open (engineering) |
| S13-6 | The stand-in pair test's circuits are a table of the kernels' specifications; `e2e_s13.py` not run (needs the vectors' kernels lowered and the heavy lock); harness Q/F/D not run on the script path. | tested / pending |
| S13-7 | The refusal statement is structural (`seal_refused_silent`: nothing released after a status ≠ 255; `Reveals` for the kinds), not a view statement listing exactly the two releases (widths, status) against any adversary. | open (small) |
| S13-8 | `bundleEnvBytes` (the `bundle-seal` envelope length computed from `sealMessageValue` on zeros) is not proved equal to the kernel's output length (a wrong length makes `check` refuse the slice or opens a prefix of public bytes). | open (small) |
| S13-9 | ORD-1 not restated over the Lean flow (P4 not done; the backend keeps the legacy results and call order). Security.lean as a whole not compiled on this branch (4 GB; section 7d standalone); every importer of `Engine/Labels.lean` needs a rebuild after the merge (`kinds`/`all` grew). | open / pending check |

## Merge notes: files touched

* New Lean: `TlsMpc/Node/Flows/{Send,SendProofs,SendBackend}.lean`.
* Changed Lean: `TlsMpc/Node/Engine/Labels.lean` (labels `counterWidths` (40), `sealedEnvelope` (41);
  `kinds`, `all`, `all_codes`), `TlsMpc/Node/Flows/Registry.lean` (imports `Flows.Send`; S13 entries
  in `declared`; `s13_flows_reveal`; the bounded theorems), `TlsMpc/Security.lean` (imports
  `Flows.SendProofs`; section 7d; the SEND and ORD-1 items of section 8; `#print axioms` lines),
  `REORGANIZATION_PLAN.md` (S13 status).
* Not touched: `TlsMpc/Node/Types.lean` (no new kind: all S13 kinds existed), `Reveal.lean`
  (`Reveal.ephemeralPublic` is S11's), the controller, `Main/Session/Flow/*Legacy/Channels/Messages/
  Policy`, the S10/S12 flow files, every module an emitter imports (the kernels, `SealSend`,
  `RequestFrame`, `EstablishRequest` only imported), the C++.
* Rust: `node_worker/src/loader.rs` (`SEND_RECORD_BYTES`, `send_script_kernels_check`, a test); new
  `node_worker/tests/{s13_pair.rs,s13_vectors.txt,e2e_s13.py,lean/S13Vectors.lean}`.
* With S11: `SendBackend.Curve` above; `Flows/Send*.lean` import neither `Flows/Curve` nor
  `Local/{Field,Edwards}`. With S14/S15: separate flow files; `Registry.lean` and `Labels.lean` gain
  entries side by side (merge by concatenation).
