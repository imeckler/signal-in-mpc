# Stage S12: GHASH shares and TLS — notes

Branch `s12-tls` (from `s10-conversions`; started early, in parallel with S11 on `s11-curve`).
REORGANIZATION_PLAN.md 7.1 (P-GHASH), 8.1 (T3, T4-TLS) and 10.2 S12.

## What moved from C++ to Lean

| C++ (read-only, unchanged) | Lean | File |
|---|---|---|
| `gcm_shares.h` `gf_multiply`, the squaring in `ensure`, `half` | `Local.Ghash.mul` (= `Ghash.multiply Ghash.concrete`), `extend`, `half` (= `GhashShares.localTag` over `Gcm.authInput`) | `TlsMpc/Node/Local/Ghash.lean` |
| `gcm_shares.h` `reshare` on `gcm-key-share` / `gcm-multiply`, `ensure` | `Ghash.keyShareScript`, `Ghash.roundScript` (doubling rounds), `TlsBackend.ensure` | `Flows/Ghash.lean`, `Flows/TlsBackend.lean` |
| `tls_kernels.h` `tagged`, `seal_control`, `seal_application` (public buffers) | `Tls.sealCtrScript`, `sealClassScript`, `tagScript`; `TlsBackend.sealPhases` | `Flows/Tls.lean` |
| `tls_kernels.h` `open_application` (typed) | `Tls.parserScript`, `Tls.openScript` (`gcm-check`, `tls-open-typed`, `tls-frame`) | `Flows/Tls.lean` |
| `tls_kernels.h` `rotate` | `Tls.updateScript` (+ the direction's shares dropped) | `Flows/Tls.lean` |
| `tls_kernels.h` `reveal_range`, `public_buffer` | `Tls.revealScript`, `rangeScript`, `publicScript`; `TlsBackend.recordLength`, `revealRange`, `publicBuffer` | |
| `tls_kernels.h` `derive` (after the agreement), `open_handshake`, `verify_finished`, `finish`, `retire`, `abort` | `Tls.deriveScript`, `openHandshakeScript`, `verifyScript`, `finishScript`, `dropScript`; `TlsBackend.scriptBackend` | |
| `tls_worker_v3.cpp` op 4 (authentication agreed, incl. each party's decision) | `Tls.agreeScript` (the request digest and decision as public bits in the agreed skeleton) | |
| `tls_worker_v3.cpp:321-329` (64-record window), `:336-338` (drop after seal) | `Tls.Window.push`, `Tls.Buffers.receive`, `Buffers.sealed` | |
| `TlsKernels::Parked`, `exchange`, `buffers` | `Tls.Conn`, `Tls.Direction`, `Tls.Buffers` (to live in `Session/Pool`, below) | |

`TlsBackend.scriptBackend : TlsClient.Backend Unit` and `scriptApplicationBackend :
TlsApplication.Backend TlsWorker.BufferHandle` have the legacy backends' types, so they are a drop-in
alternative (`Flow.Tls.handshake` / `application` would take one or the other); nothing selects them
yet. Every value they hand on passes through the same `Reveal.*` wrapper as the legacy backend's.

### Deviations from the C++ (both parties change together; the legacy library keeps its own)
* **GHASH powers in doubling rounds**: every odd power of `(m, 2m]` in ONE `gcm-multiply` run with
  `copies` (a `pick` lays out each copy's inputs; A's masks and the share of H are `once` and reach
  exactly one copy each), one `openBoolTo` B per round. H¹ … Hⁿ take 1 + ⌈log₂ n⌉ rounds instead of
  about n / 2 (`GcmShares::ensure`: one engine round per odd power).
* **One opening per kernel output group**: header ‖ ciphertext in one opening (the C++ opens the two
  fields separately); `tls-seal-class`'s accepted ‖ header ‖ ciphertext in one.
* **Authentication agreement**: the C++ op 4 agrees the whole request; the script agrees its
  SHA-256 digest and the decision (public bits in the skeleton), aborting both on any difference.
* **Not in the script backend** (the legacy backend keeps them until S13): sealing a received
  buffer (`tls-seal-private-ctr`, the echo fixture only), request buffers with a service sealer
  (`PrivateBuffer::sealer`), the test producer.

## The key-agreement parameter (to join with S11)

`TlsBackend.KeyAgreement (Sc : Type)` — `Sc` is S11's per-connection scalar state:

```lean
structure KeyAgreement (Sc : Type) where
  begin : M (Sc × Bytes)            -- M = TlsClient.M = ExceptT String IO
  agree : Sc → Bytes → M BoolH
  erase : Sc → M Unit
```

Specification S12 relies on (S11 `Flows/Curve.lean` `Curve.split` / `Curve.agree`):
* `begin`: draws this party's scalar summand `k_P` (`Channels.random`; the sum clamped as RFC 7748),
  opens the joint public key share `u((k_A + k_B)·B)` (P-SPLIT; kinds `ownPublicPoint`, `commitment`,
  `commitOpening`, `curveChecks`, `maskedDenominator`) and returns the state and the 32-byte
  little-endian u-coordinate for the ClientHello (`scriptBackend.begin` wraps it with the hello
  random from `Random.joint` into `Reveal.handshakeShare`).
* `agree st peer`: the server's 32-byte share with its top bit cleared and reduced mod p (as
  `tls_kernels.h:116-117`); computes `X25519(k_A + k_B, peer)` in the engines; ABORTS on zero
  (RFC 8446 7.4.2); returns a FRESH Boolean handle of 255 private bits (marks `never`, not `once`),
  the little-endian value below p (P-F2W `Convert.fieldToWord`), allocated from the session's
  `Counters`; releases nothing beyond P-SPLIT's kinds. `Tls.deriveScript` consumes it (concat with
  the public hello hash, `tls-derive`, whose `agreement` input is a `.word`) and frees it.
* `erase st`: drops the scalar state (retire and abort; idempotent).

Join: `scriptBackend (r : Runner) (ka : KeyAgreement Curve.State) check refs`.

## The `Session/Pool` change (not made here: `Session/Pool.lean` is not edited)

* Per connection (today's `parkedStates` / the C++ `Parked` behind op 90): a `Tls.Conn Curve.State`
  — the handshake handles, the two `Tls.Direction`s (traffic block handle, this party's `Secret`
  shares of H¹ … Hⁿ and their count), the parser handle, S11's scalar between begin and derive.
  Selecting a connection (op 90) becomes choosing which entry the backend's `TlsBackend.Refs` points
  to: no engine call. Replacing a closed connection (op 91) drops that entry's handles
  (`Tls.Conn.handles`, `dropScript`).
* Per session: `Tls.Buffers` (buffers by public id, `next`, the 64-record window), the engine
  `Counters` (handle ids, never reused) and the runner's store slots.
* The legacy connection table in C++ keeps the WebSocket service state until S13–S15.

## What is proved, and what is not

Restated in `TlsMpc/Security.lean` section 7c (18 entries, compiled standalone: standard axioms
only; see "Checks"). In short:
* P-GHASH (a): per round of the doubling schedule (`Local.Ghash.shared_extend`) and with the
  kernels' resharing (`Ghash.keyShare_shared`, `Ghash.round_shared`, from `gcmKeyShare_reshare` /
  `gcmMultiply_reshare`). (b): `Local.Ghash.halves_xor`. (c): `Tls.seal_is_record` —
  `sealCtr_with_tag_is_seal` with `halves` discharged — and `Tls.check_accepts` for the open. (d):
  `Ghash.keyShare_hides`, `Ghash.multiply_hides` (bijection form), `keyShare_viewD_B`,
  `round_viewD_B` (B honest: empty adversary view), `keyShare_disclosure_A` (A honest: exactly the
  masked value).
* T3: `Reveals` for every script (`Registry.s12_flows_reveal`, kinds registered in
  `Engine/Labels.lean`).
* T4-TLS at the function level (each kernel's output read through the script's layout): seal,
  tag check, typed open (`open_event_refines` from `typed_pair_refines` + `class_fields`;
  `open_rejected` from `tlsOpenTyped_gated`), reveal (`reveal_value`, `range_value`), handshake
  (`openHandshake_value`, `verify_value`, `finish_value`).
* WF: `keyShare_wf`, `sealCtrScript_wf`, `tagScript_wf`, `updateScript_wf`, `publicScript_wf`,
  `rangeScript_wf`, `dropScript_wf`. The window: `Window.push_bound`, `push_newest`, `push_partition`;
  `Buffers.remove_gone`.
* Open: see "New gaps" below.

## C++ that becomes deletable, and when

After (1) the controller-side runner sends Lean batches (op 93) from the controller, (2) S11's
`Curve.split` / `Curve.agree` are merged, (3) the controller selects `scriptBackend` /
`scriptApplicationBackend` (and the fixtures pass, `e2e_s12.py` both modes):
* `gcm_shares.h` (all).
* `tls_kernels.h`: `derive`, `open_handshake`, `verify_finished`, `finish`, `retire`,
  `open_application`, `tagged`, `seal_control`, `seal_application`'s public-buffer paths,
  `reveal_byte`, `reveal_range`, `public_buffer`, `rotate`, `send_shares`/`receive_shares`, the TLS
  part of `Parked`/`exchange`, `typed_open`. (`begin` and the agreement go with S11.)
* `tls_worker_v3.cpp`: ops 2-7, 12, 14-16, 30, 43, op 13's public-buffer path, the window (lines
  321-329), drop-after-seal (336-338), the TLS part of op 90/91.
Kept until S13–S15: `PrivateBuffer` with `sealer` (request buffers), `seal_application`'s
private-length path and `test_produce`/`test_echo` (fixtures), `take_range` (envelope and bundle
takes, ops 48, 57).

## Performance (rounds per operation vs the C++)

A round = one batch with a data reply (an agreement plus a message delay). Every script below also
ends with a short batch of frees (no reply): an agreement only; the runner can carry it into the
next script's first batch (not done here; recommended).
* GHASH shares for a key, n powers: 1 + ⌈log₂ n⌉ rounds (C++: 1 + ⌊n/2⌋). A 30-byte record (n = 4):
  2 vs 2; n = 8: 3 vs 4; a full 16 KiB record (n = 1027): 11 vs 514. Paid once per key and size.
* Seal: 2 rounds (header ‖ ciphertext; tag) vs the C++'s 3 openings (header, ciphertext, tag), 4
  for a class seal (accepted) — in one worker operation.
* Open: 2 rounds (the bit; the event) vs 2 openings in the C++; the tag check stays inside.
* Reveal: first call 1 round (length) + 1 per range; the C++: the same openings.
* Handshake: derive 0 openings (one agreement), each handshake record 1, Finished 1, finish 1,
  authentication one agreement — as the C++ (plus S11's agreement).
The Lean side adds the agreement per batch (plan 5.2, R1) and the local GHASH arithmetic (a few
hundred GF(2¹²⁸) multiplications per record in Lean, `Ghash.multiply` on `BitVec 128`; measure: the
C++ `gf_multiply` is a 128-step loop, Lean's interpreter is slower; compile the controller).

## Tests

* Lean vectors: `node_worker/tests/lean/S12Vectors.lean` → `node_worker/tests/s12_vectors.txt`
  (`lake env lean --run`, light): two fresh traffic blocks, GHASH shares to H⁴ (key share, a local
  square, one round), a seal of "ping", an open of "hello!" under the server key, an open with a
  forged tag. 22 rounds, every batch admitted by `checkBatch`; `check ghash/seal/open/forged ok`
  (the shares XOR to the powers; the record is `TlsRecord.sealCore`; the event is application with
  the plaintext in the content handle; the forged record opens event [0, 0]). The vectors found a
  real WF bug (a free of a consumed handle in `openScript`), fixed.
* Stand-in two-party test: `cargo test --offline --no-default-features --test s12_pair` (2 tests):
  every reply of the two shells equals the Lean model's; the stand-in circuits are the vectors'
  evaluation table. All node_worker tests pass.
* Loader: `TLS_SCRIPT_KERNELS` and `tls_script_kernels_check` (a missing kernel or another layout,
  e.g. a key share opened to both, fails closed); unit test `s12_tls_kernels_fail_closed`. The TLS
  kernels are manifest kernels already (no re-export pending, so no placeholder pin).
* Real engines, NOT RUN: `node_worker/tests/e2e_s12.py`:
  `python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s12.py <node-worker>`
  (needs the seven kernels lowered into the cache: gcm-key-share, gcm-multiply, gcm-tag, gcm-check,
  tls-parser-initial, `tls-seal-ctr 23 4 0`, `tls-open-typed 32`). Its `handshake` mode is the
  handshake fixture of `check_tls_worker_v3.py` moved to the script backend: it needs the runner and
  S11 (instructions in the file).

## Checks

* `#print axioms` of the 18 section-7c entries (standalone file with the same text): `propext`,
  `Classical.choice`, `Quot.sound` only. `scripts/check_axioms.py` (all of Security.lean) NOT run: it
  needs `KernelSpecs/SlotEncoders` rebuilt, over this stage's 4 GB cap (as S10).
* `scripts/lint_node.py`: 0 findings.

## New gaps (PROOF_GAPS.md style; to add under F)

| # | Gap | Status |
|---|---|---|
| F13 | S12: T4-TLS is at the function level (kernel outputs read through the script's layout), not through `jointRun` for the seal, open, reveal and handshake scripts; the binding of `gcm-check`'s output to `tls-open-typed`'s `accepted` input is by the script's concat order (the stand-in test exercises it), not a theorem. | open |
| F14 | S12: WF proved for keyShare, sealCtr, tag, update, public, range, drop; not for `roundScript`, `sealClassScript`, `openScript`, `revealScript`, `parserScript`, the handshake scripts (the seal/open/GHASH ones pass `checkBatch` on the vectors; the handshake ones are untested). | tested / open |
| F15 | S12: `tls-derive` has a `.word` input: no model circuit for it (`circuitOf` covers byte inputs), so `deriveScript` has only `Reveals` (no value statement through the script); its correctness is `tlsDerive_spec` plus S11's agreement word. | open |
| F16 | S12: `tls-seal-class` composition (the class seal's record = the exact-size `sealCore`) not stated through the script (`recordClass_sealCiphertext_padded` exists at kernel level). | open |
| F17 | S12: `TlsBackend` (IO glue: `ensure`, the seal phases, the window, drop-after-seal, the reveal cache) is unverified Lean; `Runner` and `KeyAgreement` are parameters with written specifications only; nothing selects the backend yet. | open (engineering) |
| F18 | S12: `Wire.Bounded` (pipe round trip) not shown for the S12 scripts (as `Registry.*_bounded` for S9). | open (small) |
| F19 | S12: the stand-in pair test's circuits are a table of the Lean model's evaluations of the kernels' specifications (for `tls-open-typed`: concrete `openParsed`/`direct`, equal by `*_refines`); `e2e_s12.py` (real engines) not run; the handshake fixture not moved (needs the runner and S11). | tested / pending |
| F20 | S12: P-GHASH (e) (`genuine_rejected`, `accept_unique_pad`) not restated about the scripts; P-GHASH (a) over a whole `ensure` run through `jointRun` not proved (per round at kernel level); A-honest value-level T3 for `roundScript` not proved (hiding at the function level). | open |
| F21 | S12: Security.lean as a whole not compiled on the branch (4 GB); section 7c compiled standalone. Labels' `kinds`/`all` grew: rebuild every importer after the merge. | pending check |

## Merge notes: files touched

* New Lean: `TlsMpc/Node/Local/Ghash.lean`, `TlsMpc/Node/Flows/{TlsBase,Ghash,Tls,TlsProofs,TlsBackend}.lean`.
* Changed Lean: `TlsMpc/Node/Engine/Labels.lean` (labels of the TLS kinds 2-9; `kinds`, `all`,
  `all_codes`), `TlsMpc/Node/Flows/Registry.lean` (imports `Flows.Tls`; S12 entries in `declared`;
  `s12_flows_reveal`), `TlsMpc/Security.lean` (imports `Flows.TlsProofs`; section 7c; the P-GHASH and
  T4 items of section 8; the `sealCtr_with_tag_is_seal` docstring; `#print axioms` lines),
  `REORGANIZATION_PLAN.md` (S12 status).
* Not touched: `TlsMpc/Node/Types.lean` (no new kind: all S12 kinds existed), `Reveal.lean`, the
  controller, `Main/Session/Flow/*Legacy/Channels/Messages/Policy`, the S10 flow files,
  `TlsClient`/`TlsApplication`, every module an emitter imports (GhashShares, the kernels, only
  imported), the C++.
* Rust: `node_worker/src/loader.rs` (`TLS_SCRIPT_KERNELS`, `tls_script_kernels_check`, a test); new
  `node_worker/tests/{s12_pair.rs,s12_vectors.txt,e2e_s12.py,lean/S12Vectors.lean}`.
* With S11: `TlsBackend.KeyAgreement` above; `Flows/TlsBackend.lean` imports neither `Flows/Curve`
  nor `Local/{Field,Edwards}` (no conflict).
