# Stage S16: the remaining operations (the ceremony) — notes

Branch `s16-remaining` (from the main line `two-party-hybrid-worker` at b609702). REORGANIZATION_PLAN.md
8.1 (T3, T4-CEREMONY) and 10.2 S16. Scope of this branch: every worker operation that still had no
script flow, other than op 44 (J23), the receive width fix (J21), the selection closure check for the
legacy operations (J22) and the wiring in `Main.lean`, which another engineer does on the main line.
Ops 32, 47 and 46 (the plan's other S16 operations) were already scripts on the main line (STACK_NOTES
section 8, J11). What remained: **ops 80 and 81**, the registration ceremony. Nothing of the C++ was
deleted (that happens only after every flow has passed on the real engines); section 4 is the table
of what must be true first.

## 1. What moved from C++ to Lean

| C++ (read-only, unchanged) | Lean | File |
|---|---|---|
| `service_kernels.h` `ceremony_secrets` (689-701), dispatch op 80 (`tls_worker_v3.cpp` 202) | `Ceremony.secretsScript` / `secretsStep`, the reply `Ceremony.shareOf` | `TlsMpc/Node/Flows/Ceremony.lean` |
| `ceremony_register` (705-713), dispatch op 81 (203-208) | `Ceremony.registerScript` / `registerStep`; the record seal is S13's `Send.requestCtrScript` with `Ceremony.registerName` (the request kept as a `SendBackend.Request`), then S12's `Tls.tagScript` | `Flows/Ceremony.lean`, `Flows/Select.lean` |
| `Wires ceremony_password, ceremony_recovery; bool ceremony_sealed` | `Ceremony.State` (`made`, `secrets`) | `Flows/Ceremony.lean` |
| `TlsKernels::PrivateBuffer` with `sealer = "ceremony-register-ctr …"`, `extra["secrets"]` | `SendBackend.Request ⟨conv, name, frame, mask⟩` in `Select.Session.requests`, sealed by the `tls` group's `sealApplication` (`SendBackend.sealRequest`) | `Flows/Select.lean` |

THE SCRIPTS. Op 80: three `boolInputBoth` (each party's own seed 18, mask 22, recovery half 32 bytes
from its store slots, drawn from `Channels.random`), the concatenation in the kernel's input order,
`ceremony-secrets`, the three fields sliced (password `n + 8`, recovery `n + 9`, masked `n + 10`),
inputs and bundles freed, `masked` OPENED (label `maskedPassword`), freed; the controller's reply is
A: maskA ⊕ masked ‖ recoveryA, B: maskB ‖ recoveryB (`shareOf`), as the C++'s. Op 81: secrets := tail
(public bits, 0..2 bytes) ‖ password ‖ recovery (handle `n + 1`); the password and recovery handles
freed; the request's kernel name checked against `find`'s ranges (`registerOk`).

Deviations from the C++ (both parties change together; the legacy library keeps its own):
* The randomness comes from `Channels.random` (rule 5), not `emp::PRG`.
* **The plan's "`openBoolTo` replies" (plan 4.2 row 4) are not used**: `ceremony-secrets` declares
  `masked` PUBLIC (`pub`), and `check` allows `openBoolTo` only on bits marked for that recipient. The
  script opens `masked` to both, as the C++ does. B then knows masked ⊕ maskB = password ⊕ maskA,
  uniform for a uniform maskA (`masked_hides_list`); A knows password ⊕ maskB likewise. An
  `openBoolTo A` variant needs a kernel whose `masked` is marked `toA` (K2).
* Op 81 frees the password and recovery handles (the C++ kept the wires and refused a second op 81
  through `ceremony_sealed`); a second op 81 finds no secrets and aborts; op 81 checks `find`'s
  ranges when it is called (the C++ failed at seal time).
* The C++ needed the legacy service's upgrade state (`public_receive`); the script does not.

No `Ops` record: the ceremony has no parameter from another stage (its only neighbour is S13's
record seal, called by name); the state is `Ceremony.State`, as `Account.State`.

## 2. Selection

Group **`ceremony`** (`Config.scriptNames`, `Flows/Select.lean`): overrides `ceremonySecrets`,
`ceremonyRegister` (`Flows/Context.lean`), consulted by `Flow.Ceremony.secrets` / `register`
(`Flows/CeremonyLegacy.lean`). `Select.requires "ceremony" = [tls, masks, random, upgrade]`: the
request is sealed by the scripted record layer, and once `tls` is selected the legacy library refuses
the ceremony session's other operations (ops 33, 45: their legacy TLS phase is never reached, J22),
so `random` and `upgrade` come with it (`s16_ceremony_select`). The certificate stage of the ceremony
uses ops 47 and 32 (group `account`, so the contact set). With `SIGNAL_SCRIPTS` unset nothing
changes: the two overrides are `none` and the legacy ops 80/81 run as before.

## 3. What is proved (restated in `TlsMpc/Security.lean` section 7k)

| Theorem (Security.lean) | Statement | Source |
|---|---|---|
| `s16_ceremony_secrets_reveals`, `s16_ceremony_secrets_viewD_kinds` | T3 op 80: every release is labelled `maskedPassword` (kind 70, existing), against any adversary | `Ceremony.secrets_reveals`, `secrets_viewD_kinds` |
| `s16_ceremony_register_viewD` | T3 op 81's engine part: the adversary's view is empty (the record seal releases under `Send.requestSealKinds` only) | `Ceremony.register_viewD` |
| `s16_ceremony_flows_reveal` | every branch of `secretsScript`/`secretsStep`/`registerScript`/`registerStep` declares its kinds; the kinds are registered (`Registry.declared` has `Ceremony.secrets`, `Ceremony.register`; `declared_registered` by `decide`) | `Registry.s16_flows_reveal`, `s16_kinds_registered` |
| `s16_ceremony_secrets_wf`, `s16_ceremony_register_wf` | WF from any context with fresh ids (op 81: on handles with op 80's marks) | `Flows/CeremonyWF.lean` |
| `s16_ceremony_bounded` | the Lean sender's wires fit the pipe (ops 80, 81, the registration record phase) | `Flows/CeremonyBounded.lean` |
| `s16_ceremony_masked_hides` | 7.0's bijection form: every opened value comes from exactly one honest mask, whatever the password and the other mask | `Ceremony.masked_hides_list` |
| `s16_ceremony_shares_xor` | the two replies XOR to password ‖ recoveryA ⊕ recoveryB | `Ceremony.shares_xor` |
| `s16_ceremony_secretsOut_value` | `ceremony-secrets` on the script's bundle is `Ceremony.secrets` on the parties' bytes (`ceremonySecrets_spec`) | `Flows/CeremonyRun.lean` |
| `s16_ceremony_secrets_honest` | T4 op 80 through `jointRun`: both return `n + 8`, `n + 9` and the reference's masked value; the handles hold the reference's password and recovery password; handles below `n` untouched (hypothesis: T2 for `ceremony-secrets`, `SecretsLoaded`) | `Ceremony.secrets_honest` |
| `s16_ceremony_register_honest` | op 81's engine part through `jointRun`: the secrets handle holds tail ‖ password ‖ recovery | `Ceremony.register_honest` |
| `s16_ceremony_registerCtr_spec` | `ceremony-register-ctr` on every assignment = `KernelSpecs.sealedRequest` of `Ceremony.fill` (new kernel-level spec, as `signalRequestCtr_spec`) | `Ceremony.ceremonyRegisterCtr_spec` |
| `s16_ceremony_honest` | **T4-CEREMONY headline**: op 80 then op 81 on two honest parties: the request's secrets handle holds tail ‖ password ‖ recovery of the reference, and the register kernel on the record seal's bundle outputs `sealedRequest` of the frame filled with base64(tail ‖ password) and base64(recovery) (function level for the kernel) | `Ceremony.ceremony_honest`, `registerCtr_value`, `registerSlots_value` |
| `s16_ceremony_select` | `ceremony` is selectable with tls, masks, random, upgrade and not without any of them | `decide` |

No new reveal kind: `maskedPassword` (70) existed in `Types.lean`/`Reveal.lean`; it is now also a
label (`Engine/Labels.lean`: `Label.maskedPassword`, `kinds`, `all`, `all_codes` gain 70).

## 4. The C++ worker operations: script flow, selection, and what must be true before deletion

Dispatch of `tls_worker_v3.cpp` (`Worker::call`, behind `legacy_dispatch` in node_worker) and the
shell's own operations (`node_worker`: `engines::is_legacy` = 1-7, 12-16, 30, 32, 33, 36-38, 40-66, 80,
81; the shell's own: 8-11, 17, 39, 90-93; refused: 18-29, 31, 34, 35).

Preconditions shared by every row marked (*): (a) the group selected in a REAL session (`SIGNAL_SCRIPTS`)
with the whole F set passing in both modes (`--strict-produced`, `--link-delay-ms 1`); (b) J22 resolved
(no legacy service operation left in the session once `tls` is scripted); (c) every kernel the group
names in the produced sets' manifests; (d) the group made the default and the legacy path removed
from `Flows/*Legacy.lean` (the plan's "lint forbids Legacy"); (e) nobody runs the legacy worker binary
(`SIGNAL_WORKER=legacy`, `tls_worker_v3`) any more.

| Op | Name (`TlsWorker.Operation`) | What it does (C++) | Script flow | Selection | Test-only | Before its C++ can be deleted |
|---|---|---|---|---|---|---|
| 1 | begin | client key share (split ECDH summand) + joint random | `Tls` handshake backend (`TlsBackend.scriptBackend`, `JoinBackend.keyAgreement`) | `tls` | no | (*) ; `e2e_s12.py` handshake mode not built (F19) |
| 2 | derive | the agreement, `tls-derive` | same | `tls` | no | (*) |
| 3 | openHandshake | `tls-open-handshake` | same | `tls` | no | (*) |
| 4 | authenticate | each party's certificate decision (identical request) | local check (`Rpc.authenticate`) in the script backend | `tls` | no | (*) |
| 5 | verifyFinished | `tls-verify-finished` | same | `tls` | no | (*) |
| 6 | finish | client Finished | same | `tls` | no | (*) |
| 7 | retire | handshake keys → application keys | same | `tls` | no | (*) |
| 8 | abort | drop the connection's TLS state | shell's own (Rust) + `TlsBackend.abort` | (`tls`) | no | (e) |
| 9, 10, 11, 17 | connect, sendRecord, receiveRecord, pollRecord | the server socket, SOCKS, records | Rust shell (`server.rs`, `socks.rs`, S8) | — | no | (e): node_worker never forwards them |
| 12 | openApplication | record open (typed) | `Tls` application backend | `tls` | no | (*) |
| 13 | sealApplication | record seal (with sealers for private buffers) | `TlsBackend` + `SendBackend.sealRequest` / `RefreshBackend.sealFetch` | `tls` | no | (*) ; also the sealer path's last users: ops 42/62 (send), 56 (refresh), 81 (ceremony) |
| 14 | sealControl | WebSocket control record | `TlsBackend` | `tls` | no | (*) |
| 15, 16 | rotateSend, rotateReceive | key update | `TlsBackend` | `tls` | no | (*) |
| 18 | processWebSocket | fixture provider | none | — | yes (fixture) | refused by node_worker (`is_legacy`): (e) |
| 19, 20, 21 | providerCatalogue / Upgrade / Produce | TEST fixture provider | none (fixture session removed, S7) | — | yes | (e) |
| 22-28 | mux* | fixture mux (no case in the dispatch any more) | none | — | yes | already gone from the dispatch; the enum entries only |
| 29 | revealApplication | one revealed byte | superseded by op 43 | — | yes (retired) | (e) |
| 30 | publicBuffer | a public request as a buffer | `TlsBackend.publicBuffer` | `tls` | no | (*) |
| 31, 34, 35 | providerProduceOpen, providerSealOpen, providerRequest | private-profile fixture | none | — | yes | (e) |
| 32 | providerUpgradeOpen | authenticated WebSocket upgrade | `UpgradeAuth.authenticated` | `account` | no | (*) + the contact set: J21 fixed, J23 (op 44) scripted |
| 33 | publicRandom | joint randomness | `Random.joint` | `random` | no | (*) ; runs for real today (harness `--scripts random`) |
| 36, 37, 38, 40, 52, 63 | contactKey / Open / Seal / Evict / Assign, devicesOpen | contact table | `Contacts.op*` | `contacts` | no | (*) + J21, J23 |
| 39 | exchange | control-link exchange | Rust shell (`link.rs`) | — | no | (e) |
| 41, 42, 61, 62 | contactSend / Request, devicesSend / Request | sealed-sender send | `Send.*`, `SendBackend` | `send` | no | (*) + J21, J23; F59d (89-byte text, devices) |
| 43 | revealRange | server-byte reveal | `TlsBackend.revealRange` | `tls` | no | (*) |
| 44 | contactAdmit | TEST: a contact from the export into the table | **none** (J23, the main line's engineer) | — | yes (TEST) | a script for it (J23), then (*) |
| 45 | publicUpgrade | anonymous WebSocket upgrade | `Upgrade.publicUpgrade` | `upgrade` | no | (*) |
| 46 | accountAdmit | TEST: the account from the export | `Account.admitStep` | `account` | yes (TEST) | (*) + the contact set |
| 47 | accountCredentials | the credential shares in | `Account.credentialsStep` | `account` | no | (*) + the contact set |
| 48, 49, 50, 51 | envelopeTake / Drop / Open / Session | receive a first message | `Receive.*`, `ReceiveBackend` | `receive` | no | (*) + **J21** (receive-session width defect) |
| 53, 54, 55 | accountKey / Seal / Open | the account record at rest | `Account.keyStep` / `sealStep` / `openStep` | `account` | no | (*) + the contact set |
| 56-60, 64, 65 | bundleFetch / Take / Drop / Shape / Establish, scratchSeal / Commit | device refresh | `Refresh.*`, `RefreshBackend` | `refresh` | no | (*) + J21, J23; `e2e_s15.py` refresh mode (F48); ORD-2 rerun |
| 66 | contactsPrepare | per-contact curve preparation | `ContactsPrepare.prepareOneG` (non-hinted) | `curve` | no | (*) + the contact set; the hinted path (J3) or `TLS_WORKER_HINTED` retired (J20) |
| **80** | ceremonySecrets | the two passwords made in the engines | **`Ceremony.secretsStep`** (this branch) | **`ceremony`** | no | (*) ; K7, K8: the ceremony run once on the local server with `--scripts …,ceremony` and the ceremony kernels in the produced set |
| **81** | ceremonyRegister | the registration request into the engines | **`Ceremony.registerStep`** + `Send.requestCtrScript` | **`ceremony`** | no | as op 80 |
| 90, 91, 92 | useConnection, resetConnection, closeConnection | connection table | Rust shell (`connections.rs`) | — | no | (e) |
| 93 | batch | a script batch | Rust `interp.rs` (the scripts' only operation) | — | no | stays |

After every row above: the plan's S16 list (delete `legacy_abi.cpp`, `service_kernels.h`,
`tls_kernels.h`, `dyn_word_mask.h`, `x25519_fast.h`, `split_ecdh.h`, `edwards_points.h`,
`hinted_points.h`, `gcm_shares.h`, `field_program.h`, `kernel.h`, `tls_worker_v3.cpp`; the legacy
wrappers in `Reveal.lean`; the lint forbids `Legacy`; `Security.lean` version 2).

## 5. Kernels and field programs

No kernel or field program was created; no module in a flat emitter's import closure was edited
(`lint_node.py` emitter-isolation: 0 findings). The ceremony needs two existing kernels:
`ceremony-secrets` and `ceremony-register-ctr SIZE PAYLOAD AUTH TAIL RECOVERY` (one shape per frame
size; the frame's size depends on the account's keys). **Neither is in the local or the compact
set's manifest**; the production set's manifest was not read (`real_signal/state/` may not be read).
For the next manifest production: `ceremony-secrets` and the `ceremony-register-ctr` shapes the
ceremony uses (the kernel cache holds `5584 8 5552 1 365` from the C++ ceremony). Optional for a
re-lowering (K2): a `ceremony-secrets` whose `masked` output is marked `toA`, for the plan's
`openBoolTo` form.

## 6. Tests

* Lean vectors: `node_worker/tests/lean/S16Vectors.lean` → `node_worker/tests/s16_vectors.txt` (`lake
  env lean --run`, 1.3 s): flow `s16-ceremony` (A's traffic block, op 80, op 81's engine part, the
  registration record phase on `ceremony-register-ctr 5584 8 5552 1 365`, a 5584-byte frame with zero
  slots), 6 rounds, every batch admitted by `checkBatch`; `check masked/shares/secrets/request ok`.
  Stand-ins: `ceremony-secrets` as its reference, the register kernel as the right-hand side of
  `ceremonyRegisterCtr_spec`.
* Stand-in pair test `node_worker/tests/s16_pair.rs` (`cargo test --offline --no-default-features
  --release --test s16_pair`): 2 tests pass; every reply of the two shells equals Lean's model.
* **Real engines**: `node_worker/tests/e2e_s16.py` (`python3 scripts/guarded.py --heavy 16 1800 python3
  node_worker/tests/e2e_s16.py NODE_WORKER`, the kernels from the cache, pins checked): **PASS** on the
  malicious build (v3): 6 rounds, every reply byte-identical to Lean's, 62 s wall (the rounds: 0.6 s
  including engine start, op 80's round 0.01 s, the register kernel's round 1.22 s; the rest is
  process start-up and shutdown), peak 2.68 GB; **PASS** on the semi-honest build (sh-v3): 60.5 s
  wall, register round 0.22 s, peak 0.96 GB. Both used the cache's `lean-dcb2cdfee127867b` kernels.
* Runner test `node_worker/tests/lean/RunnerTest.lean`: + 7 checks (`ceremony-secrets-shares`,
  `ceremony-password-base64`, `ceremony-secrets-once`, `ceremony-register-secrets`, `-name`, `-freed`,
  `-once`): 37 checks, all ok.

## 7. Gaps (PROOF_GAPS.md style; to be copied there)

| # | Gap | Status |
|---|---|---|
| K1 | Value-level T3 for op 80 against any adversary (the view is a prefix of [masked] with masked = password ⊕ maskA ⊕ maskB by value) is not stated; proved: the kinds (`s16_ceremony_secrets_viewD_kinds`) and the hiding of the value in the bijection form at function level (`s16_ceremony_masked_hides`). The probability statement (uniform honest mask ⇒ uniform opened value) is argued, as `CeremonyProofs.masked_hides`. | open |
| K2 | The plan's `openBoolTo` replies (4.2 row 4) are not used: `ceremony-secrets` marks `masked` public, so it is opened to both (as the C++). B learns password ⊕ maskA (uniform). A kernel with `masked` marked `toA` (re-lowering) would let B see nothing. | note / optional kernel |
| K3 | T2 for the ceremony kernels: `secrets_honest` assumes `SecretsLoaded` (the circuit named `ceremony-secrets` computes the Lean kernel); `ceremony-register-ctr` is related to the script only at the function level (`registerCtr_value`), no model circuit hypothesis for it is used in a run theorem. | conditional |
| K4 | The registration request's record phase is S13's `Send.requestCtrScript` then S12's tag: no run theorem for it with the register kernel (S13's `requestCtr_joint` / `send_joint` are about `signal-request-ctr`); `ceremony_honest` stops at the secrets handle plus the kernel at function level. | open |
| K5 | WF composition: `secretsScript_wf` has no postcondition (WFP) giving the password/recovery handles' marks; `registerScript_wf` takes them as hypotheses. | open (small) |
| K6 | IO glue unverified: `Select.ceremonySecrets` / `ceremonyRegister` (randomness stashed and released, the shares computed from this party's `Secret` randomness and the opened value, the request kept as a `SendBackend.Request` and sealed by `sealApplication`). Exercised by RunnerTest (stand-in kernel) only. | open (engineering) |
| K7 | The ceremony was not run in the real harness with `--scripts …,ceremony` (the register stage talks to the local server's verification flow; the certificate stage needs `account`, so the contact set, blocked by J21/J23). Real engines: `e2e_s16.py` passes on the malicious and the semi-honest builds (the scripts' batches with the cached kernels; not the IO glue, not the tag phase, not a server). | pending |
| K8 | The ceremony kernels are in neither the local nor the compact set's manifest (production not checked: may not be read); with `--strict-produced` the `ceremony` group's batches would be refused (fails closed). Add them at the next manifest production. | pending (manifest) |
| K9 | `registerOk` transcribes `CeremonyKernel.find`'s conditions for `ceremony-register-ctr` (no theorem `registerOk → find (registerName …) = some _`); a name `find` refuses fails closed when loaded. | open (small) |
| K10 | `loader.rs` has no fail-closed layout check for the ceremony kernels (as `send_script_kernels_check`); a different layout makes `check` refuse the batch (fails closed, less precise message). | open (small) |
| K11 | Once per session (op 80 once, op 81 once after it) is enforced by the controller's `Ceremony.State` and by op 81 freeing the handles; no session-level theorem. | note |
| K12 | `Select.requires "ceremony"` adds `random` and `upgrade` because of J22 (legacy ops 33/45 refused once `tls` is scripted); asserted by `s16_ceremony_select` for the list, not derived from the legacy library's preconditions (J22's check is the main line's). | note |

## 8. Checks

* `lake build TlsMpc TlsMpcSecurity public_service_controller`: all built (61 s, peak 8.1 GB).
* `scripts/check_axioms.py`: 772 restated theorems (757 + 15 of section 7k), only `propext`,
  `Classical.choice`, `Quot.sound` (3 entries depend on `bv_decide`, as before); `SECURITY_AXIOMS.txt`
  regenerated.
* `scripts/lint_node.py`: 0 findings. Controller `recovery-check` 29/29, `policy-check` 14/14.
* node_worker: `build.sh` v3, v3-test, sh-v3, sh-v3-test built; `cargo test --offline
  --no-default-features --release`: all pass (lib 46, every integration test, `s16_pair` 2).
* No `sorry`, `native_decide`, axiom, `partial def`, `unsafe`, `opaque`, `extern`, Mathlib; no new
  `bv_decide`.

## 9. Files

* New Lean: `TlsMpc/Node/Flows/{Ceremony,CeremonyWF,CeremonyRun,CeremonyBounded}.lean`.
* Changed Lean (pure additions): `Engine/Labels.lean` (`maskedPassword`; `kinds`, `all`, `all_codes`),
  `Flows/Registry.lean` (import; `declared` entries), `Flows/Context.lean` (two overrides),
  `Flows/CeremonyLegacy.lean` (consult the overrides), `Flows/Select.lean` (import, `requires`, the
  session's `ceremony` state, `ceremonySecrets`, `ceremonyRegister`, the override entries, the doc
  table), `Config.lean` (`scriptNames` gains `ceremony`), `Security.lean` (imports, section 7k,
  section 8 item, `#print axioms` lines).
* Tests: `node_worker/tests/{s16_pair.rs,s16_vectors.txt,e2e_s16.py,lean/S16Vectors.lean}`,
  `node_worker/tests/lean/RunnerTest.lean` (section 8).
* Not touched: `Main.lean`, `Session/*`, `Types.lean`, `Reveal.lean`, every emitter's import closure,
  the C++, `PROOF_GAPS.md`.
