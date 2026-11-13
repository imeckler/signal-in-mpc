# The scripts stack: S10–S15 joined (`scripts-stack`) — notes

Branch `scripts-stack`, made from `s10-conversions` (5c66a85, which contains `field-programs-v3`),
then `s11-curve`, `s12-tls`, `s13-send`, `s14-receive`, `s15-refresh` merged one at a time, the
parameters joined (`TlsMpc/Node/Flows/Join.lean`, `JoinBackend.lean`), `s11-curve` merged again at
its later tip, and finally the main line `two-party-hybrid-worker` (18eeba7) merged in. Nothing was
pushed; no branch other than `scripts-stack` was moved.

## 1. Merge log

| # | Merge | Conflicts | Resolution |
|---|---|---|---|
| 1 | `s11-curve` (8757b7e) | none | — |
| 2 | `s12-tls` (64f223f) | `Engine/Labels.lean` (labels, `kinds`, `all`, `all_codes`); `Flows/Registry.lean` (imports, `declared`, `s11_flows_reveal` vs `s12_flows_reveal`); `Security.lean` (both 7c sections; section 8 P-GHASH / P-SPLIT items; `#print axioms`) | union everywhere, S11 before S12 in the lists; S12's section renumbered 7c → **7d** (and its two cross-references) |
| 3 | `s13-send` (f244984) | `Labels.lean` `all_codes` (git merged `kinds`/`all`) | union; S13's section renumbered 7d → **7e** (and its section 8 reference) |
| 4 | `s14-receive` (0ebc9d7) | `Labels.lean`, `Registry.lean` (imports, `declared`), `Security.lean` (imports, the S13/S14 sections, section 8 SEND/RECV items), `loader.rs` (`FIELD_PROGRAMS`: S11 and S14 placeholder pins; the s13/s14 fail-closed unit tests) | union; S14's section 7d → **7f**; S14's section 8 text became its own bullet `T4-RECV` |
| 5 | `s15-refresh` (5a6b054) | `Labels.lean`, `Registry.lean` (imports, `declared`, `s14`/`s15_flows_reveal`, the S13 and S15 `*_bounded` sections), `Security.lean` (imports, sections, section 8 T4-REFRESH / ORD-2, prints), `loader.rs` (`send_script_kernels_check` vs `REFRESH_SCRIPT_KERNELS`; the s13/s14/s15 tests) | union; S15's section 7d → **7g**; every theorem and test of every side kept |
| 6 | join commit d1a82f8 | — | `Flows/Join.lean`, `Flows/JoinBackend.lean`, `Reveal.ephemeralPublic` (pure addition to `TlsMpc/Node/Reveal.lean`) |
| 7 | `s11-curve` again (74b2ea1: `CurveWFBase`, `CurveWF`, `CurveLive`, `CurveCommit`, `CurveHonest`) | `Security.lean` only (imports; the section 8 S11 item; prints) | S11's new section 8 text replaces its old one, S12's P-GHASH item kept; all prints kept; the merge also added the `Join` imports |
| 8 | main line `two-party-hybrid-worker` (18eeba7: emitter batch 5c047ac, S8 switch c33b261, policy/ordering proofs, Stock, Rotation, PROOF_GAPS.md) | `Security.lean` (imports; section 7a engine theorems: S9's program-instruction entries vs the main line's `withAdv_bind`/`jointRun_bind`/unusable-batch/counter entries; the main line's new section "7b. Labels, the reveal registry and batching" vs the stack's 7b–7g); `SECURITY_AXIOMS.txt` (generated) | both kept; the main line's 7b renamed **7-labels** (the stack's 7b is S10), placed after 7h; `SECURITY_AXIOMS.txt` regenerated (section 3). `Reveal.lean`, `Types.lean`, `BundleSlots`, `BundleSlotWhole`, `ReceiveAcceptText`, `Engine` merged without conflict |
| 9 | `Refresh.slotFiller` | — | `'0'` (48) → NUL (0), with a JOIN NOTE next to it (the main line's emitter batch made the bundle-slot padding NUL); `s15_vectors.txt` regenerated (section 3) |
| 10 | `s11-curve` final tip (6d65fdc: `CurveRun.lean`, `quotientMany_honest`, `agree_honest`) | none | compiled on the stack (standard axioms); not yet restated in `Security.lean` (S11's engineer adds the entries) |

Labels after the merges (`Label.all_codes`): `[100, 101, 30, 31, 80–87, 90, 91–95, 102, 2–9, 40, 41,
50–57, 60–62]` — every code is `RevealKind.code` of its kind, so no value clashed;
`kinds_nodup`, `all_distinct`, `all_nonzero`, `declared_registered` (by `decide`) prove on the union.

Section numbering of `Security.lean` on the stack: 7a (S9), 7b (S10, and "7b continued"), 7c (S11),
7d (S12), 7e (S13), 7f (S14), 7g (S15), **7h (the joins)**, 7-labels (the main line's S6/S9 registry
section), 7-channels, 7-reveal as before; section 8's open lists merged item by item.

## 2. The join table

| Parameter (branch) | Instantiation | What it discharged | What remains assumed / open |
|---|---|---|---|
| S12 `TlsBackend.KeyAgreement Sc` | `JoinBackend.keyAgreement r fr : KeyAgreement SplitState`. `begin`: summand as `split_ecdh.h` (`&= 248`, `&= 31`), `Curve.splitShare` locally, `Curve.splitBegin`. `agree`: peer rejected publicly unless `liftU` gives a valid point; `Curve.splitAgreeInputs` locally; `Join.splitAgreeWord` = `Curve.splitAgree`, abort on the zero flag, `Convert.fieldToWord`, free. `erase`: nothing in the engines | the written spec's kinds: `Join.splitAgreeWord_reveals` (`keyAgreementKinds` = P-SPLIT ∪ P-F2W), `begin` = `Curve.splitBegin_reveals`; all registered (`join_kinds_registered`) | ADAPTER `FieldRunner` (`allocF`, `stashElems`, `takeWord`): S12's `Runner` has Boolean ids only, no field slots, no pool — the runner that exists one day must supply them from the same counters / the one pool. The value (`X25519(k_A + k_B, peer)` as the word) is not proved through `jointRun` (S11's `splitAgree_montU` + S10's `f2w_honest` compose, not done). S12's spec text says "no other release than P-SPLIT's": the join also opens P-F2W's masked value (`maskedFieldValue`), which S12's spec names as its conversion — say so in S12's doc when merged. A quotient whose `u` is 0 without the zero flag (num + den = 0) is not rejected (an honest server's share in the prime-order subgroup with k ≢ 0 mod ℓ never gives it) |
| S13 `SendBackend.Curve` | `JoinBackend.sendCurve r fr src`. `ephemeral id`: τ from `Random.joint` (commit-then-open, `Curve.offsetOf`), 128 mask contributions, `Join.ephemeralWord` = `Curve.offsetStep` + `fieldToWord`; the key `toBytes u` through **`Reveal.ephemeralPublic`** (added to `Reveal.lean`, pure addition; documented bound `s11_ephemeralKey`). `staticAgreement`, `senderPublic`: `SendSources` (op 66's cached words, account state) | `ephemeralWord_reveals` (`ephemeralKinds` = P-OFFSET ∪ P-F2W, plus `Random.jointKinds`), registered; the S13 note "S11 must add `Reveal.ephemeralPublic`" is done | `SendSources.offsets` / `statics`: the per-contact caches (op 66 `Curve.prepareContacts`, `offsetPrepare`) — op 66's contact-table glue is F32 (open); the IO glue unverified (F55); `offsetStep` through `jointRun` open (F22) |
| S14 `Receive.Curve` (`agree`, `signature`, `baseCheck`, `kinds`, the three `Reveals` fields) | `Join.receiveCurve sl pm` = S14's `Curve.withPrograms` (its own program-based `signature`, `baseCheck`) with `agree := Join.receiveAgree sl`: per job `Convert.sharedBits` (P-BITS) of the scalar's swap-bit shares, the point (handle, or public 9), S11's `Curve.agree` for all jobs in one instruction + one quotient round, abort on a zero flag, S14's `toWord`; everything made is freed, the inputs are not | the three `Reveals` fields PROVED (`receiveAgree_reveals`); `receive_joined_reveals`: `openFirst_reveals` / `session_reveals` with the curve instantiated, and every kind registered; **J1 RESOLVED** (section 7): every field-element input of ops 50/51 reads a slot TAKEN from `Receive.St.slots` (`Gen.takeSlot`; `programStep` and `receiveAgree` take theirs), proved read once on every run (`JoinOnce.openFirst_reads_once`, `session_reads_once`) | the coins: `AgreeSlots` keeps only `coins : Scalar → Nat` (re-reading a coins slot is harmless: P-BITS opens only the bit checks); the IO side must stash the coins for `own` and `fresh` scalars and, for `identity`, has none (J8: op 55 leaves the identity's swap bits as FIELD HANDLES, `Account.Opened.swaps`, not a coins slot) |
| S15 `Refresh.CurveOps` (`lift`, `check`, `agree`, id blocks, `kinds`) | `Join.refreshOps rc`: S14's `Gen` run on a table holding just the caller's counters and the masks taken for this call (`runAt`); `lift` = W2F, `xeddsa-recover`, F2W ×3; `check` = W2F ×2, B2F ×2 (510 bits each), `xeddsa-check` ×2 (separate mask slots), F2W ×4; `agree` = W2F of the points, `receiveAgree` on the seven jobs of `service_kernels.h` line 850 (dh1, dh2, dh3, ratchetAgreement, basePublic, ratchetPublic, dh4); id blocks `liftIdsOf`, `checkIdsOf`, `agreeIdsOf` | **S15's hypothesis `CurveOps.Reveals` DISCHARGED** (`refreshOps_reveals`); `refresh_joined_reveals`: `opEstablish_reveals` / T3 with no curve hypothesis, all kinds registered | **SIBLING OF J1, FIXED**: one `pool` served `lift`, `check` and `agree` of a step, so step 0 of device 0 gave `check` the word masks `lift` had used and freed (the engine refuses a freed handle: that step always aborted); `RefreshCurve` now has a pool and a slot supply per call (`splitPool` / `split_disjoint`; `RefreshBackend.curveFor` takes them from the session pool and new slots, `refreshOps_reads_once`). `RefreshBackend` exists (F46); the id blocks are counted upper bounds, not proved (WF of the joined scripts open, F44); non-hinted path only (S11's hinted `lift`/`signatures` not wired: they return field handles and need the `Staged` local step) |
| S15 send parameter (S13 `sealDevices` / `requestDevices`; `first_wired`'s `hconv`, `hpend`) | `Join.join_first_wired`: for the bundle S13's `devicesScript` builds (certificate ‖ stored record, pending, address, text, four words), `Send.bundleSeal_get` gives the kernel's `conversation`/`pending` inputs; `Refresh.stored_record` + `kept_outputs` close `first_wired` | `hconv`, `hpend` of `first_wired` (F45 send half / F46-in-branch-numbering) for S13's layout | `hcert` (the certificate bytes S13 prefixes are the session's certificate input: the same account certificate handle) and `hpend` (the pending block in the stored state is the session's), and that the record S13 slices from the committed state is `out₁.drop cert`: facts about the BYTES in handles across scripts (S13 `devicesScript` → S15 `opCommit` → S13), not proved through `jointRun` |

## 3. Build, tests, axioms

**Lean modules.** The `.lake/build` of the S12 worktree was copied (2.6 GB) and every module whose
olean could not be trusted was recompiled one at a time (`lake env lean -o`, guarded 8 GB): every
module changed since the branches' base on the main line (35ad303) — the six branches', the main
line's (merged in), `Engine/Labels` and everything importing it (`kinds`/`all` grew), and five
modules whose copied oleans were built from the main line's NEWER sources (checked by comparing the
`.ilean` declaration positions with the sources: `Node/Reveal`, `BundleSlotWhole`,
`ReceiveAcceptText`, `Policy/ReceiveInvariant`, `Policy/ReceiveProofs`; also forced:
`Signal/BundleSlots`, the S15 note's suspect). Modules byte-identical to the S12 worktree's sources
and built there were reused. Result: all 108 + the join modules compile, no errors; peak 6.2 GB
(`KernelSpecs/SlotEncoders`).

**`Security.lean` as a whole**: `guarded.py --heavy 12 3600 lake env lean TlsMpc/Security.lean`:
exit 0, no error, 11 s, peak 1.8 GB (the closure was prebuilt). `scripts/check_axioms.py
--from-log`: **636 restated theorems, only `propext`, `Classical.choice`, `Quot.sound`** (2 entries
depend on `bv_decide`, as before); `SECURITY_AXIOMS.txt` regenerated and committed. (After J1 and
the runner, section 7: 644 restated theorems, 10 s, 1.76 GB, only the three standard axioms.) This closes the
"Security.lean not compiled as a whole" items of all six branches (PROOF_GAPS F10, F21, F50, F59).

**`scripts/lint_node.py`**: 0 findings (io-baseline, escape-hatches, emitter-isolation, secret-val,
message-fields, flow-calls, session-state). No `sorry`, `native_decide`, axiom, `partial def`,
`unsafe`, `opaque`, `extern`, Mathlib or new `bv_decide` in the join files.

**Lean vectors**, regenerated on the merged stack (`lake env lean --run`) and compared with the
committed files: `engine_vectors`, `s10`, `s11`, `s12`, `s13`, `s14` byte-identical (before and after
the main-line merge); `s11_curve_vectors` differs only by eight benchmark lines (`time scalar-mult
… us`) that `S11Curve.lean` prints and the committed file omits — not a content change, not
installed; `s15_vectors` changed after `slotFiller` became NUL: only the filler bits of
`bundle-slot`'s input bundle and the stand-in evaluation entries keyed by them differ, every `check
… ok` line is unchanged — installed (commit f0035e0).

**Rust** (`cargo test --offline --no-default-features --release`, target under scratch-stack/,
guarded 8 GB), after every merge and at the end: all pass — lib 44 (incl. `s12_tls_kernels_fail_closed`,
`s13_send_kernels_fail_closed`, `s14_receive_kernels_fail_closed`, `s15_refresh_kernels_fail_closed`,
the placeholder-pin test), `batch_pair` 3, `engine_vectors` 1, `program_vectors` 3, `s10_pair` 3,
`s11_curve` 1, `s11_pair` 3, `s12_pair` 2, `s13_pair` 2, `s14_pair` 2, `s15_pair` 2 (on the
regenerated vectors), `shell_pair` 2, `socket_owners` 2, `socks_proxy` 1. Real-engine fixtures
(`e2e_s10.py` … `e2e_s15.py`) not run (heavy, need the V3 re-export and lowered kernels).

## 4. Open proof gaps, de-duplicated (PROOF_GAPS.md style; numbers are PROOF_GAPS.md's)

The branches' notes numbered their gaps independently (S12 F13–F21, S11 F22–F34, S14 F35–F41,
S15 "F42–F50", S13 "S13-1…9"); PROOF_GAPS.md (main line) renumbered them F7–F59: S15 is F42–F50 there
and S13 is F51–F59. The table uses PROOF_GAPS.md's numbers; "join" marks what the joins changed.

| # | Gap | Status on the stack |
|---|---|---|
| F7, F9, F12 | S10 P-CUT scope notes; P-BITS/B2F run level; the counting model's probability part (uniform arrangement, `IdealCommit`, SHA-256 as RO) | as PROOF_GAPS.md (F7, F9 closed with scope notes) |
| F8 | `_wf` for `wordToField`, `fieldToWord`, `bitsToField`, `Account.openStep` | open (tested) |
| F10, F21, F50, F59 (part) | Security.lean not compiled as a whole on the branches | **closed** on the stack (section 3) |
| F11, F31, F40 (pins) | placeholder pins until the V3 re-export (S10's three, S11's 14, S14's three); `e2e_s1x.py` not run | pending (fail closed) |
| F13, F35, F42, F51 | T4 (TLS, RECV, REFRESH-KEM/session, SEND) at function level, not through `jointRun` | open |
| F14, F37, F44, F54 | WF / `Wire.Bounded` not proved for: S12 `roundScript`, `sealClassScript`, `openScript`, `revealScript`, `parserScript`, handshake scripts; S14 `takeScript`, `openFirst`, `session`; S15 `fetchScript`, establishment, `scratchSealScript`, `opCommit`'s `Table.Inv`; S13 ops 61/62 | tested / open; **join**: the joined scripts' WF is open too (id blocks counted, `Join.liftIdsOf` …) |
| F15, F53 | `.word` inputs: no model circuit for `tls-derive`; `shapedCircuit` extends T2 | open / assumed |
| F16, F52, F58 | class-seal composition; op 61 headline and `bundle-seal` output slicing; `bundleEnvBytes` | open |
| F17, F39, F46, F55 | IO glue unverified: `TlsBackend`, `ReceiveBackend`, `SendBackend`; no `RefreshBackend`; nothing selects them | **F46 closed** (`Flows/RefreshBackend.lean`, `legacyApi` type check); **"nothing selects them" closed** (`Flows/Select.lean`, `SIGNAL_SCRIPTS`); the runner exists and supplies every runner interface from ONE state (`Runner.tls`, `.field`, `.receive`; `SendBackend.TableRef`: the table and the counters are the runner's: F55's counter join done). Still open: the glue is unverified (only the runner's pure core is proved) |
| F18 | `Wire.Bounded` for S12 scripts | open (small) |
| F19, F48, F56 | stand-in circuits in pair tests; e2e not run | tested / pending |
| F20 | P-GHASH (e) for scripts; (a) over a whole `ensure`; A-honest value T3 for `roundScript` | open |
| F22 | S11 honest runs through `jointRun` | partly closed by S11's follow-up (`splitBegin_honest`, `pointExchange_honest`, `quotientMany_honest`, `agree_honest`, `splitAgree_montU`); open: `offsetPrepare`, `offsetStep(Fast)`, `lift`, `tables`, `agreeHinted`, `agreeAffine`, `signatures`, `torsion`, `prepareContacts`. **join**: the joined compositions (`splitAgreeWord`, `ephemeralWord`, `receiveAgree`, `refreshOps`) through `jointRun` open (the pieces for split + F2W and the ladder now exist) |
| F23 | `_wf` for S11 scripts | **closed** by S11's follow-up (`CurveWF`) |
| F24 | value-level T3 for curve flows | partly closed (`pointExchange_disclosure`); open for the others and the joins |
| F25 | `commit_open_sound` for `pointExchange` | **closed** (`pointExchange_sound`) |
| F26 | `randomPoint` uniform on the group | assumed |
| F27 | P-HINT (c), (d) composed with the runs | open |
| F28, F33 | complete addition, liveness of local hints | closed in part (`addU_den_ne_zero` with `proofs/` `edwards_complete`; `sqrt_complete`, `roots_isSome`); `decode (encode P)`, `toAffineAll` tested only |
| F29, F30, F34 | local arithmetic vs a reference (tested); `shapeOf` counts; `recode` equality in `proofs/` | tested / open (small) |
| F32 | op 66's contact-table glue | open; **join**: `JoinBackend.SendSources` needs its outputs (offset states, static words) |
| F36, F47 | value-level T3 for whole receive / refresh runs | open |
| F38, F43 | output widths (receive kernels; `KemWidths`, `SessionWidths`) assumed / loader-checked | conditional |
| F41, F57 | `Reveal` wrappers applied in glue; `seal_refused_silent` structural | note / open |
| F45 | S15's joins: `CurveOps` with `Reveals` as hypothesis; the send's `bundle-seal` binding | **join**: `CurveOps.Reveals` DISCHARGED (`refreshOps_reveals`, `refresh_joined_reveals`); the binding derived for S13's layout (`join_first_wired`); remaining: `hcert`/`hpend` (bytes in handles across scripts) |
| F49 | slot filler NUL after the emitter batch | **closed** (commit 478aa86) |
| F59 (ORD-1) | ORD-1 not restated over the Lean send flow | open |
| J1 | S14 join: one mask slot for op 50's two agreements (the openings `z·m` revealed a ratio) | **closed** (section 7): supply `Receive.St.slots`, `Gen.takeSlot`; `JoinOnce.openFirst_reads_once`, `session_reads_once`, `refreshOps_reads_once` (Security 7i `j1_*`) |
| J2 | `FieldRunner`: S12/S13 `Runner` lacks `allocF`, `stashElems`, the mask pool | **closed** (engineering): `Runner.field` (same counters, same pool) |
| J3 | the joins use the non-hinted path only (S11's hinted `lift`, `signatures`, `torsion` return field handles and need the `Staged` local step; not wired to S14/S15) | open |
| J4 | `flow-calls` lint vs the script backends' `Reveal.*` | **closed**: allowlist widened to `Flows/*Backend.lean`, `Flows/Runner.lean`, `Flows/Select.lean` (same makers as the legacy flows; no second set in Reveal.lean); the pattern no longer matches `KernelSpecs.Reveal.*` |
| J5 | S12 spec text vs join: the agreement also opens P-F2W's masked value (`maskedFieldValue`), not only P-SPLIT's kinds; u = 0 without the zero flag not rejected (impossible for an honest server's subgroup share) | note |
| J8 (new) | the joined agreements take the identity scalar as a COINS slot of this party's swap-bit shares, but op 55 (`Account.openStep`) leaves the identity's swap bits as FIELD HANDLES (`Opened.swaps`); the controller holds no share to make coins from. Receive and refresh cannot run until `Scalar.identity` maps to those handles (an S14/S15 `Job` change) | open (design) |
| J9 (new) | `Main.session` still calls `Worker.start`; the switch is `Worker.startWith … config.agreed …` (one line, Select.lean's doc), and the manifest's kernel names / V3 mask counts must be passed for receive | open (main line) |
| J10 (new) | the runner's IO loop is `drive`'s steps by construction (an IO function), not by a theorem; the fake-pair test runs it against the model's shells | note |
| J11 (new) | `account` cannot be selected: the authenticated upgrade (op 32, S16) reads the credentials from the legacy worker; `contacts`, `send`, `receive`, `refresh` need `account` and `curve` (F32) with them (no handle sharing with the legacy library: `legacy_get`/`legacy_put` not built) | open |
| J12 (new) | the script account state (`Account.State`) has no sender-key word; the send's `senderPublic` and the refresh's `Refresh.Account` need it | open (engineering) |
| J13 (new) | the runner's store never frees a slot (stashed values stay for the session) | open (small) |

## 5. When this stack meets the main line

The main line (18eeba7) is already merged into `scripts-stack` (merge 8). What remains when the
integration engineer takes the stack:
* **Emitter batch** (in): bundle-slot filler NUL — `Refresh.slotFiller` = 0 and S15's vectors
  regenerated; S15's theorems used the kernel theorems by name, all still prove. `receive-text`'s
  acceptance was tightened on the main line: S14 uses `text_status`, `text_accepted`,
  `text_zero_unless_accepted` by name only; everything compiled and `s14_vectors` regenerated
  byte-identical (its stand-in tables do not exercise the kernel), so the tightened acceptance needs a
  real-engine run (`e2e_s14.py`) to be exercised.
* **The session modules** (`TlsMpc/Node/Session/*`, merged from the main line): `Session/Pool.lean`
  should take S12's per-connection `Tls.Conn Curve.State` / `Tls.Buffers` / the counters
  (S12_NOTES.md "The Session/Pool change"), and the runner's counters must be the contact table's
  `Table.ctr` (S13-5 / F55) and the source of `FieldRunner.allocF`. `Session/RefreshProofs.lean`
  (ORD-2) must be rerun when `Flow.Refresh` switches (S15's `*_entries` lemmas are its premises).
* **The controller-side script runner** exists (`Flows/Runner.lean`, section 7); the selection
  (`Flows/Select.lean`) needs the one line in `Main.session` (J9).
* **The field-program re-export** (FIELD_PROGRAMS_V3.md): one heavy run of
  `export_field_v3.py`; paste the pins into `loader.rs` `FIELD_PROGRAMS` (S10's three, S11's 14,
  S14's three placeholders `PIN_FROM_REEXPORT`), write `field-mask-sub.v3` from the S10 vectors'
  `native` line; the S11 vectors' `pin` lines must equal the export's.
* **S8 switch** (merged): the controller spawns node_worker by default; with the runner and the
  selection (section 7) a flow switches by the agreed setting `SIGNAL_SCRIPTS`.

## 6. Order in which to switch flows from legacy to scripts (`SIGNAL_SCRIPTS`, section 7)

Every step needs J9 first (the one line in `Main.session`). `Select.check` enforces the "needs"
column at session start.

| # | Group(s) | Needs selected with it | Precondition before switching |
|---|---|---|---|
| 0 | `random` (op 33) | nothing | none: exchanges only, no engine call; runnable on the real engines today (`--scripts random`) |
| 1 | `masks` (S10 pool, refilled on demand) | — | the V3 re-export (`field-mask-sub` and S10's programs pinned); the legacy C++ pool keeps running beside it (R5) |
| 2 | `tls` (S12 + split ECDH, `JoinBackend.keyAgreement`) | `masks` | the re-export (split ECDH's programs); `e2e_s12.py`; the per-connection state moves into `Session/Pool` (S12_NOTES "The Session/Pool change"; kept in `Select.Session.conns` until then) |
| 3 | `upgrade` (op 45) | `tls` | none beyond 2 (op 45's legacy receive state is read only by the legacy record layer) |
| 4 | `curve` (op 66) | `contacts`, `masks` | F32: op 66's contact-table glue (offset states and static words into the contact entries) |
| 5 | `contacts`, `account`, `send`, `receive`, `refresh` (together) | each other, `curve`, `tls`, `masks` | J11 (op 32 reads the legacy credentials: S16, or handle sharing with the legacy library), J12 (the sender-key word), J8 (identity coins for receive and refresh), the receive manifest names (J9), ORD-2 rerun for refresh, `e2e_s13.py`/`e2e_s14.py`/`e2e_s15.py` |

## 7. J1, the runner, the selection, the tests (this agent's work on `scripts-stack`)

**J1 (fixed).** `Receive.St` has a supply `slots : List (Nat × Nat)` of store slots of this
party's fresh field-element contributions; `Gen.takeSlot count` hands out the first entry and removes
it (abort if absent or of another size). `programStep` takes its mask slot from it (`ProgramMasks`
keeps only the counts: `checkSlot`, `recoverSlot`, `torsionSlot` removed) and `Join.receiveAgree`
takes its quotient-mask slot (`AgreeSlots.masks` removed, `coins` kept). `ReceiveBackend` builds a
new supply per operation (`supplyOf`, `counts`, `runWith`; `scriptApi`'s `curve` is now
`Op → M (Curve × supply)` and `Agreements` gains `takes`). Proof (`Flows/JoinOnce.lean`): a path
predicate `Once U Q seen s` (every `fieldInput … .elements` slot read is in `U` and not read
before), its state-threaded form `OnceG`, and `openFirst_reads_once` / `session_reads_once` /
`refreshOps_reads_once`: on every run, for any replies, the slots read are slots of the starting
supply and pairwise distinct. S14's theorem names kept; statements that changed: `programStep_reveals`
(no `slot` argument), `receiveAgree_reveals` and `receive_joined_reveals` (same statements, `AgreeSlots`
without `masks`), `runAt_reveals` (gains the supply). Other joins checked: S12 `keyAgreement` and S13
`sendCurve` stash a new mask slot per call (fine); S15 `refreshOps` shared ONE pool across `lift`,
`check`, `agree` (fixed: `RefreshCurve` per-call pools and supplies, `split_disjoint`).

**The runner** (`Flows/Runner.lean`): `drive` (pure core) and `Runner.run` (its IO loop through
`Legacy.call .batch`). `Runner` holds the one `Receive.St` (the contact table with THE counters,
the pool, the supply), this party's store (`Slots`, written by `Secret.stash`), the slot counter,
`Channels.random`; views `tls` (S12/S13 `Runner`), `field` (J2's `FieldRunner`), `receive` (S14's,
same state reference), `supply` (J1), `table` (`SendBackend.TableRef`). Proved: `drive_model`
(fed the model's `viewH`, the batches' instructions are `withAdv`'s trace and the result/store are
the model's), `drive_bounded`, `nextBatch_fill_only` (Security 7i: `runner_*`).

**The selection** (`Flows/Select.lean`, `Flows/Context.lean` `Overrides`, every `*Legacy.lean`
function consults its entry; `Config.Agreed.scripts` from `SIGNAL_SCRIPTS`, in `agreedText` only when
non-empty). `Worker.startWith` (not yet called by Main: J9). Groups, needs and availability: section 6.

**Tests.** `node_worker/tests/lean/RunnerTest.lean` (20 checks, all ok): two controllers in two
threads, a fake worker pair answering op 93 with `checkBatch` + the model's `shellPair`; joint
randomness, the anonymous upgrade, contacts key/load (accepted, refused)/seal/evict/re-key/assign
(stand-in contact kernels; the state's value in the model; one `Counters`), S14's backend take +
refused open. Not covered (their stand-in tables live inline in the S10–S15 vector files): mask
generation with a conversion, a record seal/open, a send, an accepted receive, a refresh. The S10,
S12, S14, S15 vectors regenerated after J1: byte-identical. Harness: `--scripts NAME,NAME` written,
not run.
