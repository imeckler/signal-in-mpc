# Stage S11: local arithmetic and the curve helpers — notes

Branch `s11-curve` (from `s10-conversions`). REORGANIZATION_PLAN.md 7.1 (P-SPLIT, P-OFFSET,
P-HINT) and 10.2 S11.

## What moved from C++ to Lean

| C++ (read-only, unchanged) | Lean | File |
|---|---|---|
| `split_ecdh.h` `LocalCurve` (OpenSSL), libsodium point ops | `Local.Field`, `Local.Edwards` (`liftU`, `decode`, `mul`, `add`, `montU`, `isValid`) | `TlsMpc/Node/Local/{Field,Edwards}.lean` |
| `hinted_points.h` `LocalField` (OpenSSL: affine, root, Kronecker), `Ed` (libsodium: add, sub, times16, random, torsion) | `Local.Edwards` (`decode`, `root`, `euler`/`legendre`, `windowBases`, `hints`, `torsionHint`, `randomPoint`, `torsion8`, `publicTable`) | `Local/Edwards.lean` |
| `field_program.h` `evaluate_clear` (service_kernels.h:122, xeddsa-recover on the server key) | `Local.Edwards.recoverPublic` (the program's Lean definition, `recoverPublic_eq`) | `Local/Edwards.lean` |
| `split_ecdh.h` `begin`, `agree` | `Curve.splitBegin` (`pointExchange`), `splitAgreeInputs` (local), `splitAgree` | `Flows/Curve.lean` |
| `x25519_fast.h` `evaluate`, `evaluate_many`, `quotient` | `Curve.agree`, `Curve.quotientMany` (field-quotient `Z` rows, n copies) | `Flows/{Curve,CurveBase}.lean` |
| `edwards_points.h` `prepare`, `step`, `step_inputs` (signed digits), K₀ commit-open | `Curve.offsetPrepare`, `offsetStep`, `offsetStepFast`, `recode`, `windowInputs`, `stepIns`, `ephemeralKey`, `pointExchange` | `Flows/{Curve,CurveBase}.lean` |
| `hinted_points.h` `lift`, `hints`, `quotients`, `prepare`, `step`, `tables`, `public_table`, `base_table`, `agree`, `agree_affine`, `signatures`, `torsion`, `shared_bits`, `public_bits` | `Curve.lift`, `hintsLocal`, `quotientMany`, `prepareFirst`/`prepareSecond`, `offsetStepFast`, `tables`, `baseTableBlock`, `agreeHinted`, `agreeAffine`, `signatures`, `torsionLocal`/`torsion`, `sharedBits`, `publicBits` | `Flows/Curve.lean` |
| `service_kernels.h` `prepare_hinted`, `prepare_batch` (op 66) | `Curve.prepareContacts` (a `Staged` flow) | `Flows/Curve.lean` |

**Local steps.** A script carries no private data (Engine.lean D1); the hints and torsion hints
depend on a party's own mask point AND the opened Z. They are the local step of a `Staged` flow
(`CurveBase.lean`): first script, then this party's own computation on its store, then the second
script. The local step releases nothing (`Staged.viewD_kinds`). Everything a node computes in the
clear is in `Local/` (pure functions); the controller fills store slots with them.

**Deviations from the C++** (both parties change together; the legacy library keeps its own):
* Point commitments for a batch: one commitment `H(tag ‖ party ‖ nonce ‖ P₁ ‖ … ‖ P_m)` and one
  opening, instead of one frame per point (`pointExchange`); same frame function as P-RAND. The
  peer's commitment must also differ from ours (copy check, as P-RAND).
* No re-comparison exchange of opened denominators (the openings are MAC-checked; as S10's
  quotient).
* Mask points: `randomPoint r t = r·B + t·T₈` instead of libsodium's `crypto_core_ed25519_random`
  plus a random torsion multiple: both uniform on the whole group (cyclic of order 8ℓ; not proved).
* `prepareContacts` takes the recipients as field handles and the identity key's bits as handles;
  the contact-table glue (the `signal-conversation-view` kernel, `word_to_field` of the recipient,
  `field_to_word` of the static agreement, the account's `sender_public` once per account) is the
  flow-API switch's (it uses only S9/S10 scripts).
* `D` rows stay `D` (owner decision): a zero denominator aborts the session.

## What is proved, and what is not

See `TlsMpc/Security.lean` section 7c and section 8. In short (all standard axioms):
* **Local**: `add_eq`, `toAffine_eq`, `montU_eq`, `mulBits_cons`, `onCurve_iff`, `toAffineAll_spec`,
  `root_spec`, `sqrt_sq`, `ofBytes_toBytes`, `recoverPublic_eq`. Tested (not proved): agreement
  with curve25519-dalek on encodings, sums, multiples, the Montgomery map, validity, decoding,
  the Montgomery lift (`tests/s11_curve.rs`).
* **P-OFFSET**: (a) the recoding lemma about the flow's own `recode` (`recode_value`,
  `recode_bound`, `recode_carry_zero`, `recode64_value`, `step_tableSum`; `recode_zero`/`_succ` are
  the equations of `proofs/` `Ed25519.recode`) and the step's program inputs (`stepIns_window`,
  `stepIns_initial`, `stepIns_length`: exactly `offsetSum_recoded`'s hypothesis); (b) the key the
  script returns (`ephemeralKey_spec`, `offsetStep_key`); (c) `offsetPrepare_gate`; (d)
  `pointExchange_gate`. Open: (a)/(c) through `jointRun`.
* **P-SPLIT**: (a) `splitAgree_honest` through `jointRun` + `addU_montU` (with `FieldInverse`;
  H-GROUP is `proofs/` R7); (b) `splitAgree_gate` (checks = `curveValue`, `onCurve_iff`); (c)
  `splitKinds`; (d) the Local theorems. Open: `splitBegin` through `jointRun`; the model form of
  `commit_open_sound` for `pointExchange`.
* **P-HINT**: (a) `lift_order`, `liftBlock_labels`; (b) `valid_bit`, `lift_valid_sound`
  (`FieldInverse`), `lift_valid_complete` (H-QR and Euler as named hypotheses `TwoNonSquare`,
  `EulerCriterion`; discharged in `proofs/` by `two_not_square` and `euler_criterion` with
  `Local.Field.pow_eq`); the op 66 status: `prepareStatus_iff` (255 ⟺ q(u) a nonzero square; with
  `proofs/` `montQ_square_iff`: ⟺ u ≠ 0 is the Montgomery coordinate of a curve point). (c), (d)
  for the runs: open (`proofs/` `curve_hinted_Z_uniform`, `entries_sound` are about the program).
* **T3**: the kinds of every flow (`*_reveals`, `s11_flows_reveal`, `Staged.viewD_kinds`,
  `prepareContacts_viewD_kinds`). Value-level T3: open.
* **`_wf`**: none proved for the S11 scripts; every batch of the vector instances is admitted by
  Lean's `checkBatch` (`verdict ok`) and by the Rust shell (`s11_pair.rs`).
* **Honest runs through `jointRun`**: only `splitAgree`; the other flows are checked executably
  (`tests/s11_vectors.txt`: 51 `check … ok` lines against `Local/Edwards` and `X25519.spec`).

## Kinds

No new kind. Labels added in `Engine/Labels.lean` for the existing curve kinds: `curveChecks` (91),
`liftW` (92), `liftZ` (93), `pointValid` (94), `linkChecks` (95), `ownPublicPoint` (102); point
commitments use `commitment` (100). Programs with `D` rows release their openings under
`maskedDenominator` (90); programs without release an empty list under the flow's check label.
`linkChecks` also covers the scalar-bit checks of `edwards-prepare-hinted` (opened together with
the links in one opening, as the C++).

## Performance

* Rounds: as the C++ (one data reply per C++ opening or transfer; the agreement per batch is plan
  R1). The lift: 3 openings + 1 (D openings ride in the batches); tables: 1; agreements: 1 (the
  quotient flags); op 66: lift (3) + validity (1) + checks (1) + K₀ (2) + agreement (1).
* Local arithmetic (R2), INTERPRETED (`lake env lean --run`, no native build): scalar
  multiplication 1.3 ms, hints 2.2 ms per point, lift root 0.6 ms, validity 2.0 ms, mask point
  1.8 ms, torsion hint 2.0 ms, public table 1.9 ms, `recoverPublic` 1.3 ms. Per message (the
  ephemeral key) about 1.5 ms; per prepared contact about 6 ms. Compiled code is faster; no native
  benchmark was built.
* Vector generation (Lean model, all flows with the real compiled programs) takes about 3 minutes
  interpreted; `s11_pair.rs` runs in about 8 s in release mode.

## C++ that becomes deletable (once the callers switch)

* `split_ecdh.h` (all, incl. `LocalCurve`, OpenSSL and libsodium uses) — when the TLS flow uses
  `Curve.splitBegin`/`splitAgree` (S12).
* `x25519_fast.h` (all) — when the legacy ops that call `agreement_word(s)` move (S12–S15).
* `edwards_points.h` (all) and `hinted_points.h` (all: `LocalField`, `Ed`, `Hinted`) — when the send
  path uses `offsetStep*`/`prepareContacts` (S13) and receive/refresh use the hinted flows (S14, S15).
* `service_kernels.h` `prepare`, `prepare_hinted`, `prepare_batch` (op 66) — at the flow-API switch
  of op 66.
* `field_program.h` (V2 loader, `evaluate_all`, `evaluate_clear`, `masks`) and the V2 `.flat` field
  programs — when the last legacy caller is gone (S16 at the latest). Every Lean flow uses
  `program.rs` only.
* libsodium and OpenSSL bignums (`BN_*`) in the worker: with the files above. (OpenSSL stays for
  `public_auth.cpp`'s X.509 and SHA-256 in C++ until those move.)

## Tests and how to run them

* Lean vectors: `node_worker/tests/lean/S11Curve.lean` → `tests/s11_curve_vectors.txt` and
  `node_worker/tests/lean/S11Vectors.lean` → `tests/s11_vectors.txt` (13 MB), both with
  `lake env lean --tstack=2000000 --run FILE` (light; the second about 3 minutes, 1 GB).
* Rust: `cargo test --offline --no-default-features` in `node_worker` (all pass, incl.
  `s11_curve`, `s11_pair`); release mode recommended for `s11_pair`.
* Program checks (light, Python): `python3 node_worker/tests/s11_program_checks.py --from-vectors`
  (passes); after the re-export: `python3 node_worker/tests/s11_program_checks.py` on the word
  directory.
* Real engines, NOT RUN: after the V3 re-export (its pins must equal the vectors' `pin` lines;
  paste them into loader.rs FIELD_PROGRAMS replacing `PIN_FROM_REEXPORT`):
  `python3 scripts/guarded.py --heavy 16 3600 python3 node_worker/tests/e2e_s11.py <node-worker>`.

## Merge notes: files touched

* New Lean: `TlsMpc/Node/Local/{Field,Edwards}.lean`, `TlsMpc/Node/Flows/{CurveBase,Curve,CurveProofs}.lean`.
* Changed Lean: `TlsMpc/Node/Engine/Labels.lean` (six labels, `kinds`, `all`, `all_codes`),
  `TlsMpc/Node/Flows/Registry.lean` (S11 entries, `s11_flows_reveal`; imports CurveProofs),
  `TlsMpc/Security.lean` (section 7c, section 8 items, `#print axioms` lines),
  `REORGANIZATION_PLAN.md` (S11 status).
* Not touched: `TlsMpc/Node/Types.lean` (no new kind), the controller,
  `TlsMpc/Node/{Main,Session,Flow,Flows/*Legacy,Channels,Messages,Policy}*`, the S10 flow files,
  every module an emitter imports (EdwardsAffine, EdwardsHinted, FieldDag*, FieldProgramsV3 only
  imported), the C++. `scripts/lint_node.py`: 0 findings.
* Rust: `node_worker/src/loader.rs` (14 placeholder pins), `node_worker/Cargo.toml` and
  `Cargo.lock` (dev-dependency curve25519-dalek 4.1.3, vendored); new
  `node_worker/tests/{s11_curve.rs,s11_curve_vectors.txt,s11_pair.rs,s11_vectors.txt,e2e_s11.py,s11_program_checks.py,lean/S11Curve.lean,lean/S11Vectors.lean}`.
* `SECURITY_AXIOMS.txt` not regenerated (check_axioms.py does not fit the 4 GB cap); the 14 new
  entries were compiled standalone with standard axioms only.
* After a merge with S12: every module importing `Engine/Labels` needs a rebuild.
