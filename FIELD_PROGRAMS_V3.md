# Field programs, format V3

Branch `field-programs-v3` (REORGANIZATION_PLAN.md 5.5, 7.1 P-INV / P-FIELDPROG, stage S9).
The export has **not** been run. This file says what to run, once, and how to check it.

## The format

The specification is `TlsMpc/FieldDagV3.lean`. Its doc comment has the canonical text. The
summary:

```
EMP_HYBRID_FIELD_DAG_V3
INPUTS MASKS ROWS OUTPUTS
57896044618658097711785492504343953926634992332820282019728792003956564819949
I i | C n | A a b | S a b | M a b | D a b m | Z a b m | F k      (one row per line)
O node mark                                                    (one output per line, mark 0|1)
```

- **Masks are explicit.** A program has two input vectors: data inputs and masks.
  - `D a b m` computes `a / b` with mask `m`. The evaluator opens `o = b·m`, aborts if `o = 0`, and
    otherwise computes `(a·m)·o⁻¹`.
  - `Z a b m` does the same, but gives 0 instead of aborting when `o = 0`.
  - `F k` is the public zero flag of the `Z` row `k`.
- **Masks are used once.** The `D`/`Z` rows name the masks `0 … MASKS−1` in order, and no other
  row can read a mask (P-INV (d)).
- **Output marks.** Each output is marked 0 (never: it stays in the engine) or 1 (public: both
  parties may open it).
- **The text is canonical.** It uses single spaces, `\n` line ends, and numbers without leading
  zeros. The parser accepts exactly the rendered texts of valid programs (`parse_render`,
  `render_parse`, `parse_valid`), so a pin names exactly one program.
- **The semantics.** `eval program inputs masks` returns the outputs and the openings, or `none` on
  an abort.
  - `eval_ofArtifact`, `eval_ofArtifact_some` and `eval_compileAll`: V3 evaluation agrees with
    FieldDag, so `compileAll_correct` and every theorem about the source expressions carry over to
    the V3 file.
  - These theorems assume `FieldInverse` (Fermat for p), a named hypothesis. It holds because p is
    prime, and the Mathlib package can discharge it (`FieldBridge.toZMod_inverse`).

The engine instruction is `program` (opcode 22, `TlsMpc/Node/Engine.lean` design note items 3, 5
and 6, and decision D14).
- **Check rule.** The program must be loaded, the counts must match, and the label must be nonzero.
  The masks must be live with mark `never`, and the instruction **consumes** them. The inputs must
  be live and must not be masks. The outputs get the program's output marks (`check_program`,
  `check_program_openable`).
- **Releases.** It releases the openings `b·m` to both parties. The reply to the script is unit,
  and the instruction does not end a batch.
- **Ideal semantics.** `Model.lean` defines it with `runProgram`, through `FieldDagV3.eval`
  (`idealStep_program`, `runProgram_lengths`).

The Rust side:
- `node_worker/src/program.rs` holds the parser and the level-by-level evaluator.
- `handles.rs` and `interp.rs` handle opcode 22.
- `loader.rs` has `FIELD_PROGRAMS` (pins), `Programs::add_pinned`, and adds the programs to the
  start agreement.

The C++ `field_program.h` and the V2 files stay for the legacy library until S11.

## Which modules the emitter imports, and what changed

`EmitWordMask` (`word_mask_emitter`) now also imports `TlsMpc/FieldProgramsV3.lean`, which imports
`TlsMpc/FieldDagV3.lean` and modules the emitter already imported (FieldBits, X25519Fast,
EdwardsShare, EdwardsAffine, EstablishField, ReceiveField, EdwardsHinted, FieldDag,
FieldDagMulti).
- **New modules:** `TlsMpc/FieldDagV3.lean` and `TlsMpc/FieldProgramsV3.lean`.
- **Unchanged:** every module the emitter imported before, including FieldDag and FieldDagMulti.
  The V2 printers `renderField` / `renderFieldAll` and every existing mode of `EmitWordMask.main`
  are unchanged. The new modes are `v3 list` and `v3 NAME`.
- No `TlsMpc/Node` module is imported. `scripts/lint_node.py` reports 0 findings, including
  emitter isolation.

**Consequence.** The emitter binary changes, so its outputs must be regenerated once. The V2 and
Boolean texts must come out byte-identical. The flat-kernel emitter and its circuit cache are not
affected: `EmitFlatKernel` imports none of these modules.

### The marks of every exported program (`FieldProgramsV3.find`)

The public outputs below are the ones today's C++ opens to both parties. A survey of
`handshake_backend/EmpHybridWork` found them. **Check this table before the export:** a wrong
mark means another re-export.

| program | public outputs | evidence |
|---|---|---|
| field-quotient (new, natively V3: x/z with a `Z` row; replaces field-mask-pair and the C++ quotient) | 1 (the zero flag) | x25519_fast.h:43-64, hinted_points.h:162-174 |
| field-bit-check | 0 | word_mask.h:163-164, dyn_word_mask.h:114-115 |
| field-bit-xor | none | word_mask.h:165-166 |
| field-recompose | 0 | word_mask.h:162-164 |
| x25519-fast | none (z is opened only after masking, by the quotient) | x25519_fast.h:24-44 |
| edwards-on-curve | 0 | split_ecdh.h:110 |
| edwards-add-u | none | split_ecdh.h:111-112 |
| edwards-prepare | 0 … 504 (`prepareChecks`) | edwards_points.h:71-73 |
| edwards-offset-sum | none | edwards_points.h:107 |
| xeddsa-recover | none (opened today only on a public input; S11 evaluates those locally) | service_kernels.h:122-123 |
| xeddsa-check, receive-torsion | none | service_kernels.h:313-314, 359-360 |
| lift-open | 0 … 4 (w, two bit checks, two curve checks) | hinted_points.h:124-131 |
| lift-point | 0 (valid, opened by `Hinted::prepare`), 3, 4 (Z) | hinted_points.h:134-136, 185-186 |
| edwards-prepare-hinted | 0 … 629 | hinted_points.h:201-222 |
| edwards-offset-sum-fast | none | hinted_points.h:230-232 |
| edwards-bit-table | 0 … 125 | hinted_points.h:245-248 |
| edwards-bit-sum, edwards-affine-bit-sum, edwards-signature-sum, edwards-torsion-hinted | none | hinted_points.h:278-321 |

`field-mask-pair` has no V3 form.

**Divisions that hit a public abort.** The C++ `D` divisions open `den·r` inside the evaluator and
abort on zero. In V3 they are `D` rows with masks the script supplies, and they still abort when
the opening is zero. The programs with `D` rows are:
- edwards-prepare, edwards-offset-sum
- lift-point
- edwards-prepare-hinted, edwards-bit-table, edwards-torsion-hinted, edwards-signature-sum

The survey could not rule out a zero denominator on a twist input (edwards-prepare) or a wrong hint
(torsion-hinted). S11, which writes those flows, should decide whether any of them should become a
`Z` row.

## The one re-export (heavy, alone)

```
python3 scripts/guarded.py --heavy 16 3600 python3 handshake_backend/EmpHybridWork/export_field_v3.py
```

`export_field_v3.py` does the following:
1. **Snapshot.** It records the SHA-256 of every `*.flat` and of `word_circuit_pins.h` in
   `.deps/emp-hybrid-word-v1`, and keeps a copy of the directory.
2. **V2 re-export.** It runs `lower_word_circuits.py`, which rebuilds `word_mask_emitter` and
   re-exports every V2 field program and Boolean word circuit with its own checks.
3. **Byte-identity check.** It fails if any of those files differs from the snapshot. That is the
   byte-identity check for the V2 outputs: the C++ pins in `word_circuit_pins.h` must not move.
   - To check it again by hand afterwards: `shasum -a 256 .deps/emp-hybrid-word-v1/*.flat` should
     equal the `flat_sha256` values in `handshake_backend/EmpHybridWork/word-circuits-report.json`
     at the merge base (only `lean_sources` in that report changes, because the source of
     `EmitWordMask.lean` changed).
4. **V3 export.** It prints each V3 program with `word_mask_emitter v3 NAME`. For each one it:
   - parses the text as program.rs does and re-renders it;
   - evaluates it on random inputs and nonzero masks against the V2 file of the same program
     (`field-quotient` against x/z and the zero flag);
   - writes `NAME.v3`.
5. **Outputs.** It writes:
   - `field_program_v3_pins.txt` (`NAME SHA256`) and `field_program_v3_pins.rs.txt` in
     `.deps/emp-hybrid-word-v1`;
   - `field-programs-v3-report.json` next to the script.

After the export:
- Paste `field_program_v3_pins.rs.txt` into `FIELD_PROGRAMS` in `node_worker/src/loader.rs`. The
  `field-quotient` pin is already there: `ec4abf2b…` is the SHA-256 of Lean's
  `render FieldDagV3.quotient`, checked by `tests/program_vectors.rs`, and the export must
  reproduce it.
- Commit the report.

## Tests and how to regenerate the vectors

The Lean vectors are `node_worker/tests/lean/EngineVectors.lean` → `tests/engine_vectors.txt`.
They now carry:
- 20 `program` cases, accepted and refused (one per refusal of the check rule);
- a two-party `program` flow;
- V3 texts with their signatures;
- `runProgram` evaluations, including aborts;
- 22 parser vectors.

They use row-written programs only, so generating them compiles no field program and is not an
export. To regenerate (light):

```
lake env lean --run node_worker/tests/lean/EngineVectors.lean   # stdout → node_worker/tests/engine_vectors.txt
```

Rust tests: `cargo test --offline --no-default-features` in `node_worker`.
- `engine_vectors.rs`: Rust `check` equals Lean `check` on every case, including the program cases.
- `program_vectors.rs`: the parser agrees with Lean on accepting and refusing texts; `evaluate` on
  a clear stand-in engine gives Lean's outputs and openings and aborts where Lean aborts; nothing
  leaks; the pin is checked.
- `batch_pair.rs`: the program flow runs on two shells with stand-in engines.

The real-engine e2e tests skip the program flow until the files exist.

## Merge notes: files touched

- **New:**
  - `TlsMpc/FieldDagV3.lean`, `TlsMpc/FieldProgramsV3.lean`
  - `node_worker/src/program.rs`, `node_worker/tests/program_vectors.rs`,
    `node_worker/tests/common/field.rs`
  - `handshake_backend/EmpHybridWork/export_field_v3.py`
  - `FIELD_PROGRAMS_V3.md`
- **Changed (Lean):**
  - `TlsMpc.lean` (imports)
  - `TlsMpc/Node/Engine.lean` (opcode 22, `Ctx.progs`, `ProgSig`, `useMasks`, `check`, the
    codec, the design note, D5, D14, `check_program*`)
  - `TlsMpc/Node/Engine/Model.lean` (`Env.programs`, `runProgram`, `idealStep`)
  - `TlsMpc/Security.lean` (restatements)
  - `SECURITY_AXIOMS.txt` (regenerated)
  - `handshake_backend/EmpHybridWork/EmitWordMask.lean` (import, `v3` modes)
- **Changed (Rust):**
  - `node_worker/src/{interp,handles,loader,shell,main,lib}.rs`
  - `node_worker/tests/{engine_vectors.rs,engine_vectors.txt,batch_pair.rs,common/mod.rs,e2e_engines.rs,e2e_batches.py,lean/EngineVectors.lean}`
- **Not touched:**
  - the controller;
  - `TlsMpc/Node/{Main,Session,Flow,Flows/*Legacy,Channels,Messages,Types,Reveal,Policy}*`;
  - FlatLowering, EmitFlatKernel, ReceiveFirst and BundleSlot*;
  - `field_program.h` and the V2 files.
- **Theorem statements.** No existing theorem statement changed. The proofs that cover every
  instruction (`check_label`, `check_unit_of_not_ends`, `wire_enc`, `skeletonBytes_inj`,
  `idealStep_labels`, `idealStep_toH`, `fill_bounded`, and others) cover the new case with their
  existing proofs.
- **`Ctx` has a new field.** Code that builds a session's starting context should now use
  `{ progs := … }` (Lean `Env.progs`; Rust `Shell::set_programs`).
