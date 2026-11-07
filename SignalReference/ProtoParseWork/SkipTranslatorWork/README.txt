Quarantined Prost skip_field translator and reference candidate

This directory does not replace an accepted reference. Root review, if granted,
must be recorded separately. The old Never-continuation candidate is not used.

Actual computation:
- KeyReferenceWork/Artifacts/skip-step/selected.llbc is the unchanged pinned
  Prost extraction after seven explicit unused Step metadata removals. Its
  review.json and changes.json preserve the original computational fingerprint.
- continuation-pass.diff adds one invocation of the existing remove_useless_joins
  pass before update_loops. This is extra translation trust, not a proved compiler
  transformation. candidate-build-report.json records all original source hashes,
  exact delta, binary and build environment. candidate-comparison.json records
  actual inputs/generated outputs and supported/unsupported regression cases.
- No generated skip function or existing Aeneas loop definition is hand edited.
- Modules/.../LoopMonotone.lean proves the missing loop monotonicity registration
  in the kernel. The actual mutually recursive generated skip functions compile.
- The accepted contiguous-byte-slice Buf and valid-usize unsafe-index models are
  inherited. FunsExternal adds core Result::map. Its scope here is the generated
  capture-free Unit closure; arbitrary Rust destructor effects are not modeled.

Reference theorem:
Modules/SkipTranslatorWork/SkipSemantics.lean defines the recursive skip grammar.
Its rules mention decoded varint/key results, fixed byte widths, explicit errors,
exact recursion-count decrease and group tags; no rule calls skip_field or any
numeric circuit. skip_semantics_reference proves every finite derivation agrees
with the actual translated skip function, including exact remaining buffers.
The varint/key decoder premises connect to the separately replayed accepted
reference theorems. The theorem does not establish existence of a derivation for
every input, numeric circuit skip equivalence or complete Signal parser behavior.

Reproduce:
  python3 SignalReference/ProtoParseWork/SkipTranslatorWork/replay.py
  python3 SignalReference/ProtoParseWork/SkipTranslatorWork/audit_current.py
The full audit rebuilds every candidate proof module and prints transitive axioms
for 27 endpoints; only propext, Classical.choice and Quot.sound are permitted.
--report-only audits existing objects and explicitly records that distinction.
