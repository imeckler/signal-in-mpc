# Parser error-state v2 checkpoint

Core SignalMessage parsing now preserves Prost's error-time field initialization
and exact failure cursor. The accepted prefix/table and basic plan declarations
remain textually identical; `planWithCursor` supplies the actual mutable-buffer
failure semantics, and `applyPlan` initializes absent known fields before merge.
Existing fields survive rejection; successful duplicates still overwrite.

The cursor model distinguishes key errors, wrong wire type, fixed-width
underflow, scalar/length errors, bytes underflow and recursion refusal. A failed
contiguous Prost fast varint decoder consumes zero bytes. The short slow decoder
consumes up to ten available bytes. Final-row decoder status supplies the common
last-byte continuation-bit condition without adding a secret input or changing
public wire/output shapes.

Validation:

- `lake build TlsMpc.Signal.ProtoParseProofs`: compiler/hom proofs rebuilt.
- `python3 .../ParserErrorStateV2Work/audit.py`: versioned kernel proofs,
  current compiler endpoint and foundational-axiom audit.
- `python3 .../ParserErrorStateV2Work/check_oracle.py`: 1,722 actual locked
  Prost `Message::merge` comparisons of status, exact consumed cursor/suffix
  and all six mutated Option field contents on success AND rejection.
- `python3 .../ParserErrorStateV2Work/check_artifact.py`: four capacity-64
  compiled AIG lanes match current concrete results (valid, duplicate and
  malformed messages). This is compiler evidence, not MPC execution.

Universal proofs cover absent/existing scalar and bytes initialization under
the content projection, rejection retaining initialized fields and exact plan
cursor, and arbitrary remaining public scan positions preserving the complete
failed state. The final-byte mask is kernel-checked for every U8. Historical v1
and corrected v2 wrong-wire behavior are both retained as kernel regressions.

## Historical receipts

HistoricalV1.lean preserves the prior decodePrefix/table/plan/applyPlan/step/
parseBody definitions over shared unchanged record types. Frozen historical
proofs, reports and artifacts have not been edited. historical-dependencies.json
records the previous core hash, identical retained declarations and affected
numeric/source-closure receipts. Whole-file freeze guards including this core
file intentionally need versioned revalidation; old receipts are not silently
reused as acceptance of v2. Replayed/ recompiles three unchanged dispatcher
integration proof sources against the current core (import paths only).

## Remaining proof boundaries

This checkpoint fixes and tests the full parser's internal error states; it does
not prove arbitrary-message Rust refinement. Complete successful scan/table/
field/group induction, decoder lookup/absolute-cursor invariants, and totality
of accepted finite skip derivations remain. Error-kind classification is not a
new numeric output; the parser still records rejection and preserves fields and
cursor. Existing dispatcher diagnostic-stack quotient and successful bounded
contiguous Vec allocation below isize::MAX remain explicit model boundaries.
No translator/model is newly root-accepted here. Public/secret interface,
masked external rejection output and application readiness policy are unchanged.
