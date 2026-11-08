# Actual dispatcher integration candidate

Run `python3 SignalReference/ProtoParseWork/DispatcherIntegrationWork/audit.py`.
30 kernel endpoints currently pass with only foundational axioms. This is an
unaccepted integration candidate, not whole-parser or runtime readiness.

Implemented:

- Reproducible actual generated SignalMessage dispatcher. FnItemRound2 retains
  pure zero-input literal function items as pure carriers instead of wrapping
  their type in Result; its existing monadic-let guard is retained. Six boundary
  translation cases pass. Generated Funs/Types are not manually edited.
- Concrete standard Option/map_err/function-item/default models and structural
  adapters to accepted actual uint32, bytes, Vec replacement, and skip bodies.
  There are no parser correctness axioms in imported models/proofs.
- All six known field dispatches and all six total contiguous field references,
  retaining both rejection and success, mutated fields and exact suffixes.
- Actual unknown-tag dispatch to the accepted recursive skip body; its finite
  derivation/totality boundary is inherited, not discharged here.
- Counter low32 projection, exact numeric metadata write, malformed scalar
  suffix/rejection, and ciphertext content view from secret offset/length.
- Diagnostic-stack-only projection and outer Result failure preservation.

Model boundaries are recorded in model-provenance.json. In particular error
annotation closures use identity modulo diagnostic stack, under successful
bounded allocation. The source append changes only stack; error_projection
proves arbitrary stack changes preserve description, fields and suffix. This
is an explicit model boundary, not actual annotation-closure extraction.

The two accepted primitive extracts have conflicting auto-generated global
Discriminant instance names. Isolated FieldReplay/SkipReplay use import-path
substitutions, remove unused Cow/error-kind attributes, and spell out the same
wire discriminant mapping with unique instance names. Their computational
parser bodies are unchanged. Replayed source is regenerated on demand and
excluded from the source commit to avoid duplicating frozen proof bodies. Original accepted/frozen files stay untouched.
prepare_replay.py and prepare_skip.py record exact origin/replay hashes.

Reproduction: build MessageReferenceWork/FnItemRound2/build.py, run
FnItemRound2/extract_regressions.py for default/literal/negative and compare.py,
extract.py dispatch_error_models, regenerate.py, prepare_replay.py, prepare_skip.py,
model_provenance.py, then audit.py. Existing pinned archives, LLBC and accepted
primitive builds are dependencies. Build objects, compiler source trees and
binaries are excluded from the scoped source commit.

## Blocking refinement mismatch

RejectionMismatch.lean proves body [18,0] has an absent counter initialized to
Some 0 by actual generated merge_field before wrong-wire rejection. Numeric
ProtoParse.applyPlan suppresses all failed field writes and retains absence.
Thus a claimed relation preserving mutated fields on rejection is false for
the current numeric parser. Changing core parser/error-state representation
requires coordination; observation was not weakened to success-only.

Whole scan/table/group/metadata invariants, all malformed/duplicate/unknown
message composition, primitive representation/translator review, and compiled
artifact agreement remain. No external execution or MPC security claim.
