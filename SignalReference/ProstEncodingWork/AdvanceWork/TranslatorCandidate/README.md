# Exact-pin Never-call translator candidate

The isolated candidate fixes the observed `Cps.Unit` failure on the actual
`bytes` 1.12.0 slice-advance method. Its one-file patch and root-only extraction
selection passed independent review in
`SignalReference/TranslatorNeverReview/review.json`. **The selected reference
remains unaccepted pending a decision about an existing standard-library type
axiom and integration.** The accepted translator, models and pin files were not
changed.

The proof audit compiles twenty endpoints. Fourteen use only the three permitted
foundational axioms or no axioms. Six actual slice endpoints additionally depend
on Aeneas's existing `core.fmt.Formatter : Type` axiom through the real panic
helper's formatting dictionary. This is a type declaration, not an assumed
cryptographic or buffer computation. The strict rejection is retained in
`strict-audit-failure.json`, `strict-check.py` and `strict-axiom-report.txt`.
`proof-report.json` gives the exact split and model-source hash. No model or
generated definition was edited to hide the dependency.

The exact Aeneas source is commit
`5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`; its Charon pin remains
`4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`. Both the unchanged baseline and
candidate were built locally with OCaml 5.3.0, dune 3.19.1 and the required
visitors 20260520 / ppxlib 0.37.0. `build-environment.json` records tools, hashes,
commands and the read-only external compiler/GMP inputs. The workspace-local
opam installation and dependency cache do not modify the user's switch.

`never-continuation.patch` changes only the continuation of a symbolic call whose
instantiated output is exactly `TNever`. It retains the original call and its
error/divergence propagation. It uses the existing panic expression only as the
unreachable successful-return continuation. `NeverContinuation.lean` proves
that this expression equals elimination of `Result Never`, preserving every
failure and divergence. It does not assert that a never-returning function must
panic.

The comparison runs identical inputs through the baseline and candidate. The
baseline rejects the actual slice and generic never-call regressions; the
candidate emits both without templates, and the generated Lean type-checks.
The previously accepted varint and UInt32 translations remain identical except
for their import destinations. A separate negative control still reports the
existing unsupported infinite-loop-without-breaks case. It is retained in
`Regressions/infinite-loop-negative.log`; arbitrary divergent `Result Never`
behavior is covered by the generic dictionary regressions.

`SliceSelected` changes only `ordered_decls`: it omits unrelated opaque roots
introduced by Charon's inability to start directly from a reference-type
implementation. Every declaration, signature and computational body remains
unchanged. The actual method, `panic_advance`, range index and formatting calls
are retained. The selector and independent review record this extra trusted
preprocessing boundary.

Useful imports and endpoints:

```lean
import ProstEncodingWork.AdvanceWork.TranslatorCandidate.RegressionProofs
import ProstEncodingWork.AdvanceWork.TranslatorCandidate.SliceProofs
```

- `LibSignalReference.Candidate.NeverRegressionProofs.call_eq` and `guarded_eq`
  quantify over every supplied never-returning dictionary result. Dedicated
  theorems cover every failure, divergence, guarded success and the actual
  synthetic panic caller.
- `LibSignalReference.Candidate.SliceAdvance.advance_exact` covers every slice
  and count: exact suffix on an in-range count, actual panic otherwise.
  `advance_bytes` exposes the retained list and length; `advance_all` proves
  complete consumption. These six endpoints have the `Formatter` dependency.

After preparing the recorded source/build environment, the reproducible steps
are `extract_regressions.py calls`, `select_slice.py`, `compare.py Baseline`,
`apply_candidate.py`, rebuilding/copying the candidate using the recorded build
command, `compare.py Candidate`, and `check.py`. `apply_candidate.py` requires
the exact original source hash and cannot silently apply twice. The final check
compares the accepted release binary against its pinned archive, checks the
source patch, dependency checksums, independent review, generated files and
twenty theorem assumptions.

This directory does not complete the concrete `Vec::put` adapter or whole
Signal serialization. Actual reserve/as_slice operations and field/message
composition remain separate obligations. No MPC backend or native execution is
claimed here.
