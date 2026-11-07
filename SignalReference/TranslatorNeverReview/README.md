# Independent Never-continuation candidate review

This review checks the helper's isolated patch against the exact pinned Aeneas
source archive. All 794 original files match except `InterpStatements.ml`.
After removing comments, the only change selects `Panic` instead of `Unit` when
the instantiated return type is exactly `TNever`, retaining the original
symbolic call continuation. This represents an unreachable successful-return
tail; it does not replace the called operation or its failure/divergence.

The generated actual slice operation retains `panic_advance` before that tail
and retains the original range-from index for successful inputs. The generic
regressions retain the supplied Never-returning call. The existing successful
Prost varint and uint32-field translations are identical to baseline output
after normalizing only their import destination.

The separately selected actual slice graph changes only the code-generation
root list. Every original declaration, body, signature and type remains
identical. The reviewer replays and reverses this change, checks that removed
function roots were opaque and unused by the actual operation, and scans the
retained computational signatures and bodies. The generated result has no
external templates. Official slice/scalar/panic-formatting models remain
trusted translation dependencies.

Run `python3 SignalReference/TranslatorNeverReview/check.py` from the workspace
root. `review.json` pins the exact reviewed artifacts and source archive. This
is a trusted engineering review, not a mechanized proof of Aeneas or selection.
The candidate's own kernel proof audit must also pass before adopting this
binary for a selected new extraction profile. No accepted binary, model,
libsignal source or existing proof reference is replaced by this review.
