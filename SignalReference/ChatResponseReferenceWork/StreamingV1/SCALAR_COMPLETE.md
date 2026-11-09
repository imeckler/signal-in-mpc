# Joined actual scalar field transition

`ScalarData` proves actual Core ID/status terminal updates preserve all other
cached response fields; full64 ID sets presence, status truncates exactly low32.
Actual scalar terminals return to key mode. `ConsumedPrefix` proves equal actual
native suffixes determine a unique consumed prefix, so independently established
data and validity statements cannot refer to different byte spans.

`NativeScalarData.actual_scalar_field_complete` joins the actual generated
ID/status dispatcher result with a single complete numeric transition: exact
consumed-prefix/native-suffix, cached field update/other-cache preservation,
validity, key mode, initial position and zero accumulator. Absent and duplicate
source fields are included. No caller prefix/table/primitive-correctness premise.

Initial valid/seen/unfinished scalar state, recognized tag, depth zero and
budget/child counter bounds are explicit state relations for the full source
scan to establish. This is the successful-field induction branch, not an
assumption that whole messages parse. Separate all-input source/rejection
components retain every native error, optional initialization/diagnostic/suffix
effect and child-overrun case. The cache projection does not redefine the final
parser observation or discard source contents/events.

Post-field child/outer scope/counter joins, byte/string/header/group/unknown
validity/events, private EOF, HTTP/correlation/full compiler composition and
inherited explicit source/std/model boundaries remain open.

Run `check_scalar_complete.py` for a clean immutable three-module combined check.
