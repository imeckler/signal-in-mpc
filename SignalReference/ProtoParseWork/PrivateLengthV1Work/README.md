# Private-length SignalMessage parser V1 candidate

The new `TlsMpc.Signal.PrivateProtoParseV1` module preserves the frozen accepted
public-length parser. Its input is the entire public-capacity wire buffer plus
shared BE16 actual total length and an upstream validity byte. Framing is
version || protobuf body || MAC8; MAC verification remains external. The target
capacity is256, with intended proof domain public capacity≤512 and actual
length≤capacity. Status masks are canonical0/255. Offsets remain body-relative:
wire offset = body offset+1. Zero-based fields0/3/4/5 are ratchet/ciphertext/PQ/
addresses respectively. `Parsed` exposes state, wireLength, bodyLength, valid and
released metadata; `parseCore` returns the existing valid::metadata shape.

No byte at or past the private body end can terminate a varint: it is replaced
by0x80, a zero-payload continuation. All payload bounds, failure cursors and the
last-byte fast-path guard use the private end. Scanning is public-capacity but
state updates are disabled at/past that end. Unaddressable fixed-stack tail
writes are disabled; the proof relates the internal stack by explicit zero
extension, retaining actual fields/cursor/error behavior.

Initial validated components:

- `Padding` and `DecoderPadding`: arbitrary continuation padding preserves the
  entire decoded row, including malformed/truncated/overflow cases.
- `BoundedBytes` and `Table`: the private table is exactly the accepted decoder
  on `take n`, for all table positions, including unused capacity rows.
- `Plan`: private bounds and native failure-cursor rules specialize to the
  accepted public-length rules for every n≤512 and scanned position<n.
- `Stack`: zero-extension lookup, bounded writes, native applyPlan and initial
  stack correspondence; no success-only premise.
- `Select`: exact canonical-mask selection of equal-shape parser states.

Open: full lookup-window/scan induction, private wire framing/metadata theorem,
proof-only exact error classification and actualRust composition, Hom/compiler
endpoints, and capacity256 functional/native validation. No complete private
parser or receive-security acceptance is claimed. A large interpreted fixture
run reached its explicit120-second limit; it produced no correctness result and
has terminated. The universal component proofs passed independently.

Run `check.py TlsMpc.Signal.PrivateProtoParseV1 Padding Plan BoundedBytes
DecoderPadding Table Select Stack`. `PRIVATE_PARSE_OUTPUT_ROOT` selects a
separate output tree; accepted dependencies are linked read-only. No global
Main/core imports or accepted historical proofs are modified.
