# Private canonical record candidate

The encoder's public Node tree is a capacity schema, with private presence masks,
lengths and every byte/scalar. It serializes proto3 default omission, optional
presence, repeated slots, canonical variable varints and nested private lengths.
No live secret shape is read to construct the public tree. Encoder Hom and AIG
compiler agreement are kernel checked (5 endpoints, foundational axioms only).
These are model/compiler agreements, not actual Rust serializer refinement.

The private update writes selected525 root/sender/receiver/PQ receive data into
that retained tree and updates active-receive Tahini/prekey acknowledgment fields.
New receiver child/message presence must activate together; the first actual-byte
comparison caught this and the candidate was fixed. It retains full other record
fields and opaque PQ/auth/KEM inner data, rather than storing a stale record plus
a selected overlay. The supported tree has five receiver capacity slots, one
active PQ link, no skipped keys/epoch transition, four-byte selected counters and
8-byte-capable generic scalars. The public fixture schema currently uses small
32-bit epochs; full uint64 epoch profile remains required.

Four public-fixture concrete executions compare all encoded bytes with the
actual pinned libsignal record: new DH receive, repeated known receive,
LocalNew with pending prekey/Kyber metadata acknowledged, and rejected receive
preserving the original record. Rust SessionRecord reload/whole-record equality
is independently checked by the oracle. The Python decoder is only a disposable
PUBLIC-fixture adapter, never a runtime private parser/import path.

Still required: private schema/profile validation, update Hom/compiler theorem,
actual source semantic refinement, private record parse/reprojection after reload,
full SPQR/KEM/skipped/prekey transitions and coherent send-record update. No
provider admission, native MPC serializer, atomic state/outbox restart or runtime
retirement is established by these tests. Keep the normal recovery gate closed.

## Private snapshot/reprojection checkpoint

`PrivateRecordSnapshotV1` stores the private tree itself in a fixed public schema:
all private presence bytes, buffer status/BE16 length/capacity bytes, scalar bytes
and nested fields. Restore reads those shares under the same authenticated schema;
there is no host protobuf parsing. Private re-projection yields the selected525
bytes. The four cases now flatten→restore before both projection and actual full
protobuf byte comparison. The rejected case checks the prior selected state.
Only canonical bounded fixtures are checked; malformed-schema/buffer rejection,
general roundtrip/projection proofs, native archive/import and runtime admission
are not established. Do not restore from stale serialized baseline plus overlay.

## Canonical sender checkpoint

`PrivateRecordSendV1` applies the actual service output prefix to sender CK/index
and the sole PQ send-link next key/counter, preserving full receiver/root/private/
prekey/opaque PQ phase state. It implements pinned Tahini on_send: only prior
ReceiveInactive increments the direction-change counter; last_act becomes Send.
The bounded profile excludes that counter's overflow, skipped keys and PQ phase/
epoch transitions. It does not yet compute a full private profile-validity guard.
Four additional private-ops cases flatten/restore and compare the ENTIRE private
tree against actual pinned post-encryption records: first send, repeated send,
ReceiveInactive bookkeeping, and rejected unchanged state. Tests found that fixed
receiver capacity slots must be right-aligned to the selected525 layout; the
public fixture schema adapter now pads repeated slots on the left. No live secret
field count is inspected to build that schema. The sender model is not yet a
native MPC/profile admission result or a source refinement proof.

## Immutable numeric native candidates

Public schema generator declares5550 private snapshot bytes (tags, nesting and
capacities only; it never reads a live record). Candidate1 failed the stronger
flat comparison because inactive receiver children retained noncanonical fields.
Candidate2 then exposed hidden acknowledged-prekey payloads. Both closures are
preserved and unpromoted. The update now clears complete inactive receiver and
acknowledged optional nodes under computed masks, with a kernel-checked clear
helper Hom. Candidate3's8 exact AIG evaluations match actual canonical full tree
and selected525 for new/known/LocalNew/rejected receive and first/repeated/
ReceiveInactive/rejected send. Compilation includes only state codec operations,
not duplicate cryptography or protobuf serialization. Actual MPC execution and
full update/source theorem remain pending.31 compiler rounds per stage is a
public circuit cost, not throughput; compile timings may overlap TLS work.
The older4-case report.json is the historical pre-clear serialization test;
artifact-report.json/native-compile-report.json bind the current candidate.

Candidate4 corrects the exact pinned is_known_by_peer predicate: pending prekey
presence, not origin, triggers acknowledgement/clearing. It preserves Kyber-only
pending state and LocalNew without pending prekey.10 exact AIG cases now pass;
prior artifacts/receipts remain unpromoted historical evidence. The current
record adapter syntax check is C++20/CCD128 only, not a linked/native run.
