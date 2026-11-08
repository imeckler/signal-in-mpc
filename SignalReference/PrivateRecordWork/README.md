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
