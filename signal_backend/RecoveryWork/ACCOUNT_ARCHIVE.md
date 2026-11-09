# Local account archive/certificate integration candidate

`LocalAccountCheckpoint` fixes the public account schema/member/epoch/context/
manifest/sharing/inner-section-encoding domain at construction. `persist` packs the sections into one
local share-evaluation owner, seals AES256SIV and installs/fsyncs immutable
ciphertext before returning an opaque Prepared capability. Reserve/Commit have
distinct authenticated schema domains. The V3 COMMIT-HEAD phase-schema commitment also
binds the explicitly configured inner section codec digest; capacities alone do
not distinguish protobuf bytes from a private canonical-tree snapshot. Wrong
inner codec restoration rejects before any provider use. A vote requires the actual persisted
own ciphertext digest in the proposal, exact owner/schema/slot, and a verified
predecessor certificate (or configured genesis for slot1). Commit binds its
Reserve attempt. The NEXT Reserve chains from the certified COMMIT, independently
of remote service acknowledgments; loading needs Reserve+Commit, not delivery. The existing
durable no-double-sign journal flushes before signatures escape.

`EvidenceCodec` persists canonical whole certificates and verifies actual member
signatures and epoch on decode. Loading a committed checkpoint runs the complete
public certificate/fresh-status domain gate, immutable digest/size check and AEAD
authentication, returning quarantine only. It never creates Bits or activates a
provider. Prior committed ancestry/status transport, all-party readiness,
private semantic checks/re-sharing and completed pre-Session retirement remain
mandatory. This adapter is not yet the normal store's Reserve/Commit callback.

The fixture constructs both ciphertexts before the archive experiment; it does
not establish reserve-before-actual-encryption ordering. The separate store
ordering test covers host hooks, not the integrated actual operation.

The sanitizer integration fixture uses an actual pinned libsignal sender record
AFTER a send in each of two independent conversations sharing one actual sender
identity, together with the exact emitted SignalMessage ciphertext,
which the actual recipient decrypts. It stores the full serialized record, its
selected525 state and immutable typed ciphertext together under each committed
bundle. Disposable local degree2 GF128 evaluations include high field bits;
there is no host interpolation. Five members persist/sign both attempts, with no remote acknowledgment. The
second commit advances conversation1 while retaining conversation0's committed
but unsent outbox and complete state. A child
then exits via _exit (no destructor flushes). The parent reopens journals/files,
verifies fresh signed status and all certificates, authenticates/reloads all18
sections for each member and compares exact local evaluation bytes. It rejects
rollback to the earlier checkpoint and an altered certificate. The earlier unacknowledged conversation remains unchanged, and an observed
higher unresolved reservation still blocks loading an older head.133 checks pass.

This test is PUBLIC and uses known disposable account/polynomial/member/storage
keys. Credentials/prekey/service/global-ID sections remain dummy, and the
selected-service section contains only sender136, not full shape.input_bytes().
Thus it is not a populated normal account or provider admission test. The private
canonical codec is checked separately; this fixture archives actual Rust record
bytes and does not claim it invoked the private codec/MPC. It does not yet call
the real store's checkpoint hooks, re-admit full records into fresh native CCD,
retire runtime traces, retry an uncertain outbox, or restore TLS. Those are real
remaining integration tasks, not established by the local cross-layer test.

Disposition codes distinguish Absent, CommittedUnsent, TransportAttempted,
ObservedServerAccepted, ObservedServerRejected and Uncertain. They are PRIVATE
archive data, not host branches. This fixture exercises only Absent and
CommittedUnsent; it does not invent a sent attempt or server response. HTTP
acknowledgments never roll back Signal state, and no exactly-once delivery is
claimed. Account identity is genuine shared across the two generated peer
fixtures; other bootstrap/service fields remain explicitly partial/dummy.
