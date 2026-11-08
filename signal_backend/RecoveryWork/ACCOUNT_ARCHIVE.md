# Local account archive/certificate integration candidate

`LocalAccountCheckpoint` fixes the public account schema/member/epoch/context/
manifest/sharing domain at construction. `persist` packs the sections into one
local share-evaluation owner, seals AES256SIV and installs/fsyncs immutable
ciphertext before returning an opaque Prepared capability. Reserve/Commit have
distinct authenticated schema domains. A vote requires the actual persisted
own ciphertext digest in the proposal, exact owner/schema/slot, and a verified
predecessor certificate (or configured genesis for slot1). Commit binds its
Reserve attempt; acknowledgment binds the exact committed bundles. The existing
durable no-double-sign journal flushes before signatures escape.

`EvidenceCodec` persists canonical whole certificates and verifies actual member
signatures and epoch on decode. Loading a committed checkpoint runs the complete
public certificate/fresh-status domain gate, immutable digest/size check and AEAD
authentication, returning quarantine only. It never creates Bits or activates a
provider. Prior acknowledged ancestry/status transport, all-party readiness,
private semantic checks/re-sharing and completed pre-Session retirement remain
mandatory. This adapter is not yet the normal store's Reserve/Commit callback.

The fixture constructs both ciphertexts before the archive experiment; it does
not establish reserve-before-actual-encryption ordering. The separate store
ordering test covers host hooks, not the integrated actual operation.

The sanitizer integration fixture uses an actual pinned libsignal sender record
AFTER each of two encryptions and the exact emitted SignalMessage ciphertext,
which the actual recipient decrypts. It stores the full serialized record, its
selected525 state and immutable typed ciphertext together under each committed
bundle. Disposable local degree2 GF128 evaluations include high field bits;
there is no host interpolation. Five members persist/sign both attempts. A child
then exits via _exit (no destructor flushes). The parent reopens journals/files,
verifies fresh signed status and all certificates, authenticates/reloads all18
sections for each member and compares exact local evaluation bytes. It rejects
rollback to the earlier checkpoint and an altered certificate. One unrelated
conversation remains unchanged.96 checks pass.

This test is PUBLIC and uses known disposable account/polynomial/member/storage
keys. Credentials/identity/prekey/service/global-ID sections are dummy, and the
selected-service section contains only sender136, not full shape.input_bytes().
Thus it is not a populated normal account or provider admission test. The private
canonical codec is checked separately; this fixture archives actual Rust record
bytes and does not claim it invoked the private codec/MPC. It does not yet call
the real store's checkpoint hooks, re-admit full records into fresh native CCD,
retire runtime traces, retry an uncertain outbox, or restore TLS. Those are real
remaining integration tasks, not established by the local cross-layer test.
