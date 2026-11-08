# Account schema V1: local-evaluation container, admission closed

`AccountSchemaV1` fixes ordered sections/capacities for an entire account rather
than serializing only the selected sender. Its canonical public descriptor binds
conversation order, section types and every capacity into the archive schema
digest. `pack/unpack` preserve every full128-bit LOCAL evaluation byte exactly;
no host interpolation or account plaintext is involved. The outer OwnShareBox
must bind this descriptor digest. All declared sections are mandatory and nonempty.
Private-length serialized records/outboxes require their length/status fields
inside their declared private section, not an observable host length.

This is a concrete storage container, NOT a populated full-session serializer.
The current code cannot validate that callers supply coherent section contents.
It never admits providers or calls a section `implemented` merely because space
is reserved. `CurrentAndPreviousSessionRecords` must preserve the entire pinned
RecordStructure, including opaque serialized PQ state; it cannot be a baseline
record left stale while an unrelated selected sender overlay changes. A private
projection/update relation must tie these representations together before use.

## Required field/transition checklist

Target source: libsignal904c8dc, rust/protocol/src/proto/storage.proto.

| Section | Required data and current missing work |
|---|---|
| Credentials | Reusable account UUID/password/UAK provenance; current one-use upgrade credential ownership must gain an authenticated persistent vault. |
| IdentityKeyPair | Local identity private/public, trusted remote identity bindings. Bootstrap/import and identity-change policy remain missing. |
| RegistrationAndPreKeyStores | Local registration; one-time/signed/Kyber keys, consumed markers, certificates and expiry. Full fresh-session/prekey transitions remain missing. |
| GlobalRequestCursor | Connection-global private64-bit next ID, exhaustion/never-reuse state. Bind allocator reservations to durable intent before evaluation. |
| RecipientAndServiceBinding | Recipient UUID/device/UAK/service profile and certificate; preserve existing selected input fields, authenticate original bootstrap. |
| CurrentAndPreviousSessionRecords | Current session version, local/remote identity, root, previous counter; sender ratchet public/private, CK/index; ordered receiver ratchets/CK/index plus every skipped MessageKey index/cipher/MAC/IV/seed; pending prekey optional ID/signed ID/base/timestamp; pending Kyber ID/ciphertext; local/remote registration IDs; Alice base key; complete pq_ratchet_state; origin; previous sessions; Tahini last_act/direction counter. Actual private parser/serializer/update and full SPQR/prekey/skipped-key transitions remain required. |
| SelectedVariableSendInput | Preserve all shape.input_bytes() inputs (cert/key/service binding and selected sender/PQ/metadata), not merely CK/counter. Prove coherent projection to current SessionRecord; update both atomically. |
| SelectedReceiveState | Preserve all525 retained receive/root/sender bytes; bind identities and full record. Known/new in-order models exist; skipped-key/out-of-order/full epoch handling remains missing. |
| FrozenIntent | Exact private text/content/timestamp/recipient/requestID/shape and prestate consumed under Reserve; never regenerate differing plaintext under a burned attempt. |
| ImmutableOutbox | Exact committed ciphertext/request private length+capacity/status, expected response ID, transport-independent pending payload. Never persist TLS traffic keys/nonces/sequences/handles. |
| OutboxDisposition | Pending/acknowledged/definite failure/uncertain state and monotone ticket; authenticated correlated response only; non2xx/timeout cannot roll back consumed Signal state. |

On recovery validate the certified phase/schema/domain, load every section,
collectively import/check the complete account, destroy helpers, complete the
pre-Session epoch/host wipe barrier, and build fresh TLS/HTTP upgrade. Actual
runtime binding, atomic reserve/commit/outbox store updates and populated schema
remain open; callback ordering tests do not establish any of them. The container
has a public1Mi-bit aggregate cap; current raw import supports4096 bits per batch,
so complete-account chunked import with a single activation barrier is still
required. Membership/capacity changes need a new explicit schema, not truncation.
