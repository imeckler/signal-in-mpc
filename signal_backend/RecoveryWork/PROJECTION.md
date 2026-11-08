# Canonical receive projection/update candidate

The public-only Rust `session_projection.rs` updates the complete pinned generated
RecordStructure from a525-byte selected receive state. It updates root/sender,
ordered retained receiver chains and active PQ receive next-key/counter. All
other canonical session/previous-session data remain present. Successful active
receive also performs the inspected pinned Tahini bookkeeping: clear legacy/new
unacknowledged prekey metadata, mark LocalNew as LocalAcked, and mark the record's
last action ReceiveActive. This bookkeeping was missing in the first candidate;
full-record comparison caught it before acceptance.

For three actual PQXDH-initialized disposable peer pairs, one new-ratchet and
three repeated known-ratchet receives each, the updated WHOLE canonical record
must equal the actual libsignal message_decrypt_signal result. Actual selected
SPQR phases are overridden exactly as in the existing in-order oracle; this is
not full bootstrap/SPQR sender agreement. SessionRecord serialize→deserialize
then re-project must reproduce every selected525 byte. Archived-session retention,
an unrelated conversation, rejected-status identity update and malformed widths
are checked. Actual badMAC/replay rejection preserves the actual record.

Unsupported sender/receiver skipped keys, PQ previous keys/multiple epoch links
and epoch advancement reject explicitly. The current implementation is a PUBLIC
fixture oracle. It is not called on operational private keys, does not reconstruct
shared state, and is not a secure runtime serializer. Its selected values come
from actual transition expectations; the earlier circuit differential checker
separately establishes the bounded selected-state behavior. There is no new
end-to-end proof from this Rust helper to the private circuit.

Next implementation: private canonical field encoding/update, retained full PQ
phase/history and skipped/prekey state transitions, coherent selected send input,
and durable intent/outbox linkage across process restart. AccountSchemaV1 and
BootstrapOrder stay closed until these and actual import retirement are bound.
Existing older in-order model receipts bind their earlier exact binary; this new
receipt does not silently refresh or broaden those proofs/native results.
