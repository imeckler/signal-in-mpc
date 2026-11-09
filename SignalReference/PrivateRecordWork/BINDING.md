# Computed canonical record/service binding candidate

`PrivateRecordBindingV1` computes equality of the retained canonical record and
actual overlaid service input: version, sender/receiver identity, ratchet point,
chain/counter/previous, active PQ send key/counter/epoch. It also checks canonical
presence/buffer statuses (normal proto3 scalar slots are always present in the
private capacity representation), required key widths/type5, no version negotiation,
canonical NoHeaderReceived tag and no-chunk kind, and rejects Tahini inactive
counter overflow. These are secret operations, not host-supplied correctness flags.
The actual service result's status is ANDed with those checks. Rejection selects
the prior service fields and retains the canonical record; acceptance applies the
canonical sender update. The binding does not recompute crypto.

The function is intended between the pinned producer and store preview; it is not
wired into the normal provider yet. The producer prefix must come from actual
private service evaluation, not a public import/RPC. The current concrete tests
use a prefix derived from actual Rust sender states, a public dummy certificate
and real selected fields; they do not execute private service crypto.20 cases
cover accepted first/repeated/Tahini sends and mutations of all bound fields,
producer/noncanonical statuses, malformed presence, unsupported KeysUnsampled
phase and overflow. All selected snapshots stay private model bytes; fixtures are
public and disposable.

Profile selection by the first canonical V1State key is not a complete parser or
proof of arbitrary serialized KEM validity. Full bootstrap/schema validation,
actual source and Hom/compiler theorem, full SPQR/skipped/prekey transitions,
native bound owner, durable callbacks/import and retirement remain required.
Normal recovery/provider admission stays closed.
