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

## Internal owner wiring candidate

`RecoveryWork/NativeRecordBinding.h` names only the fixed pinned
`signal_private_record_bind_v1` function. Its future input is the 5550-byte private
snapshot, actual 611-byte staged call and actual 81-byte service prefix; output is
bound prefix81, selected525 and snapshot5550. `ExportBinding.lean` typechecks that
layout, but an exported/compiled binding artifact has not been tested yet.

`NativeCanonicalSendOwner.h` owns the canonical snapshot and volatile service
view alongside the store. B1 delegates to the batch-first path: reserve one full
account, evaluate the actual service batch once, privately bind each lane,
preview all results, durably commit all selected records/outboxes, then install
all stores before releasing any payload. An uncertain failure closes every
admitted owner. Distinct conversations retain independent response completion;
remote delivery acknowledgment is not the state-commit boundary. Transactions
must preserve unrelated conversations and earlier pending outboxes.

The compile-only probe instantiates B1 and batch templates with actual OwnedBits;
it does not execute MPC, persist an account or grant admission. Actual archive
transaction callbacks, complete account fields, checked import and pre-Session
helper/epoch retirement remain unbound. No normal provider selects this path.

The owner additionally retains the 525-byte selected receive view and includes it
in reserve/commit borrows. Its replacement comes from the same private binding
output as the canonical snapshot, rather than leaving a stale receive overlay.
Initial record/selected/service coherence must be established by the future
checked bootstrap resolver; constructor dimension checks do not establish it.
