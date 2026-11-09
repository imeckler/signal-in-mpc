# Scalable restored account: proposed next implementation

Status: design for review, not implemented or authorized activation. The verified predecessor is88196/81737f4, c1 and bounded four-entry outboxes. Preserve active head3 at `retry-aaaa6047d704/account`; do not reopen the historical head2 capture. Compact Boolean/t2 decision frontier d9721df and the unmet27.8msg/s target remain independent blockers.

## Source constraints

`AccountLayoutV2.h` restricts conversations to1..4 and `OwnedAccountV2::clone` copies every share section. `AccountRecoveryEngineV1::Persistence` fixes layout to c1, and resolve derives the pending ordinal from certificate slot. `AccountDurableOwnerV1::reserve/commit` clones the full account, restricts certificate slots to1..4 and writes outbox cell `slot_`. Thus increasing an array limit alone neither removes the send ceiling safely nor supplies scalable persistence.

## Smallest durable architecture change

Introduce a versioned sharded checkpoint schema while retaining the existing signatures, journal/current-head authorization, encryption and checked GF128 import:

- One global shard owns credentials, identity/global stores and the private account request-ID cursor. Each opaque public conversation slot owns a fixed-size shard containing canonical record, selected/service state, frozen intent and its bounded outbox. Slot linkage is already permitted metadata; no Signal identifier becomes public.
- A certified root commits to a persistent paged/Merkle directory of per-party encrypted shard digests, versions and schema domains. Reserve/Commit update the global cursor shard and only the selected conversation shards, plus directory paths. Unchanged ciphertext references remain immutable. No full private-account clone, serialization or MPC revalidation per send. The certificate still binds all five party roots and the exact program manifest.
- Keep at most four active conversations in the existing connection/VM batch. Lazy admission verifies a shard's inclusion in the authorized current root and privately validates its fixed profile. Unchanged-shard validity is inherited from the authorized previous root; replacement shards require the actual computed binding checks. This inheritance and migration rule must be tested, not assumed from a hash alone.

Separate the monotonic certificate sequence from outbox storage. Under the existing one-pending-per-conversation policy, a small private compaction kernel may reuse only absent or authenticated observed-accepted cells. Preserve committed-unsent, attempted, uncertain and rejected entries conservatively; if no eligible cell exists, reject before durable Reserve. Do not infer delivery from2xx. Bind completion leases to certified head, boot context, conversation slot, cell and generation; stale ACKs cannot modify a reused cell. A public fixed destination is possible by privately compacting eligible cells before insertion, avoiding a secret host index. Preserve original request ID and Signal ciphertext on resume; remask each new transport frame as today.

One account Reserve still binds the entire batch's frozen inputs and final private cursor before producer evaluation; one Commit binds all actual results/outboxes before release. Uncertain reserved ID ranges remain burned, unresolved higher Reserve still blocks activation, and failure poisons the admitted batch. TLS sequence/nonces remain connection-local and fresh after restart.

## Bounded implementation order

1. Implement immutable shard-directory storage and certificate-root transition checks with the actual coordinator/journal. Test unchanged-reference inheritance, changed-shard authentication, crash between Reserve/Commit, missing shard, stale root, and recovery without reading unchanged ciphertext bodies. Count bytes/shards touched for2 versus1000 synthetic opaque slots; host tests are not native admission evidence.
2. Add the small versioned outbox compaction/generation circuit with kernel/compiler proofs coordinated with crypto. Test no overwrite of dispositions1/2/4/5, stale leases, ACK/restart uncertainty and exact retained-wire/ID preservation. The existing full service producer need not be recompiled for this policy change.
3. Implement an explicit quorum-authorized schema/program-domain migration from head3. Preserve all shares, cursor and pending entries; old history stays immutable and the new current-head chain must prevent activation of the predecessor domain. Never relabel an old archive or restart genesis with the same account state. Migration authorization and cross-domain rollback handling are acceptance requirements before using the active fixture.
4. Native local-peer acceptance: two genuinely distinct conversations, at least six new sends per conversation, equal-work B2 execution, reordered replies, retained uncertain entry through restart, stale old completion rejection, actual recipient body/counter checks, and fresh TLS on restore. Record changed-shard costs separately from MPC producer/parser costs. No production gate promotion from host tests.

This is a persistence/state-scaling change, not a promise of throughput. Existing GF128 Boolean traffic and refresh/mobile-compromise assumptions remain. New directory metadata leaks opaque slot access/linkage, consistent with the current public slot interface; it must not carry private identifiers or lengths.
