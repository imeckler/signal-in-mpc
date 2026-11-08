# Throughput-first execution milestone

Target100000/hour=27.78 messages/s. Four existing outstanding WebSocket slots
currently overlap response waits; they do NOT make producer MPC concurrent.
No latency-profile native four-text run was launched. Full latency compile
receipts remain optional evidence, not the selected throughput configuration.

## Implemented first checkpoint

Versioned `backend_adapter.aig_batched` plans ONE immutable public DAG and
packs independent message instances together within each AND/local-XOR group.
It avoids duplicating exported graphs or materializing a whole Cartesian group.
One VM caller executes it; it adds no shared-Machine concurrency or protocol
change.1344 public differential cases compare independent sequential outputs,
partial lane batches, inversion routing, exact AND-bit consumption and depth
boundaries at sizes1/2/3/4/8/17/64 and lane widths1/7/64. These are adapter tests,
not native protocol/performance evidence. Production dispatch remains unchanged.

## Two-phase conversation ownership

Crypto owner coordinates a bounded transaction API: stage/reserve distinct
conversation inputs and connection-global private unique requestIDs; invoke ONE
pinned batch; validate all dimensions/status policy; commit selected ratchet,
PQ/counter/request state for every admitted item BEFORE releasing any payload.
One pending request per conversation; at most four pending per connection in
first profile. Unknown callback failure, partial commit, cancellation, timeout or
uncertain send poisons all admitted conversations, with no rollback/retry.
Each computed rejection remains attached to its instance and must not become a
normal zero payload. Whether rejection isolates a safely uncommitted item or
closes the batch must be explicit; initial policy is fail-all.
TLS record sealing and connection sequence allocation remain serialized after
batch commit. Responses correlate privately to global IDs; duplicate/replay or
ambiguous matches never unlock a conversation. No concurrent unsafe VM calls.

## Mixed field and lifecycle scope

This first executor batches ONLY the Boolean DAG. Current four X25519 field
computations and checked daBit conversions are scalar and serial in mixed.py;
end-to-end measurements MUST include them. A later mixed vector/batch entry must
preserve bitness checks, fresh coefficients/scalars/masks, independent recipient
binding and exact conversion rejection semantics; vector register IO alone is
not proof of protocol batching or lower network cost.

Current every-record epoch renewal is candidate policy, not a TLS requirement.
Amortization may retain preprocessing within an explicitly defined compromise/
refresh epoch only after runtime ownership, retirement, failure cancellation and
rollback guarantees are tested. No bypass of the cleanup barrier, reused TLS
nonce, untracked preprocessing batch or lowered security parameter is authorized.
Loader preparation must be keyed by immutable pinned closure/runtime epoch;
cache reuse and epoch setup costs must be measured separately.

## Next bounded experiments before another full export/build

1. Compile tiny sequential versus batched Boolean fixtures at sizes1/2/4/8;
   compare exact outputs, AND demand, actual VM rounds and packed instruction
   counts. Run same five-party CCD128/t2 fixtures with authenticated rejection,
   per-instance outputs and terminal cleanup, using diagnosticv4 counters.
2. Implement and sanitizer-test coordinated store reserve/eval/commit order,
   duplicate conversation and stale-ID rejection, reentrancy and partial failure.
3. Select gate-efficient carry profile for one required same-capacity full-service
   artifact migration; do not rebuild merely to demonstrate latency. Reuse the
   mathematical service compiler/Hom endpoint and actual recipient text oracle.
4. In ONE necessary persistent test compare equal nonempty48-byte-capacity text
   workloads, two genuinely independent conversation states, counters127→128,
   sequential versus batch2 (then4 when four independent states exist). Keep
   TLS persistent, include reversed responses/pings and actual recipient decode.
   No repeated fixture pretending the same live ratchet can be evaluated twice.
5. Report total/offline/preprocessing/online payload bytes per successful message,
   consumed versus generated/discarded preprocessing, prep/load/epoch/setup
   overhead, useful steady messages/s and all failure costs. CLOCK_MONOTONIC_RAW
   is the suspend-aware elapsed clock; log public child PIDs/phase/rusage.
   Sum operations are not critical-path rounds. Packed bits are not assumed to
   be packed network bits. No throughput claim from graph depth alone.

Historical four-text~5.205GB MPC payload/message would require~144.6GB/s per
party at target rate by simple linear scaling, before external/link overhead.
The13.1% SHA-block gate saving is not enough by itself. Cross-instance packing
can amortize opens/round/setup overhead but does not remove logical AND work;
protocol/preprocessing bytes and the mixed-field cost decide feasibility.

## Frozen persistent-window attribution and TLS connection choice

Root's nonoverlapping top-level party0 RPC slice (first rpc24..last rpc25 in
`a30680461a80ab54/party-0.log`) totals20821778000B:
producer9657935744(46.384%), private response7996251776(38.403%), TLSseal
2715856896(13.043%), TLSopen250014208(1.201%), control16905408(.081%),
rotate184813968(.888%). TLS-related total15.213% is a BYTE fraction, not walltime.
The endpoint8899B/4≈2.225kB/message including setup/control would be~61.8kB/s at
target for this fixture shape; MPC internal transport dominates those external
TLS bytes. Preserve the old suspend-clock caveat in all time comparisons.

Prioritize same-connection batch sealing with an ordered, unique TLS sequence
range reserved before computation and a quarantined ciphertext queue released
in order after complete successful checks. Failed/uncertain reservations never
reuse a nonce; KeyUpdate/abort cannot cross pending-range boundaries. Current
single pending_send API does not already implement this. Do not add threads
calling the same Machine. A bounded2/4-connection shard remains an option ONLY
if measurements isolate TLS queue/head-of-line blocking after batching; it does
not remove MPC bytes or single-Machine serialization. Real service same-account
connection acceptance/replacement policy must be verified before pool integration;
no assumption that the service accepts arbitrary parallel authenticated sockets.

## Tiny native evidence (Boolean stage only)

`native-report.json`: all five parties passed independent private-input aggregate
output comparisons and a deliberate functional mismatch rejection at B2/4/8,
two alternating orders; no shared inputs/outputs were opened. This is NOT a
malicious MAC-tamper test. Epoch renewal follows each pair, so first/second call
preprocessing/setup asymmetry is visible rather than hidden. B8 party0 means:
sequential45.68ms vs batch31.10ms,~1.47x tiny-call throughput; identical3552
consumed AND triples and mean1251424B per batch (~156428B/instance). This is not
steady service throughput, WAN performance or an8x claim from compiler rounds.

Online binary traffic is exactly128B per logical AND here; preprocessing is
about224B/AND plus small fixed overhead. The historical producer's6738497 ANDs
already imply862527616B perparty online alone at that rate, BEFORE field-DH,
response parsers/TLS/offline generation/epochs. Scheduling cannot close the
100k/hour communication gap. After executable mixed/store batching, prioritize
fewer circuit gates or an evidenced malicious n5/t2 backend with lower per-bit
wire cost, preserving security128. Do not infer a new protocol from packed IO.

## Representative mixed-domain checkpoint

`mixed-native-report.json` allfivepass,9.577s cleanup[], exact output comparisons
on retained private instance inputs. The mixed fixture adds per-instance checked
binary→Fp conversion, scalar square+17, and canonical Fp→binary conversion; the
field stage remains serial. It is NOT four X25519 operations or a service test.
B8 consumes17856 bittriples,2104 daBits,8 fieldmults in BOTH modes; measured
20344480B/call in BOTH. Mixed compiler rounds2439→2355, party0 pairedmeans
1.225s→1.151s (~1.064x); B4 batch was slightly slower .666s vs .658s.
This explicitly limits the Boolean-only scheduling result. Offline batch/setup
and field/conversion costs must remain in a real throughput comparison.
