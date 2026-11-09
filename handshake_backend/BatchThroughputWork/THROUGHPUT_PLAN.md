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

## Candidate normal-profile integration

Opcode26 now accepts a bounded public list of opaque owner/input handles. The
controller's explicit `batch` mode selects TWO ready distinct conversations,
waits for response ownership to release them, and sends returned TLS records in
order through the existing sequence allocator. This is actual producer batching,
not just outstanding WebSocket slots; there is still ONE synchronous VM entry.
`NativeConversation` uses the staged crypto helper4e644ba with one collective
readiness and whole-group commit/install before any result; registry validates
all dimensions before retaining, preserves every computed/upstream validity,
burns global private IDs first and performs ONE retirement checkpoint. Any
uncertainty closes the entire admitted registry. Its current no-op durable
reserve/commit hooks preserve the existing nonrecovering profile; authenticated
full-account durability/bootstrap gates remain closed.

Host sanitizer ownership/rejection tests, old registry regressions, actual Lean
controller elaboration and normal worker/OwnedBits API compilation pass. No
full-service batch artifact/native recipient pass is claimed yet. Explicit next
command is `python3 -u handshake_backend/BatchThroughputWork/prepare_service.py
260 80 0 0 --count2 --sha-profile gate-efficient` (spell CLI as `--count 2`).
It preserves old products, compiles a same-profile SINGLE baseline and B2 closure,
pins source/public profile identity, and records public phase PID/CPU/RSS/elapsed.
The workload will be two distinct established conversations, four nonempty
messages each with actual retained recipient state, same capacity/security/
epoch policy in sequential versus batch runs. End-to-end bytes and throughput,
not SHA depth, choose adoption. More repetitions will be required before a
credible steady-state/WAN production estimate.

## Equal-work runner ready, native comparison pending

Extended fixture1e7667a supplies eight actual recipient-validated texts at the
same capacity. The new disposable worker enables ONLY diagnosticv4 telemetry:
`TLS_DOMAIN_METRIC` bins are domain-major (unattributed/field/binary) then phase
(unattributed/online/preprocessing); counts/times are nested inclusive scopes,
never sum their wall times. Loader and initialization-reset counters are explicit.
Legacy worker builds without the macro retain their prior telemetry layout.
The runner uses one identical manifest/runtime/worker across `sequential` and
`batch`, four rounds per conversation, unique result files, and RAW elapsed/PIDs.
All source/product/oracle hashes are checked across each run. Explicit runtime
library selection is necessary because the diagnostic library's install ID is
relative; the frozen runtime itself is not edited. Real archived-cache profile
substitution, unknown collision rejection and loader checks passed WITHOUT MPC.

The ongoing92684 builder has completed its single closure at6116602 bittriples /
122242 VMrounds. Batch compile is still pending; none of these runner checks are
an end-to-end batch/recipient/throughput pass. After this frozen comparison, the
priority is an explicit compact Boolean-backend audit (n5/t2/malicious, actual
wire/offline costs and conversions). Current GF128 CCD is functionally Boolean+
Fp hybrid but is NOT compact Boolean wire sharing. Any3PC/t1 alternative must be
separately labeled as a security tradeoff, never a silent default change.

## Frozen equal-work native result

Both eight-text runs PASS all five parties, no cleanup errors, exact same
source/worker/runtime/manifest identity. Actual target recipient validates all8
texts/timestamps/certificates on2independent conversations, reordered responses,
9pongs, TLS1.3/H1/KeyUpdate and terminal abort. No live account effects or client
plaintext opening. Reports: sequential2ebd4e9, paired comparison-report.json.

|Local equal8-message sample|Sequential|Batch2|
|---|---:|---:|
|Inclusive elapsed seconds|1505.434|1256.156|
|Inclusive messages/second|0.005314|0.006369|
|Persistent-window party0 payload bytes/message|4951091390|4946014800.5|
|Window loader seconds|702.910|521.577|
|All reported epoch renewals|48|44|

Inclusive throughput improves1.198x; payload falls only0.103%. Binary online
window bytes are IDENTICAL14314139136; binary preprocessing25065459280→
25065409872. Most byte saving is field preprocessing. Fewer producer group
checkpoints account for4fewer epochs; every-record policy itself is unchanged.
Both counter streams reconcile exactly after recorded initialization-reset bytes
(23616/21312). RPC-only window durations exclude host gaps and are upper-bound
rates, NOT measured wall-window steady throughput. Eight messages/local parties
are not enough for a WAN production estimate. Generated/discarded triple counts
remain unavailable; measured preprocessing traffic includes their cost.

Repeated single producer calls take104–111s, with64–66s program loading EACH;
B2pairs take151–152s with86–87s loading/pair. Source prepare() unconditionally
clears progs and reloads the schedule. Immutable public-code caching is justified,
but cannot fix bytes. At~4.946GB/message,27.78/s requires~137.4GB/s perparty
MPC payload alone, before link overhead. Target100k/hour remains unmet.

No further full application baseline is warranted without an actionable change.
Next: actual compact Boolean/small-field verification/backend-selection audit,
LN17/CHI23 controls, checked active n5/t2 conversions and full128 statistical
parameter mapping. Do not assume128-bit statistical checks require128-bit value
shares; verify published machinery and supported pinned code, never invent an
unaudited construction. Loader cache is a separate bounded implementation task.
