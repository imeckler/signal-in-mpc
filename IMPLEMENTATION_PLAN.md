# Implementation handoff — Sol workers

## Current assignments — 2026-11-09

This section supersedes the historical assignments below. Per-work receipts and
source pins govern the scope of completed checks; this plan is not a blanket
acceptance of their results. All three Sol workers are active. Sharing refresh
remains paused.

- **tls_sol:** preserve the successful integrated restore evidence, then extend
  restoration to multiple conversations and more than four sends. Crypto has
  handed over account engine/persistence/owner/layout work for this milestone.
  First inspect the c1 and certificate-slot limits and specify a concrete state
  and outbox change that preserves uncertain pending entries and durable cursor
  reservations. Avoid copying or revalidating thousands of unchanged conversation
  records on every send. Do not substitute a larger fixed test cap for scalable
  persistence. Coordinate the revised account schema and circuit profiles.
- **signal_crypto_sol:** continue actual pinned Rust CTR implementation
  refinement in isolated work, then the remaining crypto wrapper composition and
  fresh-session/PQXDH, SPQR and skipped-message/session transitions. The accepted
  CTR conversion/exhaustion prefix is narrower than full CTR/AES/HMAC agreement.
  Keep explicit extraction/standard-library/model boundaries; do not modify
  TLS/account-engine files now owned by tls_sol without coordination. Established
  restored sends do not cover fresh-session functionality or full refinement.
- **signal_parser_sol:** connect the complete owned-envelope scan to the numeric
  streaming parser, then finish HTTP validation, private response correlation
  and compiler composition. Commit `5b2ee7d` supplies the bounded actual-source
  scan composition, not the full streaming relation. Preserve error/failure/
  divergence observations and explicitly track static-push, UTF8 and content
  model boundaries in
  `SignalReference/ChatResponseReferenceWork/PROOF_GAPS_CURRENT.md`.

Bounded integrated milestone: root inspected
`handshake_backend/OutboxResumeWork/integrated-report.json` for run 88196,
raw directory `19ccc57d3b64c8d6`: all five controllers exited 0 in 396.952 seconds, integrity true,
cleanup empty, actual certified c1 account import/barriers, fresh TLS/HTTP101,
retained-outbox replay with actual Rust recipient state preserved, then one new
message decrypted, followed by KeyUpdate/abort. Production gate and full-system
completion remain false. This is one conversation with bounded outbox slots,
local fixture credentials and no live Signal account side effects. Successful
working clone `retry-aaaa6047d704/account` advanced to head 3; the original head 2
capture is historical evidence, not a rollback source for that active account.
Preserve the first failed run 90731 and its source/binary snapshots as well.

Performance remains unresolved. The tested hybrid uses Fp25519 and Boolean CCD
with full GF128 shares; batching/caching do not remove its communication cost.
The bounded compact-backend assessment (`d9721df`) found no validated five-party
drop-in: Coral's examined release lacks required checks and contains two-party
preprocessing/conversion assumptions. Compact Rep3 measurements have a weaker
corruption/statistical profile. No production security change is authorized by
those measurements. Preserve this decision frontier and the throughput target
while completing functional work; neither the restore test nor cache tests
establish 100,000 delivered messages/hour. References:
`handshake_backend/BooleanBackendSelectionWork/AUDIT.md` and
`handshake_backend/BatchThroughputWork/comparison-report.json`.

Coordinate heavy native runs between workers. Commit owned files at meaningful
checkpoints; hold an exclusive `fcntl.flock` on `/tmp/tls-mpc-git-index.lock`
across index mutations and commits, using explicit paths and `git commit --only`.
Do not alter other workers' staged changes or historical receipts.

Completion still requires the full TLS/Signal integration, fresh and established
sessions, durable shared state, requested circuit/compiler/refinement coverage,
and appropriate interoperability and persistent-session performance evidence.
Local fixture success does not establish live Signal service compatibility or
100,000 delivered messages/hour. The backend remains unverified. Paused refresh
work cannot support a claim of completed mobile-adversary protection.

User direction, 2026-11-07: reduce token consumption and delegate actual
implementation to Sol. This supersedes the earlier Astra-high preference.
The user has resumed the root goal and explicitly authorizes delegated
implementation. Astra workers have been interrupted.
Sharing refresh remains paused.

## Operating rules

- Use Sol for implementation; do not spawn more workers or use Astra.
- Work in bounded, tested checkpoints, then continue toward the assigned
  functional milestone. The latest user instruction authorizes further Sol
  implementation; do not stop merely because a small checkpoint is complete.
  Stop at the milestone or a concrete blocker requiring external input.
- Read this file and relevant current files. Avoid replaying the entire history,
  repeated full audits, giant logs, or unrelated refactors.
- Preserve frozen proof checkpoints. Add new work in separate directories.
- Keep secrets shared. Do not enable application readiness or acknowledge
  retirement without the required cleanup. Backend execution is unverified;
  circuit/compiler correctness and runtime security are distinct claims.
- Each worker owns its assigned files. Do not stage or commit other workers'
  edits. Write a short handoff with changed files, test commands/results and
  any live process handles. Check existing handles before restarting work.

## Current baseline

Latest commit: `5738ce4`, isolated fixed-field lifetime cleanup. Earlier commits:
`a5d512b` VM scratch cleanup, `10c4928` dynamic TLS application shapes/bulk I/O,
`3a4bfab` reviewed bounded Prost bytes reference.

Five-party Shamir/CCD uses Fp25519, GF(2^128), threshold two and statistical
parameter 128. TLS handshake cryptographic stages pass. Application kernels
pass component checks; full application sessions remain gated on erasure.
No end-to-end Signal client or 100,000 messages/hour result exists.

`handshake_backend/CONTINUATION.txt` records detailed evidence and handles.
Canonical `.deps/sharing-refresh/MP-SPDZ` sources/library must remain unchanged
while runtime patches are tested in isolated trees.

## Worker 1: TLS runtime cleanup

Implement serialized-buffer lifetime cleanup as the next checkpoint. Own a new
`handshake_backend/ByteBufferWork/` and corresponding preparation/check scripts.
Build on the archived ScratchWork and LifetimeWork patches in a fresh isolated
runtime; preserve their frozen files and canonical backend.

Concrete source findings, not yet implemented:

- `Tools/octetStream.{h,cpp}` frees allocations without wiping them in destruction,
  clear, growth and replacement. `assign` frees the old buffer before allocating
  the new one, leaving invalid ownership if allocation fails. Make replacement
  transactional; preserve self-assignment and cursor/bit-buffer semantics.
- `resize_precise` can shrink the allocation while retaining out-of-range
  length/read pointers. Account for `Hash::final`, which intentionally shrinks
  its destination before resetting it; do not simply forbid that caller.
- `Tools/FlexBuffer.h` takes ownership from/to octetStream. Cover its destruction,
  growth and replacement too. Ownership transfer must preserve the live data
  and wipe only the discarded owner/storage. Fix allocation-failure handling.
- `Networking/Exchanger.h` caches the send-data pointer, then may resize the same
  receive/send stream. Refresh that pointer after an in-place reallocation.
  Test partial sends plus a larger incoming message with local socket pairs.
- Do not wipe borrowed data on `consume`, or change logical reset semantics
  without checking callers. Full live-buffer cleanup remains separate.

Validation: public synthetic allocation observers before deallocation,
allocation-failure injection, copy/transfer/cursor preservation, exchange
regression, and existing five-party X25519/router reuse tests against a fully
rebuilt candidate library. Adding nontrivial field destruction changes ABI;
never mix candidate and baseline objects. Keep sanitizer checks enabled.

Later TLS checkpoints: live Beaver/input/opening/preprocessing cleanup; raw and
bigint copies; PRNG state and correlated randomness renewal; failures/epochs;
then application activation, opaque-handle lifecycle and private Signal/H2
binding. The non-AES PRNG branch also retains old seed material in `state`;
disabling USE_AES alone is not an erasure solution.

## Worker 2: Signal parser implementation refinement

Take over `SignalReference/ProtoParseWork/MessageReferenceWork/` and new parser
composition work. Preserve accepted primitive references and frozen TopFieldWork.

Accepted: varint/key/skip references, conditional skip-plan correspondence,
uint32 merge, and bounded bytes content reference. Consult each root-review.json
for its exact assumptions. Bytes acceptance requires valid contiguous U8 buffers
and successful bounded allocation below isize::MAX.

Latest Astra state: actual generated SignalMessage dispatcher extraction is in
progress. Isolated FnItemCandidate changes handle pure function items and guard
Result-let simplification with `when monadic`; five synthetic kernel endpoints
and six translation boundary cases reportedly pass. These changes are NOT
root-accepted. Actual error-annotation closures need an explicit observable
projection that retains rejection, input suffix and fields while dropping only
diagnostic stack text. Do not substitute a success-only result for full refinement.
Source visibility/dependency closure, including opaque error layouts, remains
in progress. Inspect current logs before repeating extraction.

Next checkpoint: finish the smallest actual generated dispatcher reference that
kernel-checks, with explicit extraction/model boundaries and tests. Then compose
numeric parser lookup/scan/group/field metadata invariants against it. Frozen
TopFieldWork has 38 reported endpoints and five modules, awaiting root review.

## Worker 3: XEdDSA/prekey refinement and integration

Take over `SignalReference/XEdDsaReferenceWork/` and new reference/integration
work. Preserve frozen XEdDsaWork, PreKeyWork and PreKeyReferenceWork.

XEdDSA Lean primitives and `signal-xeddsa` root export dispatch are implemented
but uncommitted; 33 profiles reportedly match frozen standalone exports exactly.
Implementation-refinement review and private mixed-domain runtime binding remain.
The prior helper selected actual pinned dalek FieldElement51::from_bytes/load8_at
used in XEdDSA recovery, targeting low-255-bit/noncanonical normalization
agreement with the frozen shared-input boundary. Inspect current artifacts/logs
and complete that bounded actual-Rust/Aeneas refinement first.

PreKeyWork has numeric composition/policy checks but external trust-result and
typed-input assumptions. PreKeyReferenceWork has actual constructor extraction
with explicit Option/NonZero/closure models, eight reported endpoints and 2048
native cases; it is not yet accepted. Neither checkpoint proves full async
process_prekey_bundle, store updates, complete Signal sessions or native MPC.

Later checkpoints: complete signed-prekey verification/refinement and state/store
transitions, connect established-session send producers to private TLS/H2 inputs,
then measure persistent-session throughput. Existing measured costs are far below
the target; do not extrapolate component timings into delivery throughput.

## Review queue and completion

Frozen unreviewed checkpoints: TopFieldWork, XEdDsaWork/root export, PreKeyWork,
PreKeyReferenceWork, and new translator/model experiments. Review only the
dependency needed by the next implementation checkpoint; avoid duplicate audits.

Completion still requires functioning persistent TLS + Signal sessions with
secret identifiers/keys, intended compiler/refinement proofs, runtime lifecycle
integration, interoperability evidence and an honest performance estimate.
No worker may redefine completion around its own component tests.

## Round 2: root review and active assignments

The user requested review and redistribution of work toward system completion.
All three existing Sol workers have been restarted. Sharing refresh remains
paused. The earlier Worker 1–3 sections describe the historical first round;
the assignments below now take precedence. Review evidence is recorded in
`benchmarks/results/sol-round1-root-review.json`.

### Reviewed results

- **ByteBufferWork:** reviewed patch/checker; independently reran the sanitized
  buffer harness successfully (12 observed wiped releases). Verified all 35
  source, 7 product and 23 log hashes in the recorded report, including successful
  five-party results at capacities 6, 1029 and 16385. Those five-party runs were
  inspected, not repeated by root. Accept only the isolated discarded-owned-buffer
  cleanup checkpoint; it does not implement complete session retirement.
- **MessageReferenceWork:** independently reran its five-module Lean check.
  The observation definitions and conditional unknown-tag result check, but the
  dispatcher theorem depends on seven external axioms. A manual generated-code
  correction and unproved Rust/model correspondence remain. Retain as a candidate
  scaffold, not accepted parser refinement. Conditional skip-plan agreement must
  not be confused with an accepted actual `skip_field` implementation reference;
  exact primitive review receipts control the usable dependency boundary.
- **XEdDsaReferenceWork:** reviewed actual decoder proof/input bridge and reran
  `check.py`: 17 kernel endpoints, 838 decoder cases, 1,676 native normalization
  comparisons. All 24 receipt files still match after the independent rerun.
  Accept only actual byte-decoder/normalization refinement and the stated circuit
  input/alias bridge. Full point recovery/verifier and private execution are open.

Acceptance here is a scoped review decision. Preserve historical candidate
receipts rather than rewriting their acceptance flags or claiming readiness.

### tls_sol: persistent native TLS lifecycle

Own handshake_backend, TLS scripts and new isolated runtime candidates. Implement
safe quiescent lifecycle cleanup and correlated-randomness renewal for remaining
protocol/preprocessing/opening/PRNG/bigint state; connect real retirement,
rotation and abort capabilities to NativeSession. Preserve live application
shares and protocol consistency. Audit failure and zero-size ownership paths.
Do not enable readiness until the required conditions actually hold.

Milestone: five parties complete an authenticated handshake and repeated private
application records with a local TLS peer, including KeyUpdate, authentication
failure, abort and sequence/lifecycle checks. Coordinate a private producer handle
interface with signal_crypto_sol. Never reconstruct application keys or identifiers.

### signal_parser_sol: actual dispatcher and circuit agreement

Own ProtoParseWork and new parser composition modules. Fix the isolated translator
and reproduce generated output without a manual patch. Replace dependencies using
actual justified references, preserving rejection, fields, suffix and recursion
budget; prove the error projection within the supported contiguous-buffer domain.
Compose scan/group/field metadata and numeric parser agreement. If actual skip
extraction remains blocked, state its exact remaining obligations and progress
send-critical work independently. No new assumed-correctness axioms.

Milestone: usable parser implementation refinement for the supported message
domain, with malformed/duplicate/unknown/group cases and remaining boundaries
explicit. Prioritize send-path needs and separate receive-only obligations.

### signal_crypto_sol: verifier and private send integration

Own new Signal crypto/reference/session integration modules and Signal backend
files. Extend actual decoder agreement to point recovery and XEdDSA/prekey
verification; reuse matching pinned BAF artifacts where justified. Prove circuit
agreement with implementation behavior, including rejection, rather than internal
cryptographic security. Preserve frozen earlier checkpoints.

Audit established-session send circuits, implement missing state/store transitions
and private mixed-domain binding, then feed shared ciphertext and recipient/request
data into the TLS producer interface. Coordinate ownership with tls_sol before
editing interface files. If verifier proof blocks fresh sessions, make independent
progress on established sends without misrepresenting the fresh-session scope.

Milestone: actual libsignal differential/interoperability evidence and a private
established-session send path through TLS; document remaining fresh-session proofs.
Use scoped git commits for reproducible source/proofs, excluding vendor/build trees.

### Integration and measurement exit criteria

After these milestones, integrate persistent TLS transport with Signal request
framing, response handling and durable shared conversation state. Test repeated
sends, fresh and established sessions, rejection/abort, nonce/state persistence,
and absence of secret reconstruction in the output path. Share refresh is a
separately paused dependency: do not claim mobile-adversary protection complete.
Benchmark actual persistent-session workloads, reporting payload sizes, party
count, preprocessing cost, bandwidth and RTT; distinguish local measurements
from WAN estimates. 100,000/hour means about 27.8 delivered messages/second,
not circuit evaluations per second. No throughput or system-completion claim
until the corresponding evidence exists.

## Resumed goal: actual relay service path

Root inspected `../secret-shared-db/server/relay-node/src/notify.rs`,
`signal_requests.rs`, and the workspace Cargo.lock after the crypto worker
identified a transport mismatch. The relay locks imeckler/libsignal commit
`c1d9fb55ded1eca7ef6aae35cdedc2452bf6529c` and uses ChatConnection's
WebSocket chat path. Sending requires Content/DataMessage encoding and padding,
private UUID/access-key handling, recipient device lookup, per-device
`sealed_sender_encrypt`, and type-6 JSON messages submitted via
`PUT /v1/messages/{UUID}?story=false`.

The generic HTTP/2/gRPC helper and its synthetic protobuf are transport fixtures.
Their successful tests do not establish compatibility with this relay or the
Signal service. No further H2-specific implementation is on the critical path
unless actual inspected service requirements justify it. Compatibility with a
current deployed service is a separate verification obligation from matching
the pinned relay; no real account/message side effects are authorized by tests.

Active dependency sequence and ownership:

1. **tls_sol:** finish the running repeated-private-record/KeyUpdate/rejection
   test, then expose the transport-independent opaque payload and receive handles
   needed for a persistent WebSocket connection. Preserve real lifecycle checks.
2. **signal_parser_sol:** fix the core numeric parser's error-time initialization
   mismatch and corresponding compiler/refinement proofs. Root explicitly grants
   ownership of `TlsMpc/Signal/ProtoParse.lean` and dependent parser proofs; no
   further coordination permission is needed for this fix. Preserve historical
   receipts and document which previous source-bound claims must be rechecked.
3. **signal_crypto_sol:** implement actual private request encoding, sealed-sender
   envelopes, certificate/UAK/device semantics and state persistence. Coordinate
   WebSocket upgrade, framing and response correlation with TLS. Bare SignalMessage
   wire is not a sealed-sender envelope. Continue fresh-session/verifier reference
   closure in the same queue, without claiming established sends cover it.
4. **Next available Sol worker:** complete service response parsing and device
   refresh/retry policy without exposing identifiers or reusing uncertain send
   state. Reuse parser work once its current correctness issue is closed.

Reported intermediate evidence (not a fresh root acceptance): five-party
shared-state Signal fixture completed two sends; candidate TLS handshake and
retirement succeeded. Persistent application test is still running. Full
to_edwards extraction is blocked on the pinned Step.forward_overflowing model.
The dispatcher candidate now has concrete dependencies, but a kernel example
shows numeric/Prost rejection-state disagreement. These facts change the next
implementation actions; none establishes end-to-end delivery or throughput.

Completion still requires both established and fresh session functionality,
durable secret-shared state, implementation/compiler proof coverage, actual
service-compatible private request/response integration, and persistent-session
performance evidence. Sharing refresh remains paused by user instruction.
