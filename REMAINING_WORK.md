# Remaining work: TLS and Signal in MPC

Status snapshot: 2026-11-09. This is a planning document, not a new assignment or
authorization to restart workers. All three current workers reported completed
checkpoints and no live jobs. Sharing refresh remains paused. The historical
Signal/Astra workers are not present in the current agent roster.

This snapshot supersedes stale progress statements in older handoff documents;
individual source-bound receipts still govern what has actually been checked.
No secure full EMP/field application or target-throughput result exists yet.

## 1. Agent status

| Agent | Latest checkpoint | Completed scope | Remaining scope |
|---|---|---|---|
| `signal_crypto_sol` | `003b81f`; rejected extraction recorded in `dcb73ab` | Five recent proved checkpoints: nested four-block XOR, actual CTR exhaustion preflight, buffer write/drop under scoped models, tail generator, selected parallel chunk through key schedule and compiler. 57 foundation-only endpoints and 11,328 actual-library observations. | Full callback cannot yet typecheck: three mutable-iterator/owner-exit mismatches. Whole buffered caller/private-length composition and HMAC/KDF refinement remain open. |
| `signal_parser_sol` | `0ca46a9` | Complete actual inner-group state/cache/frame refinement, all wire kinds and nested groups, errors/private bounds/recursion limits; generated dispatcher/callback and full parent-loop outcomes composed. Focused kernel checks passed. | Complete source event trace, outer groups and whole schema scan, HTTP validation, private correlation, final compiler composition. |
| `tls_sol` | `9285b59` | Reproduced EMP private-input disclosure and output forgeries; isolated input repair passes eight controls and AES/SHA. Prior hybrid value conversions, one-use pool and word roundtrip have functional tests. | Secure active validation/output layer is blocked. Input repair deliberately rejects PUBLIC/ALICE openings. Native hybrid X25519 is compiled, not executed. All application, lifecycle and performance integration still required. |

No new tasks were sent to these agents when preparing this plan.

## 2. Scope and architecture to retain

- Two computing parties A/B, EMP Boolean computation plus native arithmetic over
  `p = 2^255 - 19`; MP-SPDZ MASCOT is the arithmetic candidate. At least one
  computing party must remain honest. Abort is acceptable. A larger storage
  quorum does not restore the former two-corrupt-compute-party guarantee.
- Keep Signal identifiers, private keys, conversation state and TLS traffic
  secrets inside shared computation. Public server-authentication metadata,
  opaque conversation handles and repeated-send linkage are allowed.
- Convert representations around whole curve computations, not every field
  operation. Curve coordinates, scalar-order arithmetic, arbitrary key bytes
  and PQ polynomial domains must remain distinct typed representations.
- Lean specifications and circuit/compiler correctness, with agreement against
  pinned Rust translated by Aeneas. Proving the internal cryptographic security
  of libsignal is not required. MPC backend security need not be mechanized,
  but its implementation and composition assumptions must be credible and explicit.
- Finish established and fresh sessions, including the actual relay request and
  response path, durable shared state, restart and required session transitions.
- Target 100,000 logical sends/hour (27.78/s), mostly established sessions,
  thousands of conversations, internet links, persistent TLS and possibly
  multiple connections. Device deliveries and logical sends count separately.
- Existing-key import remains a required supported route unless explicitly
  replaced; fresh joint generation is an available deployment option.
- Mobile-corruption protection is unfinished and refresh is paused. It requires
  its own model and integration for the new storage/compute architecture.

## 3. First blocker: establish a secure Boolean backend

**Priority P0.** The pinned EMP rewrite
`a245ca0f67abaf2d48c711e3c050ce961e60ad29` is not an accepted private or malicious
backend. The reproduced failures are raw private-input transmission, forged
PUBLIC output accepted by Alice, and false reported AND output accepted by Alice.
These are findings about this implementation, not a break of the published
authenticated-garbling protocol.

The owner-only input repair is partial. A masked-input regression and successful
AES/SHA execution do not establish confidentiality or malicious security. Keep
`secure_hybrid_backend=false`; all previous EMP/hybrid performance and conversion
results are functional evidence only.

Progress 2026-11-09 (later): step 1 has a recorded recommendation — complete the
modern engine — with an implemented candidate `validated-v3` and attack
regressions; see [route record](handshake_backend/EmpHybridWork/VALIDATION_ROUTE.md).
A fourth failure was reproduced: with only the input repair, a malicious
evaluator recovers garbler wire values by misreporting masked AND outputs. v3
rejects it, and the earlier input, padding, zero-AND carry and state-continuation
regressions pass on it. Triple generation was compared with the published
figures ([audit](handshake_backend/EmpHybridWork/TRIPLE_POOL_AUDIT.md)). The
stock in-place construction and its unauthenticated correction bits were judged
unsound for malicious security; v3 now uses fresh triples per bucket layer with
per-layer checks, a joint coin and authenticated openings. Step 4's padding original-output equivalence is kernel-checked
for a hand-written Lean model (`PaddingSemantics.lean`); joining it to the C++
and compiler is open. v3 is unreviewed, so the acceptance flag is unchanged.

Remaining steps:

1. Choose between completing the exact revised KRRW active-validation/output
   protocol and adapting a supported historical engine after a source/security
   audit. Record precise protocol revision, dependency pins, parameters and
   implementation mapping before selecting the route. Do not silently replace
   EMP or use a guessed reciprocal-MAC patch as the security argument.
2. Implement and review input authentication, both-party validation, output
   authentication, ordering and privacy of checks, and retained authenticated
   state. Resolve possible chosen-message/MAC-query effects in the composition.
3. Retain and rerun the input-disclosure, PUBLIC-lie and false-Gamma attacks, plus
   malformed encodings, retained-key corruption and nonlinear continuation tests.
   Validate both roles and each supported output recipient.
4. Revalidate the zero-AND mask-propagation repair and tiny-kernel padding against
   the chosen engine. Finish the Lean original-output-equivalence theorem for
   padding; dummy wires must participate in real checks before disposal.
5. State computational/statistical parameters and whole-run failure accounting.
   Current configured statistical 40 is not statistical 128, and configuration
   alone does not validate a protocol. Include the number of batches/checks over
   the intended deployment lifetime.

Exit: an explicit reviewed implementation/security argument and passing attack
regressions for the required active-MPC interface. No claim that tests alone prove
security. This gate precedes accepting the bridge or running real secrets.

Evidence: [security status](handshake_backend/EmpHybridWork/SECURITY_STATUS.md),
[input-boundary report](handshake_backend/EmpHybridWork/input-boundary-report.json).

## 4. Complete and revalidate EMP/native-field integration

Existing reusable work: native field owner, checked coin-generation candidates,
bidirectional conversion algebra, canonical modular addition, session-bound
one-use pools, full private word roundtrip and compiled X25519 FieldDag adapter.
Their security depended on the invalid EMP black-box assumption and must be
re-established after section 3.

Progress 2026-11-09 (later): decisions — malicious security retained; statistical
128 is the production profile for Boolean buckets, bridge pools and the native
engine. On candidate v3 at that profile the full-word roundtrip and its
wrong-counter fault pass, and the native X25519 candidate **executed for the
first time**: private scalar/point, result checked in MPC against an independent
library, low-order and mismatch cases rejected
([results and cost](handshake_backend/EmpHybridWork/HYBRID_V3.md)). One X25519
costs about 2.3 GB of native traffic per party at this profile. A candidate
cheaper path (scalar swap bits kept in the field, full-width masks checked in
the Boolean engine, a leaner Lean ladder with masked inversion; every circuit on
it compiled from Lean) measures 0.29 GB and passes the same checks plus five
fault cases
([levers](handshake_backend/EmpHybridWork/CONVERSION_COST_LEVERS.md)); its
construction needs review. Step 6 is exercised for TLS: the private X25519
result feeds the Lean handshake-secrets circuit unopened and the derived secrets
match an independent implementation. Rule adopted 2026-11-10: every circuit is
compiled from Lean; `TlsMpc/BoolDag.lean` is the gate-level compiler for circuits
that need exact gate structure. Steps 3, 5 and 6 are exercised but not accepted;
steps 1, 2, 4 and 7 remain, as do the Signal-side producers for step 6.

1. Map the MArBled Circuits daBit construction to the accepted Boolean and MASCOT
   interfaces. Review input fixation, fresh joint challenges, cut/bucket checks,
   non-bit rejection and authentication before release. Track generated,
   sacrificed, consumed and unused correlations separately.
2. Complete generic Lean conversion/compiler composition: bit/field agreement,
   canonical encoding and modulo addition, accepted-mask range, rejection,
   padding and state ownership. Separate proved value identities from the
   unmechanized randomness/security argument.
3. Revalidate both conversion directions, full-word roundtrip and fault controls.
   Enforce same A/B identities, code/runtime closure, epoch, operation counter,
   direction and consumed-mask range. Burn reservations before opening; reject
   replay and cross-owner/session handles without leaking intermediate values.
4. Replace loopback identity assumptions with authenticated peer/channel binding
   across both transports. Handle asymmetric failure, crash and cancellation;
   cooperative readiness before teardown is not crash-safe cancellation.
5. Execute the prepared native X25519 candidate only after the security gate:
   private scalar/point, clamping and encoding, all-zero rejection, checked
   conversions, actual FieldDag execution and independent result comparison.
   The prepared graph has 9,437 nodes and 4,589 multiplications; compilation is
   not execution. Include conversion/preprocessing costs in measurements.
6. Integrate curve results directly into unopened KDF and producer state, with
   no host-provided agreement or reconstructed scalar/DH/key shortcuts.
7. Finish full-wire accounting, including OpenSSL/BIO paths missed by raw-socket
   counters; report cold setup, consumed work and unused preprocessing separately.

Exit: secure-interface-backed private curve-to-KDF execution, adversarial
rejection, checked state continuity and reproducible cost receipts.

Evidence: [hybrid design](handshake_backend/EmpHybridWork/DESIGN.md),
[word roundtrip](handshake_backend/EmpHybridWork/word-roundtrip-report.json),
[curve build](handshake_backend/EmpHybridWork/curve-build-report.json).
The newer security status takes precedence over positive language in older reports.

## 5. Finish backend-independent cryptographic refinement

1. Resolve the actual `ApplyBlocksCtx` extraction blocker recorded in `dcb73ab`.
   Establish a source-grounded scoped iterator/owner-exit model or correct the
   translator, preserving unchanged computational bodies. Prove owner-update
   coherence and any unobserved-index projection; do not assume the callback's
   cryptographic result or edit generated code to force acceptance.
2. Compose full parallel chunks, tails, captured cipher-owner updates, buffered
   heads/tails and caller mutation. Include zero lengths, block boundaries,
   aliases, counter exhaustion and rejected-state preservation. Specify panic/
   unwind scope and preserve the explicit fixed-array/Drop/forget model boundaries.
3. Join the full caller to secret-length circuit semantics and compiler output:
   inactive capacity bytes cannot affect the meaningful ciphertext or next state.
4. Finish actual pinned HMAC/SHA/HKDF wrapper refinement and compose the chain,
   root, message-key and sealed-sender derivations. Existing numeric/compiler
   proofs and differential vectors do not replace actual-source agreement.
5. Inventory and close remaining send-critical actual-source joins for AES-CBC,
   padding/MAC, hashing, X25519/XEdDSA, prekey validation and PQ KEM wrappers.
   Reuse accepted proofs; distinguish already proved components from their
   missing caller compositions. Full libcrux refinement remains separate from
   its current differential evidence.
6. Promote optimized fixslice AES/key-schedule reuse only with its exact refined
   interface, measured circuit costs and production artifact/compiler binding.

Exit: complete supported call-path statements from pinned Rust/Aeneas semantics
through Lean circuits and compiler, including rejection/state behavior and an
enumerated trusted-library/translation boundary. No new whole-crypto axioms.

Evidence: [CTR work](SignalReference/CtrReferenceV1Work/README.md),
[rejected callback](SignalReference/CtrReferenceV1Work/BlocksCallbackV1Work/README.md).

## 6. Finish parser, HTTP and response-correlation refinement

The inner-group state theorem is complete for initial context 99/depth at most
99. It is not a complete response-source theorem.

1. Complete recursive source event-trace composition, including active/rejected
   event masks, exact source suffixes and all callback/parent continuations.
2. Cover outer groups with context/depth 100 and compose complete inner/outer
   schema scans. Derive cursor, child bounds and recursion invariants from actual
   execution, including malformed input, duplicates, unknown fields, private EOF,
   headers, UTF8 and declared-length overruns.
3. Compose HTTP header/name/value validation and Rust Unicode trim, envelope/type/
   request-ID checks, and private response correlation. Keep the current stricter
   non-2xx global-abort policy explicit; do not claim full per-request
   ChatConnection equivalence for that policy.
4. Join the actual source observation to the production circuit/compiler and
   fragmented transport assembly. Preserve source errors/cursors before applying
   any justified observation projection.
5. Keep unsafe std UTF8, allocation/content models and static-reference error-push
   extraction boundaries explicit; close or consciously retain each as scoped
   trust, rather than treating a foundation-only axiom audit as source completeness.
6. Integrate the already proved compact parser/Mux representation into the
   selected runtime and measure it. The isolated byte-step reduction
   65,825 → 40,529 ANDs (38.4%) and mixed admit/feed compiler proofs are not runtime
   promotion or full Rust-response agreement. Further bounded-counter/whole-buffer
   optimizations need their own equivalence proofs and measured gains.

Exit: source-to-compiled private response handling and correlation over the
supported domain, including adversarial errors and no premature ACK acceptance.

Evidence: [current proof ledger](SignalReference/ChatResponseReferenceWork/PROOF_GAPS_CURRENT.md).

## 7. Complete Signal sessions and service compatibility

Progress 2026-11-10: two chained nonempty established sends run as one Lean
circuit (`TlsMpc/HybridSend.lean`) on candidate v3 at statistical 128 with
private inputs, outputs and retained state, matching an independent reference
([results](handshake_backend/EmpHybridWork/ESTABLISHED_SEND_V3.md)). Signal's
DH ratchet runs on a private X25519 result. The same generic runner executes the
existing steady SPQR send and new-ratchet receive exports and the TLS record
seal/open circuits with private inputs (16 runs pass). Measured cost is about 1.32 million
AND gates and 0.57 GB of traffic per send, which puts the 100,000 sends/hour
target at about 16 GB/s; see that note before planning section 10.

1. Integrate nonempty established sends into the accepted hybrid backend:
   message Content/padding, ratchet/KDF, SPQR, per-device encryption, sealed sender,
   private recipient/device/access-key data and exact request serialization.
   Verify actual Rust recipients decrypt repeated messages using returned state.
2. Finish genuine fresh bootstrap: private bundle parsing and trust lookup,
   both computed signed-prekey checks, joint base/ratchet entropy, all computed
   PQXDH and initial-ratchet DH agreements, exact Kyber1024 encapsulation,
   initial ML-KEM768/SPQR state, first PreKeySignalMessage and subsequent sends.
   Do not substitute supplied agreements, trust-result flags or established-phase
   fixture state. Bind malformed-key/domain/sampling failure policy.
3. Port and execute staged KEM dependencies in the selected backend. Existing
   Kyber and ML-KEM compilation demands and Lean/Rust first/second-message
   comparisons are not native full-bootstrap results. Preserve Kyber versus
   ML-KEM tags and pinned representations.
4. Complete SPQR negotiation beyond the bounded first/two-send profile, incoming
   chunks/epochs and continuing send state. Finish retained/new-DH receive,
   skipped-key/receiver-chain policies and atomic session/store commits. Existing
   small jump/store bounds must remain explicit until full policies are supported.
5. Complete device-list changes, stale-device responses, identity/trust changes,
   prekey consumption, certificate renewal, retries and uncertain-send handling.
   Keep identifiers private through lookup, validation, routing and error paths.
6. Reconcile the relay's older libsignal pin with the implementation reference
   (currently v0.106.1 / `904c8dc8216073b078a5f2f5090e3da8382e6a92`) and the
   actual intended server. Verify current transport/API compatibility and update
   pins/proofs if required. The inspected relay uses WebSocket chat and
   `PUT /v1/messages/{UUID}?story=false`; older H2/gRPC fixtures are not proof of
   this path. Conflicting historical documentation must be corrected.
7. Test service behavior locally against the intended framing/protocol; live
   account/message tests require an explicitly authorized account and recipients.
   No live Signal messages are authorized by this planning document.

Exit: fresh and established private sends, continuing session transitions and
actual recipient interoperability, with explicit supported version/policy bounds.

Evidence: [bootstrap work](signal_backend/BootstrapWork/README.md),
[Signal reference inventory](SignalReference/README.md).

## 8. TLS integration, persistence and runtime lifecycle

The old five-party path has local handshake/application/KeyUpdate and bounded
two-conversation cut/restart evidence. Those results are reusable specifications
and tests, not evidence that the new two-party hybrid application works.

1. Port the full TLS 1.3 handshake, key schedule, record seal/open and post-handshake
   control path to accepted hybrid execution. Retain public server-authentication
   checks and private application bytes. Recheck transcript/Finished binding,
   authentication failure, sequence exhaustion, fragmentation, KeyUpdate, alerts
   and supported/rejected handshake variants against the existing spec scope.
2. Compose TLS with actual WebSocket upgrade/framing/control and private request/
   response handles. Perform repeated nonempty sends in a persistent connection,
   then reconnect/retry and multi-connection isolation tests.
3. Implement checked import/export and re-admission of durable authenticated state
   into fresh EMP/native contexts. Old five-party CCD archives cannot simply be
   relabeled as two-party authenticated shares. Use fresh fixture domains or an
   explicit authenticated migration; support exact-byte existing-key import.
4. Port durable Reserve/Commit, cursor/nonce allocation and immutable outbox
   semantics. Bind completion to account head, boot, cell and generation; test
   actual stale ACK after cell reuse, duplicate/out-of-order ACK, crash between
   phases, unresolved Reserve, uncertain send, replay and rollback rejection.
5. Remove scalability limits without discarding pending state: global latest-send
   ancestry scan (bounded at one million), 64 MiB journal cap, 8,192-byte global
   store, four-active-conversation/64-input profile limits and fixed four-cell
   outbox selection. Index/checkpoint/compact provenance and shard stores so work
   per send does not scan thousands of unchanged conversations. Measure scaling.
6. Replace fixture providers with actual credential/key/storage provisioning and
   authenticated source inventories. Preserve historical account heads and raw
   receipts; the successful sharded fixture advanced to Commit 10, not a reusable
   reset point.
7. Complete secret-memory/serialized-buffer/PRNG/bigint/preprocessing cleanup in
   both selected engines, correlated-randomness renewal, safe cancellation/join
   and durable retirement. Existing patches for older runtimes do not prove EMP
   cleanup. Fatal `_Exit`, a reaped process or an empty process list is not an
   erasure guarantee. Specify storage, swap, dump and backup assumptions.
8. Finish functional composition of transport, ratchet, outbox, admission and
   commit order; bind executable artifacts to the verified compiler/source
   manifests. Keep unverified runtime/security boundaries explicit.

Exit: repeated private service sends, authenticated responses, safe durable
restart and scalable state ownership in the selected backend, with negative
cases and lifecycle assumptions documented and tested.

Progress 2026-11-10 (unreviewed; `secure_hybrid_backend` stays false): step 1's
handshake part runs on the two-party hybrid. `tls_worker_v3.cpp` speaks the
existing `TlsWorkerPipe` RPC; each party runs the unchanged Lean controller
(`handshake_backend/SessionWork/NativeHandshakeFixture.lean`) with its own
worker, the workers agree on every request before acting, and party 0 owns the
socket. X25519 key generation and agreement (native field, masked inversion),
the handshake key schedule on the unopened shared secret, handshake record
opening behind the Lean type gate, server Finished verification, application
key derivation and the sealed client Finished all run inside the engines from
Lean exports (`TlsMpc/HybridKdf.lean`, sizes on demand via `circuit_cache.py`).
OpenSSL accepts the client Finished; both controllers report an authenticated,
retired session ([report](handshake_backend/EmpHybridWork/tls-worker-v3-report.json)).
The application phase runs too (`check_tls_application_v3.py`, unchanged Lean
`NativeApplicationFixture`): private buffers behind public handles, sealing of
private payloads, authenticated receive through the Lean post-handshake parser
(`TlsPostHandshake.openCore`; only the event and request bytes are opened),
client and server-requested KeyUpdate with key rotation in both directions,
rejection of a replayed record and terminal abort. Three payloads that neither
party knows are sent; OpenSSL echoes them and the workers verify the echo
against the sent payload inside the engines
([report](handshake_backend/EmpHybridWork/tls-application-v3-report.json)).
The payload source in that test is a test-only producer, not the Signal path.

Worker operations are now Lean kernels with named fields
(`TlsMpc/HybridKernels.lean`): key/IV positions inside traffic blocks, the
assembly of a send from retained state, next-state selection, control-queue
slots and the open/private marking of every output are defined in Lean. The
emitter writes the field layout beside each circuit, both parties pin circuit
and layout, and the C++ (`kernel.h`, `tls_kernels.h`, `service_kernels.h`)
binds wires by name, sequences kernels and runs the field-engine agreements.
`TlsMpc/HybridKernelsProofs.lean` proves, for every kernel, that the exported
gates compute its Lean definition, and gives functional statements for
KeyUpdate and application receive (including that the opened event bytes of an
application record do not depend on its content). The other kernels have no
functional theorem as wholes yet.

The service path runs on this worker (operations 18–21, unchanged Lean
`ProviderController`; `check_signal_service_v3.py`): authenticated WebSocket
upgrade with private credentials, private parsing of the 101 response, frames,
pings and correlated responses, masked pongs, and four established
sealed-sender text sends with SPQR over two conversations. The local fixture
server's retained libsignal recipient sessions decrypt all four messages and
check body and timestamp
([malicious report](handshake_backend/EmpHybridWork/signal-service-v3-report.json),
[semi-honest report](handshake_backend/EmpHybridWork/signal-service-sh-report.json)).
Measured full-path cost per message round trip is about 14.4 M ANDs and 6,348
field products: ≈ 7.8 GB malicious, ≈ 0.66 GB semi-honest. This supersedes the
session-encryption-only figure in section 7 and the estimate in section 10;
see [SECURITY_MODES.md](handshake_backend/EmpHybridWork/SECURITY_MODES.md).
Sender state enters through the public disposable test fixture, not
authenticated provisioning. Not yet on this worker: the multiplexed operations
(22–28), outbox/durable state, bootstrap/PQXDH, receive-side Signal sessions,
HelloRetryRequest and fragmentation negative cases, erasure (retire/abort only
drop handles), remote deployment identity. Request forwarding of received
records from the socket owner to the other party treats the socket owner as the
network, which TLS already assumes hostile.

Evidence: [integrated restore receipt](signal_backend/RecoveryWork/ShardedAccountWork/integrated-report.json),
[account work](signal_backend/RecoveryWork/ShardedAccountWork/README.md),
[TLS security notes](handshake_backend/SECURITY.txt).

## 9. Share refresh and mobile compromise — paused dependency

Do not restart the refresh agent as part of this plan. When resumed:

1. Reconcile the five-party/two-exposures-per-epoch storage prototype with the
   selected two-party computation. State which machines may be compromised
   across adjacent epochs, including storage-to-compute transfers, and what
   recovery/erasure prevents historical views from combining. Static 2PC security
   does not establish mobile security if both compute hosts are exposed over time.
2. Resolve scalable refresh without repeating one identical zero mask across all
   records. The existing `MaskReuse.lean`/multi-epoch regression rejects that
   construction. Evaluate the already documented independent per-record mask
   expansion and proactively shared wrapping-key alternatives, including their
   seed-compromise and old-ciphertext retention consequences. Constant-size seed
   setup is not constant total database update work or independent mask reuse.
3. Implement authenticated inventory and valid-source checks, exact domains and
   alternate-cache consistency, coordinated quiescence, prepared/commit/cleanup
   epochs, rollback-resistant recovery and checked repair of recovered parties.
4. Renew compromised channels, authentication/MAC contexts, OT/PRSS seeds,
   preprocessing and entropy; retire old shares and all correlated copies.
   Preserve required TLS/Signal keys while refreshing their sharing, without
   resetting protocol counters or reusing consumed randomness.
5. Complete the nonmechanized composition argument, actual network/adversarial/
   crash tests and refresh-cadence cost measurements. Determine whether internal
   participant checks suffice for the old zero-sharing ZKP role; public
   verifiability requires a separate hiding proof/commitment construction.

Exit: specified and supported mobile-adversary protection for the entire
application, not just algebraic preservation of each secret during refresh.

Evidence: [refresh security and obligations](refresh/SECURITY.txt),
[refresh alternatives](refresh/PRZS.txt).

## 10. Throughput and optimization plan

No existing result establishes 100,000 full logical sends/hour. EMP comparison
timings excluded curves, TLS, parser and nonempty full application work, and the
examined rewrite now fails the security acceptance gate. Older five-party cost
models do not transfer directly to authenticated garbling.

1. After backend acceptance, establish a full nonempty repeated-send baseline:
   persistent TLS, retained state, actual recipient decryptions, response parsing,
   durable commits and live preprocessing. Attribute CPU, bytes, memory, setup,
   preprocessing, conversion and persistence per stage.
2. Apply proved circuit savings: compact parser integration, AES schedule reuse,
   SHA/HMAC adder/gate improvements, private-length/buffer/base64 reductions and
   safe message-independent precomputation. Evaluate native GHASH only with its
   own justified domain conversion and measured total benefit; Fp25519 is not
   the GCM binary field.
3. Cache immutable programs and batch independent conversations. Pipeline work
   only with durable reservations and serial ratchet consistency; never reuse
   triples, masks, message keys or uncertain entropy. Measure preprocessing
   generation rate against consumption and its storage/lifetime limits.
4. Sweep batch size, workers, conversation distribution, payloads/device fanout,
   new-session mix and realistic RTT/bandwidth. Separate latency from throughput;
   use the accepted engine's actual communication schedule, not one round per
   Boolean AND level by assumption.
5. Compare one persistent TLS connection with multiple connections only after
   stage attribution. Isolate per-connection keys/nonces/sequence and response
   routing, then verify service support and rate limits. Parallel sockets cannot
   remove a producer, conversion, bandwidth or account-persistence bottleneck.
6. Run a sustained representative hour, including setup amortization, refill,
   device fanout, occasional bootstrap/reconnect/KeyUpdate and durable outcomes.
   Report accepted logical sends separately from recipient decryptions and
   delivery claims, plus full wire bytes and actual WAN conditions. If the target
   is missed, provide measured bottlenecks and resource estimates, not a
   microbenchmark extrapolation presented as achieved throughput.

Decision 2026-11-10: reduced throughput is accepted in the malicious setting;
malicious/statistical-128 remains the default. A semi-honest mode is kept as an
explicit build-time alternative (`-DEMP_HYBRID_SEMI_HONEST=1`: half-gates
garbling and MAC-free field shares behind the same two engine interfaces) so
both can be costed on identical circuits. Measured side by side in
[SECURITY_MODES.md](handshake_backend/EmpHybridWork/SECURITY_MODES.md): one
established send is ≈ 0.57 GB malicious vs ≈ 42 MB semi-honest; a full TLS
handshake ≈ 4.2 GB / 10 s vs ≈ 0.38 GB / 3.4 s. The 100k/hour target is out of
reach in malicious mode with current constructions (≈ 136 Gbit/s) and at the
edge of a 10 Gbit/s link in semi-honest mode. These are per-stage loopback
measurements and arithmetic, not the sustained run step 6 requires.

Evidence: [historical throughput review](throughput-research/signal-mpc-throughput-review.md),
[benchmark comparison](benchmarks/TwoPartyComparisonWork/README.md).

## 11. Dependency order and completion gates

1. **Security foundation:** section 3, then secure bridge/native-curve acceptance
   in section 4. Core crypto/parser proofs in sections 5–6 are independent and
   can proceed when implementation work is separately resumed.
2. **Established application:** hybrid established sends + TLS/private responses
   + durable state, with actual recipients and adversarial controls.
3. **Complete functional scope:** fresh bootstrap, continuing SPQR/session
   transitions, recovery, service compatibility and scalable storage. Proof
   closure proceeds alongside implementation; component vectors are insufficient.
4. **Performance:** begin attribution once a secure established path exists;
   finish sustained mixed-workload evidence after full integration.
5. **Mobile protection:** separately resume section 9 and compose its guarantees
   with the completed runtime before claiming the original proactive-security goal.

Final release gates: no known confidentiality/integrity blocker; exact supported
TLS/Signal scope and version; complete requested functional/compiler/source
proofs with explicit trust boundaries; full positive/negative interoperability
and restart tests; appropriate lifecycle and mobile-security argument; reproducible
sustained throughput evidence or an explicit unmet-target report. Do not mark
the overall objective complete merely because an agent finishes its checkpoint.

Before final acceptance, reconcile stale requirements and documentation:
`benchmarks/config/requirements.json` still records the old five-party compute
profile, historical notes still mention denied sockets or obsolete transports,
and several README files mix earlier open gaps with later completed milestones.
Update these without rewriting historical receipts. Preserve dirty/untracked
work; commit reviewed owned artifacts with the shared index lock and exact paths.
