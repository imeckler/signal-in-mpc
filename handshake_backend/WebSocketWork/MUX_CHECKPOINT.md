Candidate checkpoint: four-slot private response correlation

The Lean model and fresh AIG regressions are recorded in
benchmarks/results/tls-chat-mux-checks.json (commit73271c4). The new
prepare_mux.py compiled separate immutable mux-byte, mux-admit, joint-VM-RNG
request-ID initialization, and request-ID advancement closures. Existing
single-response closures were preserved.

NativeChatMux has been compiled/linked with actual OwnedBits, including its
admission, byte-step and completion-drain template boundaries. It opens validity
before bounded completion slot metadata. Request IDs and response contents stay
shared. The circuit consumes matching IDs before host drain; the host clears
only authenticated completed slots and queue entries. Native execution and
multi-provider/controller integration remain pending; compilation is not a
five-party correctness claim.

NativeConversation separates admitted per-conversation state from one connection
upgrade. Activation is an internal authenticated-connection event. Same-account
association/authenticated bootstrap remains an embedding responsibility. Each
conversation allows one pending response and closes without state rollback on
failure. Connection-global ID allocation commits advancement before production.

Deferred NativeTextInput evaluates the real text48/bucket80 builder only after
collective factory/fence readiness, preserving its computed validity and exact
payload/timestamp. It does not construct plaintext or fixture credentials.

PublicMetrics is optional and dormant in existing launch profiles. It reports
public protocol payload counters, summed communication operations (not network
critical-path rounds), stage wall time and pinned verification/Machine.run time.
Compiler-declared preprocessing is distinguished from actual usage; the frozen
runtime has no actual-usage getter, so availability is explicitly false. Epoch
snapshots exclude retirement-tail traffic; epoch wall times include cleanup.
No cache or runtime loader behavior has changed. The next necessary nonempty
text/mux integration run must establish native correctness and measured costs.

Follow-on bounded-registry candidate

PrivateMuxRegistry owns up to four admitted conversations and 64 one-use inputs
bound to their owning conversation. It reserves a global ID before production,
allows one pending request per conversation, and authenticates combined
credential/state/input/producer validity through mux admission before retaining
application output. Completions use internal authenticated slot events and
release the corresponding conversation only after the coordinator barrier.
Nine ASAN/UBSAN host-mock profiles pass (tls-private-mux-registry.json), including
four outstanding slots, reordered responses, reuse, misuse and failure burning.
NativeWebSocketMux and Session's separate mux methods compile/link with actual
OwnedBits; partial parser/correlation/control state is discarded on peer close,
leaving only the already encoded close reply. These methods are not exposed by
the existing launch profile or RPC dispatcher yet. No new native run is claimed.

Normal explicit mux launch profile (candidate, native execution pending)

New opcodes22–25 are catalogue/upgrade/produce/process. The dedicated default
worker links NoMuxProvider and admits nothing. A separate fixture binary links
two distinct TextMuxFixtureFactory states and four deferred nonempty inputs.
Legacy lifecycle_worker_main rejects all mux opcodes; NativeDispatch also rejects
them unless a launch profile deliberately implements the private extension.
The connection has one credential upgrade, a public nonce, and a collective
agreement on the public provider/input profile inventory before private VM work.
Request-ID reservations are generated inside the VM and remain shared.

MuxProviderController pipelines separate conversations, supports authenticated
out-of-order completions, sends controls, performs KeyUpdate and aborts after all
inputs complete. Receipt owners are opaque conversation handles, mapped only in
a new erased host call after the receive cleanup barrier. No correlation ID,
private length, response body or header is opened. The driver records external
TLS wire bytes at the bridge, separate from runtime protocol payload counters.

Validation: both default and text-fixture workers compile/link; Lean controller
checks;1481 ASAN/UBSAN framing/bounds/replay checks;25-op Lean/C++ pipe,32-exchange
concurrent pipe and duplex pipe checks;26 application-contract rejections pass.
No five-party mux/text/lifecycle or throughput pass is asserted by these checks.
