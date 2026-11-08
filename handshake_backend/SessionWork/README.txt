Native Session lifecycle integration candidate

Preparation: python3 scripts/prepare_tls_session_runtime.py
Build: make libSPDZ.so in its fresh .deps/tls-session-runtime/MP-SPDZ tree,
then use this directory's Makefile for tls-worker and tls-session-host-checks.
The candidate-only worker uses actual NativeLifecycle; the canonical worker_main
supplies no capability and retains its closed application gate.

Session clears owned scalar/handshake/main-secret copies before runtime epoch
renewal. Traffic rotation installs the newly derived host shares, wipes the old
owned values, then renews runtime/prep/protocol/transports. App/producer/handle
shares survive as OwnedBits. Abort wipes owned state and terminally discards the
runtime/host transport without starting another epoch. A missing/failed capability
never acknowledges erasure. Unsupported profile/global state rejects.

Bootstrap, every RPC and destruction run exclusively on owned erased host stacks.
A monotonic host-call completion barrier publishes only after pthread_join, TLS
cleanup, thread-local destruction and full stack wipe. Session requires an active
erased host call and denies app work until the retirement/rotation generation has
completed; retirement cannot enable application work inside the same host call.
Private Signal evaluation is exposed only as a typed same-worker shared-Bits hook,
using the pinned SendShape/Worker::signal interface; no RPC imports plaintext.

Evidence: sanitized tls-session-host-checks passes success/failure/nesting and
checks that completion is false inside the job, true after the erase barrier.
benchmarks/results/tls-native-session-lifecycle.json records the actual Lean
controllers/OpenSSL server run: all five verify certificates and server Finished,
send client Finished, retire successfully and accept the session; 114.709seconds.
This first integration run does not yet test repeated application records,
KeyUpdate or private producer handoff; those are the next milestone.

The runtime cleanup guarantee is scoped to owned process storage and this pinned
profile. Trusts OpenSSL internal secret cleanup, compiled code and host OS/memory
assumptions; no OS/kernel/persistence/compiler-copy erasure proof is claimed.
Exceptional allocation/startup or failed protocol checks can terminate without a
cleanup receipt. No process-exit erasure claim. Sharing refresh remains paused.

Persistent application checkpoint (subsequent to the handshake-only run):
  python3 scripts/check_worker_boundary.py
  python3 scripts/check_native_application_lifecycle.py --build

Final native report: benchmarks/results/tls-native-application-lifecycle.json,
raw/native-application-lifecycle/f6ff406ae42c4004; all five controllers exit0,
381.041seconds,39 source/product hashes stable,11 raw log hashes, no cleanup
errors. Real OpenSSL accepts three unopened producer payloads. Client KU,
server-requested KU and automatic response work across protocol/transport renewal.
Replaying the third echo causes GCM rejection; repeated abort receipts succeed,
and subsequent private sends remain terminal. Canonical library hash is unchanged.

Only the macro-built tls-private-application-worker initializes the disposable
PublicSyntheticProducer: actual shared Signal state advances and fixed228-byte
synthetic HTTP2/gRPC frames. No frame or client key is opened by the client.
This is NOT the relay's actual service protocol: it uses HTTP1.1 WebSocket and
sealed-sender JSON. The ordinary candidate worker has no synthetic initializer.

Two integration defects were fixed, without weakening lifecycle checks:
- Old canonical public compiler only accepted integer handshake sizes. Provision
  the application-capable helper and real missing traffic-update kernel before
  private startup; all application shapes are checked and boot-pinned.
- Lean pipe treated every rejection as broken framing. Complete bounded worker
  rejection now permits only terminal abort receipts. Malformed/truncated/I/O
  responses permit no cleanup exchange; private work remains blocked. The native
  worker stays available only for these receipts after a terminal operation error.
The worker-boundary suite tests both permitted and forbidden terminal paths.

Earlier failed raw runs are retained:92fbd492ee158460 (cleanup group-signal
sandbox issue),a46fb89448af58c2 (stale compiler),e5a5b64044770a4f (pipe cleanup).
The harness now records direct-child cleanup fallbacks/errors and reaps handles.

No per-message Signal runtime-retirement claim: kernel traces currently retire
at TLS lifecycle boundaries. Next is transport-agnostic private chunk consumption
and explicit private-computation checkpoint for the actual WS/service producer.
