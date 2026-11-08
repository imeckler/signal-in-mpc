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
