# Caught-failure candidate foundation

SocketCancellation.h is an isolated cancellation primitive, not a runtime patch.
The ASAN/UBSAN socket_cancellation_checks.cpp test passes duplicate ownership,
move ownership, terminal reattachment rejection, idempotent cancellation, and
32 concurrent blocked readers followed by join/unregister. It does not establish
MPC exception cleanup, retirement, bootstrap cleanup, or crash/OS erasure.

The runtime integration remains blocked on replacing worker exit/rethrow paths
with owned exception propagation, waking failed queues, cancelling transport I/O,
joining workers and wiping owned stacks/state before reporting cleanup. See
../BackendPackingWork/FATAL_FAILURE_BOUNDARY.md. No runtime capability is enabled.

Reproduce:

```
clang++ -std=c++17 -pthread -fsanitize=address,undefined -g \
  handshake_backend/ExceptionWork/socket_cancellation_checks.cpp \
  -o /tmp/tls-socket-cancellation-checks
/tmp/tls-socket-cancellation-checks
```

`prepare_queue_candidate.py` creates an exact-source isolated WaitQueue candidate
from diagnostic v4. It changes wait predicates to loops, broadcasts terminal stop,
rejects pushes after stop, and reads the terminal result under the mutex. The
ASAN/UBSAN queue test covers normal delivery, suppression of queued results after
stop, 32 joined blocked consumers, and empty-queue signals. These changes do not
connect ThreadQueue/Machine failure propagation yet. Existing runtime sources
are unchanged. Run the preparation script then compile the test with
`-I.deps/tls-caught-failure-queue` and the same sanitizer flags above.

## Isolated runtime checkpoint

`prepare_runtime.py` creates `.deps/tls-caught-failure-runtime/MP-SPDZ` from
immutable diagnostic-v4 source/config identity. `--verify` regenerates the
source overlay in temporary storage and checks exact equality with the candidate.
It never changes the frozen functional runtime. Build `libSPDZ.so`, then use
`fixture.mk` for the small executable. `check_native.py` runs the bounded local
five-party series and preserves source/product snapshots and original failures.

The current checkpoint passes all five parties for repeated positive execution,
a deliberately inconsistent private polynomial evaluation (actual `mac_fail`),
a one-party worker exception, and a one-party teardown exception. Only positive
synthetic comparison flags open. On failure the test checks terminal execution
rejection, false lifecycle retirement acknowledgment, cleared owned inputs,
zero remaining registered TLS sockets, and at least seventeen wiped owned
stacks. The queued result is not delivered after cancellation. The caught path
returns through C++ owners rather than `exit`, including instruction wrappers.

The candidate owns per-worker Player/MC/Processor via RAII; failure cancels
registered TLS I/O before owners unwind. TLS stream construction owns the fd
before registration; a partial CryptoPlayer construction closes transferred
and remaining raw fds and destroys helper owners. Sender/receiver owners are
destroyed before their TLS streams. Processor destruction suppresses fresh
protocol checks during terminal unwind. The host joins VM workers, wipes stacks
and VM memory, deletes its transport, and refuses retirement. Normal retirement
adds a collective completion exchange AFTER local checks/joins/wipes, so a peer
teardown failure cannot be mistaken for completion.

macOS SO_NOSIGPIPE is required by this candidate; unsupported platforms reject
explicitly rather than changing the embedding process's signal policy. The
first two raw runs exposed instruction-level `exit(1)` and peer SIGPIPE,
respectively. Their failed evidence remains alongside the successful run.

Supported test scope is exactly one VM worker, five encrypted parties, live CCD128
preprocessing, post-bootstrap controlled protocol failures, and quiescent host
ownership. No application capability/default is enabled. Bootstrap/server-thread
failures, partial Processor-constructor ownership, OS-level join failures,
SIGKILL/crash/suspend and OS copies are not certified. Communication helper
joins still require explicit return-code accounting before promotion; the
checkpoint's controlled cases use successful valid pthread joins. OT/Tinier
owners and their destructor checks are outside this CCD candidate. Caller-owned
private inputs/handles must be closed/wiped by the embedding session on failure;
Machine does not own those buffers and cannot erase independent copies.
