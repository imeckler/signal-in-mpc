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
