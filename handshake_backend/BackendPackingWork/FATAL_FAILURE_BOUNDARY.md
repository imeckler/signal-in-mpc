Worker-exception retirement boundary (source observation, no fault run yet)

Pinned Processor/Online-Thread.hpp438–455 catches a worker exception and calls
exit(1); throw_exceptions instead lets the exception escape the pthread entry.
A live-prep Main_Func_With_Purge calls Sub_Main_Func directly. Consequently,
normal host-controlled joins, guarded stack release and object destruction are
not reached by that path. Positive epochs and explicit TLS status-rejection/
abort tests do not establish cleanup after an MPC share/MAC exception. Process
exit is neither an owned-memory wipe receipt nor erasure of OS copies.

No existing runtime is changed here. Before a new backend can acknowledge this
failure path, add a separate candidate path that catches into an owned worker
failure record, wakes the waiting host, sends only a fixed public failure
category through a cancellation mechanism, and interrupts/reaps affected peers
and local workers. On failure, skip output publication; destroy/wipe local
processor, preprocessing, PRNG, serialized buffers, helper stacks and correlated
state through a failure-aware teardown. It must not retry checks on invalid
protocol state or wait indefinitely on an unresponsive peer. Test faulted shares,
MAC/correlation failure and partial network/job failures with bounded direct-child
cleanup and source-bound wipe evidence. No successful retirement receipt may
precede that cleanup. No failed cryptographic message contents should be logged.

BMR has separate GC/garbling owner and worker structures; generic Machine cleanup
cannot simply be assumed to cover it. Tiny/Tinier's128-bit sacrifice rejection
remains a separate prerequisite, not fixed by better cleanup.
