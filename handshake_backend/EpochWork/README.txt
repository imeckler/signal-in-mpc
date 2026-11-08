Quiescent worker epoch renewal candidate

Reproduce:
  python3 scripts/prepare_tls_epoch_runtime.py
  python3 scripts/check_tls_epoch.py --build

The source-only candidate layers archived ScratchWork, LifetimeWork and
ByteBufferWork patches without changing them or the canonical backend. All
candidate objects originate from its fresh isolated tree. retire_worker_epoch
rejects non-host, uninitialized, outstanding-job, disk-memory and file-prep use
before mutation. It joins and destroys per-thread Processor/preprocessing/
protocol/MC/Player ownership trees, clears VM memory and tinfo, and advances a
monotonic namespace. The next run collectively creates fresh correlated/local
PRNG owners and fresh epoch-qualified network connections. Host-owned native
shares and fixed arithmetic/binary domains remain unchanged.

PRNG destruction explicitly erases seed, state, random cache and both AES key
schedules. Reseeding resets prior bit/byte caches. Explicit invalidation makes
future nonempty generation reject until seeded again. Temporary global/derived
seeds and non-AES hash input use scope guards. The bigint random-import temporary
is wiped before successful release; exception-safe heap/limb history still needs
the allocator checkpoint. Hash state is wiped before reset and free.

Exchanger destruction publishes a received length only after complete exchange;
allocation/read failures reset the receive logical heads rather than constructing
out-of-range pointers or publishing partial data. Null-storage transfer setters
avoid null-pointer arithmetic. Local sanitizer tests include allocation-failure
exchange unwinding, zero-size transfer, PRNG reseed/copy/invalidation, and direct
inspection of secret PRNG array ranges in still-allocated public test storage.

Initial epoch renewal failed closed at all five parties because upstream thread
connection IDs are single-use. The candidate now appends worker_epoch to each
thread connection namespace; it never silently reuses old channels or streams.

This is NOT a full retirement receipt. Default pthread stack caching, dynamic
GMP limb history, BitVector raw capacity, failure-path ownership/cleanup and
host/machine-global secret-bearing state remain under explicit review. A failed
thread protocol check can terminate the worker process before successful epoch
completion; no cleanup acknowledgment is issued. No application readiness or
retirement gates are enabled. Sharing refresh stays paused.
