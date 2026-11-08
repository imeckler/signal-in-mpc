Owned worker stacks, GMP allocations and BitVector cleanup checkpoint

  python3 scripts/prepare_tls_lifecycle_runtime.py
  python3 scripts/check_tls_lifecycle.py --build

Fresh isolated .deps/tls-lifecycle-runtime/MP-SPDZ source layers frozen scratch,
field, byte-buffer and epoch patches. It never changes the canonical backend.
Online workers get owned mmap stacks with guard pages; after pthread_join their
entire usable mappings are wiped before munmap. Per-thread shutdown also destroys
thread-local bigint/GMP random state. SecureGmp installs wipe-before-free and
allocate-copy-wipe-free reallocation callbacks before any allocated GMP object
and before worker threads. Callback failure is fatal, as required by GMP; no
exception recovery is invented. BitVector growth/destruction wipes full owned
capacity, including bytes beyond a shortened logical length.

GNU GMP requires installation before live allocated GMP objects and disallows
allocator exception/null recovery: https://gmplib.org/manual/Custom-Allocation
The tested executable installs first in main, before options/field/thread setup;
linked fixed-field static objects use allocation-free default mpz initialization.
SecureGmp is not an API for retrofit into an arbitrary running process.

Evidence: benchmarks/results/tls-lifecycle-checks.json, raw run ce411d38dab27407.
- Sanitized local observer verifies 12 GMP allocations zero immediately before
  underlying free, including grow/shrink and GMP random-state destruction.
- A real pthread runs on an owned stack, joins, and its full usable allocation
  is observed zero before unmap. Guard pages are outside the wiped span.
- 14 byte/BitVector releases zero; PRNG and exception/zero-size checks pass.
- All five parties pass renewal/X25519/router reuse at capacities6/1029/16385.
  Every tested worker renewal observes stack wiping and GMP release counters.

This does NOT enable application readiness or establish full retirement. Remaining
closure: top-level Player/SSL transport keys and transcript state, network thread
stacks, actual host-call stack lifetime, machine-global non-profile state guards,
normal-versus-failure destruction and integration with Session retire/rotate/abort.
In particular, retaining an encrypted channel's key would let a later compromise
decrypt captured older MPC traffic. Renewing only protocol generators is insufficient.
No OS/kernel/persistence/compiler-copy erasure claim. Sharing refresh stays paused.
