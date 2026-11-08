Partial VM scratch cleanup candidate, 2026-11-08

The canonical backend and production Session retirement gates are unchanged.
This work removes a concrete class of retained VM copies, not all historical
secret state. It does not establish mobile-adversary security or full erasure.

Reproduce from the retained pinned MP-SPDZ source archive:
  python3 scripts/prepare_tls_scratch_runtime.py
  python3 scripts/check_tls_vm_scratch.py --build

The preparation command refuses an existing destination. The test build uses
the separate .deps/tls-scratch-runtime/MP-SPDZ source tree and rebuilds its own
libSPDZ.so. On macOS the library ID is set to @rpath/libSPDZ.so before linking.
CONFIG.mine and read-only dependency headers/libraries come from the baseline;
no canonical source, shared library, program cache, or live state is rewritten.
The three source edits are archived in vm-scratch.patch with before/after hashes
checked against the source archive pinned in benchmarks/config/dependencies.json.

Hooks and lifetime boundary:
- StackedVector::visit_full_storage visits every constructed backing object,
  including popped frames and the suffix hidden by logical resize. It preserves
  the view and stack bookkeeping. It cannot reach freed or unconstructed storage.
- Machine::visit_secret_scratch visits primary arithmetic memory, binary memory,
  primary secret registers, binary secret registers, and temp.Sansp in every
  initialized processor. The TLS profile uses NoShare for the secondary
  arithmetic domain; this is not a cleanup implementation for that domain.
- The host must exclusively own all Machine calls. Before invoking any visitor,
  the hook rejects worker-thread invocation, missing/terminated processors,
  active tapes, and queued jobs whose result has not been collected. These are
  checks under the serial host-owner contract, not a general concurrent API.
- Export execution completes and checks the protocol before copying outputs
  into externally owned shares. Worker's optional callback then runs before the
  call returns. Only the isolated fixture installs this callback currently.
  The normal worker has no callback and acquires no new erasure capability.
- VmScratch.h uses sodium_memzero on the fixed-width primary field limbs and
  every constructed CCD GF(2^128) part. It preserves object representation,
  vector dimensions, retained external scalar/traffic state, and output shares.
  Callback failure propagates; no success or retirement receipt is synthesized.

Evidence in benchmarks/results/tls-vm-scratch-checks.json:
- ASan/UBSan test translation unit checks 18,720 real field cells at packed
  widths 1..64 through two hidden stack frames, shrink, pop, and subsequent
  reuse. The independently copied public test input stays intact. The linked
  runtime library is a normal optimized build, not a fully sanitized build.
- Five actual Shamir/CCD parties (t=2, GF(2^128), security parameter 128) run
  three public synthetic router calls at each capacity 6, 1029, and 16385.
  Automatic callback cleanup is followed by zero checks over the same storage.
  Actual output shares survive and are reused on the next call; authentication
  rejection still works. Only deliberately public fixture outputs are opened.
- The capacity-6 case also runs actual tls_begin and tls_agreement with public
  peer coordinate 9. After cleanup, base-point agreement equals the previously
  opened public key, checking retained scalar survival across field and bit VMs.
- Uninitialized and outstanding-check-job invocations reject before visiting
  any storage. Peer logs, sources, library, executables and manifest are hashed.
- This fixture pins its program closure locally. It does not test collective
  program agreement, certificates, a TLS application session, or WAN throughput.

Still required before an operational erasure acknowledgement:
- Overwrite secret values before vector shrink, replacement, reallocation and
  destruction throughout the runtime, including inner CCD register allocations.
- Handle Beaver multiplicands/results/triples, input and opening buffers, and
  all preprocessing/daBit copies, including already-consumed buffers. The current
  hook deliberately leaves them intact; clearing just the final buffers misses
  earlier allocations and copies.
- Retire/renew local and correlated randomness with protocol agreement. The
  pinned AES-CTR PRNG still retains seeds that reproduce earlier outputs.
- Audit clear/masked temporaries, bigint allocations, nested preprocessing
  processors, network buffers, thread stacks and OS/persistence assumptions.
- Cover failures and epoch transitions, preserve only declared active shares,
  and establish quiescence/cleanup before enabling Session retire or rotation.

The sharing_refresh agent remains paused. This patch changes no refresh scheme.
