Fixed-field lifetime cleanup candidate, 2026-11-08

This isolated backend change wipes fixed-width field payloads when their C++
objects are destroyed. It builds on ScratchWork's explicit VM scratch cleanup.
Production Session retirement/application activation remains disabled.

Reproduce with the retained pinned archive and existing baseline dependencies:
  python3 scripts/prepare_tls_lifetime_runtime.py
  python3 scripts/check_tls_vm_scratch.py --build --lifetime

The first command refuses an existing destination. It creates a fresh source
tree at .deps/tls-lifetime-runtime/MP-SPDZ, applies the existing scratch patch,
then adds two small field-class changes. The canonical backend stays unchanged.
Every object and the shared library must be rebuilt: adding a nontrivial
destructor changes C++ ABI calling conventions even though payload size and
serialized field format are unchanged. Do not mix candidate and baseline C++
objects/libraries. The harness also builds a separate baseline negative control.

Patch scope:
- gf2n_::~gf2n_ uses sodium_memzero on its entire fixed-width field value.
- modp_::~modp_ wipes all fixed-width limbs, including unused high limbs.
- Explicit default copy construction/assignment preserve the previous value
  semantics. Arithmetic algorithms, randomness, field widths and security
  parameters are unchanged. The patch preserves the original file line endings.
- Ordinary std::vector pop/shrink/erase/clear/reallocation/destruction now invoke
  these payload destructors, including through the arithmetic and CCD share
  inheritance chains. Nested CCD register vectors use the same field payloads.
  Completed member construction also gets cleanup during exception unwinding.
- This covers destroyed field objects in consumed preprocessing buffers and
  Beaver vectors. It does NOT erase still-live protocol buffers, raw serialized
  byte copies, bigint limbs, PRNG state, or objects whose lifetime never ends.
  Logical-prefix containers, mapped storage, and compiler/OS copies need separate
  handling. The tested profile uses ordinary memory, not DiskVector/mmap storage.

Evidence in benchmarks/results/tls-field-lifetime-checks.json:
- The same ASan/UBSan test translation unit runs against baseline and candidate
  libraries. A custom allocator inspects field payload bytes in deallocate,
  before freeing the allocation. It never dereferences destroyed objects or
  reads freed storage. Offsets are measured from live objects. Unused allocation
  slots start with public zeros; all constructed test payloads are public 0xa5.
- Each vector mutation ends its scope immediately, leaving discarded payload
  slots untouched until inspection. Cases cover growth, pop, shrink, short copy
  assignment, clear, move replacement, shrink_to_fit, and forty copy-constructor
  exceptions after field-member construction. Surviving independent copies retain
  their expected values. The five tested types are modp_<4>, Fp25519, the native
  arithmetic share, GF(2^128), and the native CCD part share.
- Baseline: 975 inspected payload slots, 555 still nonzero. Candidate: the same
  975 slots, all zero. Each profile checks 90 allocation releases and 40 injected
  failures. Sanitizers cover the test translation unit; the library is optimized
  normally. This is evidence about the tested object lifetimes, not all memory.
- All five parties pass automatic scratch cleanup at router capacities 6, 1029
  and 16385, with real output-share reuse and authentication rejection. Capacity
  6 also checks X25519 retained-scalar reuse after cleanup. The existing hidden
  stack test still passes 18,720 field cells across packed widths 1..64.
- Native timings are local component checks, not controlled performance
  comparisons or evidence for the 100,000 Signal messages/hour target.

Development checks exposed a test-inspector issue: reading discarded capacity
directly triggers libc++'s ASan container poisoning even before the allocation
is freed. The final test instead inspects from allocator deallocate, after the
container removes its annotations and before free. No sanitizer checks were
disabled and no use-after-free inspection is used. The initial failed log is
retained under benchmarks/results/raw/tls-field-lifetime.

Still required: wipe live Beaver/input/opening/preprocessing state, raw-byte
buffers and dynamic bigint copies; retire local and correlated PRNG state;
cover failures, logical-prefix containers and epoch transitions under explicit
OS/persistence assumptions. No full erasure, mobile-security, TLS application
activation, or production backend migration is established by this checkpoint.
Sharing refresh remains paused.
