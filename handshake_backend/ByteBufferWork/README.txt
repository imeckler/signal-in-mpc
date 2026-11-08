Serialized-buffer lifetime cleanup candidate

Reproduce from the repository root:
  python3 scripts/prepare_tls_byte_buffer_runtime.py
  python3 scripts/check_tls_byte_buffers.py --build

Preparation refuses an existing destination. It verifies the pinned archive,
extracts fresh source into .deps/tls-byte-buffer-runtime/MP-SPDZ, and applies the
archived ScratchWork and LifetimeWork patches without rewriting frozen files.
Only dependency headers/libraries are shared with the canonical backend. All
candidate objects and libSPDZ are rebuilt; fixed-field destruction changes ABI.
Never mix baseline and candidate objects. Canonical sources/library are untouched.

The additional patch wipes the entire owned capacity with sodium_memzero before
release in octetStream and FlexBuffer. Growth and replacement allocate first, so
allocation failure retains the previous owner, content and metadata. Copy/self
assignment preserve cursor and bit state. Reused octetStream assignment clears
the old capacity before copying the new prefix. Destruction also wipes its inline
bit buffers. Clear resets bit state; ordinary read/write-head resets retain their
logical semantics and borrowed consume results are not wiped.

Shrinking octetStream clamps length and read cursor to the retained prefix and
resets partial-bit metadata when content is truncated. This supports Hash::final,
which shrinks its destination before resetting it. FlexBuffer growth preserves
live length/cursor; its resize_copy rejects a size below the live prefix.
Ownership transfer resets the source and preserves the destination's live bytes
and byte cursor. It does not erase the transferred allocation. Transfers retain
the upstream byte-aligned contract; FlexBuffer has no partial-bit representation.
Exchanger refreshes its send pointer after potentially reallocating its in-place
receive stream. Append capacity checks also avoid null-pointer arithmetic found
by UBSan when appending to a fresh stream.

Checks use only public synthetic bytes. A global new[]/delete[] test replacement
injects allocation failures and observes selected owned capacities immediately
before free, without reading freed storage or disabling sanitizer checks. On
macOS a dylib uses two-level symbol binding, so the buffer harness compiles the
exact candidate Tools/octetStream.cpp into the sanitized test executable. The
rest of the completely rebuilt candidate library is optimized normally. Frozen
field-lifetime and hidden-stack harnesses plus five-party X25519/router reuse
checks run against that candidate library. The socket-pair regression prevents
the peer draining the outgoing stream until a larger incoming length has forced
reallocation, guaranteeing remaining partial sends after growth.

Results: benchmarks/results/tls-byte-buffer-checks.json and its recorded raw logs.
An initial failed attempt is retained in raw/tls-byte-buffer/2366cf9a9cc20a1f and
.deps/tls-byte-buffer-initial-failed. It exposed fresh-stream pointer arithmetic
and the macOS observer-binding limitation, addressed without disabling ASan/UBSan.

Limits: this is allocation-lifetime cleanup and selected regression evidence,
not full live-buffer erasure or a proof about every allocation/copy. Logical
reset, same-allocation receive replacement, Hash/check_sum temporary copies,
bigints, live Beaver/input/opening/preprocessing buffers, PRNG/correlated state,
failure epochs, OS/persistence assumptions and private application integration
remain separate work. Application readiness/retirement gates remain closed;
sharing refresh stays paused. No end-to-end throughput claim is established.
