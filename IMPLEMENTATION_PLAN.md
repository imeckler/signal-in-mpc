# Implementation handoff — Sol workers

User direction, 2026-11-07: reduce token consumption and delegate actual
implementation to Sol. This supersedes the earlier Astra-high preference.
The automatic root goal was paused; the subsequent user instruction explicitly
authorizes delegated implementation. Astra workers have been interrupted.
Sharing refresh remains paused.

## Operating rules

- Use Sol for implementation; do not spawn more workers or use Astra.
- Work in bounded checkpoints: implement one meaningful change, run its relevant
  checks once, report evidence and remaining limitations, then stop for review.
- Read this file and relevant current files. Avoid replaying the entire history,
  repeated full audits, giant logs, or unrelated refactors.
- Preserve frozen proof checkpoints. Add new work in separate directories.
- Keep secrets shared. Do not enable application readiness or acknowledge
  retirement without the required cleanup. Backend execution is unverified;
  circuit/compiler correctness and runtime security are distinct claims.
- Each worker owns its assigned files. Do not stage or commit other workers'
  edits. Write a short handoff with changed files, test commands/results and
  any live process handles. Check existing handles before restarting work.

## Current baseline

Latest commit: `5738ce4`, isolated fixed-field lifetime cleanup. Earlier commits:
`a5d512b` VM scratch cleanup, `10c4928` dynamic TLS application shapes/bulk I/O,
`3a4bfab` reviewed bounded Prost bytes reference.

Five-party Shamir/CCD uses Fp25519, GF(2^128), threshold two and statistical
parameter 128. TLS handshake cryptographic stages pass. Application kernels
pass component checks; full application sessions remain gated on erasure.
No end-to-end Signal client or 100,000 messages/hour result exists.

`handshake_backend/CONTINUATION.txt` records detailed evidence and handles.
Canonical `.deps/sharing-refresh/MP-SPDZ` sources/library must remain unchanged
while runtime patches are tested in isolated trees.

## Worker 1: TLS runtime cleanup

Implement serialized-buffer lifetime cleanup as the next checkpoint. Own a new
`handshake_backend/ByteBufferWork/` and corresponding preparation/check scripts.
Build on the archived ScratchWork and LifetimeWork patches in a fresh isolated
runtime; preserve their frozen files and canonical backend.

Concrete source findings, not yet implemented:

- `Tools/octetStream.{h,cpp}` frees allocations without wiping them in destruction,
  clear, growth and replacement. `assign` frees the old buffer before allocating
  the new one, leaving invalid ownership if allocation fails. Make replacement
  transactional; preserve self-assignment and cursor/bit-buffer semantics.
- `resize_precise` can shrink the allocation while retaining out-of-range
  length/read pointers. Account for `Hash::final`, which intentionally shrinks
  its destination before resetting it; do not simply forbid that caller.
- `Tools/FlexBuffer.h` takes ownership from/to octetStream. Cover its destruction,
  growth and replacement too. Ownership transfer must preserve the live data
  and wipe only the discarded owner/storage. Fix allocation-failure handling.
- `Networking/Exchanger.h` caches the send-data pointer, then may resize the same
  receive/send stream. Refresh that pointer after an in-place reallocation.
  Test partial sends plus a larger incoming message with local socket pairs.
- Do not wipe borrowed data on `consume`, or change logical reset semantics
  without checking callers. Full live-buffer cleanup remains separate.

Validation: public synthetic allocation observers before deallocation,
allocation-failure injection, copy/transfer/cursor preservation, exchange
regression, and existing five-party X25519/router reuse tests against a fully
rebuilt candidate library. Adding nontrivial field destruction changes ABI;
never mix candidate and baseline objects. Keep sanitizer checks enabled.

Later TLS checkpoints: live Beaver/input/opening/preprocessing cleanup; raw and
bigint copies; PRNG state and correlated randomness renewal; failures/epochs;
then application activation, opaque-handle lifecycle and private Signal/H2
binding. The non-AES PRNG branch also retains old seed material in `state`;
disabling USE_AES alone is not an erasure solution.

## Worker 2: Signal parser implementation refinement

Take over `SignalReference/ProtoParseWork/MessageReferenceWork/` and new parser
composition work. Preserve accepted primitive references and frozen TopFieldWork.

Accepted: varint/key/skip references, conditional skip-plan correspondence,
uint32 merge, and bounded bytes content reference. Consult each root-review.json
for its exact assumptions. Bytes acceptance requires valid contiguous U8 buffers
and successful bounded allocation below isize::MAX.

Latest Astra state: actual generated SignalMessage dispatcher extraction is in
progress. Isolated FnItemCandidate changes handle pure function items and guard
Result-let simplification with `when monadic`; five synthetic kernel endpoints
and six translation boundary cases reportedly pass. These changes are NOT
root-accepted. Actual error-annotation closures need an explicit observable
projection that retains rejection, input suffix and fields while dropping only
diagnostic stack text. Do not substitute a success-only result for full refinement.
Source visibility/dependency closure, including opaque error layouts, remains
in progress. Inspect current logs before repeating extraction.

Next checkpoint: finish the smallest actual generated dispatcher reference that
kernel-checks, with explicit extraction/model boundaries and tests. Then compose
numeric parser lookup/scan/group/field metadata invariants against it. Frozen
TopFieldWork has 38 reported endpoints and five modules, awaiting root review.

## Worker 3: XEdDSA/prekey refinement and integration

Take over `SignalReference/XEdDsaReferenceWork/` and new reference/integration
work. Preserve frozen XEdDsaWork, PreKeyWork and PreKeyReferenceWork.

XEdDSA Lean primitives and `signal-xeddsa` root export dispatch are implemented
but uncommitted; 33 profiles reportedly match frozen standalone exports exactly.
Implementation-refinement review and private mixed-domain runtime binding remain.
The prior helper selected actual pinned dalek FieldElement51::from_bytes/load8_at
used in XEdDSA recovery, targeting low-255-bit/noncanonical normalization
agreement with the frozen shared-input boundary. Inspect current artifacts/logs
and complete that bounded actual-Rust/Aeneas refinement first.

PreKeyWork has numeric composition/policy checks but external trust-result and
typed-input assumptions. PreKeyReferenceWork has actual constructor extraction
with explicit Option/NonZero/closure models, eight reported endpoints and 2048
native cases; it is not yet accepted. Neither checkpoint proves full async
process_prekey_bundle, store updates, complete Signal sessions or native MPC.

Later checkpoints: complete signed-prekey verification/refinement and state/store
transitions, connect established-session send producers to private TLS/H2 inputs,
then measure persistent-session throughput. Existing measured costs are far below
the target; do not extrapolate component timings into delivery throughput.

## Review queue and completion

Frozen unreviewed checkpoints: TopFieldWork, XEdDsaWork/root export, PreKeyWork,
PreKeyReferenceWork, and new translator/model experiments. Review only the
dependency needed by the next implementation checkpoint; avoid duplicate audits.

Completion still requires functioning persistent TLS + Signal sessions with
secret identifiers/keys, intended compiler/refinement proofs, runtime lifecycle
integration, interoperability evidence and an honest performance estimate.
No worker may redefine completion around its own component tests.
