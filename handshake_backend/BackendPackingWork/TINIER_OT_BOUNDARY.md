# Tinier128 source mapping and candidate blockers

This is source/representation feasibility evidence, not a Tinier protocol run.
The authoritative MP-SPDZ v0.4.4 pin is **113c4e47dd94bca9ecab029d2f0abe649bea5c52**,
archive SHA256 `53cb2822dce57379f1c66647511b866e3e5db3e2f32b530a13e0c872a418ab78`.
Security-source bytes were checked against that cached archive. Earlier audit
prose incorrectly used `73aa234...` as an upstream revision; this metadata-only
correction changes no measured source/product bytes. An extracted tree has no
independent Git identity: check `git rev-parse --show-toplevel` before consulting
Git, or a parent workspace revision can be mistaken for a dependency revision.

| Phase | Exact source behavior | 128-target boundary |
|---|---|---|
| Raw triple generation | TinyPrep sets no amplification/check in its MascotParams, then applies shuffle sacrifice and combine | Use FKOS/FLNW construction bounds, not MASCOT arithmetic sacrifice or repeated40-bit checks |
| Triple correctness | C opened triples; every homogeneous-bucket residual individually opened/checked and authenticated | Exact divisible M=T*U*L+C, C>=T; per-batch correctness N/binom(M,T), N=U*L |
| One-sided leakage | Separate fresh GlobalPRNG shuffle before combining U triples | Strict FKOS condition L**(U-1)>2**127 for target128; T/U separation requires actual implementation changes |
| Raw authentication | TinierMultiplier auth_ot_ext is deliberately passive; unchecked correlated extension authenticates three columns | This is an internal raw-auth construction covered by TinyOT assumptions, not evidence that the entire protocol is passive |
| Authentication width | Triple AND input paths currently call `int128(...).get_lower()` | Drops64 high MAC bits. LONG_BIT_MAC_KEY alone is insufficient; both paths need full-width conversion and high-half tests |
| Random OT extension | rot_ext uses malicious correlation_check; CONFIG defaults SoftSpoken/libOTe2 | Exact pinned SoftSpoken implementation/build and assumptions must be tested, not silently replaced by KOS |
| KOS alternative | check_correlation calls insecure(); ordinary build exits rather than accepting it | Do not define INSECURE or bypass this guard. Official v0.4.4 docs require insecure mode for KOS |
| Input masks | generateInputs adds ceil(MACbits/valuebits) masks, joint coefficients, a field-authenticated check_sum and MC.Check | For bit inputs/GF128 this is128 extra masks; input/field checks remain separate terms, not covered by triple combinatorics |
| MAC check | Joint seed, fresh GF128 coefficients, commit/open aggregate; reset after check | Keep per-check constants/union terms explicit. GF128/config128 does not imply a whole lifetime failure<=2^-128 |
| Key binding | Static complete MascotMacKey owns key plus committed OT root; read_or_generate persists root | Retained authenticated shares require the same bound commitment root, or checked private reauthentication under a fresh bound key |
| Failure | mac_fail_remove removes persisted secrets; Tree_MAC_Check destructor terminates on pending unchecked opens | Needs caught-failure integration and terminal key invalidation before any runtime capability |

The checked public arithmetic report contains separate correctness/leakage
bounds. A full accounting still includes authentication (FKOS explicitly has
an authentication constant), every MAC/input check and computational OT/PRG/
commitment assumptions. Sum these per-phase/batch terms with explicit query
counts. No query-independent deployment-lifetime bound is required or claimed.
The exact source mapping to the primary authentication theorem is not yet a
complete accepted proof boundary, so no final numeric total is asserted.

## Concrete OT ownership/key-root blocker

BaseMachine's on-demand setup is thread-local and keyed by Player pointer;
OTTripleGenerator's complete MAC key is process-static. The latter retains a
key-bound OT root and is advanced by get_fresh. Default MascotMacKey also writes
secret root material to Player-Data. A new epoch must NOT simply clear these
setups and regenerate OT under a retained MAC key. Upstream documents the
resulting key-equivocation/selective-failure issue. A feasible implementation
needs an embedding-owned, in-memory, collectively bound commitment root with
serialized advancement, no rollback/reuse, explicit retirement policy, and
safe reauthentication if that root/key is replaced. It also needs RAII/owned
stacks/cancellation for setup pthreads, OT multiplier threads, SoftState threads,
BitMatrix storage, seed copies and pending MAC destructors. The CCD failure
candidate intentionally does not certify these owners. No OT reset was added.

The exact upstream gitlink for libOTe2 resolves to mkskeller/libOTe
`fe6b2ff82a976a5332b3a2efe325831588b1324a`. It is not among the repository's
currently installed CCD dependency pins. Its malicious SoftSpoken sender/receiver
classes were inspected read-only; no library build or protocol test has occurred.

## Communication feasibility

Actual public matrix serialization checks pass under ASAN/UBSAN:128 raw bits
pack into2048 bytes,129 into4096. Tinier authenticates three raw columns to each
of four peers, so its authentication-COT matrix payload ALONE is at least
`12*ceil(M/128)*2048` bytes sent per party, excluding framing, raw multiplication,
shuffle/combine openings, MAC checks, inputs and online work. This lower bound
is source-derived, not a measured protocol benchmark.

For381 final triples, the separate-bucket proposal T=C=11/U=16 needs67,067 raw
triples and at least12,877,824 authentication-COT payload bytes per party. The
measured CCD tiny fixture used275,600 bytes total for381 logical ANDs (including
its other setup/input/comparison work). Even million-output batches retain a
roughly56raw/output expansion with separate sizes. Thus this conservative
established construction offers no evidenced communication advantage; a heavy
Tinier build is not justified as a throughput optimization by serializer ratios.
A small future functional/security candidate would remain explicitly separate
from a performance claim.

Primary sources: [MP-SPDZ v0.4.4](https://github.com/data61/MP-SPDZ/tree/113c4e47dd94bca9ecab029d2f0abe649bea5c52),
[OT defaults](https://mp-spdz.readthedocs.io/en/v0.4.4/readme.html),
[key-binding fixes](https://mp-spdz.readthedocs.io/en/v0.4.4/security-fixes.html),
[FKOS15](https://eprint.iacr.org/2015/901.pdf),
[FLNW17](https://eprint.iacr.org/2016/944.pdf),
[SoftSpokenOT](https://eprint.iacr.org/2022/192), and
[pinned SoftSpoken implementation](https://github.com/mkskeller/libOTe/blob/fe6b2ff82a976a5332b3a2efe325831588b1324a/libOTe/TwoChooseOne/SoftSpokenOT/SoftSpokenMalOtExt.h).
