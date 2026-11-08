The measured cost is material; changing register packing alone will not fix it.

The passed four-text native mux window sent20,821,778,000 party0 worker protocol
payload bytes, about5.205GB/message. With unchanged work,27.78messages/s requires
144.60GB/s outgoing payload per party (~1.157Tb/s), before TLS/socket overhead
and retirement-tail traffic. Required traffic reduction is about1157x for a
1Gb/s link,116x for10Gb/s, or11.6x for100Gb/s. These are linear extrapolations of
this small, bounded local fixture, not a production throughput model.

Current representation (pinned base113c4e47dd94bca9ecab029d2f0abe649bea5c52):
StrongShamirShare uses malicious prime-field Shamir plus MaliciousCcdSecret over
GF(2^128). VectorSecret's default_length64 is a vector of part shares.
VectorProtocol loops over individual registers; TinyMC opens individual parts;
ShamirMC serializes each field share. gf2n_long::pack writes16bytes, ignoring its
optional bit-count parameter. The public serializer fixture confirms128 logical
bit values occupy2048bytes as gf2n_long, versus16bytes through Bit::pack, with
round-trip checks. It does not execute either MPC protocol or measure its MAC,
preprocessing, broadcast or malicious-check overhead. A Shamir field share is
not itself a clear bit: truncating it or calling Bit::pack on its low bit is not
a sound compression or conversion.

Candidates for the same five-party/two-corruption/abort requirement:

| Candidate | Assessment |
| --- | --- |
| Tested malicious CCD128 | Preserves existing five/two and lifecycle evidence; full field shares remain costly. |
| Tinier with128-bit MAC field | Malicious dishonest-majority candidate; stronger corruption setting covers two of five. Its bit value serialization can pack, but MAC/OT preprocessing remains. Default short MAC-field build is insufficient for the intended128-bit profile. |
| Tiny | Malicious candidate, but Spdz2kShare<1,S>::open_type is Z2<1+S>; do not assume its masked openings use packed single bits. Requires a separate serializer/protocol audit. |
| Malicious Shamir BMR | Documented multi-party candidate; different garbled-wire representation and preprocessing, not a drop-in mixed bit type. |
| Rep3/PS/SY/Rep4 | Fixed three/four-party variants do not meet the five-party/two-corruption profile. |

The upstream mixed-protocol pairing table associates Malicious Shamir with CCD,
and MASCOT with Tinier. Replacing StrongShamirShare::bit_type alone does not
establish the checked conversion protocol. A coherent experimental candidate is
MASCOT over the same prime plus Tinier128, checked daBits and five participants,
or a separately justified authenticated CCD↔Tinier conversion bridge. Existing
Shamir-owned handles cannot be reinterpreted as additive/MAC bit shares. The
current lifecycle explicitly rejects nonempty machine.ot_setup; an OT-based
candidate therefore needs mapped ownership, cleanup and safe renewal of OT/base
OT/PRNG/MAC state before any application capability can be acknowledged.

Evidence and next code:

The run measured helper-stage time, binary Worker verification/Machine.run time,
and aggregate worker bytes. It did not isolate byte counts by arithmetic/binary
protocol, preparation-only time, or actual preprocessing usage. Field and binary
execution share a Player, so aggregate Player bytes cannot supply that split.
The adapter demand receipt was incomplete; a future-only prefix fix is committed.
Repeated abort snapshots are deduplicated in analysis. Pinned verification totals
~3.135C++ seconds on party0; eliminating those hashes cannot remove20.8GB of MPC
traffic. Machine.run includes preparation and execution; its loader-only share
is unknown. No immutable prepared-code cache or protocol switch has been made.

Next implement a NEW isolated diagnostic runtime exposing quiescent actual
DataF usage and public per-domain protocol operation counts, with preparation
and online/preprocessing phase timers. Add domain/phase tags at protocol network
operations, because a shared Player cannot attribute bytes. Validate those
counters on a small existing binary AND/checked-daBit fixture. In parallel design
a separate Tinier128/MASCOT lifecycle candidate and test input authentication,
checked conversions, corruption rejection and epoch cleanup before comparing a
representative existing kernel. Preserve the tested CCD runtime and closure.
Only after attribution should loader caching or backend changes be prioritized;
no further expensive end-to-end run is justified just to repair instrumentation.

Primary references (local pinned files are hash-bound in audit.json):

- [Protocol models and implementations](https://mp-spdz.readthedocs.io/en/latest/readme.html#protocols)
- [Supported mixed-protocol pairs](https://mp-spdz.readthedocs.io/en/latest/non-linear.html#protocol-pairs)
- [Pinned vector multiplication](https://github.com/data61/MP-SPDZ/blob/113c4e47dd94bca9ecab029d2f0abe649bea5c52/GC/VectorProtocol.hpp)
- [Pinned Shamir opening](https://github.com/data61/MP-SPDZ/blob/113c4e47dd94bca9ecab029d2f0abe649bea5c52/Protocols/ShamirMC.hpp)
- [Pinned Tinier share](https://github.com/data61/MP-SPDZ/blob/113c4e47dd94bca9ecab029d2f0abe649bea5c52/GC/TinierShare.h)
- [libc++ Apple clock](https://github.com/llvm/llvm-project/blob/main/libcxx/src/chrono.cpp)
- [CPython3.9 Apple clock](https://github.com/python/cpython/blob/3.9/Python/pytime.c)

Clock limitation: local probes show Python3.9 uses mach_absolute_time, while
C++steady_clock matches CLOCK_MONOTONIC_RAW. Suspend is excluded by the former
and included by the latter. The959.434driver seconds and1201.916summed RPC seconds
cannot establish active steady throughput or first-call cold-start overhead.
