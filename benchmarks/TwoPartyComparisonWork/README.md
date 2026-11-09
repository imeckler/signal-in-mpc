# Isolated two-party comparison

Status: source/build feasibility and adapter implementation, **not full Signal throughput**.
Bootstrap and sharing refresh remain paused. No production configuration changes.

## Plan and acceptance

1. Pin backend sources and actual checks; build locally without disabling security guards.
2. Run identical Lean-exported AES/SHA/component graphs with private XOR-share inputs. Account for live preprocessing, all channels/directions, CPU/wall/RSS and cold/warm loading. Never reuse consumed preprocessing.
3. Retain outputs as private shares across repetitions; verify public-known fixture outputs independently. Add curve work with actual private inputs before labeling any result a complete producer.
4. Compose established Signal, TLS seal/open, response parsing and updated conversation state; verify with the pinned Rust recipient. Compare equal-work sequential/batched repetitions, bounded by measured resources. Target27.78 messages/s. Loopback is not WAN.

## Source selection

EMP main README explicitly says “Heads up — AI-assisted rewrite, not yet audited.” Main inspected at a245ca0f67abaf2d48c711e3c050ce961e60ad29. Candidate is final legacy v0.3.0, **not claimed audited**:

| source | commit | official archive SHA256 |
|---|---|---|
| emp-ag2pc v0.3.0 |356cfd824772af9334ac9a994d1eec17ab5f565a|2e6073489eab9a318d63ed1e2c4b7d96b843d3a82fade5413a7be4fe79a9e9b6|
| emp-tool0.3.0 |11093a7d2160e7e7a4dcae3ffd9e6935bf2b8c1c|efa46fccf39643461078b88b82d797e7ce9f1b9357010611045b1afd0254a277|
| emp-ot0.3.0 |52b32c8371c09c1567e3d650c0f0adfbb229a270|a625ad596ec2bc3b6ba989a632407823a90b2efc2c527e64b315f89d71aac6ce|
| MP-SPDZ v0.4.4 |113c4e47dd94bca9ecab029d2f0abe649bea5c52|53cb2822dce57379f1c66647511b866e3e5db3e2f32b530a13e0c872a418ab78|

Official EMP archive URLs are https://codeload.github.com/emp-toolkit/REPOSITORY/tar.gz/COMMIT. Checked README/tag API responses are preserved here. Source trees live outside git in `.deps/two-party-comparison`.

## Security/interface boundaries under investigation

- Legacy C2PC `SSP=5` bytes (comment says40); `MASK=0xFFFFF` truncates some label comparisons to20 bits. Exact composition must be mapped, not called uniform S128. Fpre uses size-dependent buckets3/4/5 and minimum320 triples.
- `2pc.h` production label-mismatch branches print and continue. A benchmark must detect/reject these, not accept outputs after them. Legacy `LeakyDeltaOT` uses IKNP with internal malicious check disabled; outer authenticated-bit/triple protocol supplies checks. This alone does not establish either insecurity or complete security.
- Bob-only output is the default. State sharing can add fresh Alice-owned output pads to the exported graph; only Bob receives masked state. Alice retains pads, Bob retains masked state. Revealing masked outputs to Alice would reconstruct secrets and is forbidden.
- MP-SPDZ stock Tinier shuffle sacrifice caps40. Prior exact audits in `handshake_backend/BackendPackingWork/TINIER_OT_BOUNDARY.md` also identify64-bit truncations and key/OT-state lifecycle obligations. No128 claim or guard deletion.
- MP-SPDZ KOS fallback is rejected by the secure build. The isolated comparison needs supported checked SoftSpoken and exact dependency closure; canonical CCD build has no installed libOTe2. This is a build prerequisite, not permission to use insecure fallback.
- EMP has no established compatible native Fp25519 bridge here. Complete comparison requires an implemented private curve path and exact conversion accounting; Boolean-only results remain components.

## Interruption inventory

No own live bootstrap processes found by approved direct process inventory. Prior bootstrap compiler handles are terminal with preserved reports. No new native groups started at this checkpoint. Other agents may continue independent proof work; immutable graph snapshots will bind benchmark inputs.

## Executed component checkpoint
Both graphs have identical logical bits/gates across backends. Inputs are supplied as XOR shares; outputs agree with OpenSSL AES256 and hashlib SHA256-empty compression. EMP receives padded outputs only at Bob. The MP component entry opens padded public-known fixture outputs; it is **not** the retained-secret continuation entry. MASCOT-wrapper rows execute Tinier Boolean instructions and zero application Fp multiplications.
These are cold loopback smoke runs, not sustained throughput or a fully validated common malicious-security profile. EMP uses the explicit40-bit comparison-mask correction plus six fail-closed rejection branches; stock-mask results are historical. MP uses fresh per-case MAC/OT directories, checked SoftSpoken, S40 and batch-size option10000. Generated/discarded batches differ; no consumed preprocessing is reused.
| graph | backend | controller wall (s) | global payload bytes sent | max party RSS (MiB) |
|---|---|---:|---:|---:|
| aes256 | EMP legacy+overlay | 0.0815 | 5,638,006 | 19.0 |
| sha256-empty | EMP legacy+overlay | 0.0904 | 37,748,706 | 71.8 |
| aes256 | tinier | 0.2139 | 19,130,414 | 86.4 |
| aes256 | mascot | 0.2595 | 25,397,438 | 103.2 |
| sha256-empty | tinier | 0.7115 | 112,955,758 | 103.4 |
| sha256-empty | mascot | 0.7490 | 113,018,738 | 109.2 |

Byte counters exclude TCP/IP headers/retransmissions. MP counters include socket framing/startup and reconcile total sends/receives; EMP counts all protocol/subchannel payload. CPU and phase details are in reports; MP printed phase CPU values overlap and must not be summed. No WAN emulator used.

Reproduce on the recorded Apple Silicon/Homebrew environment:

```sh
python3 benchmarks/TwoPartyComparisonWork/prepare_emp.py
python3 benchmarks/TwoPartyComparisonWork/check_adapter.py
python3 benchmarks/TwoPartyComparisonWork/run_emp_smoke.py
python3 benchmarks/TwoPartyComparisonWork/prepare_mp.py
python3 benchmarks/TwoPartyComparisonWork/run_mp_smoke.py
```

The original numeric graphs are retained under the paths/hash identities in the reports. A clean checkout must provision those exact public graph artifacts before running; these scripts do not silently regenerate from changing sources. `prepare_mp.py` is syntax-checked; the current binaries were built through its equivalent recorded commands, not by a clean-room replay of the completed script.

Remaining acceptance: full parameter/theorem mapping and adversarial MP controls; immutable closure replay; representative producer component; actual EMP curve/conversion implementation; authenticated private state continuation; full logical Signal/TLS/response/state-update workload; warm/batch sustained rates and epoch/checkpoint costs. Existing X25519 field DAG has4589 multiplications/curve; pure Boolean figures cannot omit this. S128 remains unvalidated for these comparison candidates. Production5party/t2/S128 remains unchanged.

Primary protocol: [Wang–Ranellucci–Katz2017](https://obj.umiacs.umd.edu/papers_for_stories/KatzWangRanellucciBestPaperACMCCS2017.pdf), AppendixA.4 discusses rho-bit transmitted checks; this motivates retaining all40 transmitted bits but does not replace complete implementation validation.

## Executed mixed curve control

`python3 benchmarks/TwoPartyComparisonWork/run_curve_control.py` runs the existing Lean X25519 field DAG with secret XOR-shared scalar and recipient point, checked daBit conversions into MASCOT Fp25519, and canonical field-to-binary conversion. Only low-order/equality predicates open; the expected dummy result is independently computed by cryptography/OpenSSL, not supplied as an agreement. Positive and low-order rejection groups pass. Exact resource/time/bytes and unconsumed preprocessing are in `curve-control-report.json`. This is one curve, not the four-curve producer; EMP curve execution remains unimplemented. MAC-corruption rejection and caught-failure cleanup are distinct untested boundaries of this new runtime.

## Fused Signal-core intermediate

`prepare_signal_core.py --steps 2` and `run_emp_signal_core.py` passed two consecutive fixed-width zero-plaintext Signal/SPQR core sends inside one AG2PC execution. The first returned chain/counters feed the second graph internally; final state is padded with fresh Alice-only random pads and delivered only to Bob. No independent-session authentication/durability claim follows from XOR sharing. The301MB Bristol graph has3,647,972ANDs; measured cold total3.624s, global payload1,829,102,274B, peak party RSS3,530,227,712B. Loading alone took1.43–1.45s; this is not a sustained-rate estimate. Expected wires/state come from the historical coupled public fixture, not a new full recipient/TLS run.

A matched equality-only wrapper (`prepare_core_check.py`, `signal_core_check.mpc`) is now a **passed component** comparison entry: it preserves the two-send state evolution but opens only a balanced equality predicate against the public-known fixture, avoiding sender-state reconstruction in a binary runtime without private reveal. Its MP-SPDZ compile and all three native groups passed; this remains an intermediate component.

## Matched core comparison (cold, two internal sends)

All three entries execute3,650,587 logical ANDs:3,647,972 core plus2,615 balanced verification gates. MP packing changes register execution, not logical work. Both input shares have1464bits. Only the final equality bit opens; no final sender chain is reconstructed.

| backend | wall seconds | global socket/protocol payload sent | max party RSS MiB |
|---|---:|---:|---:|
| emp | 4.154 | 1,830,255,263 | 3368.5 |
| tinier | 40.445 | 6,604,933,082 | 1149.8 |
| mascot | 45.949 | 6,604,999,522 | 1066.0 |

EMP generated3,650,588 authenticated triples for3,650,587 consumed ANDs; Tinier entries report5unused logical triples. This removes the tiny-AES overshoot explanation for most of this component difference. MP uses stock bucket4; a supported bucket3/bulk-preprocessing control remains warranted before calling this an optimized Tinier result. Cold loading is included: EMP reports1.59–1.61s loading, while MP loader time is not yet separately instrumented. Phase details are in the report; no warm/sustained-rate or full-message inference follows.

The MP compile took446.99s and produced133,120VM rounds; compilation is public offline work, excluded from native run totals. Source adapter and public artifacts are frozen by the report hashes. The historical numeric Signal fixture has zero plaintext; actual nonempty Content/sealed-sender/TLS/recipient response semantics remain required for the final benchmark.
