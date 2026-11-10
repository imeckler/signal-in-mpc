# Signal-in-MPC throughput review: route to 100,000 messages/hour

Date: 2026-11-09. Scope: read-only review of the `tls-mpc` repository, its benchmark receipts and backend audits. No code was changed. Figures marked **measured** come from receipts in the repo; figures marked **estimated** are mine and should be validated before anyone plans around them.

## 1. Summary

- The target is 27.8 logical sends/second. The current system does **0.0053 msg/s** (eight-message native run, two conversations, all five parties on one machine), about 5,000x short.
- The binding cost is the MPC backend's **per-AND wire and CPU cost**, not scheduling. Each secret bit is a full GF(2^128) Shamir share, so one AND costs ~352 bytes per party and ~5 to 15 µs of CPU. One message is ~14M ANDs and **~4.95 GB of traffic per party**.
- Batching and parallel instances do not reduce bytes or CPU per AND. Their measured effect on payload was 0.1%. They matter only for hiding round-trip latency.
- Two things are needed together: (a) a 3 to 5x cut in Boolean gate count and a 4 to 5x cut in circuit depth, both available with identifiable changes; and (b) a backend with 50 to 100x cheaper ANDs. For **5 parties / 2 corruptions** no such backend exists off the shelf. The repo's own audits (CCD, Tinier, BMR, Coral, DEN22) confirm this.
- The realistic decision is between **3 parties / 1 corruption** (stock malicious Rep3, measured 129x less traffic, or Rep4 with 4 parties / 1 corruption) and **funding a custom honest-majority small-field protocol for 5/2** (months of work, research-grade security review).
- For **non-co-located nodes (30 ms RTT)** the dominant constraint for every compact backend becomes circuit depth. Sustaining 27.8 msg/s needs on the order of **108,000 messages in flight today, ~21,000 after depth fixes**, and that count is also a workload requirement: that many distinct conversations must be mid-send at once, and no single conversation can exceed roughly one message per minute.

## 2. Current system and measured baseline

Backend: MP-SPDZ v0.4.4 pin, `StrongShamirShare` = malicious Shamir over Fp25519 plus `MaliciousCcdSecret<gf2n_long>` (GF(2^128)) for Boolean, 5 parties, threshold 2, statistical security 128, live preprocessing. Circuits are compiled from Lean via the AIG exporter and the packed adapter (≤64 lanes).

Measured per-AND cost on this backend (`handshake_backend/BooleanBackendSelectionWork/AUDIT.md`, `BatchThroughputWork/THROUGHPUT_PLAN.md`):

| Quantity | Value |
|---|---:|
| Online bytes per logical AND per party | 128 B |
| Preprocessing bytes per logical AND per party | ~224 B |
| Total bytes per AND (warmed 344k-AND comparator) | 355.6 B |
| CPU throughput per party process (loopback) | 63k to 170k ANDs/s |

Eight-message native run, sequential producer (`BatchThroughputWork/comparison-report.json`):

| Quantity | Value |
|---|---:|
| Inclusive elapsed for 8 messages | 1,505 s |
| Inclusive throughput | 0.0053 msg/s |
| MPC payload per party per message (persistent window) | 4.95 GB |
| Producer call duration | 104 to 111 s |
| Of which program/bytecode load (prepare() clears and reloads every call) | 64 to 66 s |
| Batch-2 payload change | -0.1% |
| Batch-2 wall-time change | 1.2x faster |

Prime-field work (four X25519 operations, ~20k field multiplications, ~1.8k daBits per message) is under 1% of bytes. Everything below is about the Boolean circuit.

### Where the bytes go per message

| Stage | Share of MPC bytes | Approx. ANDs/msg | Notes |
|---|---:|---:|---|
| Producer (chain step, Signal message, sealed sender, JSON/base64, WebSocket frame) | 46% | 6.74M (measured, `service-aig-resources.json`) | 114,049 dependent AND levels; 122k VM rounds |
| Private response parser | 38% | ~5.4M (derived from bytes) | **65,825 ANDs per response byte** (measured on `tls-chat-mux-byte-4096-4.json`); the 982-byte parser state round-trips through the VM once per byte |
| TLS record seal (AES-128-GCM) | 13% | ~1.7M | GHASH is ~16,384 ANDs per 16-byte block in binary; AES-128 block is 6,400 ANDs (at the Boyar-Peralta optimum) |
| TLS open, control, KeyUpdate | 3% | | |

Other measured component costs:

| Component | Measured | Known-optimal | Ratio |
|---|---:|---:|---:|
| SHA-256 compression | 59,759 triples (51,945 with isolated carry-save) | 22,573 ANDs (Bristol) | 2.6x |
| AES-128 block incl. key schedule | 6,400 ANDs | 6,400 | 1.0x |
| AES-256 block incl. key schedule | 8,832 ANDs | ~8,800 | 1.0x |

The SHA-256 overhead comes from Lean Std's bitblaster, which emits a 3-AND full adder; the standard circuit uses 1 AND per bit (carry = c ⊕ ((a⊕c)∧(b⊕c))).

## 3. Circuit-level reductions (backend-independent)

These preserve the proof structure (new modules with refinement theorems, as the repo already does for carry-save and parallel-prefix experiments).

| # | Change | Estimated effect | Effort |
|---|---|---|---|
| 1 | **Response parser as one fixed-shape whole-buffer circuit** over a small capacity instead of a per-byte state machine. The success response is a tiny protobuf (id, status, empty headers/body). | 5.4M to <0.5M ANDs per message; ~35% of total bytes; removes ~80 sequential per-byte function calls (also a large depth win) | Medium |
| 2 | **1-AND-per-bit adder** for SHA-256 (replace Std's 3-AND full adder in the word-add path) | SHA 59.8k to ~22.6k per compression; SHA/HMAC/HKDF is likely half the producer, so ~15% of total | Medium (proof of a custom adder) |
| 3 | **Parallel-prefix (or carry-save + prefix) adders** in SHA-256 for depth | Compression depth from ~4,800 to ~900 levels; producer depth from 114k to ~25k | Medium; isolated module `Sha256ParallelPrefix.lean` already exists |
| 4 | **GHASH on native GF(2^128) shares** while on CCD. MP-SPDZ's `gf2n_long` modulus is x^128+x^7+x^2+x+1, the GCM polynomial. CCD bit-shares are Shamir shares in that field, so packing 128 bit-shares into one element is a local linear map; one GHASH block becomes one field multiplication plus one bit decomposition for the tag. | TLS seal from ~1.7M ANDs to ~0.5M; ~10% of total | Small to medium (new native kernel, bit-order reflection, proof of equivalence) |
| 5 | **Program and preprocessing reuse** across calls within an explicitly defined epoch (immutable public-code cache; keep the retirement barrier) | 2 to 2.5x wall time; zero bytes | Small; already identified in THROUGHPUT_PLAN.md |
| 6 | **Attribute private-length plumbing.** `PrivateBuffer` append/resize, private-length HMAC over full capacity and `PrivateBase64` have no per-module gate attribution. Export `PrivateService` sub-stages and count. | Unknown; could be another 1M+ ANDs | Small |
| 7 | **Precompute message-independent work** per conversation off the critical path: chain step, message-key HKDF, both sealed-sender KDFs and the ephemeral DH do not depend on the plaintext | Message-dependent depth from ~25k to ~15k rounds after items 1 and 3 | Medium (state/commit semantics) |
| 8 | **Sealed sender v2** (multi-recipient) for recipients with several devices | Fanout stops multiplying the AES/HMAC work per device | Medium; needs relay/service compatibility check |

Plausible outcome of 1 to 4: about **3 to 5M ANDs and ~25k rounds per message** (vs 14M and ~130k). On the current backend that is still 1 to 2 GB per message, requiring hundreds of Gbps per party. The backend must change as well.

## 4. Backend options

| Option | Trust model | Bytes/AND per party | CPU | Status in pinned code | Bytes/msg at 5M ANDs |
|---|---|---:|---|---|---:|
| Current malicious CCD GF(2^128) | 5/2, S128 | 352 (measured) | 63k to 170k ANDs/s (measured) | Working | ~1.8 GB |
| Malicious Rep3 binary | 3/1, S40 (stock sacrifice cap) | 2.75 (measured, same synthetic workload) | 16.5M ANDs/s online window (measured) | Stock; already run as a control in the repo | ~14 MB |
| Rep4 binary (Fantastic Four) | 4/1, guaranteed output delivery | ~0.3 to 1 (published cost; **not measured here**) | likely ≥ Rep3 | In MP-SPDZ (`rep4-ring-party`), not built here | ~2.5 MB |
| Shamir over GF(2^3)/GF(2^8) with batched extension-field verification (LN17 / CHI18 / BGIN19 family) | 5/2 | 3 to 15 (**estimated**) | unknown; assumed 3M ANDs/s | No implementation. AUDIT.md notes the small-field paper text had a 2026 erratum; corrected proof and parameters must be bound first | 15 to 75 MB |
| 7 parties, t<n/3 protocols (Furukawa-Lindell 2019, DEN22) | 7/2 | 2 to 8 (**estimated**) | unknown | DEN22 artifact rejected as incomplete (missing checks, zero-seeded PRG) | 10 to 40 MB |
| Malicious Shamir BMR (garbled circuits) | 5/2, constant round | ~5,100 (14.6x CCD, measured on a 381-AND fixture) | heavy | Built as a candidate; no advantage | ~25 GB |
| Tinier/TinyOT, Coral | 5/2 | worse than CCD or insecure as released | | Audited and rejected (`BackendPackingWork`, `CoralAssessmentWork`) | |
| Stock CCD over GF(2^40) at S40 | 5/2, S40 | ~176 (8-byte serialization) | | Guard rejects at S128 | ~0.9 GB |

Bandwidth implication at 27.8 msg/s: 14 MB/msg is 3.1 Gbps per party; 75 MB/msg is 17 Gbps. Rep3 or Rep4 with the circuit fixes fit a 10 Gbps interconnect. A custom 5/2 protocol needs the low end of its estimate or a 25 Gbps fabric.

For the prime-field part, Rep3/Rep4 have field variants and daBit/edaBit conversions in MP-SPDZ; the X25519 kernels and conversions would need re-binding and re-validation.

## 5. Latency, batching and non-co-located nodes

All compact options use one communication round per AND level (plus a batched check), so rounds per message ≈ AND depth: ~130k today, ~25k after items 1 and 3 above, ~15k with item 7. BMR is the only constant-round option and is excluded by bytes.

Throughput model per party, with N messages in flight (SIMD lanes × parallel VM instances):

```
msg/s ≈ 1 / ( rounds × RTT / N  +  bytes_per_msg / link_bytes_per_s  +  core_seconds_per_msg / cores )
```

Bandwidth and CPU scale out, since a "party" can be a cluster of machines in one trust domain. Rounds × RTT does not scale out; only N hides it.

### Estimates at 30 ms RTT, 10 Gbps and 32 cores per party

Today's circuits (14M ANDs, ~130k rounds). Values are msg/s; target is 27.8.

| Backend | MB/msg | Latency/msg | N=1k | N=4k | N=32k | N=∞ (10 Gbps) | N=∞ (1 Gbps) |
|---|---:|---:|---:|---:|---:|---:|---:|
| CCD 5/2 (current) | 4,928 | 65 min | 0.09 | 0.13 | 0.14 | 0.15 | 0.02 |
| Rep3 3/1 | 38.5 | 65 min | 0.26 | 0.97 | 5.2 | 13.4 | 2.8 |
| Rep4 4/1 (est.) | 7.0 | 65 min | 0.26 | 1.0 | 6.5 | 28.8 | 11.7 |
| Custom 5/2 small-field (est.) | 112 | 65 min | 0.25 | 0.84 | 2.8 | 4.3 | 1.0 |
| 7-party t<n/3 (est.) | 56 | 65 min | 0.25 | 0.88 | 3.2 | 5.3 | 1.7 |
| BMR 5/2 | 71,960 | seconds | 0.01 | 0.01 | 0.01 | 0.01 | 0.00 |

After circuit fixes (5M ANDs, ~25k rounds):

| Backend | MB/msg | Latency/msg | N=1k | N=4k | N=32k | N=∞ (10 Gbps) | N=∞ (1 Gbps) |
|---|---:|---:|---:|---:|---:|---:|---:|
| CCD 5/2 (current) | 1,760 | 12.5 min | 0.31 | 0.38 | 0.40 | 0.41 | 0.07 |
| Rep3 3/1 | 13.8 | 12.5 min | 1.3 | 4.8 | 20.2 | 37.6 | 8.0 |
| Rep4 4/1 (est.) | 2.5 | 12.5 min | 1.3 | 5.1 | 28.3 | 80.5 | 32.9 |
| Custom 5/2 small-field (est.) | 40 | 12.5 min | 1.2 | 3.7 | 9.4 | 11.9 | 2.7 |
| 7-party t<n/3 (est.) | 20 | 12.5 min | 1.3 | 4.0 | 11.0 | 14.7 | 4.7 |
| BMR 5/2 | 25,700 | seconds | 0.04 | 0.04 | 0.04 | 0.04 | 0.00 |

Model parameters used: CCD 352 B/AND and 150k ANDs/s per core; Rep3 2.75 B/AND and 10M ANDs/s (conservative vs the 16.5M measured); Rep4 0.5 B/AND and 15M ANDs/s (estimated); custom 5/2 8 B/AND and 3M ANDs/s (estimated); 7-party 4 B/AND and 3M ANDs/s (estimated); BMR 5,140 B/AND, 20k ANDs/s, 30 rounds. The custom-protocol rows are dominated by the CPU guess; Rep3-like CPU efficiency would move them toward the Rep3 row for bandwidth-permitting links, but not change N.

### Per-party resources to sustain 27.8 msg/s at 30 ms RTT (each bound alone)

| Backend | Gbps (today / fixed) | Cores (today / fixed) | In-flight N (today / fixed) |
|---|---:|---:|---:|
| CCD 5/2 (current) | 1,095 / 391 | 2,593 / 926 | 108k / 21k |
| Rep3 3/1 | 8.6 / 3.1 | 39 / 14 | 108k / 21k |
| Rep4 4/1 (est.) | 1.6 / 0.6 | 26 / 9 | 108k / 21k |
| Custom 5/2 small-field (est.) | 25 / 9 | 130 / 46 | 108k / 21k |
| 7-party t<n/3 (est.) | 12 / 4.4 | 130 / 46 | 108k / 21k |

### What the in-flight count means

- **Depth is the binding constraint at 30 ms** for every compact backend. At 130k levels a message takes 65 minutes of wall clock regardless of per-AND cost; at 25k levels, 12.5 minutes.
- **N is a workload requirement, not just a resource.** Messages on one ratchet are serial. With pipelined chain stepping, one conversation advances at most once per chain step: ~290 s today (9.6k levels), ~54 s with prefix adders (1.8k levels). So 100k/hour at 30 ms RTT needs 20,000+ distinct conversations mid-send within any 12-minute window and no conversation faster than about one message per minute. A workload of a few thousand chatty conversations cannot reach the target at this RTT with any of these protocols.
- **Memory for N≈21k is feasible but not free.** For Rep3 a 64-lane producer instance is roughly 50 to 100 MB of registers and triple buffers, about 1 to 2 MB per in-flight message, so 20 to 40 GB per party plus shared bytecode. This requires item 5 (no per-call bytecode reload, no per-record preprocessing renewal) first.
- **Co-location changes the picture entirely.** At 1 ms RTT the required N after fixes is ~700; at 0.2 ms it is ~140. If the nodes can sit in one metro region, depth stops being the first-order problem and the backend choice dominates. `benchmarks/config/requirements.json` currently says `deployment: internet`; this should be revisited as an explicit RTT requirement.

## 6. Recommended route

1. **Do the circuit work first** (section 3, items 1 to 5, then 6 and 7). It is backend-independent and proof-preserving, and the repo already has the scripts to measure each change. Depth reduction (items 1, 3, 7) is as important as gate count if nodes are not co-located.
2. **Decide the trust model now**, because it gates everything else.
   - If 3/1 (or 4/1) is acceptable: build the service on `malicious-rep-bin-party` (or Rep4) with the matching field protocol for X25519, rerun the eight-message fixture, and measure bytes, CPU and rounds. Expected after circuit fixes: tens of MB and well under a second of CPU per message, so 100k/hour becomes a deployment question (link, cores, N). Label the S40 sacrifice cap explicitly.
   - If 5/2 must hold: budget a research-grade implementation of honest-majority Shamir over a tiny binary extension field with batched extension-field verification and a checked conversion to Fp25519. `AUDIT.md` lists the obligations. Expect months, plan for 15 to 75 MB per message, and bind the corrected small-field theorem and parameters before writing protocol code.
3. **Decide the deployment topology.** Co-located (≤1 ms RTT) nodes reduce the required in-flight count by 30x and make per-conversation rate limits irrelevant. If nodes must be far apart, plan for N≈21k, 20 to 40 GB per party, and a workload with tens of thousands of concurrently active conversations.
4. **Build the pipeline for concurrency**: 64-lane batches of independent conversations across many VM threads or instances sharing one loaded program, pipelined chain stepping per conversation, and message-independent KDF precomputation.
5. **Re-measure end to end** with the repo's existing policy (payload bytes, consumed vs generated preprocessing, CPU, rounds, RTT reported separately) before any throughput claim.

## 7. Risks and caveats

- All measurements in the repo are loopback on one machine or static gate counts; no WAN run exists. Transport framing overhead is unmeasured.
- The Rep3 control was run at statistical 40 (the stock cut-and-choose cap); the production profile is 128. Any 3/1 or 4/1 choice is a trust-model change and must be labeled as such everywhere.
- Rep4, custom 5/2 and 7-party figures are estimates from published costs, not measurements on this code.
- The Signal service rate-limits per account and per connection; 27.8 msg/s likely needs many accounts and connections, and the service's acceptance of parallel authenticated sockets per account is unverified.
- Device fanout multiplies producer cost (not TLS) unless sealed sender v2 is used; the target counts logical sends.
- Proactive share refresh, VM erasure/retirement and durable state commits are unfinished and add cost not included here.

## 8. Sources in the repository

- `README.md`, `IMPLEMENTATION_PLAN.md`, `benchmarks/config/requirements.json`
- `handshake_backend/BooleanBackendSelectionWork/AUDIT.md` (per-AND costs, Rep3 control, backend matrix)
- `handshake_backend/BatchThroughputWork/THROUGHPUT_PLAN.md`, `comparison-report.json` (eight-message run, byte attribution, load times)
- `handshake_backend/BackendPackingWork/AIG_RESOURCE_FINDINGS.md`, `service-aig-resources.json`, `SINGLETON_PACKING.md` (producer gate counts, depth, SHA compression cost)
- `handshake_backend/CoralAssessmentWork/ASSESSMENT.md`, `BackendPackingWork/TINIER_*.md` (rejected backends)
- `benchmarks/results/lean-signal-throughput-baseline.json`, `lean-signal-steady-send-costs.json`
- `handshake_backend/WebSocketWork/NativeChatMux.h`, `.deps/tls-websocket-upgrade-native/Worker-Public/tls-chat-mux-byte-4096-4.json` (per-byte response parser)
- `.deps/sharing-refresh/MP-SPDZ/Math/gf2n.cpp` (GF(2^128) modulus `{128, 7, 2, 1}`)
- `TlsMpc/Ghash.lean`, `TlsMpc/Sha256ParallelPrefix.lean`, `TlsMpc/Sha256CarrySave.lean`, `TlsMpc/Signal/PrivateHash.lean`, `PrivateBuffer.lean`
- Throughput model script: `tput_model.py` and `tput_req.py` alongside this file.
