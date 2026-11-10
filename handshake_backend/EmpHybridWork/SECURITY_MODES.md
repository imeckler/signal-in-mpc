# Security modes and their cost

Decision (2026-11-10): **malicious security at statistical 128 is the default
and is what any "secure" claim refers to; lower throughput in that mode is
accepted.** A semi-honest mode stays available as an explicit alternative so its
throughput and cost can be measured on the same circuits.

## How the switch works

The mode is a build-time choice. It is never a runtime fallback, and the two
modes produce different binaries and different report files.

| | malicious (default) | semi-honest (`-DEMP_HYBRID_SEMI_HONEST=1`) |
|---|---|---|
| Boolean engine | `DynSession` over validated-v3 authenticated garbling (`dyn_session.h`) | `ShSession`: free-XOR + half-gates Yao, semi-honest IKNP OT (`sh_session.h`) |
| Field engine | MP-SPDZ MASCOT shares with MACs (`field_engine.cpp`) | MP-SPDZ `SemiShare`: additive shares, OT triples, no MACs (same file, same interface) |
| Conversion masks | cut-and-choose + buckets, Boolean mod-p checks (`dyn_word_mask.h`) | `r = rA + rB`, each party inputs its own `r` to both engines; no checks |
| Build names | `tls-worker`, `dyn-run` | `tls-worker-sh`, `dyn-run-sh` (`build_hybrid_v3.py`) |
| Checks | `check_tls_worker_v3.py malicious`, `check_lean_runs.py` | `check_tls_worker_v3.py semi-honest`, `check_lean_runs.py semi-honest` |
| Reports | `tls-worker-v3-report.json`, `lean-runs-report.json` | `tls-worker-sh-report.json`, `lean-runs-sh-report.json` |

Everything above those two engine interfaces is shared: the Lean circuits and
their pins, the circuit cache, `tls_kernels.h`, `tls_worker_v3.cpp`, the Lean
TLS controller. Both sessions expose the same operations (private inputs,
public constants, select/concatenate wires, run a pinned circuit, open).

The semi-honest mode gives **no** protection against a party that deviates:
no authenticated shares, no checks on garbling, inputs, conversions or
outputs. The request-agreement and circuit-pin comparisons in the worker remain
but are not a substitute.

## Measured cost, same circuits, local loopback, one machine

Bytes are the sum over both directions. ANDs are the Boolean gate count.

| Workload | ANDs | malicious bytes | semi-honest bytes | ratio |
|---|---:|---:|---:|---:|
| TLS 1.3 handshake vs OpenSSL, split key agreement (default; `split_ecdh.h`) | 6.12 M / 5.61 M | 3.03 GB (3.02 Boolean + 0.015 field, 11 products) | 0.180 GB (0.180 + 0.0003) | 16.8× |
| same, shared-scalar ladder route (X25519 ×2 in the field engine, 6,348 products) | 6.12 M / 5.61 M | 4.15 GB (3.02 Boolean + 1.14 field) | 0.380 GB (0.180 + 0.200) | 10.9× |
| Two chained established Signal sends | 2.65 M | 1.144 GB | 84.9 MB | 13.5× |
| → one established send | 1.32 M | 0.572 GB | 42.4 MB | |
| SPQR steady send (256) | 2.19 M | 1.068 GB | 70.2 MB | 15.2× |
| New-ratchet receive | 5.48 M | 2.365 GB | 175.5 MB | 13.5× |
| TLS record seal | 0.131 M | 72.4 MB | 4.23 MB | 17.1× |
| TLS record open | 0.141 M | 78.1 MB | 4.55 MB | 17.2× |

The handshake's key agreement has two routes, selected per run and agreed by
both workers. Because the base point and the server's key share are public,
the default route shares the ephemeral scalar additively, lets each party do
its own scalar multiplications locally, and uses the field engine only to check
and add two points (`TlsMpc/EdwardsShare.lean`, 11 products). The ladder route
keeps the shared-scalar Montgomery ladder that is proved against RFC 7748 in
Lean; the split route's link to RFC 7748 rests on the Edwards group law, which
is not mechanised (see the header of `split_ecdh.h`). Signal's DH ratchet works
on private points and always uses the ladder.

Wall time for the whole handshake (circuits already cached): 8.1 s malicious and
3.2 s semi-honest with the split route; 10.0 s and 3.4 s with the ladder. The malicious handshake spends 534 k of its ANDs generating
16 conversion masks, of which one is used.

Per unit: malicious ≈ 0.43–0.55 KB per AND and 179 KB per field product (both
parties); semi-honest = 32 B per AND and 31.5 KB per field product.

Compute, per party, for the two-send circuit: malicious ≈ 4.3–4.9 CPU-seconds
(≈ 2.3 s per send); semi-honest garbling/evaluation ≈ 0.08 s (≈ 0.04 s per send;
the 1.5 s fixture time is dominated by parsing the circuit file, which a
long-lived worker does once).

## Full service path (measured end to end)

`check_signal_service_v3.py`: TLS handshake, authenticated WebSocket upgrade,
four sealed-sender text sends over two conversations, private response parsing,
pongs, KeyUpdate; a libsignal recipient decrypts all four messages. Both modes
pass. Whole run: 67.6 M ANDs, 38,099 field products; malicious 33.4 GB Boolean
+ 5.6 GB field in 98 s, semi-honest 2.15 GB + 0.80 GB.

| Per message, steady state | ANDs | field products | malicious bytes | semi-honest bytes |
|---|---:|---:|---:|---:|
| Send (text content, SPQR session encrypt, sealed sender, relay request, WebSocket frame, TLS seal) | 6.7 M | 6,348 | ≈ 3.7 GB | ≈ 0.41 GB |
| Response (two TLS records through frame, control and response parsers, pong) | 7.7 M | 0 | ≈ 4.1 GB | ≈ 0.25 GB |
| **Round trip** | **14.4 M** | **6,348** | **≈ 7.8 GB, ≈ 24 s** | **≈ 0.66 GB, ≈ 0.6 s** |

The "one established send" row in the table above (1.32 M ANDs) is the session
encryption step alone. The full path costs about eleven times that: sealed
sender needs two X25519 ladders per message on the private recipient key, and
the response parsers run a full state-machine step for every byte slot of
every received record.

## Public-receive profile (privacy policy of 2026-11-10)

Policy: only the contact list and the client's own keys must stay hidden from
the parties. Under it, authenticated server records are revealed to the two
controllers and parsed in the clear by the same Lean parsers
(`PublicServiceController.lean`; `check_signal_service_v3.py MODE public`).
Server-initiated messages are never revealed beyond their first two bytes,
because an unsealed incoming envelope names a contact; they abort the session
(receiving is not built on this path). Request ids and WebSocket masks are
public. The send side is unchanged and fully private.

Both modes pass with a libsignal recipient decrypting all four messages. Whole
run: 42.6 M ANDs (was 67.6 M); malicious 19.9 GB Boolean + 5.6 GB field in
61 s (was 33.4 + 5.6 GB in 98 s).

| Per message, steady state | ANDs | malicious bytes | semi-honest bytes |
|---|---:|---:|---:|
| Send (unchanged) | 6.7 M | ≈ 3.7 GB | ≈ 0.41 GB |
| Receive (record decryption in the engines, public parsing) | 2.0 M | ≈ 1.1 GB | ≈ 0.07 GB |
| **Round trip** | **8.7 M** | **≈ 4.8 GB, ≈ 8 s** | **≈ 0.48 GB** |

With this profile: malicious ≈ 94 messages/hour on 1 Gbit/s and ≈ 940 on
10 Gbit/s; semi-honest ≈ 940 and ≈ 9,400. The send now dominates.

### Open-envelope send (same profile, current default of the public controller)

The sealed-sender envelope (what the Signal server receives) is opened after
the gated status; the controllers assemble JSON, base64, protobuf and the
WebSocket frame in the clear with a public request id and a joint public mask;
a small kernel (`signal-request-seal`) formats the recipient UUID, access key,
device id and registration id from the private record into four fixed-width
slots and seals the TLS record. Device and registration ids are space-padded
so their digit counts stay private (not yet checked against the real service).
Both modes pass. Whole run: 34.5 M ANDs; malicious 16.3 GB + 5.6 GB in 52 s.

| Per message, steady state | ANDs |
|---|---:|
| Session encryption + SPQR + sealed sender (`signal-seal`) | 4.97 M |
| Request record seal with private slots (≈ 1,260 bytes) | 1.41 M |
| Two response record opens | 0.29 M |
| Pong seal | 0.11 M |
| Response byte reveals | 0.06 M |
| **Round trip** | **≈ 6.9 M** (+ 6,348 field products) |

≈ 3.9 GB and ≈ 7 s per message malicious; ≈ 0.42 GB semi-honest. Remaining
levers, unmeasured: a public-length message profile and the gate-efficient
SHA-256 backend for `signal-seal`; local GHASH shares for record sealing.

## Throughput estimates (private-receive profile)

Arithmetic on the full-path measurements, not load tests.

| | per message | 1 Gbit/s link | 10 Gbit/s link | 100 000/hour needs |
|---|---:|---:|---:|---|
| malicious-128 | ≈ 7.8 GB | ≈ 58/hour | ≈ 580/hour | ≈ 1.7 Tbit/s |
| semi-honest | ≈ 0.66 GB | ≈ 680/hour | ≈ 6,800/hour | ≈ 147 Gbit/s |

The 100k/hour target is not reachable in either mode with the current
circuits. The two dominant costs are the response parsers (53 % of the gates)
and the per-message ladders; both are circuit-design problems, not engine
problems.

## Earlier estimate, session-encryption step only

One send = one established-send circuit plus one TLS record seal. Superseded by
the full-path numbers above; kept for comparison.

| | per send | 100 000 sends/hour (27.8/s) needs | on a 1 Gbit/s link | on a 10 Gbit/s link |
|---|---:|---|---:|---:|
| malicious-128 | ≈ 0.61 GB, ≈ 2.4 CPU-s per party | ≈ 17 GB/s ≈ 136 Gbit/s, ≈ 67 cores per party | ≈ 740 sends/hour | ≈ 7 400 sends/hour |
| semi-honest | ≈ 47 MB, ≈ 0.045 CPU-s per party | ≈ 1.3 GB/s ≈ 10.4 Gbit/s, ≈ 1.3 cores per party | ≈ 9 600 sends/hour | ≈ 96 000 sends/hour |

So the original 100k/hour target is out of reach in malicious mode with the
current constructions and is at the edge of a 10 Gbit/s link in semi-honest
mode. Bandwidth, not compute, is the binding constraint in both.

Not implemented, for scale only: in the semi-honest mode a three-halves
garbling scheme would cut Boolean bytes by 25 %, and an OT-based (GMW-style)
evaluation with silent OT would cut them by more than an order of magnitude at
the price of rounds proportional to circuit depth. In the malicious mode the
levers are those in `CONVERSION_COST_LEVERS.md` plus fewer ANDs per send
(gate-level rewrites of the SHA-256/HKDF circuits).

## Status

Both modes pass: a full TLS 1.3 handshake against OpenSSL driven by the Lean
controller (`check_tls_worker_v3.py`), the TLS application lifecycle with three
private payloads, KeyUpdate in both directions and replay rejection
(`check_tls_application_v3.py`; whole run including the handshake: 9.24 M ANDs
and ≈ 5.8 GB malicious, 8.72 M ANDs and ≈ 0.48 GB semi-honest), and all 16
pinned-circuit runs including wrong-expectation rejection (`check_lean_runs.py`). Neither mode has been
reviewed; `secure_hybrid_backend` stays `false`.
