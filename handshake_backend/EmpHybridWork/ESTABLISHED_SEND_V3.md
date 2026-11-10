# Established Signal sends on candidate v3

Status 2026-11-10. REMAINING_WORK.md section 7 step 1, first slice: nonempty established sends with retained private state on the validated Boolean engine at statistical 128. Functional evidence on local loopback with fixture secrets; `secure_hybrid_backend` remains `false`.

## What runs

`TlsMpc/HybridSend.lean` defines two consecutive sends as one circuit. Each is the existing proved step `ChainSend.sealCore` (chain-key derivation, AES-256-CBC with PKCS7, serialization, message MAC). The second send takes its chain key and counter from the first send's private output inside the circuit, so returned state feeds the next message without leaving the computation.

`lean_run_fixture.cpp` is a generic runner: every input bit is XOR-shared between the two parties, the share-combining XOR and the output comparison are Lean circuits, all outputs stay private, and one bit is opened saying whether the output equals a public expectation. It can run any pinned Lean circuit profile written by a lowering script.

`lower_send_circuit.py` exports the circuit (17-byte plaintexts, 5 PQ bytes, counter width 5, previous width 2, with addresses), checks it against a reference that does not use the circuit (hashlib HMAC/HKDF, the openssl binary for AES-256-CBC, the serialization helpers of the existing fixture scripts) and pins it. `check_lean_runs.py` runs it on the engine.

## Results (`lean-runs-report.json`)

| Lane | Outcome |
|---|---|
| Two accepted sends, second on the first's returned chain key and counter | Output equals the reference; passes |
| Invalid PQ-key flag | State preserved and wires zeroed, as the reference specifies; passes |
| Wrong expectation | Rejected at the equality bit |

## Cost of two sends (per party, loopback, one cold run)

| | |
|---|---|
| AND gates | 2,648,613 |
| Boolean traffic, both directions together | 1.14 GB |
| Circuit time | 1.8 s (plus 1.3 s to load and hash the 2.6 M-AND circuit file) |
| Peak memory | 1.6 GB |

That is about 1.32 million AND gates, 0.57 GB and 0.9 s per established send, or about 430 bytes per AND at this chunk size and statistical 128.

## What this means for the throughput target

100,000 sends per hour is 27.8 per second. At the measured cost that is about 16 GB per second of traffic between the two parties, which no internet link carries. The time is less of a problem (about 25 cores' worth of work) than the bandwidth.

Where the bytes go: the garbled circuit itself is 2κ+2 bits per AND, about 42 MB per send. The remaining roughly 390 bytes per AND is triple generation, which scales with the bucket size (7 at this circuit size for statistical 128; 3 would suffice at statistical 40).

Levers, none measured here:

- Fewer AND gates per send. The circuits come from the bit-vector compiler path and were not written for gate count; the gate-level compiler (`TlsMpc/BoolDag.lean`) took the modular add from 1,275 to 765. SHA-256 dominates.
- Cheaper correlated OT under the triples (emp-ot ships Ferret as an alternative to SoftSpoken); this shrinks the OT share of the traffic, not the half-gate ciphertexts of the leaky ANDs.
- Larger chunks lower the bucket size only slowly at statistical 128 (6 at about 2^26 ANDs).
- The statistical parameter itself.

Even a tenfold reduction leaves 1.6 GB per second at the target rate. Reaching 100,000 sends per hour over internet links at statistical 128 needs roughly two orders of magnitude, which the levers above do not obviously provide together. This should be treated as an open design question, not an engineering backlog item.

## Further circuits on the same runner

`check_lean_runs.py` now runs every profile in `.deps/emp-hybrid-word-v1/*.json`; all 16 runs pass, and each profile has a wrong-expectation run rejected at the equality bit.

| Profile | Source | AND gates | Lanes | Time per run |
|---|---|---|---|---|
| `signal-two-sends` | `TlsMpc/HybridSend.lean`, independent reference | 2,645,910 | accepted, rejected-flag | 3.2 s |
| `signal-spqr-send-256` | existing export (steady send with SPQR, 256-byte plaintext) and its fixtures | 2,184,573 | 2 | 2.7 s |
| `signal-new-ratchet-receive` | existing export (receive starting a new DH chain) and its fixtures | 5,473,355 | 2 | 6–7 s |
| `tls-seal-record` | `TlsRecord.sealCore`, checked against `cryptography` AES-GCM | 129,993 | 2 sequence numbers | 0.3 s |
| `tls-open-record` | `TlsReceive.openCore`, same reference | 140,046 | valid, forged tag, wrong sequence | 0.3 s |

`lower_tls_record.py` and `import_profiles.py` produce the TLS and imported profiles. For imported profiles the expected outputs are those of the earlier fixture work; this run shows the engine reproduces them on private inputs, not that the fixtures are right.

## Not covered

Recipient decryption with actual libsignal, SPQR, sealed sender, the TLS record layer and durable state commit are not part of this slice. The key-derivation and send circuits are lowered by the shared unverified adapter.
