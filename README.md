# TLS and Signal in MPC

Build a Signal client whose keys, recipient identifiers, protocol state, and
decrypted messages remain shared among computing nodes. Protocols and circuit
construction live in Lean. Compiler proofs connect those specifications to
numeric circuit artifacts. A generic unverified adapter executes the artifacts
through an unverified MPC backend. MPC security is outside the requested
mechanization scope.

The deployment target is five parties tolerating two colluding malicious
parties, with abort acceptable, over internet links. The target is 100,000
logical sends/hour (27.78/second), mostly established sessions. Device fanout
must be counted separately. This rate has **not** been measured or established.
Random opaque recipient handles and repeated-send linkage are acceptable.
Signal identifiers, identifying public keys, tokens, and identifier-bearing
requests and responses must remain shared.

Proactive security is required: at most two distinct nodes may be compromised
per refresh epoch, with different nodes potentially compromised in later epochs
and no lifetime limit of two. Old shares must not accumulate into a usable
reconstruction set across epochs. The refresh and recovery design must enforce
the corresponding erasure and transition assumptions.

Nothing has been deployed. Pallas and the storage format can change. Existing
keys may be imported in shares, preserving their exact byte encoding; sharing
cannot undo an earlier party's knowledge of those keys. Repository fixtures are
synthetic public data. Requirements and experimental benchmark sweeps are
separated in `benchmarks/config/requirements.json`.

The implementation is a collection of proved components and test harnesses.
Five independent Lean controllers now drive persistent native MPC workers
through a TLS handshake against OpenSSL over localhost. Each controller checks
the certificate and server Finished; OpenSSL accepts the MPC-generated client
Finished. The run also covers certificate fragmentation and dynamic compilation
and agreement of record-size kernels. See `benchmarks/results/tls-native-handshake.json`.
The client deliberately refuses to activate the application session because
full VM key retirement is unfinished. Application integration, a complete
Signal-server request, proactive security and WAN throughput remain unestablished.
The separate synthetic-peer stage test is recorded in
`benchmarks/results/tls-native-worker-network.json`.

## Lean implementation and proof scope

| Component | Implemented and proved | Remaining boundary |
| --- | --- | --- |
| Boolean compiler | Typed stack compilation, input-independent traces, AND cost, numeric instruction export | Native exporter, JSON, adapter and backend execution are unverified |
| Bit-vector compiler | Lean Std's proved bit-vector/AIG lowering, plus proved export to a numeric DAG | The unverified adapter recovers XORs; addition and depth remain unoptimized |
| SHA-256 and HMAC | Executable byte/word specification, symbolic refinement, numeric DAG compilation, padding and output lengths | Handwritten specification's correspondence with the standards requires review |
| HKDF and TLS key schedule | Extract/expand, encoded labels, no-PSK handshake secrets, application secrets, AES-128 traffic key/IV, Finished and traffic updates | Native handshake composition tested; application activation and full VM retirement remain |
| AES | AES-128/256 key expansion, encryption and decryption; forward/inverse S-box correspondence and numeric compilation | Full correspondence to RustCrypto's complete cipher wrappers remains unfinished |
| GCM | AES-128-GCM encryption and authenticated opening, shared key expansion, GHASH, tag equality and zero-on-rejection plaintext release | Nonce uniqueness and key-use policy belong to connection state; GHASH cost needs optimization |
| TLS records | Complete protected-record encoding and opening; authenticated header validation, inner type/padding parsing and zeroed rejection outputs | Stream framing, connection-state routing and durable sequence/key management remain pending |
| TLS handshake | X25519 field DAG/refinement, full initial public controller, retries, transcript assembly, Finished, handshake-only release gate; native five-party OpenSSL exchange tested | Controller is tested, not fully mechanized; OpenSSL auth and mixed runtime are unverified; retirement blocks application activation |
| Signal symmetric derivation | Chain-key HMAC steps, SPQR salt input, WhisperMessageKeys derivation, compiled refinement | Equivalence to libsignal's RustCrypto dependencies remains pending |
| Signal CBC and receive | AES-256-CBC encryption/opening, strict PKCS7, identity-bound truncated HMAC and authenticated opening of bounded serialized spans | Full protobuf parsing, session transitions and RustCrypto wrapper equivalence remain pending |
| Actual Rust reference | Key accessors, clamp, service IDs, tag decoders, PKCS7, AES leaves and full SHA-256 compression; separate full AES-256 software schedule proof | Digest/HMAC wrappers, AES representation composition and Signal state machines remain unfinished |
| Share refresh | Conditional Lean preservation/epoch guards and a native refresh prototype for prime and CCD binary fields | Durable epoch commit, recovery, erasure and whole-service proactive security remain pending |

The TLS normative reference is [RFC 9846](https://www.rfc-editor.org/info/rfc9846/),
which supersedes RFC 8446. The Lean files cite relevant clauses. Differential
checks use [RFC 5869](https://www.rfc-editor.org/rfc/rfc5869) and
[RFC 8448](https://www.rfc-editor.org/rfc/rfc8448) vectors and independent
hashlib/HMAC and OpenSSL results. AES and GCM follow
[FIPS 197-upd1](https://doi.org/10.6028/NIST.FIPS.197-upd1) and
[SP 800-38D](https://doi.org/10.6028/NIST.SP.800-38D).
Tests support specification review; they do not prove
the prose-to-Lean correspondence.

Compiler modules are `TlsMpc/Boolean.lean`, `Artifact.lean`, `AigExport.lean`,
and `ByteCircuit.lean`. `BvConstruct.lean` proves constant folding for public
subexpressions. TLS components are in `Sha256.lean`, `TlsKdf.lean`,
`Protocols.lean`, `TlsLayout.lean`, `Aes.lean`, `Ghash.lean`, `Gcm.lean`,
`GcmOpen.lean`, `TlsRecord.lean`, `TlsInner.lean`, `TlsReceive.lean` and
`TlsHandshake.lean`. `ByteAuth.lean` implements shared byte
comparison and masked release. `HmacPrepared.lean` and
`TlsKdfPrepared.lean` reuse HMAC prefix states, with proofs that this preserves
the direct specification. Sharing these states also prevents pathological
expression-comparison costs during export.
The bit-vector compiler also uses Lean's standard `shareCommon'` identity
primitive to share repeated expression objects before bitblasting. Its native
implementation is part of the existing trusted runtime boundary.

The root package uses Lean 4.31.0 and its standard library. Audited theorems use
only standard `propext`, `Quot.sound`, and, through Std's bit-blaster,
`Classical.choice`. There are no placeholder proofs or custom crypto axioms.
Mathematical numeric-artifact evaluation is verified; native Lean execution and
JSON serialization are trusted. JSON is parsed back and compared before
emission, and the adapter rejects malformed graphs and instructions.
The adapter's XOR rewrite uses a proved Boolean identity, but the Python graph
traversal and pruning are unverified and checked with differential tests.

## Signal reference

The pinned reference is upstream libsignal v0.106.1, commit
`904c8dc8216073b078a5f2f5090e3da8382e6a92`. `SignalReference/pins.json` records
source hashes, Aeneas/Charon commits, Rust and Lean toolchains. Extracted Lean is
under `SignalReference/LibSignalReference/Generated`; refinement proofs are in
the adjacent `Proofs` directory. This separate package uses Aeneas and mathlib.

The reference proof target is **our circuit agrees with the faithfully
Aeneas-translated Signal implementation**. We trust the extraction and its
explicit standard-library models. We do not require an independent proof of
Signal's internal algorithms, protocol correctness or cryptographic security.
Internal lemmas are needed only insofar as they establish that equivalence.

Completed reference proofs use the actual pinned Rust sources. Broader
extraction encounters RustCrypto generic associated types and, with
monomorphization, unsupported pointer and standard-library operations. A
successful process exit is insufficient: extraction inventories must have no
errors, unexplained opaque functions or missing declarations. Lean symmetric
derivation has a compiler proof but **does not yet have RustCrypto refinement**.
The actual compact SHA-256 compression proof covers all 64 rounds and
feed-forward, and also connects the compression used by the existing hash
circuit to the translated implementation. Byte buffering and complete
digest/HMAC/HKDF wrappers are still outside that result. A separate actual
AES-256 schedule proof covers all 120 software bitplane words; its complete
representation bridge to the byte-oriented cipher and cipher wrappers remains
unfinished. See `SignalReference/README.md` for precise per-component scope.
Service identifiers use one shared ACI/PNI bit plus sixteen shared UUID bytes;
the complete seventeen-byte encoding has an implementation-reference proof.
Tag decoding preserves both valid results and the original rejected byte.
`SignalReference/BAF_REVIEW.md` records pinned reuse candidates and outstanding
assumptions from Beneficial AI Foundation's repositories.

Scalar clamping covers byte masks, not field reduction, X25519 or private-key
decoding. Symmetric derivation accepts a shared 32-byte SPQR salt: the caller
must select the actual SPQR key or the specified zero salt inside MPC. SPQR,
PQXDH, DH ratchets, skipped keys, sealed sender, general parsing and server APIs
remain to be integrated. Bounded receive circuits authenticate one shared
serialized message and select the ciphertext from that same input; a future
in-MPC protobuf parser must establish field offsets and presence. Their compiler
proofs do not yet establish full libsignal receive equivalence. Updating the sibling relay
also requires auditing its older libsignal fork for changes to preserve.

## Sharing and execution design

The intended mixed backend uses bits for symmetric cryptography and appropriate
fields for curve operations, with secure conversions at coarse boundaries.
The typed field IR and conversions remain to be implemented and benchmarked.
Arbitrary 256-bit keys must remain lossless bytes: reducing them modulo a
smaller field changes the key.

`specs/sharing-refresh.json` records the database audit and proposed migration.
The old format stores two polynomials on different evaluation grids; their
constants' difference is a contact-encryption seed. Migration must recover
that value only inside MPC, preserve its canonical encoding, derive the
existing key and authenticate the encrypted record. The old leader-generated
refresh delta is reused across rows. Reusing the same zero sharing leaves
pairwise record-share differences unchanged across epochs, so a mobile attacker
can reconstruct secret differences from successive corruptions. The replacement
needs distinct masks per object/component. The refresh agent is investigating
amortized seed setup; this does not permit reusing the same mask or retaining
an epoch-independent refresh seed. `refresh/PRZS.txt` describes the experimental
fresh-seed alternative and its mobile-corruption assumptions. Another storage
option keeps conversation records encrypted and proactively shares only a
master wrapping key. That can make periodic refresh independent of record
count, at the cost of additional MPC AEAD work per access; version/rollback
binding and retirement of cached session state would still be required. The
storage architecture has not been changed.

Malicious-backend checks can enforce an internal zero-refresh relation; public
third-party verification would be separate. Lean refresh proofs assume valid
linear sharings and checked external evidence. They do not prove entropy,
secrecy, backend security, certificates or disk atomicity. Protection against
changing compromised parties is required and needs a precise period model,
recovery, erasure and refreshed channels. Compromise during refresh is accounted
in both adjacent periods; a bound on simultaneous compromise alone is weaker.
The current backend integration does not yet establish proactive security.
`refresh/SECURITY.txt` records the native prototype's exact per-component
refresh transcript, full-field output checks, snapshot candidates and isolated
TLS transport policy. Local native and memory-BIO tests passed; five-party
network execution, authenticated worker import, epoch commit and erasure remain
unimplemented or untested. A candidate file is not an active database epoch.

Libraries keep values shared. Test programs import public fixture fragments
through private MPC inputs; this is not a persistent native-share format. The
**test harness deliberately opens fixture outputs**, including derived keys,
and must not be used with live secrets. Public lengths and circuit shapes need
an explicit deployment leakage policy and padding where appropriate.

## Reproduce

Build Lean and audit the proof dependencies:

```sh
lake build emit_mpc
lake env lean Checks.lean
python3 scripts/check_lean_proofs.py
python3 scripts/check_sharing_spec.py
```

Exporters accept public sizes, without accepting secret key values:

```sh
.lake/build/bin/emit_mpc tls-traffic-keys > /tmp/tls-traffic-keys.json
.lake/build/bin/emit_mpc signal-derive-keys > /tmp/signal-derive-keys.json
```

Other modes include `sha256`, `hmac-sha256`, `hkdf-sha256`, `tls-expand-label`,
`tls-handshake-secrets`, `tls-application-secrets`, `tls-finished`,
`tls-update-traffic`, `tls-verify-finished`, `tls-verify-finished-transcript`,
`tls-retry-transcript-hash`, `aes128-block`, `aes256-block`,
`aes128-decrypt-block`, `aes256-decrypt-block`, `gcm-seal`, `gcm-open`,
`tls-seal-record`, `tls-open-inner`, `tls-parse-inner`, `tls-open-record`,
`signal-cbc-encrypt`, `signal-cbc-open`, `signal-message-mac`, `signal-open-span`, `signal-clamp`,
`signal-service-id`, `signal-service-id-kind`, `signal-ciphertext-message-type`,
`tls-nonce`, `tls-inner`, `tls-header`, and `authenticated-release`.
Each artifact describes its input/output order, including mixed input widths.
Exporter resource caps are stricter than some specification limits.
`tls-open-inner` assumes the caller has checked the canonical public header;
its successful shared output still needs inner type/padding validation before
the application can consume it. `tls-open-record` performs header authentication,
type and padding validation together. Its output is a secret acceptance byte,
type, two-byte content length and fixed-size buffer; rejection zeros every byte.
It still needs connection-state policy and negotiated limits. Finished verifiers
return a secret acceptance mask and check the complete 36-byte handshake message.
They require a correctly assembled transcript and do not replace certificate
or CertificateVerify validation.

Prepare the backend, then run checks sequentially because they share paths:

```sh
python3 scripts/prepare_backend.py
python3 -m unittest discover -s tests -p test_lean_adapter.py -v
python3 scripts/check_lean_artifacts.py
python3 scripts/check_lean_crypto.py
python3 scripts/check_lean_aes.py
python3 scripts/check_lean_gcm.py
python3 scripts/check_lean_tls_records.py
python3 scripts/check_lean_tls_receive.py
python3 scripts/check_lean_tls_handshake.py
python3 scripts/check_lean_signal.py
python3 scripts/check_lean_signal_metadata.py
python3 scripts/check_lean_signal_receive.py
python3 SignalReference/check.py
```

Backend setup needs Python 3.12+, curl, make, a C++20 compiler, GMP, libsodium,
Boost, and OpenSSL 3 development packages. It installs no system packages;
the independent AES/GCM test oracles also use Python's `cryptography` package.
`--offline` requires cached archives. Signal reference checking additionally
needs the pinned Aeneas checkout and matching mathlib package cache; its script
accepts `--packages-dir` for a matching existing cache.

Artifact suites compare outputs and compile MP-SPDZ bytecode, without native
MPC execution. Reports and logs under `benchmarks/results/` distinguish clear
evaluation, bytecode compilation and native execution.

## Experimental reference harness

`tls_mpc/*.py`, `programs/protocol.mpc`, and `tests/test_protocols.py` are earlier
unverified references, not the requested Lean implementation. They cover
older receive-side CBC and inner-record parsing experiments. Their tests
and costs must not be attributed to the Lean implementation. The composed
fixture places a Signal message inside TLS; it is not a valid server request.

The native harness has built MP-SPDZ's five-party malicious CCD binary backend
and three-party malicious replicated binary backend. The latter tolerates one
corrupt party and does not meet the two-colluder target. Neither has executed
successfully here. On a host allowing local sockets:

```sh
python3 scripts/check_kernels.py
python3 scripts/run_benchmark.py --backend shamir5 --kernel aes128 --batch 64
python3 scripts/run_benchmark.py --backend rep3 --kernel aes128 --batch 64
```

The AIG export is a correctness baseline. XOR recovery reduces the adapter's
AND count, while general bit-vector addition and circuit depth still need work.
Static counts and compiler VM rounds do not establish WAN performance.
Measure complete sends, fanout, preprocessing, authenticated checks, responses
and durable state writes under identical security settings. Prepared message
keys must be consumed once and invalidated by relevant ratchet changes.

The persistent mixed worker now builds with the Lean RPC controller, public-stage
agreement, leader TCP transport, and a pinned public-length circuit compiler.
Native network execution, handshake-state erasure/retirement, native application
record operations and durable epoch/sequence management remain. Deployment also needs
complete Signal transitions, identifier-private server requests, native share
persistence and refresh, rollback-safe state commits, interoperability checks,
and measured malicious MPC execution over WAN links.

`TlsMpc/TlsApplication.lean` now provides the application controller over opaque
shared handles. Its public policy reserves sequence numbers before cryptographic
effects, limits sending key use, handles requested/crossed KeyUpdates and
half-close, and makes failures terminal. A separate receive lock permits sends
while waiting for incoming bytes. Both handshake and application controllers
catch protocol errors and underlying I/O exceptions; cleanup failure is reported
explicitly. The policy has kernel-checked lemmas, but the effectful controller
itself is tested rather than formally refined.

Run `python3 scripts/check_tls_application_controller.py` for the 305 boundary
checks and mock-handle sequencing, concurrency and error-path fixtures. These
checks execute no cryptography or MPC. The application RPC binding and native
dispatch methods now exist, but application execution remains disabled until
real VM retirement is implemented. The worker still rejects retirement and
traffic-key erasure instead of claiming success. Application kernel provisioning,
shared Signal/H2 buffer integration and handle retirement remain unfinished.
Worker-owned share buffers now overwrite their values on destruction,
replacement and abort. This does not erase retained VM/preprocessing copies or
random-generator history; see `handshake_backend/ERASURE_REVIEW.txt` for the
source trace and remaining requirements.

The application RPC uses opaque buffer IDs, never plaintext or private lengths.
Native code keeps received length/content shared, preserves original inputs on
parser DEFER, and matches each send to its reserved ciphertext. Received buffers
cannot be sent as fixed-length payloads without private stream processing.
Application receives use nonblocking record polling; a pipe mutex prevents
concurrent requests from mixing responses. Public pipe fixtures check 32
concurrent exchanges and a pending receive that allows a send to complete.
These are local transport tests, not five-party scheduling or MPC execution.

`TlsPostHandshake.lean` supplies shared streaming framing for ignored session
tickets and KeyUpdate, rejects interleaved record types and bytes following a
KeyUpdate in the same record, and handles close/user-canceled/error alerts.
Only its event and request bytes may be opened. The 11-byte parser state,
application length and payload stay shared. Compiler proofs cover both the
parser and its composition with authenticated AES-GCM record opening; a
separate theorem shows the public application event is payload-independent.
`scripts/check_tls_post_handshake.py` checks numeric artifacts against buffered
framing and AES-GCM oracles. `scripts/compile_tls_post_handshake.py` compiles
isolated MP-SPDZ functions without changing the live worker's pins. The general
streaming parser is expensive (3,280 compiler VM rounds for a 64-byte buffer).
`TlsApplicationRoute.lean` now provides a first-stage circuit that bypasses
that scan for ordinary application and alert records, with a proof of exact
agreement for every non-handshake record. At capacity 64 it compiles to 1,585
bit triples and 72 VM rounds, excluding record decryption. Event 5 means the
caller must run the complete parser on the **original shared input** and
discard the routing result. Only event/request bytes may be opened; this
dispatch reveals an authenticated handshake record's type, not its body or
length. `scripts/check_tls_application_route.py` checks 378 numeric cases and
six chained records. Native binding remains pending; these counts are not
measured WAN latency.

The pinned server/client transport review is in
`handshake_backend/SIGNAL_SERVER_REVIEW.txt`. The old relay uses HTTP/1.1
WebSockets, while pinned libsignal v0.106.1 selects the HTTP/2 chat endpoint.
Private HTTP/2 framing remains part of the integration work; no production
TLS record trace has been captured here.

## Full initial TLS handshake checks

The supported profile is TLS 1.3 with X25519, AES-128-GCM/SHA-256 and server
certificate authentication. Server certificates and authentication transcripts
are public by explicit policy. The client handles HelloRetryRequest, fragmented
handshake records, compatibility CCS, and an initial client-certificate request
with an empty response. Resumption, 0-RTT and post-handshake processing are outside
this initial-handshake profile.

`TlsMpc/TlsClient.lean` runs over opaque secret handles. `HandshakeFixture.lean`
uses public test values only and interoperates with real OpenSSL memory-BIO
servers. Its 25 cases include six application-controller cases with four key
rotations in each direction, requested and crossed updates, fragmented echoed
data, both close orders, corrupt-tag/replay rejection and final cleanup. Two
cases negotiate `h2`; they check TLS behavior, not HTTP/2 framing. All crypto
and private parsing in these fixtures execute the Lean specifications on public
test values, rather than the native MPC backend.
`handshake_backend/session.py` composes Lean artifacts inside one mixed
VM; it is a compiler-side kernel interface, not yet a live transport bridge.
See `handshake_backend/SECURITY.txt` for disclosure and runtime obligations.

```
python3 scripts/check_full_handshake.py
python3 scripts/check_mixed_handshake.py
python3 scripts/check_handshake_release.py
python3 scripts/check_lean_proofs.py
```

Reports under `benchmarks/results/lean-*-handshake-checks.json` and
`lean-handshake-release-checks.json` distinguish clear fixtures from native MPC.
No WAN throughput or live five-party execution is claimed.

The native worker uses `ShapeCompiler.h` to prepare missing handshake receive
circuits for public AES-GCM wire lengths 22..16406. `scripts/prepare_tls_shape.py` only
orchestrates the Lean exporter and MP-SPDZ compiler; protocol computations remain
in Lean. The compiler process receives a length, with player sockets and RPC
descriptors closed. Every party verifies its boot-pinned local toolchain and
agrees the generated descriptor/schedule/bytecode manifest before registration.
Existing program hashes cannot be replaced. Cache paths and compiler inputs are
independent of checkout location; the Python interpreter is pinned because
different Python versions can produce different bytecode.

Provision the toolchain offline in the worker's MP-SPDZ directory using:

```sh
python3 scripts/prepare_tls_shape.py --install .deps/sharing-refresh/MP-SPDZ --emitter .lake/build/bin/emit_mpc
```

Include `Worker-Public/tls-shape-compiler` and
`Worker-Public/tls-shape-toolchain.json` when generating the boot manifest with
`scripts/pin_tls_worker.py`. A toolchain upgrade requires a fresh cache; cache
receipts deliberately reject a changed toolchain. This compiler and the native
runtime remain unverified. Public shape checks are separate from MPC execution:

```sh
python3 scripts/check_tls_shape_cache.py
python3 scripts/check_tls_shape_reproducibility.py
```

TLS record opening now uses a balanced Lean padding/type parser, proved equal
to the original specification for every input. Its 1024-byte parser has 27 AND
layers, down from 1040, at the cost of more gates. The compiler theorem and
rejection behavior are retained. `scripts/check_tls_parallel_inner.py` checks
exported artifacts and records this depth comparison; these are circuit
measurements, not MPC throughput measurements.

`backend_adapter/aig_packed.py` is an opt-in unverified adapter that batches
independent gates into at most 64 lanes, grouped by nonlinear depth. The public
shape compiler uses it; existing boot kernels retain their pinned bytecode.
It is checked against the original numeric AIG evaluator and native local-share
packing primitives. Real multiplication/preprocessing over the network is
still untested. The baseline 1024-byte receive compilation timed out; packed
compilation succeeded, and splitting at nonlinear-depth boundaries reduced
that measured compile from 317 seconds to 208 seconds. Those measurements used
the former sequential parser. The balanced 1024-byte full receive build also
succeeded: 184 VM rounds instead of 1176, with about 1.43 million bit triples
instead of 1.41 million. It took 230 seconds to compile, so cold-cache latency
and large-record compilation still need work.
