# EMP authenticated Boolean + native field candidate

Status: implementation plan and checked public parameter model. **No EMP↔field bridge has executed yet. No deployment/production gate is enabled.** The user selected two computing parties A/B, tolerating one malicious party with abort. The same A/B identities own both engines; a storage quorum does not restore compute t2. Sharing refresh remains paused. Existing MP/legacy receipts and historical account heads remain immutable references.

## Pins and current evidence

| component | exact revision / setting |
|---|---|
| current EMP AG2PC | `a245ca0f67abaf2d48c711e3c050ce961e60ad29` |
| emp-tool | `339bde8479842c88d115cec16ffca90a4c050c3f` |
| emp-ot | `5072bdab546c89a24be3368a7ce2bab1cdefec1f` |
| native MASCOT candidate | MP-SPDZ `113c4e47dd94bca9ecab029d2f0abe649bea5c52`, p=2^255−19 |
| native checked OT | libOTe `fe6b2ff82a976a5332b3a2efe325831588b1324a`, cryptoTools `f70175e0cbd36b808475c0c1bbf585304e43d3d0` |
| parameters | computational target128; configured statistical40; no S128 claim |

Archive hashes, dependency closure, diagnostic overlays and environment are recorded in [the comparison work](../../../benchmarks/TwoPartyComparisonWork/README.md). Current EMP explicitly warns of an **unaudited AI-assisted rewrite**. Our current build has namespace-only compatibility qualification and byte counters, not a security audit. SoftSpoken<4> malicious mode is the EMP default; native MASCOT uses its checked SoftSpoken path. No KOS/insecure fallback or guard deletion.

`4d2d329` demonstrates imported AES/SHA gates, authenticated-result checkpoint retention, Bob-only output and actual c_gamma rejection after local key corruption. It does not yet demonstrate two nonlinear replays consuming returned state. `0e15ff1` demonstrates actual native X25519 and MASCOT↔Tinier conversion controls; **those daBits are not an EMP bridge**. Pure Boolean X25519 optimization is superseded; no such implementation/export was started.

## Selected bridge route

Use the published daBit construction of Rotaru–Wood, *MArBled Circuits*, [2019/207](https://eprint.iacr.org/2019/207), §4.1/Figs5–6, through two active-MPC interfaces. Each party privately inputs fresh bit contributions in both engines. After both input sets are fixed, cut-and-choose checks a random subset; the remainder is combined and randomly bucketed. Authenticated XOR-difference openings check consistency. Only one pair per approved bucket survives, after both engines' checks. No raw MAC-key reinterpretation is involved.

The read full-text copy came from [CORE](https://fileserver-az.core.ac.uk/download/579865063.pdf), SHA256 `3e7ef95912e9b5a68e09e367808eca5517b8c6261f3f73f792aa1250a0730583`. Direct eprint PDF retrieval returned403; byte identity with that endpoint is not asserted. MP-SPDZ documents this family in README “Classic daBits”; its low-level `ProtocolSetup`/`ProtocolSet` API supplies the native field operations. We instantiate the paper's restricted Boolean operations with EMP authenticated logical bits, **not** with casts of garbled labels into field shares. This instantiation/composition remains an unmechanized security obligation.

For ell kept pairs, bucket B and cut factor C, there are m=C·B·ell candidates per party. A fixed set of c=B·t inconsistent positions can escape only by surviving the cut and filling whole retained buckets. The exact counting bound used here is:

`Pr[accept bad] <= choose(ell,t) / choose(m,B*t)`.

The parameter checker considers every t=1..ell, additionally requiring a conservative output-bucket union on the published sufficient expression. It does not infer a whole-deployment lifetime bound. `parameter-report.json` is **public model evidence only**:

| kept ell | B | C | candidates/party | exact worst-bound bits |
|---:|---:|---:|---:|---:|
|1|41|2|82|78.49|
|16|8|2|256|44.54|
|64|6|2|768|41.99|
|256|5|2|2560|41.70|

Boolean inputs are bits by type. Field contributions may be malicious non-bits: cut/range checks and the bucket test must reject them, rather than coerce them to low bits. For odd p, XOR-polynomial `x+y−2xy` with one valid bit and one non-bit remains a non-bit. Range/consistency checks and native/EMP authentication checks precede release of **any** kept pair. Random challenges use fresh commit/open coins after input fixation and unbiased sampling; no signed-modulo shuffle shortcut. Padding/trimming cannot change the checked population after the challenge.

## Value and operation invariants

Opaque `AuthBool` and `AuthField` handles own authenticated backend storage and carry session, epoch and generation. A private constructor creates `VerifiedDaBitBatch` only after actual checks over its exact candidate handles. An externally supplied flag, nonzero digest or prior-root validity cannot authorize it. MAC keys remain in their own engines.

* Bit→field: consume a verified pair(rE,rF), authenticate/open only d=b XOR rE in EMP, then compute rF when d=0 and1−rF when d=1 using native authenticated arithmetic. Public d is a uniform mask, not b.
* Field→bits: consume255 verified pairs, form r=Σ2^i·ri in both domains, and privately check r<p. Reject/burn on failure. Open c=x−r in native field MPC **with MAC checks before use**. Import only its canonical public32-byte encoding. EMP computes (r+c) mod p; it must retain/check the final carry rather than silently truncate it. On acceptance r is exactly uniform Fp, so c hides x.
* Scalar-bit vectors and coordinate field elements are distinct types. Existing wire format is32 little-endian bytes with MSB-first bits within each byte; global bit i is wire index `8*(i//8)+7−i%8`. X25519 scalar clamping stays in the existing FieldDag; RFC7748 point high-bit masking is explicit.

Local share/MAC mutation cannot become a new valid value without defeating a backend check or the daBit checker. No unmasked scalar, DH result, traffic key or session key is reconstructed at a host. Only sacrificed preprocessing values, uniform masks and explicit validity predicates may open. Masked public values remain quarantined until their checks finish. A failure poisons both engines and all pending derived handles; no partial success or retirement acknowledgment.

Each operation binds version, joint fresh session nonce, A/B identity mapping, both source/program closures, p/encoding, parameters, epoch, monotone operation counter, direction and consumed-mask range. Counters/ranges are burned before the first opening and never rolled back. Cross-session/stale/repeated handles reject before execution. One A/B process owns both local engines; same-process coupling is the initial local-fixture assumption. Remote deployment additionally needs authenticated channel/identity binding across both transports; raw loopback TCP is not that evidence.

## Implementation order

1. **Nonlinear EMP continuation:** two imported AES calls consuming authenticated returned data across checkpoint; tamper retained state/key and reject before output. Keep legacy/smoke programs immutable.
2. **Tiny legitimate kernels:** append independent secret dummy ANDs when actual count is1..1023. Keep dummy outputs live through all checks, then securely discard them. Actual checked AND count must be at least1024; never merely change a sizing argument or bypass the guard. Zero-AND linear chunks remain zero-AND. Prove original-output equivalence and test actual preprocessing counts/rejection.
3. **Two opaque engines:** EMP authenticated-wire execution and MP-SPDZ's supported low-level native Fp API in separate translation units behind typed handles. Avoid vendor namespace collisions and mixed/no-mixed template ODR mismatches; use a distinct supported field counter/type. One serialized owner per native protocol instance. No unsafe concurrent calls into one VM/protocol.
4. **RW daBit generation + conversions:** start ell16/64, actual secret inputs, fresh candidate/check frames; then256 for canonical field conversion. Test wrong contribution, non-bit, MAC corruption, wrong session/counter and mask reuse. Measure generated/consumed/discarded resources, both engines and all channels, cold/setup and repeated calls. Preserve failed receipts.
5. **Native field operation + X25519:** unchanged exported FieldDag, actual private scalar/point inputs, checked conversion both ways and low-order rejection. Open equality bits only in fixtures. Reuse no supplied agreements. Four curve computations and fresh private ephemeral/mask randomness remain in the producer accounting.
6. **Nonempty established Signal + TLS:** unchanged pinned Boolean kernels, actual retained ratchet/SPQR state, Content/padding, sealed sender, fresh TLS handshake, repeated records, KeyUpdate, WebSocket/private response/correlation and actual Rust recipient. No default/blanket gate opening. Then sustained batching/pipelining and bytes/message; target27.78 messages/s is currently unmet.

Backend-independent Lean obligations are separate: candidate/bucket semantics and exact finite bounds; bit↔Fp value preservation; accepted-mask uniformity/range; canonical modulo addition/encoding; circuit compiler agreement and dummy-padding output equivalence. Successful vectors do not prove the malicious backend/composition assumptions. Both backend authentication/COT errors and per-batch daBit errors require explicit composition accounting.

## Mandatory remaining system gaps

* Generic authenticated dynamic state ownership, checkpoint pruning, fresh randomness renewal and failure cancellation/join/secret-storage wiping. Current EMP fatal `_Exit` paths do not establish erasure or safe caught-failure retirement.
* Full application proof/caller refinements: private parser/schema/control semantics, authenticated response correlation, transport/ratchet commit order and all legitimate private lengths. Component passes are not a finished application.
* Genuine fresh PQXDH/prekey initialization, private bundle/trust/signature validation, exact Kyber/ML-KEM tags, all computed DH/KEM agreements, continuing SPQR negotiation beyond the initial two-send stage, receive/new-DH/skipped-key/epoch transitions. Existing prepared-state fixtures are not bootstrap evidence.
* Durable account/outbox/cursor transactions, restart/current-head authorization, anti-rollback and checked re-admission into **fresh** EMP/native sessions. Old5-party CCD archives cannot be relabeled as2-party authenticated state. A storage threshold does not increase this computation's corruption tolerance. Start a genuinely fresh isolated account/domain for new functional tests unless an authorized conversion is implemented.
* Scalable provenance/outbox lookup, multiplex ordering and pending/uncertain retransmission semantics; backend preprocessing must never be restored/reused after uncertain consumption.
* Full refinement/security/lifecycle review and representative sustained measurements. No production deployment or stronger statistical/mobile-corruption guarantee is authorized by selecting EMP.
