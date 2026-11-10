# Bounded prekey-bundle validation prefix

This work adds three Lean modules, `PreKeyWire`, `PreKeyBundle` and
`PreKeyValidation`, and an abstract shared adapter that computes **both** prekey
signatures through the frozen XEdDSA verifier. It does not implement identity
trust policy, session creation/persistence, private conversion, or production
PQXDH authorization. The frozen XEdDSA work is a dependency requiring its own
root acceptance; this checkpoint does not accept it on the root's behalf.

## Exact source scope

The reference is libsignal `v0.106.1`, commit
`904c8dc8216073b078a5f2f5090e3da8382e6a92`. The oracle links the unchanged actual
`libsignal-protocol` crate. All 177 dependency package identities/checksums match
its Cargo.lock. Both default features and the explicit `kyber768`/`mlkem1024`
feature profile are built offline. Cargo's MSRV gate is ignored for the installed
nightly; no computational Rust source or dependency manifest is replaced.

The actual `PreKeyBundleContent` constructor checks required fields in this order:
registration, device, signed ID, signed public key, signed signature, PQ ID,
PQ public key, PQ signature, identity. The shared presence slots follow the
Rust struct declaration order; `PreKeyBundle.required` implements the different
argument-evaluation order. Optional ID and public key are combined with `zip`:
a mismatch becomes `None`, with no new validation error. Full 32-bit registration
and prekey IDs are retained, including 0 and `0xffffffff`. Device IDs accept 1..127.

Raw key decoding is a separate boundary because the actual constructor already
accepts typed keys. EC tag 5 keys permit trailing bytes; reserialization retains
only tag 5 and the first 32 payload bytes. KEM public keys require exact lengths:
tag 7 / 1185 bytes when enabled, tag 8 / 1569, tag 10 / 1569 when enabled. KEM decoding
adds no coefficient validity check. The signature messages are the normalized
serialized keys **including their type tags**.

The actual `process_prekey_bundle` first asks the external identity store whether
this identity is trusted for `Direction::Sending`, then verifies the EC signed
prekey, then the PQ prekey. Only afterward does it load a session. The native
oracle calls that actual function and intentionally stops at `load_session` using
a fixture error. A reported prefix success means this sentinel was reached;
it is not a successful whole session initialization. No store writes occur.

## Shared composition and boundaries

`adapter.py` normalizes the same supplied identity and public keys that feed the
two signature checks. It returns the ordered prefix result and normalized
internal key candidates. All values remain shared; only lengths and feature
profiles control host branches. Both signatures execute even when trust is
rejected, preserving a fixed circuit trace rather than Rust's short-circuit
execution trace. Public malformed signature lengths use the frozen zero-result
length rejection. No caller supplies a signature-validity Boolean.

The external trust result is a distinct code:0 means `Ok(true)`,1 means
`Ok(false)`,2 means callback failure. The caller must bind it to the **canonical
serialized identity**, remote address and Sending direction. The adapter neither
calls an identity store nor implements TOFU, equality-based trust, or any other
trust policy. It does not treat cryptographic validity as identity authorization.

The constructor/validation result is20 shared bytes: status255/0, normalized
error class, optional-present0/1, registrationBE4, device1, optionalIDBE4,
signedIDBE4 and PQIDBE4. Failure zeros the optional flag and metadata. Codes 1..9
name the missing fields in the above order; 16 is untrusted identity, 17 is an
external trust error and 18 is signature validation failure. These normalize
error classes, not the full address/callback-error object. Individual decoder
errors remain separate. Local code 32 means a present raw key/device could not
establish the typed-input boundary; it is not a libsignal error or a claimed
combined raw-parser ordering. Missing slots' dummy bytes do not cause code 32.

Private field/byte conversion and stage orchestration inherit the explicit
unverified XEdDSA boundary. Required runtime security remains five parties,
two malicious parties, statistical128 and abort. There is no native MPC
execution, whole mixed-composition proof, actual Aeneas refinement, or root CLI
integration in this checkpoint.

## Checks and reproduction

`report.json` audits 28 kernel endpoints using only standard Lean axioms.
Theorems cover compiler agreement plus exact first-missing-field, optional-zip,
EC error and trust/signature precedence specifications. Actual-source/numeric
checks cover 1,025 EC lanes, 3,074 KEM lanes across both feature builds, 261 device
cases, 768 optional-slot lanes, all 2,048 constructor presence combinations and
2,304 prefix-selection lanes. The real protocol prefix is exercised in 36 cases,
including traced callback ordering. `composition-report.json` records 18 full
two-signature shared-stage compositions plus one explicit typed-boundary failure.
These include tag-domain mistakes, EC trailing bytes, missing slots with garbage
dummy data, ID boundary values, malformed signature lengths and trust precedence.

From the repository root:

```sh
python3 SignalReference/PreKeyWork/check.py
python3 SignalReference/PreKeyWork/check_composition.py
python3 SignalReference/PreKeyWork/provenance.py
python3 SignalReference/PreKeyWork/audit.py
```

The first script builds the isolated Lean exporter and both actual Rust oracle
profiles. The composition script reads frozen XEdDSA artifacts; additional
length profiles are generated only into this new work directory. `audit.py`
verifies all reports and the unchanged frozen XEdDSA manifest before writing
`completion.json`. Build/Bin/Artifacts outputs are regenerable and ignored.
No frozen XEdDSA source/report, accepted reference tree, root import/CLI,
production backend, Git state, or native fixture receipt is modified.
