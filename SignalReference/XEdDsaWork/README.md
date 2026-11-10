# Shared XEdDSA stages

This work implements the computational stages of the pinned Signal XEdDSA
verifier in Lean and numeric Boolean/Curve25519-field artifacts. It does **not**
connect them to PQXDH, implement identity trust or signed-prekey bundle policy,
or claim actual Aeneas refinement or a native MPC execution.

The six modules are `TlsMpc/Signal/XEdDsa{,Field,Sha512,Scalar,Challenge,Binding}.lean`.
They cover exact signature byte preprocessing, Montgomery-to-Edwards recovery,
complete extended-coordinate addition, fixed-loop `[s]B - [h]A`, SHA-512,
512-bit little-endian reduction modulo the Edwards subgroup order, signature-sign
binding, compressed point comparison, and the final internal conjunction.
No operation reveals a value. `adapter.py` routes shared values through those
stages without a secret-dependent host branch or trusted validation Boolean.
Its private conversion interface is abstract; it is exercised only with public
canonical arithmetic here. Five parties, two malicious parties, statistical
security128 and abort remain requirements, **not a tested runtime claim**.

## Checked scope

* `report.json`: 22 kernel-checked theorem endpoints, 1,280 scalar-envelope/length
  numeric lanes, 180 recovery cases, 48 double-scalar cases, and 103 comparisons
  against the actual libsignal verifier. This original staged test uses native
  challenge hashes as an explicit boundary.
* `challenge-report.json`: 29 additional theorem endpoints; 64 numeric SHA-512
  lanes spanning padding boundaries and the 1,633-byte Kyber-key domain; 56
  modulo-order lanes; all 103 verifier fixture results reproduced with numeric
  hashing/reduction (92 full crypto paths and 11 public/secret early rejections).
  The native-hash boundary is absent in this second report.
* `binding-report.json`: 11 additional endpoints and 28 complete executions of
  the branch-free adapter, 252 numeric stage calls. Every stage executes even
  when a secret check fails. The tests include valid/tampered signatures,
  malformed/noncanonical Montgomery encodings, sign and scalar high bits,
  zero/small-order points and the `x=0, requested sign1` case.

The 62 audited endpoints use only the standard foundational Lean axioms.
The proofs establish symbolic/concrete/numeric-compiler agreement with the Lean
formulas; scalar reduction additionally proves the exact mathematical integer
and output-byte specification. These are **not** a proof of the Edwards group
laws, cryptographic security, actual Rust source equality, or the full mixed
adapter/conversion composition. The actual-source evidence is native public
fixture differential testing against unchanged pinned implementations.

## Exact reference behavior

`source-provenance.json` verifies existing accepted source pins and all55 oracle
dependencies against libsignal commit `904c8dc8216073b078a5f2f5090e3da8382e6a92`
(`v0.106.1`) and its Cargo.lock. The oracle calls the actual `libsignal-core`
public verifier and signer, and actual `curve25519-dalek5.0.0` and `sha2 0.11.0`
public APIs. No computational Rust source is copied into a replacement verifier
or altered. The installed `nightly-2025-09-24` builds it offline with
`--ignore-rust-version` because libsignal declares a newer MSRV; the exact
compiler and flags are recorded.

The actual verifier clears the sign bit in the last signature byte and requires
only `s < 2^253`, then reduces modulo `ell`. It does not require canonical
`s < ell`: all nine `S + ell` signatures in these fixtures verify successfully.
The Montgomery decoder masks bit255 and reduces modulo `2^255-19`. It rejects
`u=-1` and twist points while accepting some small-order points. The implementation
preserves those behaviors, including sign0 compression when the recovered x is0.
This work does not add a new canonicality or subgroup policy.

The actual prekey-bundle caller additionally checks identity trust and verifies
both signatures over **serialized typed** public keys. This adapter verifies an
exact raw-key32/signature64/message input; it does not establish that the message
came from the same parsed bundle as any downstream DH/KEM inputs.

## Artifact cost

Current field exports validate and execute each output independently, duplicating
shared subexpressions across output artifacts. Recovery uses `[2548,2033,509]`
field multiplications; signed double-scalar outputs use `[12723,12723]`.
The complete current adapter therefore executes30,536 field multiplications per
signature, before conversion. A shared multi-output artifact can reduce that
cost, but is not claimed here.

Boolean counts after the existing adapter's XOR recovery:

| Stage | AND | XOR |
| --- | ---: | ---: |
| Sign binding | 256 | 1 |
| SHA512,97-byte domain (typed DH prekey) | 149,047 | 137,740 |
| SHA512,1633-byte domain (typed Kyber1024 key) | 2,009,169 | 1,850,128 |
| 512-bit modulo-ell reduction | 476,462 | 99,194 |
| Final validity and compressed-R check | 513 | 256 |

These are circuit counts, not native runtime, bandwidth or throughput measurements.
All runtime keys, message bytes, signatures, coordinates, digests and statuses
remain shared. Shape lengths are public; hash export is capped at2048 bytes.

## Reproduce

From the repository root:

```sh
python3 SignalReference/XEdDsaWork/provenance.py
python3 SignalReference/XEdDsaWork/check.py
python3 SignalReference/XEdDsaWork/check_challenge.py
python3 SignalReference/XEdDsaWork/check_binding.py
```

`check.py` builds the isolated exporter and offline actual-source oracle.
The later scripts reuse those builds and exported hash/field artifacts.
Numeric artifacts under `Artifacts/signal-*.json` are regenerable and ignored;
public fixtures, proofs, source hashes and reports are retained. The standalone
Lean exporter is `SignalReference/XEdDsaExport.lean`; its isolated executable is
built by `lake build` in this directory. No root CLI, main library imports,
production backend, accepted reference tree, native receipt, or frozen Tinier
candidate is changed by this work.
