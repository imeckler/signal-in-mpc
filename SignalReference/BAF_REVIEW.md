# Beneficial AI Foundation source review

Reviewed on 2026-11-06. These are source and dependency audits at the commits
below, not claims that the external repositories' full builds were reproduced.
The required result here remains **our MPC circuit equals the behavior of the
selected, faithfully translated libsignal operation**. A protocol-security proof
or a specification theorem with an opaque cryptographic hypothesis does not
establish that equality.

| Repository / review commit | Useful material | Compatibility and remaining boundary |
| --- | --- | --- |
| [libsignal-verify](https://github.com/Beneficial-AI-Foundation/libsignal-verify/tree/a69cb0119dd48477dd268bc011a5b3347985f71d) `a69cb011` | Aeneas extraction profiles; address conversions; PQXDH key splitting; HKDF specification | Lean 4.31.0, so a useful tooling example. Its upstream libsignal pin is `e8cc2dddd578859b4a029c9c94670b24ce2b616a`, not our `904c8dc…`. It changes Rust wrappers and keeps HMAC/HKDF/AES/ML-KEM opaque. Its PQXDH splitting theorem assumes the HKDF contract. |
| [SparsePostQuantumRatchet-verify](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/tree/1acabbc34dbc5cbd40362a62848b68fdbe80e033) `1acabbc3` | Extracted SPQR; GF(2^16), polynomial and serialization lemmas; successful state-machine transition refinements | Its upstream SPQR pin `06959b4708f9b7b1e94d0f8cc835f3958c077e94` exactly matches ours. All 39 upstream `src/*.rs` files compared recursively are byte-identical. Extraction nevertheless applies `translation-patches/`, and its Lean version is 4.35.0-rc4. Patch equivalence and external functions must be checked before accepting its extracted semantics. |
| [curve25519-dalek-fork](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork/tree/95b5831c63ff1c5f6287bd3a77569412a9afdbfb) `95b5831c` | Current dalek 5.0.0 verification; Montgomery arithmetic, scalar arithmetic and X25519 bridge lemmas | Lean 4.35.0. Its `montgomery.rs` and serial/u64 `scalar.rs` are byte-identical to our locked crate. Other files differ. `mul_clamped_spec` reports `RustAx.core`, `RustAx.subtle`, and `RustAx.zeroize`; those need a faithful model audit or discharge for our selected operation. No whole-crate compatibility claim. |
| [curve25519-dalek-lean-verify](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/tree/52cad87d054943c96c984d99d9ea9e5d043b0d65) `52cad87d` | Earlier scalar/field proof library | Lean 4.31.0, but dalek 4.2.0 rather than our 5.0.0; source modifications and generated-text adjustments exist. Its README redirects current development to `curve25519-dalek-fork`. |
| [secure-messaging](https://github.com/Beneficial-AI-Foundation/secure-messaging/tree/b45e0cb7393a1759e568f7e4e0e4fb8583c2bfca) `b45e0cb7` | Abstract CKA/SCKA and double/triple-ratchet constructions | Lean 4.35.0. Useful protocol models, but not a libsignal byte-level implementation reference. Abstract security proofs are outside the requested proof scope. |
| [spqr-sm-bridge](https://github.com/Beneficial-AI-Foundation/spqr-sm-bridge/tree/a7541a9a2d59522eb8021217c448f2272a06d834) `a7541a9a` | Connections between extracted SPQR and abstract messaging models | Lean 4.35.0; different dependency pins from the reviewed heads. Its README explicitly lists four `BridgeObligations` and three remaining axioms. It is not a completed whole-API equivalence result. |
| [libcrux-verify](https://github.com/Beneficial-AI-Foundation/libcrux-verify/tree/1f9c89853b4217deb41c85fea973e74b652e2186) `1f9c8985` | `specs/sha3/proofs/aeneas-lean` | Tree and selected files inspected, not the full archive. The Lean material found is generated hacspec SHA3, with Lean 4.30.0-rc2. This audit found no drop-in complete proof of our libcrux ML-KEM implementation. |

The SPQR state-machine results in
`Spqr/Specs/Braid/StateMachine/{Model,Relation,Run,Refinement}.lean` concern
successful transitions under their stated assumptions. They do not by
themselves establish totality, every failure result, serialization, or the
behavior of the actual libcrux cryptographic implementation. In particular,
`SrcTranslated/FunsExternal.lean` supplies handwritten ML-KEM models, and
`Spqr/Specs/Kdf/HkdfToSlice.lean` assumes the HKDF implementation link.

The [libsignal address theorem](https://github.com/Beneficial-AI-Foundation/libsignal-verify/blob/a69cb0119dd48477dd268bc011a5b3347985f71d/rust/Libsignal/Spec/Core/Address/ServiceIdFixedWidthBinary.lean)
is narrower than its prose: its actual proposition establishes the leading
ACI/PNI tag, not the sixteen-byte UUID tail or a parser round trip. We therefore
extract the complete encoder directly from our pinned source and prove the
whole output against our circuit. The external theorem is not accepted as a
whole-operation result.

One small reusable component is already integrated:
`External/BafRFC5869.lean` is the pure specification from SPQR's
`Spqr/Crypto/RFC5869.lean`, with only Lean module syntax and namespace changes.
`Proofs/BafHkdf.lean` instantiates its HMAC parameter with our concrete HMAC and
proves extract, expand, and numeric-circuit equalities. This is a reusable
specification bridge; it does **not** close the outstanding RustCrypto link and
does not add an opaque crypto assumption. Its exact copy/changes are recorded
in `Extraction/baf-rfc5869-port.json`. No further independent RFC proof work is
needed for the user's requested implementation-equivalence goal.

The most useful next reuse is to retarget SPQR's extracted serialization and
GF arithmetic to our exact source and compiler, and to reuse dalek field and
scalar bridge lemmas for the hybrid MPC path. Each selected operation still
needs the circuit-to-translated-code theorem, including its supported failures,
state and randomness. A separate Lean 4.35 proof package can host those newer
dependencies; upgrading the root compiler or silently replacing our reference
pin is unnecessary.

Licensing is per component: upstream libsignal/SPQR and their generated code
carry AGPL-3.0-only; the BAF handwritten RFC5869 file carries Apache-2.0;
dalek Rust is BSD-3-Clause; `secure-messaging` declares Apache-2.0 and the
bridge declares MIT. Preserve each selected file's notice when importing it.
No AES or GCM circuit-equivalence implementation suitable for replacing the
current TLS work was found in this reviewed material.
