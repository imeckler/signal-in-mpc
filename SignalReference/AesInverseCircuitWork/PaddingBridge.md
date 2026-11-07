# Receive-result composition

`PaddingBridge.lean` proves that `TlsMpc.Signal.OpenResult.finish` encodes the
result of the actual Aeneas-translated `block-padding` 0.4.2 strict
`Pkcs7::raw_unpad` operation. It imports the accepted canonical extraction and
proofs; it does not introduce a Rust replacement or a padding model.

The domain is an arbitrary list of leading bytes followed by a 16-byte final
block, with authentication represented by the secret mask 0 or 255. This
includes every public number of complete leading CBC blocks. Every possible
final-block byte value is covered, including invalid padding counts and
nonuniform suffixes. The existing Rust reference result distinguishes accepted
bytes from its inner padding error, and the composition preserves that result.

The output always has `9 + candidate.length` bytes: one acceptance byte,
eight big-endian retained-length bytes, then a candidate-sized plaintext area.
On acceptance, the leading bytes and retained final bytes are followed by
zeros. On either rejection, every output byte is zero. The circuit keeps these
fields secret; it does not reveal acceptance or retained length.

Import `AesInverseCircuitWork.LengthEncoding`. The main theorems are in
`LibSignalReference.Proofs.OpenResult`:

- `finish_reference`: successful evaluation of the actual Rust operation and
  exact equality of the receive encoding for either authentication mask.
- `finish_reference_length`: fixed output size for every final-block value.
- `finish_reject_reference`: an actual Rust padding error zeros every output
  byte for either authentication mask.
- `finish_refines_artifact`: every numeric compiled output bit equals the
  encoding of the actual Rust result, for every matching secret assignment.
- `finish_retained_length`: accepted output decodes to the exact retained
  length, assuming the public candidate length is less than `2^64`.

`LengthEncoding.lean` proves eight-byte big-endian encoding is lossless below
`2^64`; it also derives the retained final-block bound from the actual Rust
operation. These are composition lemmas, not additional cryptographic or
protocol-security claims.

Run `python3 SignalReference/AesInverseCircuitWork/check_padding.py` to rebuild
the selected generated reference, canonical padding proofs, and this bridge,
then audit its 13 endpoints. `padding-proof-check.json` records source hashes,
the accepted reference manifest and all theorem assumptions. The permitted
foundational assumptions are `propext`, `Classical.choice`, and `Quot.sound`.
The inverse-AES fixture report remains separate and unchanged.

This result assumes a supplied authentication mask; it does not establish how
that mask was computed. Equivalence of the complete RustCrypto CBC/decryption
wrapper remains pending. The accepted extraction and official standard-library
models remain trusted, as do native serialization and backend execution.
