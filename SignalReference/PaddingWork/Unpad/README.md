This is the bounded receive-side counterpart to the actual PKCS7 padding
reference. The selected functions are the unmodified locked `block-padding`
0.4.2 `Pkcs7::raw_unpad`, its inherent `unpad` implementation and inequality
closure, and the actual Rust slice iterator `any` implementation that it calls.
The libsignal revision and dependency pins remain those in `../../pins.json`.

`Circuit.lean` is a standalone Std-only implementation intended for
`TlsMpc/Signal/Unpad.lean`. It takes sixteen secret bytes and returns eighteen
secret bytes: an acceptance mask (`255` or `0`), the retained byte length
(`0`–`15`), and sixteen retained bytes with a zero suffix. Rejection produces
eighteen zero bytes. Its sixteen candidate counts and all list indices are
public. It uses byte equality masks and conditional selection; no branch or
index depends on a secret byte. No result component is opened by this module.

`Bridge.lean::unpad_refines_artifact` proves every numeric circuit output bit
equals this representation of the actual translated `raw_unpad` result for
every 16-byte block. `encoded_result_injective` proves the representation is
lossless within the stated result-size bound. These are universal Lean proofs,
not tests over sample padding strings. `Proofs.lean::unpad_spec16` also proves
the auxiliary function's behavior with either value of its `strict` parameter;
the circuit implements the public `raw_unpad` wrapper, which always uses
`strict=true`.

Within this 16-byte domain, the actual function returns `Err(())` when the last
byte is zero, exceeds sixteen, or disagrees with any required preceding
padding byte. Otherwise it returns the prefix of length `16 - last_byte`.
All these outcomes are included in the circuit theorem. Runtime panic cases
for empty or oversized public input slices are outside this circuit's domain.
Inverse AES, complete CBC decryption, whole-message wrappers, and composition
with authentication and persistent state are still separate obligations.

The default distributed Rust standard library had already inlined iterator
`next` into raw-pointer operations in its optimized MIR. Selecting the real
`any` body therefore initially failed Aeneas. The successful extraction uses
an isolated full-MIR sysroot built from the official matching Rust
`nightly-2026-08-18` sources with the official matching Miri component. No Rust
or tool source was patched. In this MIR, the actual `any` loop retains its
`next` call, which maps to Aeneas's existing slice-iterator standard model.
The returned iterator state is discarded by the actual unpad operation; the
loop lemma proves precisely the Boolean result needed by that operation.

The complete provenance is recorded in `sysroot-provenance.json`, including
official archive hashes, selected Rust source hashes, and generated sysroot
artifact hashes. `review.json` separates the computational standard iterator
model from thirty unused opaque type declarations pulled in by generic
Iterator signatures and panic formatting. The generated Lean has only two
type aliases and nine function, loop, and trait definitions; it has no external
templates. No missing cryptographic or iterator operation is assumed.

Reproduce the successful extraction with:

```sh
python3 SignalReference/PaddingWork/Unpad/build_sysroot.py
python3 SignalReference/PaddingWork/Unpad/extract_unpad.py RawSliceIterator --full-mir
python3 SignalReference/PaddingWork/Unpad/check.py --packages-dir /path/to/matching/.lake/packages
```

`build_sysroot.py` expects the official Miri archive at
`miri-nightly-2026-08-18.tar.xz`, downloaded from
`https://static.rust-lang.org/dist/2026-08-18/miri-nightly-aarch64-apple-darwin.tar.xz`.
Its pinned SHA-256 is
`912904e20c37ffe461264ac7c005bc56b778d7a58fcbb29deed3445912283d21`.
All installations, Cargo caches, build outputs, and sysroot files stay inside
this directory. `--full-mir` uses a separate Cargo target directory to avoid
mixing dependencies built against different core libraries.

The checker validates original source and archive hashes, unchanged Aeneas
standard models, matching extraction tools, exact selected-function inventories
and exclusions, generated-file hashes, matching Lean/mathlib versions, and all
twelve proof endpoints. `proof-check.json` records the results. The trusted
reference boundary remains faithful Charon/Aeneas translation plus the listed
existing standard models. The accepted theorem dependencies contain only
Lean's usual `propext`, `Classical.choice`, and `Quot.sound`.

The generated `block-padding` reference uses the MIT-or-Apache-2.0 licenses
preserved in `../licenses/`. The generated iterator loop derives from the Rust
standard library at commit `8fa1c96cfd489e4c27654c144ae871ce2c4db6c6`, also
MIT-or-Apache-2.0; its license texts are preserved in `licenses/`.
