# Candidate actual CTR conversion and exhaustion-prefix proof

Pinned libsignal904c8dc uses aes0.9.1, ctr0.10.1 with zeroize, cipher0.5.2,
and protocol `aes_256_ctr_encrypt`: zero nonce16, `Ctr32BE<Aes256>`, then
`apply_keystream`. The authoritative `remaining_pinned_v1` extraction observes
the actual zeroize compiler flag and checks ctr's registry checksum/source files
against Cargo.lock. The proof checker additionally checks caller/manifest/lock
bytes against the pinned release archive. No Rust or generated bodies are edited.

`ConversionFinal` selects only ordered type roots7/8 and actual function27
(`u32 -> usize TryFrom`) from that LLBC. Every declaration/body/signature stays
unchanged; restoring the ordered roots exactly recovers the original. This new
selection is candidate provenance requiring independent review. No array model,
Result::ok/Drop model, cryptographic stub or validity assumption is imported by
the actual conversion theorem. Official pinned Aeneas scalar/Result semantics,
Charon/Rust/Aeneas translation remain the trusted functional boundary.

Eight kernel endpoints use only foundational axioms. The actual conversion
always returns Ok and preserves the unsigned value. The *authored arithmetic
prefix* of `remaining()` (MAX32-counter followed by that actual conversion)
therefore never reaches Err; remaining0 iff counterMAX32. It checks the SS
message8192-byte/512-block bound from counter0. These prefix theorems are NOT a
full actual remaining/CTR/AES/HMAC source refinement. In particular, no generic
owned-Drop behavior is assumed; proving the actual complete remaining function
or a justified success-only specialization remains required.

The actual library count is MAX32-counter, not unrestricted 128-bit increment.
At counterMAX32 remaining is0; its stream-wrapper exhaustion/check semantics
must be composed before claiming encryption refinement. Actual nonce init,
big-endian current/next block, AES invocation/key initialization, stream buffering
and HMAC/SHA wrappers remain open. The zero-nonce caller profile must be proved
through actual `from_nonce`, not inferred from the prefix's conditional counter0.

Preserved diagnostics: CLI features cannot be specified for a dependency package;
Charon impl selectors reject explicit trait generics; unchanged hybrid-array GAT
analysis blocks the full nonce type; included generic Result::ok fails Aeneas's
owned Err/drop analysis. The parser's unaccepted drop translator is not used.
Older quiet-log inventories did not observe the cfg flag (their false field is
not evidence of a different feature); the verbose pinned profile is authoritative.
No partial generated module containing missing-trait placeholders is imported.

Reproduce in the pinned local environment:

```
python3 SignalReference/CtrReferenceV1Work/extract.py remaining --candidate remaining_pinned_v1 --opaque-array --include-core --opaque-core-ok
python3 SignalReference/CtrReferenceV1Work/select_conversion.py
python3 SignalReference/CtrReferenceV1Work/check_conversion.py
```

Extraction refuses to overwrite prior candidates. Large LLBC and Build products
remain ignored; exact commands/input/output/body hashes and proof sources are
retained. This scope does not change production circuits or execute MPC/network.
