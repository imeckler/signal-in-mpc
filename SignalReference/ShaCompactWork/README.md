The complete selected portable compact SHA-256 compression operation is now
proved against its actual translated Rust implementation and integrated into
the canonical reference package. The implementation is
`TlsMpc/Signal/ShaCompact.lean`; the generated reference is
`LibSignalReference/Generated/Sha256Compact`; the operation endpoint is
`LibSignalReference.Proofs.ShaCompact.compress_refines_artifact`.

It covers all eight u32 input state words, all sixteen u32 block words, every
round, the rolling message buffer, all bounds and final feed-forward. The
result remains secret. The root full-list SHA variant and the digest, buffering,
HMAC, HKDF and libsignal wrappers remain separate equivalence obligations.

`check.py --packages-dir PATH` audits fourteen operation/compiler endpoints and
compares exported artifacts against 45 public OpenSSL compression fixtures.
The public inputs include arbitrary initial states and nine padded messages
checked again with hashlib. `proof-check.json` records source and artifact
hashes, oracle version, assumptions and costs. Native MPC execution is not
claimed. The earlier standalone proof-development files remain here for
provenance; the checker and exporter now use canonical modules.

The extraction uses an additional explicitly trusted metadata filter,
`MetadataWork/trim_step_metadata.py`. It removes two unused opaque standard-
library Step fields and their declarations. Every retained computational body
is unchanged. An independent review and the rejection scan cover all retained
semantic JSON, globals and function pointers. The original graph is pinned in
full except for the ordering of the diagnostic short_names map; the actual
LLBC is not reordered by that comparison. This filtering is not mechanized.
Exact edits and provenance are in
`Extraction/sha256-compact-metadata/review.json`. Reproduce with
`python3 SignalReference/extract.py sha256_compact_reviewed`.
