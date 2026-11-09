# Actual CTR current-block extraction checkpoint

`check_current_models.py` replays deterministic name-only LLBC specialization and the pinned unchanged Aeneas exporter, then byte-compares generated Types/Funs/external-template. Computational LLBC declarations are unchanged by the replay (semantic equality and exact inverse checks). Full qualified instantiation hashes identify names; collisions fail closed. This does not adopt the unaccepted Drop translator candidate.

The thin Source harness calls actual `ctr::flavors::Ctr32BE` methods with concrete U16 and the pinned release zeroize feature. Charon monomorphization avoids the generic GAT path. `extract_mono.py --candidate CurrentModelViewsV1 --root current --include-helpers --opaque-default --opaque-views` produced the retained source graph. Dependency checksum inventory records the exact pinned lock comparison.

`FunsExternal.lean` is authored by `bind_current_models.py`, not generated computational Rust translation: ten external functions forward to official pinned Aeneas Array/Slice/Range/scalar content models. Hybrid raw-pointer views map to valid fixed-array content and default16 to official zero-byte defaults. Successful resources, address/layout/Drop behavior and erasure are explicit external model boundaries. Native endian maps to little endian on the extracted aarch64 target. No AES, CTR payload, supplied validity or whole-wrapper correctness is assumed.

Two foundational-kernel endpoints currently establish actual typenum CS=4 and actual terminal loop-body preservation. The full four writeback steps/current-block theorem, actual from_nonce/next/exhaustion composition, stream/AES and HMAC wrappers remain OPEN. The earlier conversion arithmetic prefix is not promoted to full actual remaining refinement. Actual Ctr32BE capacity remains MAX32-counter, rather than an unconstrained 128-bit increment.

The checker rebuilds isolated proof objects and audits only foundational axioms. No generated Funs/Types edits, native reflection, generic owned-Drop model or allocator proof is used.
