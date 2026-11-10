# Session-bound checked mask pool

`DaBitGeneratorV1::generate` is the sole constructor friend for `CheckedMaskPool`. It executes actual input fixation/cut/bucket/native MAC/EMP checks before constructing the pool; no caller-supplied success flag or nonzero hash authorizes pairs. Actual session/native party identities are checked against A/B mapping. The returned authenticated EMP holding value keeps the pool's wires live across checkpoints.

Leases bind joint fresh nonce, public full code/runtime closure digest, epoch, monotone operation, burned range, direction and the actual local Boolean/field engine owners. Reservation immediately removes/burns the range. Consume is move-only/one-shot; bad binding/reuse poisons the pool. Frames use fixed magic/version plus32-byte nonce/config, big-endian64-bit epoch/operation/range/count and direction. Both peers compare the frame before conversion opens a masked value. Configuration hashing includes public code/runtime/config only, never private share/preprocessing files.

The generator's public configuration is an embedding boundary for this local fixture, not remote attestation or production authorization. Native and EMP use the same A/B processes. Remote authenticated identity/channel binding, full malicious-composition proof, epoch renewal and secret-storage erasure remain open. Pool guards prevent honest integration misuse; they do not themselves prove backend security against arbitrary malicious code.

## Native controls and failure evidence

`pool-conversion-v2-report.json` passes positive native-field→EMP conversion and one-sided wrong session/owner, changed peer frame and reused lease controls. Each rejected case stops before `mask-range`/masked application opening; all children are terminal/reaped. `pool-conversion-report.json` preserves the failed first orchestration: wrong session/owner caused an asymmetric unwind (one party entering native destructor/check while the other awaited EMP). Its deadlines killed/reaped those groups, which is **not** retirement/erasure success.

The second fixture catches local reserve/consume guard failure and exchanges a one-byte public readiness predicate before either side unwinds or opens masked values. Both sides then abort cooperatively. This does not establish cancellation/join/erasure for a peer crash or a malicious peer that stops participating; stock fatal paths and timeout teardown remain separate system gaps.

The second matrix's initial replay group encountered native `No buffer space available` during OT generation, before reaching the pool guard. It remains in `unreached_replay_resource_failure`. A targeted unchanged replay retry after prior children were reaped reached `pool-consume` and rejected both parties without application output. No failure was relabeled as a successful fault injection. This resource boundary matters for future sustained tests; current measurements are correctness controls, not a throughput claim.

Reproduce with the pinned candidate builds and isolated linear-mask overlay: `build_field.py`, `build_pool_conversion_v2.py`, `check_pool_conversion_v2.py` in this directory. Native input/preprocessing directories must stay fresh; consumed masks and engine state cannot be restored/reused. The original v1 source/controller and failed receipt are retained for provenance. No default worker/runtime/production gate changes.
