This candidate proves the actual pinned Prost 0.14.4 `decode_varint` wrapper,
instantiated with the contiguous `&[u8]` Buf model, against the strict
`ProtoParse.decodePrefix` circuit. Independent acceptance is pending.

Run `python3 SignalReference/ProtoParseWork/FullReferenceWork/audit.py` from the
repository root. It verifies source provenance, replays the seven metadata
changes, reruns pinned Aeneas, rebuilds dependent root/reference modules in an
isolated tree, and checks every listed endpoint's transitive axioms.
`proof-report.json` is the resulting source/hash manifest; `axioms.txt` and
`build.log` contain the kernel audit and build output.

The theorem covers every contiguous slice, including empty input, truncation,
overflow, noncanonical encodings and trailing bytes. Successful results have
exact u64 values, consumed counts at most 10, and exact remaining suffixes.
Errors are exactly InvalidVarint. On error the fast dispatch preserves the
buffer; the short slow dispatch consumes all available bytes. The 17-byte
numeric artifact is status255 || consumedBE8 || valueBE8 on success and all
zeros on error. Artifact count is measured from the actual mutable suffix.

The proof endpoints are:

- `WrapperReference.decode_reference`: strict prefix agreement for the actual
  top-level function, without caller fast-path preconditions.
- `SlowReference.slow_loop_reference` / `slow_reference`: unchanged actual
  Range/Step loop and decoder, including exact remaining suffix.
- `Consumption.decode_full_reference`: prefix agreement plus exact error-side
  mutation for the same actual result.
- `ArtifactBridge.decode_refines_artifact`: every normalized numeric AIG output
  bit, universally quantified over symbolic bytes and matching assignments.

All names above are in `LibSignalReference.Candidate.ProstFull`. Proof files
contain no custom axioms or admitted proofs. The generated computational bodies
are not replaced by a specification.

The explicit review boundaries are:

1. `Artifacts/varint-step/changes.json` removes seven pieces of unused opaque
   Step metadata: functions 297/301, trait/impl slots 2/6, and their ordered
   declarations. Every retained computational body and all other JSON content
   are unchanged; no retained semantic references target removed slots; slot
   numbering is preserved. This preprocessing is additional translation trust.
2. `Modules/.../FunsExternal.lean` implements the three generated external
   signatures using the pinned bytes 1.12.0 source: default get_u8 and mutable
   remaining/chunk forwarding. `BufModel.lean` instantiates contiguous slices
   with length, self, and checked suffix advance and proves access/mutation
   specifications. Rust-to-model faithfulness remains an explicit assumption
   for review; the Lean specifications are kernel checked. `buf-model.diff`
   records the external template-to-model difference.
3. The separately accepted valid-usize unsafe-index model is reused. All reached
   unchecked accesses are proved bounded. No out-of-bounds Rust UB semantics is
   claimed. The accepted leaf review is `../root-review.json`.
4. Generated global discriminant instances prevent importing both generated
   namespaces together. `port_slice.py` replays the accepted leaf proof using
   only deterministic namespace/import substitutions. The actual slice
   computational body is byte-identical in both generated modules.
   `slice-proof-replay.json` records the exact substitutions and hashes; every
   replayed proof is rebuilt and audited.

This is not a theorem for arbitrary segmented/custom Buf implementations,
`decode_key`, `skip_field`, the full Prost parser, or whole Signal. No runtime
fixtures, backend compilation or native MPC execution are claimed by this audit.
