# Actual byte-slice advance translation boundary

The pinned unchanged `bytes` 1.12.0 implementation of `Buf for &[u8]::advance`
does not currently translate with the accepted Aeneas binary. No proof endpoint
or generated implementation from this directory is accepted.

Reproduce from the workspace root:

```sh
python3 SignalReference/ProstEncodingWork/AdvanceWork/extract.py SliceImplsClosed
python3 SignalReference/ProstEncodingWork/AdvanceWork/extract.py SliceInlinePanic
python3 SignalReference/ProstEncodingWork/AdvanceWork/check.py
```

Both extraction commands are expected to exit unsuccessfully. `check.py`
verifies these expected failures, exact vendor source hashes, the real selected
method and helper bodies, preserved calls, and the diagnostic artifacts. Its
`report.json` records the tool invocations, source/code hashes and remaining
equivalence obligations.

The direct profile starts from all actual `Buf::advance` implementations because
Charon's `--start-from` resolver rejects reference-type implementations. All
bytes bodies are opaque except the exact `&Slice<_>` method and real
`panic_advance`; the real `TryGetError` fields are included. The other start
roots are diagnostic metadata, not accepted opaque computations. The only two
actual bodies are the selected slice operation and its panic helper.

The out-of-bounds branch calls `panic_advance`, whose Rust return type is `!`.
The pinned symbolic interpreter creates a symbolic `Never` result and continues
with `Cps.Unit` at `InterpStatements.ml:1427–1430,1578–1582`. At the end of the
caller, `Interp.ml:583–589` rejects this result. Including the actual panic body
does not help because symbolic function calls use signatures rather than inline
execution. `Artifacts/SliceImplsClosed/trace.log` records the surviving symbolic
`_7 : !` value and the exact emitter location.

One standard optimized-MIR probe enables inlining with high thresholds while
retaining debug assertions and overflow checks. The real cold panic call remains;
the compiler also exposes formatting types rejected as unsupported Arrow types.
It does not produce an accepted alternative.

Any future translator repair must retain the actual called result and propagate
its failures and divergence, eliminating only the uninhabited successful return.
Replacing arbitrary `!` calls with panic would lose behavior. The intended slice
theorem must cover both exact suffix assignment when `cnt <= length` and the
actual failure branch when `cnt > length`.

Earlier `Slice` and `SliceModulePanic` artifacts diagnose path resolution and an
empty selection respectively. An empty generated namespace is not a successful
extraction. `Artifacts/SliceTrace/SliceAdvance.lean` is partial diagnostic output
containing failed and opaque declarations; it is never imported by proofs.

The downloaded `Interp.ml` and `InterpStatements.ml` are read-only evidence from
the exact accepted Aeneas commit. No accepted translator, standard model, Rust
source, or generated computational body has been modified.
