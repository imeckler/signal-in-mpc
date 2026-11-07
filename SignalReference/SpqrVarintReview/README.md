# SPQR varint reference review

`check.py` independently checks the exact seven metadata changes, replays and
reverses them, compares both retained computational declarations, and scans
all retained declarations for references to the removed entries. It also
compares all 99 upstream SPQR files and all 87 official Aeneas standard-model
files to their pinned archives, verifies the frozen proof provenance and
checks the 21 endpoints' transitive axioms through Lean.

The accepted scope is actual SPQR `encode_varint` and its uint64/uint32 circuit
bridges. The generic operation theorem retains every `Vec.push` result. The
append/artifact theorems require canonical public widths and enough room in
the official Vec model (`length + 10 ≤ Usize.max`). The normal Rust
`cfg(not(hax))` expands the actual `assume!` macro to unit; no hax proposition
is imported as a proof assumption.

The dead-metadata selection is a trusted, reviewed preprocessing step. It is
not mechanized. No Rust body, standard model or cryptographic operation was
replaced. Full SPQR serialization, crypto and state transitions remain outside
this result. The independent review and author proof report are frozen;
`SpqrReference/acceptance.json` records the precise acceptance separately.

Run from the repository root:

```sh
python3 SignalReference/SpqrVarintReview/check.py
```
