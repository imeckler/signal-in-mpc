# Numeric response streaming candidate

The first checked milestone covers the real Core's three varint lanes:

- Exact one-hot contribution at all10positions and every byte, terminal mask,
  and strict Prost tenth-byte overflow guard (independent of permissive SPQR
  payload truncation).
- Actual Core ID/type/status terminal assignments, including low32 truncation.
- Actual Core nonterminal prefix invariant in key/scalar/length lanes: lane,
  group-position and accumulated payload, with no response-validity hypothesis.
- Signed native enum/u32 cast projections and exact actual scalar merger result,
  including errors, retained old values and native suffix. Enum comparison2 is
  preserved without sign extension.

Arithmetic/finite proofs are kernel checked; no native BV-check oracle is used.
The latest receipt records the already completed focused checks and current
source/object hashes. `check.py` reproduces them in a separate output directory.

Full prefix span/absolute cursor, schema state, rejection/owned observation,
HTTP headers/Unicode trim, private correlation and compiled-output composition
are still open. Draft modules outside the receipt are not accepted by this
checkpoint. The actual static-reference diagnostic push and optimized unsafe std
UTF8/content/allocation model boundaries remain inherited and explicit. No full
streaming/source agreement or ChatConnection scheduling equivalence is claimed.
