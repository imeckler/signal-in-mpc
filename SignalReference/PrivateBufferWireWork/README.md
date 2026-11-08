# Actual append-wire mathematical refinement

`appendWire_decoded` proves the actual implementation for every capacity<65536,
every status byte, every pair of BE16 lengths and arbitrary data arrays of the
public capacity. Acceptance is exactly both statuses255 and n+m<=capacity.
The accepted wire is255 || canonical BE16(n+m) || left.take n ++right.take m
++zero tail. All other statuses/bounds/sum overflows return capacity+3 zeros;
separate theorems reject wrong public input dimensions. Valid empty remains
255/length0, distinct from rejection.

The proof establishes actual normalization, canonical mask arithmetic,
barrel-shift placement, prefix concatenation, output encoding and rejection
propagation. Ten audited kernel endpoints include the existing numeric
compiler agreement endpoint; together they link the symbolic append compiler
to this concrete mathematical specification. Only foundational axioms occur.
Small eight-bit/Boolean byte encoding identities use kernel finite evaluation,
never native reflection. No generated files or translator outputs are edited.

This closes append packing semantics, not private-varint/base64/decimal or
SHA/HMAC padding semantics, actual Rust/Aeneas cryptographic agreements,
recoverable shared storage or application readiness.
