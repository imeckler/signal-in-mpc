# Actual buffer arithmetic/endian proof checkpoint

Seven kernel endpoints establish BE16 byte reassembly/roundtrip and decoded
integer values, the actual masked ripple-adder's sum and overflow carry, and
the actual masked comparator's unsigned comparison. The masked-adder theorem
is parametric in arbitrary index lists and Boolean-mask inputs. Specialized
BE16 theorems cover all four input bytes, with no supplied validity flags.

Byte identities use explicit small finite kernel evaluation (256-byte and
2048-byte/bit cases); full-adder/borrow truth tables and ripple induction use
the Lean kernel. The checker permits only foundational axioms, never native
reflection or sorry. No generated proof files are edited.

This does not yet prove the complete append prefix/barrel-shift/packing
specification, arbitrary internal buffer canonicality preservation, private
varint/base64/decimal semantics, or private SHA/HMAC padding refinement. Those
remain proof obligations despite the functional differential evidence.
