# Actual oblivious barrel shift semantics

Four kernel endpoints prove mask-controlled byte choice, composition of
zero-filling bounded shifts, the actual16-stage shiftLoop for arbitrary mask
bits/indices, and its BE16-decoded specialization: output equals a bounded
zero-filling shift by the decoded unsigned integer. Data length/capacity is
arbitrary. No secret-dependent execution/index is introduced by the proof.

Small per-byte shift-value identities use kernel finite evaluation, not native
reflection; the checker permits only foundational axioms. Complete append
normalization, prefix concatenation/rejection specification and private hash
padding refinement remain open. This is an arithmetic/placement checkpoint,
not a completed packing/session proof.
