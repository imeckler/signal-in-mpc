# Actual private SHA/HMAC semantic refinement

Twelve audited kernel endpoints establish actual bounded private-length hash
and HMAC behavior relative to the existing executable SHA256 primitive models.
For every capacity0..16384 and arbitrary status/BE16 length/data bytes, accepted
wire is255 || BE16(32) || hash/hmac(key,data.take n). Invalid status/length,
wrong public dimensions and unsupported capacity reject to35 zero bytes.

The proof derives the unique final block index(n+8)/64, marker placement,
64-bit bitlength bytes (including HMAC's64-byte prefix), equality of every
selected private block to the ordinary Sha256.padding block, and equality of
the final private state selection to ordinary public block processing. Extra
bounded compression after the selected final state contributes zero bytes.
No validity flags or correct-digest assumptions are supplied. Prepared HMAC
prefix equivalence uses the existing proved HmacPrepared.run_prepare theorem.

The checker permits only foundational axioms, not native reflection or sorry.
The existing numeric compiler agreement endpoint is audited alongside the
mathematical wire semantics. Full actual Rust/Aeneas primitive/wrapper source
agreement and internal cryptographic security are separate boundaries; this
checkpoint proves neither. Varint/base64/decimal semantics, selected session
policy, authenticated initial state, recoverable storage and production
readiness remain separate work.
