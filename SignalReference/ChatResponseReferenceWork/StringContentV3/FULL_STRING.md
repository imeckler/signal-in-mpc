FullStringReference composes actual generated String control with the actual
varint full reference and generated canonical contiguous copier. Theorems cover
every slice and old byte-content field, with wrong-wire rejection before reads,
malformed/overflow prefix errors, length underflow, successful exact replacement,
InvalidString, and exact error/success suffixes. payload_length proves a bounded
U64 length cast cannot truncate the payload. No decoder/put correctness or
termination hypothesis is supplied by the caller.

The representation and trust boundaries in README.md and audit.json still apply:
executable UTF8 grammar (not unsafe optimized std body), successful bounded Vec
allocation/content, and scoped Take/raw loan content models. Native String's
error-local field clear is total and hidden only under the explicit owned-error
observation; stronger internal merge-state equality is not asserted. The suffix
and exact error constructors remain visible in the proof even there.

This closes the contiguous String primitive composition in those models. It does
not close the actual bytes::Bytes response schema, repeated headers, default
owned decoder, native HTTP validation, streaming/private-end or compiler relation.
check_full.py rechecks only the affected 18-module closure in separate output and
retains the earlier checkpoint receipts unchanged.
