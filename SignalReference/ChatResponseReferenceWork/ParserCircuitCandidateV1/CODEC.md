# Codec index and word bridge

`CodecIndices.lean` proves both public inverse index maps using kernel reduction,
with no native oracle. Generic get/compact/expand theorems hold for arbitrary
byte element types and arbitrary source lists (including short/defaulted lists).
Compaction after expansion preserves every compact output position. Expansion
after compaction preserves every non-high-stack output byte, including events;
exactly the high four bytes of each stack word are zeroed. The extra fourth
input/control byte beyond the 985-byte source output is excluded explicitly.

`WordCodec.lean` proves actual Word64 BE pack(bytes(word))=word and that the
serialized trimWord is exactly four zero bytes followed by the original low
four bytes. These are kernel BitVec/list lemmas, not fixture comparisons.

Remaining: whole Core/Mux state serialization/readState shape bridge and the
actual measured compact byte endpoint's recurrence/compiler composition. The
already proved semantic Core/Mux trace equivalence is retained independently.
No runtime promotion, native job or heavy export occurs in this checkpoint.
