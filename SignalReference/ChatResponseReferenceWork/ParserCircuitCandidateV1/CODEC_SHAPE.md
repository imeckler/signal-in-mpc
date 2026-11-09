# Reachable serialization shape

CodecShape and MuxCodecShape proofs establish the exact read/write ABI lengths
from initialization through arbitrary actual Core/Mux process calls, admissions
and high-stack trimming. There is no canonical-control, valid, success, accepted
message or fragment-boundary premise. Actual zipWith selection, stack writes,
UTF state, slot consumption and row mapping all preserve their required lengths.
The Core argument reuses the factoring from StreamingV1.StateShape without its
native extraction dependencies; no runtime body or frozen proof was edited.

The checked whole Core/Mux readState/stateBytes roundtrips now apply throughout
reachable operation sequences. Remaining optimization proof is compressed
serialized trim equality and the actual exported compact recurrence/compiler
join. Semantic arbitrary-operation projected event traces are already equal.
No runtime promotion, heavy export or native benchmark occurs here.
