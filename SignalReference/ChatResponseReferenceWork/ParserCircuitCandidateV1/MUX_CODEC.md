# Whole Mux state serialization

`MuxCodec.lean` proves actual Mux.readState(Mux.stateBytes(state))=state under
Core CodecShape, exactly4 slots and4 queue rows. Each actual11-byte slot is
read from its actual933+11*i slice; word pack/unpack is proved. Queue count,
private eligibility/consumed masks, IDs, rows and the complete932-byte parser
state are exact for arbitrary field values. The proof imposes no valid/success
or message-content premise. It composes the checked Core roundtrip, not a model
of readState invented for this candidate.

The optimization bridge still needs compressed serialized trim equality,
reachable ABI shape and actual compact exported recurrence/compiler composition.
The semantic arbitrary-operation Mux projected-trace theorem is already closed.
No runtime/native/profile changes or optimization promotion occur here.
