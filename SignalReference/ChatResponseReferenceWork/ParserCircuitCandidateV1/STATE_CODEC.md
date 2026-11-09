# Whole Core state serialization

`StateCodec.lean` proves actual readState(stateBytes(state))=state under exactly
the public ABI shapes: modes4, varint positions10, kinds4, group stack100,
UTF8 state8. No byte or word value, validity, success, or input-content premise
is used. The actual serialized length is932. The proof factors the100-word
stack into prefix/word-table/suffix and derives each actual slice's pack result,
then proves the remaining concrete fields including header read/serialization.
This is not a test or an assumed codec law.

Remaining optimization bridge: Mux wrapper slots/rows codec, compressed byte
projection equals trimMuxState serialization, shape preservation and exported
compact endpoint recurrence/compiler join. The arbitrary-operation semantic
Mux projected trace equality is already checked separately. No promotion or
new profile/native job occurs here. The failed unfactored roundtrip draft is
kept under Drafts outside the audited/checkable module graph.
