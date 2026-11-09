# Serialized projected-state bridge

`SerializedTrim.lean` proves the measured compact output's expansion, truncated
to its actual985-byte original output size, is exactly actual Mux.stateBytes of
trimMuxState plus all3 unchanged event bytes. State values may be arbitrary;
only the already-proved reachable ABI shape is needed. No validity/success,
canonical-mask, accepted-key or well-formed-message premise is introduced.
The theorem includes rejected high tags, all private slots/IDs/status/counters,
queue rows, UTF/header state, and body/reset/header event masks.

The proof derives arbitrary indexed reads from actual BE word chunks, proves
exact per-byte trim behavior, then composes the public codec inverse maps with
actual Mux prefix/stack/suffix layout. It is a whole serialized-state equality,
not a fixture or an assumed pack/adapter law. Original output985 versus input986
is explicit; the fourth input control byte is not incorrectly invented from an
output event. Remaining: encode state plus next4 controls, actual exported
compact endpoint recurrence and compiler-level operation trace composition.
No runtime promotion, new profile or native job occurs here.
