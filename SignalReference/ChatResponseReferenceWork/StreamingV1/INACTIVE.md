# Actual inactive padding and compiler component

`StateShape` proves the actual parser's modes/positions/kinds/stack/UTF list
lengths at initialization and after every step, finish, selection and production
process, including malformed control flags. `StateSelection` proves actual full
record selection at zero/255 masks with those lengths; no list truncation is
ignored.

`InactiveByte.process_inactive` proves the production process with activity,
beginning and ending controls all zero preserves the complete parser state and
emits zero body-data/body-reset/header-data events for every padding byte. The
fold theorem covers arbitrary inactive capacity tails. `runByte_inactive` exposes
the exact numeric byte endpoint output.

`CompiledInactive` composes this with existing production
`compiled_runByte_correct`: every exported AIG output bit equals the expected
preserved serialized state and event bytes. The raw-state decoding and zero
private controls are explicit hypotheses. This does not derive active/private
EOF controls or claim complete active-input/schema/source agreement.

Full source scan induction must still establish active field/group/private-end
bounds, known-wire guards and HTTP/correlation/compiler composition. This is not
an outer-gate replacement for those obligations. Existing explicit std/content/
allocation/static diagnostic push boundaries remain unchanged.

`check_inactive.py` records an immutable combined four-module kernel check in a
separate output directory, validating ancestor hashes and avoiding unrelated
native reruns.
