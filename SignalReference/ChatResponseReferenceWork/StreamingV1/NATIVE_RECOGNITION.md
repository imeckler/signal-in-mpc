# Native key to actual Core field recognition

`FieldRecognition` proves actual Core response/body/message/header field-kind
installation matches native U32 tags. It also proves the four-entry kind-list
shape is invariant under arbitrary actual Core byte processing.

`BoundedTerminal` generalizes the native terminal-span/counter context bridge to
all varint lanes, and supplies an outer variant. `NativeKeySpan` grounds actual
key success in its actual varint execution and native validation, then composes
those proofs: native successful key execution derives actual Core scalar and
field-kind recognition at outer and bounded inner response boundaries. There
are no caller prefix, table, new-tag or primitive-correctness premises.

The inner domain explicitly requires remaining≤4096, remaining≤physical native
input length, and returned suffix≥input−remaining. The full scan must derive
these child-cursor/counter and depth/initial-state conditions from source
submessage traces. Known-field wire guards, other field/group transitions,
private end, HTTP/correlation/compiler composition remain open. This checkpoint
does not claim a full parser theorem or discharge inherited explicit source/std/
content/allocation/static diagnostic push trust boundaries.

Run `check_native_recognition.py` for an isolated immutable three-module combined
check using verified ancestor objects.
