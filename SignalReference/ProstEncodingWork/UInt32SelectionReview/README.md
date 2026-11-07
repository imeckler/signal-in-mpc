# Independent UInt32 field-selection review

Run `python3 SignalReference/ProstEncodingWork/UInt32SelectionReview/check.py`
from the workspace root. The checker reads the parent's frozen extraction and
writes only this directory's `review.json`.

The reviewed graph preserves all ten actual computational declarations:
Prost's uint32 field encoder, field-key encoder, varint encoder, the bytes
default `put_u8`, Rust range-bound helpers, and tag constants. All ten metadata
changes replay and reverse exactly. The checker scans every retained semantic
declaration, including globals, trait defaults, signatures and function-pointer
references, for removed methods and functions.

The omitted `Step` overflow methods and unused buffer dictionary entries are
trusted extraction preprocessing. This review is not a mechanized proof of
the selector. The actual opaque `RangeInclusive::new` declaration uses the
existing Aeneas standard model. The unused opaque default `put_slice` and
`UninitSlice` declarations remain as metadata but are excluded from generated
roots. Called `put_slice` and `put_u8` dictionary entries remain unchanged.

The result covers the selected generic field encoder. Concrete buffer and
whole-message conclusions require the corresponding composition theorems;
the review does not independently establish them. Parent-owned
`SignalMessageWork/UInt32Reference.lean` instantiates the previously proved
Vec operations and proves both Signal counter tags and the numeric circuit
endpoint.
