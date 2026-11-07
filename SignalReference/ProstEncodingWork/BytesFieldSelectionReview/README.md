# Independent Prost bytes-field selection review

`python3 SignalReference/ProstEncodingWork/BytesFieldSelectionReview/check.py`
reviews the exact pinned graph and writes only this directory.

The review replays and reverses all ten selection changes, compares every
retained declaration, checks all eleven actual computational bodies, and scans
signatures, constants, function pointers, dictionary dispatch and trait/default
metadata. It checks the unchanged standard models against the exact upstream
Aeneas source archive, then recompiles the selected generated code and the nine
proof endpoints into a private build directory. The report records all hashes.
The selector remains a reviewed trusted preprocessing step; its correctness is
not mechanized.

The unconditional `field_eq` theorem retains the supplied adapter's exact
`len` and `append_to` result behavior, including failures and divergence.
The numeric artifact theorem is conditional on two explicit concrete adapter
contracts and the stated capacity bound. It covers field tags 1, 4, 5 and 6.

This does not complete the concrete Vec byte-field or SignalMessage refinement.
Actual Vec `BytesAdapter.append_to` calls `BufMut.put(self.as_slice())`, so the
existing `Vec.put_slice` varint proof does not discharge it. Concrete `put`,
`reserve`, `as_slice`, slice advancement, and whole-message composition remain
separate obligations. The unrelated candidate Never-call translator and its
Formatter-type boundary are neither changed nor accepted by this review.
