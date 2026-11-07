# Actual byte-field composition candidate

`Reference.lean` proves the exact generic Prost 0.14.4 `bytes::encode` operation
for Signal field tags 1, 4, 5 and 6. `field_eq` preserves all supplied dictionary
failures and divergence. The two `*_of_payload_contract` theorems compose this
operation with the existing numeric byte-field circuit, **conditionally** on
the concrete payload length and append methods. Those hypotheses remain
undischarged; no full concrete byte-field or SignalMessage refinement is claimed.

The original unchanged-source extraction is `Artifacts/bytes_field.llbc`.
`select_bytes.py` applies an exact ten-change reversible metadata selection:
unused overflowing `Step` dictionary slots/declarations, unused `BufMut`
required methods and their code-generation roots. All eleven computational
declarations remain byte-for-byte identical. No Rust source, computational LLBC
body, generated Lean body or accepted Aeneas model is edited. The selected
translation has no external templates and builds. Its separate independent
selection/kernel review is now complete in
`../../ProstEncodingWork/BytesFieldSelectionReview/`. `acceptance.json` records
the accepted generic scope while keeping concrete Vec refinement false; the
original proof report is frozen as the input to that independent review.

Run from the workspace root:

```sh
python3 SignalReference/SignalMessageWork/BytesFieldWork/extract.py
python3 SignalReference/SignalMessageWork/BytesFieldWork/select_bytes.py
python3 SignalReference/SignalMessageWork/BytesFieldWork/check.py
```

The first command preserves the expected unfiltered Aeneas `Step` error. The
checker audits nine proof endpoints and their source closure, allowing only
the three standard Lean foundational axioms. Its report explicitly identifies
the two outstanding payload-adapter hypotheses.

`extract_vec_adapter.py` separately extracts the real Prost Vec `len` and
`append_to` wrappers. That diagnostic profile has unresolved external templates
and is **never imported by these proofs**. The real append operation calls
`Vec::as_slice`, then a supplied `BufMut::put` with the actual slice-buffer
dictionary. The actual Vec override of `put` reserves capacity and copies its
chunks; its dependencies include `Vec::reserve`, slice `remaining`, `chunk`,
`has_remaining` and `advance`. The accepted Aeneas package currently lacks
models for `Vec::as_slice` and `Vec::reserve`, and actual slice `advance` hits
the recorded Never-call interpreter defect. The helper's isolated translator
candidate is tracked in `../../ProstEncodingWork/AdvanceWork/`; no candidate
binary or custom model has been adopted here.

Pinned Rust `Vec::deref` is exactly `self.as_slice()`, while the accepted Aeneas
package already has a transparent Vec-dereference model. A separately reviewed
registration alias may therefore resolve `as_slice` without changing its
existing semantic abstraction. Capacity reservation has an additional resource
failure boundary; it must not silently become a no-op. Neither proposal is an
accepted reference assumption in this directory.
