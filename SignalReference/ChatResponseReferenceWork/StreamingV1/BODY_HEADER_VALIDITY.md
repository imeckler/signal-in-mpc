# Native body header validity

`empty_body_length_valid` checks the actual Core terminal step for a zero decoded body length, including a child ending at that byte. No nonclosing premise is used. Strict varint bounds, actual remaining-length comparison, initial valid/seen/unfinished state and live budget remain explicit.

`native_body_header_valid` derives the exact consumed header span and Core validity from the pinned native varint result. It derives all strict terminal/tenth facts, prefix validity, the real length comparison, and the empty/nonempty child-closing distinction. Bounds are capacity4096, positive consumed header, physical input length within budget, and declared payload plus consumed header no greater than the private child remainder. No supplied varint prefix or post-header validity premise remains.

This is a header component: copied-body payload events/data/validity are checked separately and must be joined. Entire schema, UTF8/String/header semantic integration, HTTP eligibility/correlation and compiler relation remain open. Allocation/content/std UTF8/static diagnostic push boundaries remain explicit in the current ledger and historical source references. No runtime or generated computation changes.
