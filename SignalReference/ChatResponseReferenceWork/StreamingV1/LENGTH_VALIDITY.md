# Length-header validity candidate

`varint_nonterminal_valid` and `varint_prefix_valid` generalize the checked scalar invariant to actual key/scalar/length lanes. Every continuing byte must precede the explicit child and budget boundary; prefixes have at most nine continuation bytes. No parser-correctness premise is assumed. Initial validity is the induction invariant.

`body_length_nonclosing_valid` proves the actual Core terminal length step remains valid for strict bounded u64 varints, body kind, depth zero, a live budget, the actual successful remaining-input comparison, and a child counter unequal to one. It includes zero/nonzero decoded lengths before child closure.

The exact-child-end empty-length case and derivation of all header preconditions from native Bytes field success remain open. Prior source mutation/error/suffix and native copied-body event results are unchanged; this checkpoint does not claim whole response refinement. Successful allocation/content, executable UTF8, and static diagnostic-push trust boundaries remain as recorded in PROOF_GAPS_CURRENT.md.

The old focused handle28901 is no longer recognized by the tool; its log prints foundational axioms, but no recovered process-exit receipt is claimed. The separate-output combined checker provides new authoritative terminal evidence for both modules.
