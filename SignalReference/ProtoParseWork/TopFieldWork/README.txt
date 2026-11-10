Top-level fields, decoder table and public scan bridge candidate

This work imports the separately accepted SkipPlanWork/SkipTranslatorWork
reference without changing its models, translator, Rust sources or extraction.
It proves top-level known-wire requirements and unknown-field masks, exact
indexed metadata overwrite and duplicate behavior, bounded shared decoder
lookup, decoder-table contents and the ten-row payload window, end-of-buffer
invalid lookup, absolute-cursor agreement with actual translated varint/key
successes and failures, positive key consumption, and inactive/failed public
scan state preservation. No new external model is added.

The table theorems remove the former decoder-correspondence premise for actual
successful/error varint calls on arbitrary suffixes (with stated public bounds).
The payload lookup window agrees for a positive one-to-ten-byte key; positivity
is proved from the numeric decoder and accepted actual prefix correspondence.
The scan lemmas show skipped interior bytes cannot mutate any state, and
failure is absorbing. None of these assumes a caller-supplied validity Boolean.

Still outstanding: a complete inductive logical field/group parser trace,
cursor/group-stack invariant preservation across that trace, composition of
actual uint32/bytes field models into the numeric metadata representation,
SignalMessage-specific success/required fields and whole-parser AIG agreement.
The existing compiler theorem proves the implemented Lean parser but does not
alone establish these actual-Rust semantic obligations. No whole-parser claim.

Run audit.py for a complete rebuild and foundational-only axiom check.
Candidate is not accepted unless a separate root-review.json records acceptance.
