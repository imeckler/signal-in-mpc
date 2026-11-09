# Rejection lexer component candidate

`RejectedReader` proves truncated all-continuation inputs (including empty input)
and invalid tenth bytes reject in the strict decoder used by the native bridge.
`RejectedCore` derives actual Core invalid-tenth rejection after the proved prefix
invariant, and the corresponding native InvalidVarint/exact suffix. Both
terminal and nonterminal bad tenth bytes are covered.

`IncompleteFinish` proves EOF in scalar/length lanes, or after at least one
continuing key byte (up to nine), rejects independently of accumulated fields.
An empty key prefix denotes a clean field boundary, so is intentionally excluded
from that EOF rejection case. Padding is not substituted for missing bytes.

Native fast errors preserve the original cursor; slow errors consume the bounded
prefix. These source cursors are retained rather than equated to Core's byte
processing count on failure. Full schema induction, private-end process gating,
and HTTP/correlation/compiler composition remain open; inherited std/content/
allocation/diagnostic-stack boundaries remain unchanged.

Run `check_rejected.py` for a distinct immutable combined three-module kernel
check, validating inherited receipts without rerunning unrelated native cases.
An expensive draft Core proof was interrupted through PTY27215 (confirmed exit1);
the final proof uses small operation lemmas to avoid expanding the remaining
Core computation. No failed or interrupted output is accepted by the receipt.
