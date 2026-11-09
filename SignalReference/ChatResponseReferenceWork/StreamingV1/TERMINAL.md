# Terminal lexer bridge candidate

`TerminalReader` derives the accepted strict decoder-table row directly from
the actual streaming Core accumulator, a nonterminal prefix of at most nine
bytes, a terminal byte, and the strict tenth-byte bound. `TerminalNative`
composes that row with the pinned Prost varint reference, retaining the exact
returned suffix and input-length bound. Noncanonical encodings are included.

These are local lexer theorems. They do not assume a native decoder result or
response validity, and do not yet establish whole schema streaming agreement.
The span/position/lane hypotheses remain to be established by the complete
message invariant. Error cases and HTTP/correlation composition remain open.
Inherited executable content, allocation, diagnostic-stack and std UTF8 trust
boundaries remain unchanged.

Run `python3 SignalReference/ChatResponseReferenceWork/StreamingV1/check_terminal.py`.
It validates inherited receipts, checks only the two new modules in a separate
output directory, and records an immutable combined log and aggregate exit.
The earlier standalone TerminalNative tool handle was lost during context
compaction; its log reports foundational-only success, but is not used as
terminal process evidence or as the acceptance receipt. The new output path
cannot race with that earlier job.
