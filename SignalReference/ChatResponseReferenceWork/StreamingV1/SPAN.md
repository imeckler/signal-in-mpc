# Prefix span and absolute-cursor checkpoint

This extends the earlier three-module numeric milestone without changing it.
`NativePrefix` links accepted strict numeric rows to the actual pinned Prost
value/suffix/count bound; rejected rows return the exact InvalidVarint and actual
fast-path unchanged versus slow-path consumed suffix. No native primitive
correctness or termination is assumed.

`PrefixValue` proves the actual Core's complete nonterminal prefix accumulation
matches the executable reader used by the accepted native primitive reference.
The supplied lookup/span equation ensures every input lookup is present; missing
bytes cannot be replaced with padding or a synthetic zero terminator.

`AbsoluteCursor` transports both native outcomes through a global drop cursor.
Success advances by its exact count; rejection retains the real source cursor.
The4096-byte bound proves absolute64-bit cursor arithmetic cannot wrap.

These are component theorems. Terminal byte→strict row, complete schema-streaming
state/rejection, HTTP headers/trim, private correlation and compiler composition
remain open. No full streaming-source agreement is claimed. The source error
suffix is not asserted equal to the Core's already-read byte count on error;
the real owned API observation must justify that quotient. Static diagnostic
push and optimized std UTF8/content/allocation model boundaries remain explicit.
