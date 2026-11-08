# Private bounded buffers (candidate)

Wire layout is validity8 || BE16 private length || public-capacity bytes. Validity255 represents acceptance, including an empty prefix. All other input validity values reject. Appending normalizes both prefixes, ignores bytes beyond their private lengths, preserves embedded zero bytes, and rejects overflow with zero validity, length and data. No secret length is opened.

`check.py` tests integer behavior across bounded capacities and canonical varints against actual prost, including127→128. The four printed kernel endpoints establish public length arithmetic and compiler agreement with the concrete byte model; they do not establish a general integer specification of append, the mask full-adder/comparator, or canonical varint semantics. Those semantic theorems remain open. No native-reflection axioms are accepted.

The counter chunk demonstrates width changes without public profile switching. Variable-length Signal HMAC/padding, sealed-sender encryption/base64, JSON/protobuf/WS composition and persistent producer integration remain dependencies; this helper alone does not make the current fixed service profile reusable across width changes.
