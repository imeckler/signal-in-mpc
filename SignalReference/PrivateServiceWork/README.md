# Selected-chain variable-length service candidate

The circuit derives Signal/SPQR message material once, emits private canonical
counter/previous/epoch/index/chunk lengths, computes one CBC and private-length
HMAC, wraps SSv1, and encodes actual relay JSON/protobuf/WebSocket bytes. The
final request status selects both old versus candidate chain states. Output
is status8 || selected state72 || BE16 length || public-capacity request.
The payload extracted for TLS is status8 || BE16 length || capacity bytes.

`check.py` defaults to a fresh Lean export. `--reuse-artifact` evaluates an
already exported local artifact; the report records exact source/artifact
hashes. The current public fixture feeds the actual first circuit output state
into the second evaluation: Signal counter127→128 and SPQR next index127→128
change inner72→74, SS433→435 and WS900→901 bytes within capacity1186. Actual
pinned libsignal Signal construction and SS encryption/decryption/certificate
validation, plus actual generated relay schema decoding, match. Four rejects
retain both old chains and produce zero length/data. The fixture supplies
native-generated DH and intentionally reuses its public synthetic ephemeral;
it does not test private DH generation, native MPC or TLS integration.

Five audited standard-axiom endpoints prove compiler agreement with the
concrete composition. Integer packing/varint/decimal/private-hash semantics,
full Rust/Aeneas agreements, active epoch/KEM selection, authenticated private
UUID/UAK/device/certificate state binding, fanout, response correlation and
recoverable storage remain open. Only an already selected active epoch is
supported. No production or delivery claim follows.

The no-chunk/no-address, empty-plaintext candidate has23,207,219 numeric AIG
nodes and a550MiB JSON artifact. No native lowering or throughput measurement
has been performed. Packing revalidation/normalization needs optimization;
these counts are a resource boundary, not a performance estimate.
