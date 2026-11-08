Private-length TLS payload checkpoint (isolated candidate only)

Wire input to the pinned circuit is key16, IV12, sequence8, computed validity1,
private length BE16, public-capacity data. Output is shared status1 followed by
fixed-capacity TLS ciphertext. Capacity is an agreed workload profile, unrelated
to private identifiers/actual length, and is limited to 16384 bytes.

TlsPrivateSeal proves that status is255 exactly when validity is255 and the
private length fits. On acceptance its ciphertext equals the standard TLS seal
of the true prefix, type23, then zero padding. These endpoints and compiler/map
theorems use only propext, Classical.choice and Quot.sound in the checked audit.
TLSInnerPlaintext padding follows RFC8446 section5.2 (updated by RFC9846):
https://www.rfc-editor.org/rfc/rfc9846.html

NativeSession preserves computed validity with shared BE16 length and data.
StatusGate authenticates status before reconstructing ciphertext; rejection is
terminal through Session's existing guard. A producer rejection must never be
converted to a valid zero-length request. Incoming opaque handles can be consumed
once into same-worker processing without exposing data or length over RPC.
checkpoint_private_computation requires committed selected state/discarded old
owned inputs, renews runtime/transport, and blocks further application work until
the erased host call joins and its complete stack is wiped. Retained selected
state and payload shares deliberately survive; this does not erase OS copies.

Evidence:
- scripts/check_tls_private_seal.py:138 independent AESGCM cases, capacities
  0/1/16/257/900, boundary lengths/producer flags;46 valid/26 invalid public
  C++/Python shape cases; nine proof endpoints audited.
- scripts/check_native_private_payload.py:two five-party native runs with actual
  compiled cap16 seal, four valid lengths0/1/15/16 each, then length17 rejection
  or producer-status0 rejection. Valid ciphertext matches independent AESGCM;
  rejected paths call authenticated release once for status and never for wire.
  Epoch renewal follows each valid case; terminal abort is idempotent.
- reports tls-private-seal-checks.json and tls-native-private-payload.json.

Build dedicated emitter with lake build private_tls_emitter; install into a new
public program cache with prepare_tls_shape.py --install CACHE --emitter STANDARD
--private-emitter .lake/build/bin/private_tls_emitter. Reinstalling a changed
toolchain invalidates previous cache receipts. Frozen runtimes/caches are not
updated in place. SessionWork/Makefile builds the new fixture against the tested
isolated runtime; canonical worker has no lifecycle capability and stays closed.

Outgoing plaintext handles now consume once ciphertext is reserved. An explicit
ApplicationEpochPolicy selects every_record or explicit_boundaries; TLS itself
does not require network teardown for each record. The candidate worker selects
every_record and renews runtime before ciphertext's erased-host receipt returns.
The explicit policy retains VM work until its declared checkpoint/KeyUpdate/
abort and cannot acknowledge earlier cleanup. Retained TLS traffic keys still
cover earlier same-key records; runtime renewal alone is not forward secrecy.
The real persistent TLS regression passes all5,380.034s, three records+bothKU
directions+replay rejection+abort. Loopback renewal costs15.34–20.56ms per record
per party in this run; this is not a WAN/100k-hour throughput measurement.

Remaining:actual HTTP1.1 WebSocket upgrade/stream processing and service framing,
typed adaptation of the fixed901-byte service output (status+900 data) into the
903-byte private-buffer format, per-message producer checkpoint integration,
durable producer state/ack policy and a real persistent service test. Synthetic H2/gRPC evidence is not a
substitute for these requirements. NativeService belongs to the crypto worker.
