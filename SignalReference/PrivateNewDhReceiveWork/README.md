# New-DH receiving transaction: model checkpoint

The candidate composes the versioned true-private-length Signal parser, actual
PQ field slicing, retained active receiving-PQ key derivation, two RootKey HKDF
halves, DR message-key derivation, original private-prefix MAC verification,
AES-CBC/PKCS7 decoding and shared atomic state selection. Every acceptance mask is
computed; no external authentication/verification flag or supplied PQ key is used.
The fixed profile requires five receiving-chain slots, no skipped keys, unknown
remote ratchet, Signal counter0, V4/noaddresses, ciphertext96/plaintext80, and a
same-epoch in-order V1 kind0 PQ message with receiving counter<2^31-1.

Input model layout976B: sender/root136, five receiving entries345, receivePQ44,
remote/local identity public32+32, computed fresh pair and DH results128, and
private wire(validity8/BE16length/capacity256). Output608B: status, selected
sender/root136, receiver slots345, receivePQ44, private BE16 length and plaintext80.
Roots, own DH private key and PQ state remain share-valued in the native design.
On rejection, the selector kernel theorem preserves all525 state bytes and zeros
application output. Successful receiver insertion retains at most five entries.

The Rust oracle uses actual pinned PQXDH initialization to establish genuine DR
roots/keys, actual message_encrypt to emit the first unknown-ratchet message and
actual message_decrypt_signal to derive/update the receiving state. SPQR alone is
set to an explicit selected established no-chunk phase; this does not implement
fresh prekey authentication, initial SPQR negotiation or full KEM phase evolution.
Two public fixture cases compare every608 output bytes, plus twelve computed
rejections. Actual Rust MAC failure is separately checked to preserve its store.

This is **model-only**, with one foundational selector-rejection endpoint. The
numeric compiler theorem, full take-n/private parser source theorem, exact native
binding of fresh private/public and both DHs to the SAME parsed remote point, and
native complete receiving interoperability are pending. The model differential
supplies actual oracle DH results; the compiled native DH candidate generates and
computes them internally, but has not yet been composed/executed here. Identity
store callbacks/other session-management metadata and recoverable authenticated
share snapshots are not modeled by this608-byte transaction.

This checkpoint neither exports a normal receiving RPC nor admits the candidate
into a provider. Compiler/runtime/conversion and existing RustCrypto/source-proof
boundaries remain explicit; no internal cryptographic security proof is claimed.
