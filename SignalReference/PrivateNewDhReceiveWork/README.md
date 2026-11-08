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
Three public fixture cases compare every608 output bytes (including a re-MACed
wire counter2^32 accepted by actual Prost as uint32counter0), plus eighteen computed
rejections. Actual Rust MAC failure is separately checked to preserve its store.

This began as a **model-only** fixture checkpoint. The separate compiler receipt
now adds eight foundational endpoints proving the whole Boolean pipeline lowering;
it does not establish full Rust implementation agreement. The full-wire private parser take-n theorem is now available separately; final
private parser native Rust composition, exact native
binding of fresh private/public and both DHs to the SAME parsed remote point, and
native complete receiving interoperability are pending. The model differential
supplies actual oracle DH results; the compiled native DH candidate generates and
computes them internally, but has not yet been composed/executed here. Identity
store callbacks/other session-management metadata and recoverable authenticated
share snapshots are not modeled by this608-byte transaction.

This checkpoint neither exports a normal receiving RPC nor admits the candidate
into a provider. Compiler/runtime/conversion and existing RustCrypto/source-proof
boundaries remain explicit; no internal cryptographic security proof is claimed.

## Parse-once emitted circuit checkpoint

`SummaryExport.lean` emits a 259B→75B private parser summary, and
`CryptoExport.lean` emits a1051B→608B transaction using that summary. The fifteen
split/codec/compiler endpoints prove that decoding the actual parser summary and
running the transaction equals the original whole model. `check_staged.py` checks
both emitted AIGs against the same three actual transition fixtures and eighteen
rejections, all608 output bytes, including the uint64→uint32 counter case. Those
public differential rows still supply the oracle's DH values; they do not test
native fresh-key binding. Artifacts are untracked build products with exact hashes
in `staged-report.json`. The parser is evaluated once, not repeated for each DH.

The internal `signal_private_new_dh_receive.mpc` entry binds its actual summary's
remote point to both computed agreements, generating and retaining the same fresh
clamped private scalar used for its computed public key. Its input848B omits the
model's128B keypair/agreement region entirely. Compilation and native execution
have separate receipts; a source entry alone does not establish native interop.
