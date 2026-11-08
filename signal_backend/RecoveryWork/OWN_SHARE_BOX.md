# Local own-share archive candidate

This component never reconstructs a secret bit/key. It serializes only the
current party's GF128 polynomial evaluations, one16-byte little-endian field
value per original state bit. Pinned MP-SPDZ gf2n.cpp specifiesx128+x7+x2+x+1;
ShamirInput.hpp evaluates atpartyindex+1. The native adapter statically restricts
the exact MaliciousCCD128 secret/part type and checks runtime member/n5/t2/degree128
and one-bit cell shape. BMR/other authenticated representations are not aliases.
The basis codec passes16,384 pinned-native field checks; the full runtime capture
guards are compiled but not exercised by those local unit tests.

The local storage key is64 independent host-keystore bytes for AES-256-SIV. It
is NOT a Signal identity/root key. SIV was chosen so a crash cannot accidentally
reuse a GCM nonce/counter with different snapshot data. Deterministic encryption
can reveal equality of identical plaintext/associated-data pairs. Unique snapshot
slot/domain binding limits this to duplicate archives of the same version.
[Primary specification, RFC5297](https://www.rfc-editor.org/rfc/rfc5297.html).

Party/epoch/slot/bitcount/context/membership/manifest/schema/sharing-epoch and exact
field representation are authenticated as one canonical header. The tag is16bytes,
kept separately from ciphertext as required by the OpenSSL SIV API. Only one data
update is used and no plaintext escapes on authentication failure. Decrypted
local evaluations remain in a fixed zeroing owner. This covers current owned
buffers, not swap, allocator/OS history or a runtime retirement guarantee.
[Actual OpenSSL API](https://docs.openssl.org/3.0/man3/EVP_EncryptInit/#siv-mode).

58 sanitizer checks cover roundtrip, wrong keys/all domain fields, modified
header/tag/ciphertext, truncation/extension and move ownership. Three exact
ciphertext/tag/AD comparisons use the cryptography AESSIV API. These are functional
wrapper checks, not a proof of cryptographic security or an independent algorithm
implementation. The native adapter only SEALS; no restored-Bits constructor exists.
`open_quarantined` intentionally requires a future private consistency/bitness/
re-sharing step before application admission.

This generic byte owner does NOT establish that a bundle contains full Signal
state. Full schema/provider serialization, immutable outbox/intent storage,
4of5 phase/recovery wiring, authenticated fresh MPC input/re-admission and actual
restore tests remain required. No normal RPC/import path or existing burn fence
is changed by this candidate. Storage-key provisioning and honest durable storage
are explicit epoch assumptions, not a trusted external witness.

`CiphertextStore` now persists these encrypted artifacts under their exact content
hash, using no-follow files, immutable installation and file+directory flushes.
Existing artifacts must match exactly; corruption cannot be overwritten silently.
Twelve sanitizer checks include a child saving then exiting without cleanup,
parent reopen/authenticated local-evaluation recovery, idempotency and malformed/
corrupt/symlink/conflicting objects. Only ciphertext reaches disk. This supplies
local persistence, not freshness/quorum/re-admission: an old valid encrypted
artifact still requires the certified-head/fresh-status protocol and private MPC
consistency checks before any provider can consume its state.
