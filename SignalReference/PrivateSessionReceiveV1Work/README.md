# Selected established session: in-order model candidate

Target libsignal904c8dc/v0.106.1 with lockedSPQRv1.6.0/06959b47. This new version
preserves the held PrivateNewDhReceive/native fixture sources. It consumes the
same actual-parser75B summary and976B model input layout and returns608B.

A private receiver lookup selects the retained chain before **one** symmetric
key derivation, MAC and CBC computation. The fresh path still computes the two
root KDF halves, but its results are unselected for a known ratchet; the known
path preserves all136 sender/root/private/public/sending-state bytes. It updates
the first matching receiving chain and the selected active receiving-PQ chain.
New ratchets require counter0 and computed nonzero agreements; known ratchets
require exact next DR counter and exact next selected active-PQ index. All actual
acceptance masks are computed. No supplied PQ key/authentication flag is used.

The actual `PublicKey::ct_eq` in core/src/curve.rs compares key type and raw
`key_data()` bytes. It does NOT equate high-bit/modp X25519 aliases. The nearby
session.rs comment suggesting noncanonical comparison support is not functional
evidence.624 actual API cases cover208 points, including all19 top-range values
and high-bit aliases. A normalization attempt was rejected before commit when
this actual oracle contradicted it. Lookup therefore reuses raw ReceiverStore
byte equality, while X25519 agreement normalization remains a separate operation.

`check_model.py` checks one actual new-DH then three actual known-ratchet messages,
all608 projected output bytes. Actual Rust confirms sender/root/private136B is
unchanged on the three known receives and both MAC/replay failures preserve its
SessionRecord. Known model rows deliberately have zero unused fresh pair/DHs.
Eighteen computed rejections cover MAC, upstream invalidity, PQ mismatch and
profile exhaustion, replay and valid future/out-of-order wire. The latter is
**deliberately rejected**: this in-order-first profile has no skipped-key/PQ
out-of-order retention. It does not implement full libsignal receive behavior.

Two foundational kernel endpoints prove finish rejection preservation/zero
plaintext and the known-branch sender selection. Whole Hom/compiler composition,
actual RustCrypto/session source refinement and native execution of THIS new
known-path module remain pending. The separate staged native new-DH test does
not cover this new module. No provider/RPC admission, full SPQR KEM epochs,
authenticated fresh prekey bootstrap or recoverable shared-state store is claimed.
