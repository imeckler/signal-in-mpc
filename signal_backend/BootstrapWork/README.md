# Private fresh-session bootstrap work

This NEW work area targets the unchanged libsignal v0.106.1 /904c8dc8216073b078a5f2f5090e3da8382e6a92 call path. Recipient bundle/identity data remains private after secret TLS. TLS server authentication is not bundle publication or identity trust authorization. Production gates remain closed.

Required path: typed private PreKey validation with actual trust lookup and both computed XEdDSA signatures; joint base/ratchet scalars; four actual PQXDH agreements plus initial ratchet agreement; pinned Kyber1024 encapsulation with joint entropy; PQXDH KDF/root+chain/PQR; actual initial SPQR negotiation and retained state; first PreKeySignalMessage decrypted by unchanged Rust, then a second send using returned state without an established-phase override.

## Reuse and missing implementation

- `PreKeyWire/Bundle/Validation` and frozen XEdDSA adapter cover the validation prefix, not whole authorization/init. The validation oracle deliberately stops at `load_session`.
- `Pqxdh` is only the private-byte HKDF recurrence from agreement inputs. The new production composition must compute these inputs internally.
- `MlKem` and `MlKemWork/adapter.py` explicitly distinguish Kyber and ML-KEM. Existing numeric circuit tests compare actual libcrux keygen/encap/decap, but no native KEM helper exists. PQXDH uses `kem/kyber1024.rs`, tag08, raw public/ciphertext1568 bytes; it calls `libcrux_ml_kem::kyber1024::encapsulate` despite ML-KEM storage type names. No substitution with tag0A/ML-KEM1024 is permitted.
- Existing X25519 field artifact/conversion helpers can compute agreements and joint clamped scalars; all-zero agreement rejection must feed the whole acceptance predicate.
- SPQR initial A2B is `KeysUnsampled`, not the established fixture phase. Its first send generates incremental ML-KEM768 (`hdr64`, `ek1152`, `dk2400`), authenticates header, polynomial-encodes a chunk and initializes the epoch0 chains from the PQR key. Returned full state must persist. Current `PrivateSpqrSend` handles only selected active chains and cannot replace this.
- Existing private Signal/PreKey protobuf components and CBC/HMAC primitives are reusable only after exact first-message serialization/domain/length binding. Full source refinement and entropy/sampler/backend obligations remain explicit.

First implementation is a staged private native Kyber1024 encapsulation using immutable pinned component artifacts, with no host reconstruction or supplied shared-secret API. Component tapes are compiled once per shape and invoked within one VM entry to avoid exporting a monolithic KEM graph. This is a bootstrap dependency, not a completed fresh-session claim. Later milestones must bind computed agreements/KEM/status into actual init, SPQR negotiation and first/second recipient interoperability.
