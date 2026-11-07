# Inverse AES circuit

`TlsMpc.AesInverse` implements AES-128 and AES-256 block decryption in Lean,
with symbolic byte operations for the verified Boolean compiler. Its checked
`decrypt` accepts a 16-byte block and a 16-byte or 32-byte key; public shape
errors return `none`.

The reusable-key interface is:

```lean
let expanded := TlsMpc.Aes.expandKey o.aes 8 14 key
TlsMpc.AesInverse.decryptExpanded o 14 expanded ciphertextBlock
```

`o` is `AesInverse.concrete` or `AesInverse.symbolic`. The forward expanded key
is used directly, with round keys visited in reverse. CBC callers can compute
it once and reuse it across blocks. `decryptCore o 8 14 key block` includes that
expansion; AES-128 uses `4, 10`.

The inverse S-box is the existing forward S-box surrounded by inverse affine
byte transforms. Both `invSbox_forward` and `forward_invSbox` are checked for
all 256 byte values by Lean kernel reduction. It uses one 32-AND S-box plus
XORs and wiring. Inverse MixColumns shares two double-xtime corrections within
each column before applying the existing forward mix operation.

`Hom.aes` and `Hom.invSbox` give the generic operation relation.
`decryptExpanded_map`, `decryptCore_map` and `decrypt_map` prove the evaluation
homomorphism, including the checked interface's public errors. Output-length
theorems support composition with padding and authentication logic.
`compiled_decryptExpanded_correct` and `compiled_decryptCore_correct` connect
every numeric output bit to the concrete Lean operation for every assignment.

`check.py` audits 20 theorem endpoints, checks public invalid-shape examples,
exports five artifacts, and compares their clear evaluation with independent
fixtures. The inverse S-box covers all 256 inputs; each AES-128/AES-256 core
and expanded-key artifact has ten OpenSSL/FIPS fixtures, for 296 lanes total.
The public expanded-key inputs use an independent finite-field fixture helper
in Python. That helper is not part of the implementation or compiler.

| Circuit | Optimized AND gates |
| --- | ---: |
| Inverse S-box | 32 |
| AES-128, including key expansion | 6,400 |
| AES-128, supplied expanded key | 5,120 |
| AES-256, including key expansion | 8,832 |
| AES-256, supplied expanded key | 7,168 |

Run:

```sh
python3 SignalReference/AesInverseCircuitWork/check.py
```

`check-report.json` records source/artifact hashes and the audited assumptions:
only `propext`, `Classical.choice` and `Quot.sound`. The compiler refinement is
proved; block-level algorithm agreement with OpenSSL is a differential check.
Equivalence to the actual RustCrypto decryption wrapper remains pending.
Native serialization, adapter optimization and backend execution remain
unverified. This package neither compiled nor executed a native MPC backend;
CBC authentication and release gating are composed separately.
