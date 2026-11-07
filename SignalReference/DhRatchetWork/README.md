# Signal DH root and chain derivation

`TlsMpc/Signal/DhRatchet.lean` composes the existing X25519 field circuit with
Signal's `RootKey::create_chain` KDF shape: HKDF-SHA256 with the old root as
salt, the canonical agreement bytes as input and `WhisperRatchet` as info.
The 64 bytes split into a new root and chain; the new chain counter is zero.
An all-zero agreement produces a secret rejection status, retains the old
root and zeros the chain. The circuit's output is 69 secret bytes.

The 15 audited endpoints prove symbolic/concrete/compiler equality, rejection
behavior, and composition of the field and Boolean artifacts. The composition
theorem explicitly requires the exact canonical field-to-byte relation. It
does not establish the unverified MPC conversion protocol's security or
faithful equality to the actual dalek/RustCrypto wrappers. Those reference
obligations remain open.

`adapter.py` connects the two artifacts using the existing mixed backend.
Root, scalar, peer key, agreement, status and outputs remain shared registers.
The private scalar stays 256 exact bits until X25519 clamps it; only the peer
u-coordinate is top-bit masked and reduced into the Curve25519 base field.
The adapter does not reveal any output. The conversion implementation retains
its documented random-check/masked-opening trust boundary.

`program.mpc` is a compilation harness. It accepts five XOR shares of every
root/scalar/peer bit and stores output shares in memory. It does not run the
full Signal DH-ratchet state machine: fresh-key generation, peer ratchet-key
selection, skipped-key handling, two-direction state updates, atomic commit
and proactive refresh remain outside this selected operation.

Reproduce the fixture/proof check from the repository root:

```sh
python3 scripts/check_lean_signal_dh_ratchet.py
python3 scripts/check_lean_signal_dh_ratchet.py --compile-backend --compile-mixed
```

The first command exports both Lean artifacts and checks 46 public X25519
cases, 81 root/chain cases, and four executions of this adapter using public
clear primitives. The optional flags compile the Boolean stage at batches
1/16 and the mixed field/Boolean composition. Compilation and public clear
fixtures are separate from native MPC execution; no native execution or
throughput claim is made. The latest reports are
`benchmarks/results/lean-signal-dh-ratchet-checks.json` and
`SignalReference/dh-ratchet-proof-check.json`.
