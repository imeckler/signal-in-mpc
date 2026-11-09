# Certified archive domain gate (candidate)

`CertifiedArchiveGate` validates four-member certificates for the exact
Reserve→Commit chain, one slot/attempt/context/manifest, the prior
commit digest, and the exact committed ciphertext bundle.
It requires four distinct fresh-challenge signed statuses and rejects any observed
higher slot, including an unresolved reservation. The authorized local ciphertext
digest determines the expected archive domain: member identity, membership epoch,
slot, program manifest, schema and sharing epoch. `OwnShareBox` must authenticate
against this returned domain before raw-field import. No shared value is opened.

This is a public authorization component, not a complete recovery coordinator.
The caller must obtain the prior commit from an authenticated chain to
the configured genesis, choose an unpredictable fresh challenge, verify/read the
exact immutable ciphertext, and maintain durable honest no-double-sign journals.
A certificate does not establish that the private payload implements its named
schema. This component deliberately cannot create `Bits`, mark a provider ready,
or replace private MPC consistency checks. The active authorize_committed path requires no remote acknowledgement: pending
outboxes survive later unrelated commits. The historical authorize overload can
check an extra publication certificate, but it is not delivery evidence and is
not used by LocalAccountCheckpoint.

## Integration contract still closed

The TLS owner identified a pre-Session embedding boundary: after all five nodes
agree that local certificates/domains/ciphertexts are ready, perform checked
private re-sharing, destroy import helpers/inputs, retire the worker epoch under
`ErasedHostCall`, complete its host barrier, and only then construct fresh TLS.
Provider handles may activate only after the fresh authenticated HTTP upgrade.
No old TLS keys, nonces, sequence numbers or handles are recoverable state.
That hook and the helper-constructor failure/retirement path are not yet wired.

A full account checkpoint must atomically contain reusable account credentials,
connection-global request-ID cursor, every conversation's complete session state,
frozen pending intent and immutable outbox. The current 611-byte sender profile
is insufficient: full receiver/skipped-key, identity/root/DH, SPQR negotiation/KEM
and pending-prekey metadata are missing from that owner. No `full state` schema
identifier or provider admission is supplied here in place of implementing those
fields. The gate accepts the embedding's schema digest only as a domain binding;
semantic schema validation remains a separate mandatory dependency.

`check_phase.py` runs 13 actual Ed25519 positive/rejection cases under ASAN/UBSAN:
wrong chain/attempt/phase/manifest, changed outbox digest, insufficient/duplicate
certificate or status signers, stale challenge, and observed higher reservation.
This evidence is scoped to public phase/domain validation, not complete recovery,
Byzantine MPC security or performance.
