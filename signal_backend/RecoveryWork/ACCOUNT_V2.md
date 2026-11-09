# Candidate bounded account V2

`AccountLayoutV2` owns four global sections (credentials38, identity65,
canonical global-store buffer8195, next request ID8) and seven sections per
conversation: recipient binding69, canonical SessionRecord5550, service611,
selected state525, frozen intent612, four outboxes5208, dispositions4.
Device1 is this profile; binding carries recipient registration ID32, not device.
Every native bit cell must have exactly one register. Packed64 input is rejected.

The validator checks dimensions, canonical buffers, cursor domain, record/
selected/service coherence, local identity byte bindings, recipient UUID/
registration/identity/UAK bindings, intent shape, outbox presence and disposition.
Its five Hom/compiler endpoints use only foundational axioms. This is structural
coherence, not full semantic admission: the opaque global store codec/prekey
signatures, local private/public key agreement, certificate/account provenance,
full SPQR epoch/skipped/prekey state and allowed transitions still require their
actual implementation bridges and initialization. The public fixture uses actual
Rust SessionRecords/global stores, but synthetic canonical outboxes; it cannot
supply an authorized production account or claim actual encrypted outbox capture.

Required integration order: fresh signed current-head challenge and complete
certificate ancestry; authenticated local full-section ciphertext; checked
full-GF128 import; private semantic/coherence validation; destroy helper owners;
complete import host barrier; retire initialized VM/transport; complete retirement
host barrier; construct one-shot account capability; fresh TLS and authenticated
HTTP101; admit durable conversations and pending outboxes. No old TLS state is
restored. Resume leases bind head, slot, ordinal and fresh joint boot context.

Required work remains: actual complete-account capture/import/normal-provider
integration and tests; unresolved frozen reservations and crash publication;
complete global-store/private semantic validation; fresh PQXDH, SPQR epochs,
skipped-key support; full source refinement. No full-account activation is claimed.
