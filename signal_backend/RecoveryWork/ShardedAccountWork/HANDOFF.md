# TLS/sharded account handoff

Verified checkpoint: `integrated-report.json` and `integrated-evidence.json` bind the actual two-conversation cut/restart/continued-send run. Both five-party groups passed with empty cleanup and unchanged1191 pins. Twelve fresh recipient texts, one original-request replay rejected as duplicate with unchanged recipient state, two reordered response pairs, KeyUpdate and terminal handle rejection passed. No own live process remains. Public-program manifest remains511b04805187ae7f6756b8866e406bb956b182f80a617907999eda8f01c24a49.

The NEW active account is `benchmarks/results/raw/tls-sharded-account/eba2a5429624f308/account`, Commit10. Preserve it and its marker. Earlier heads are history, not restart points. Historical c1 head3 remains untouched. ACK observations coalesce into later selected-shard/outcome checkpoints; a crash may therefore retain an immutable uncertain outbox. Retransmission preserves Signal bytes/request ID, uses fresh WS masks and TLS, and does not establish unique delivery.

## Mandatory remaining TLS/account work

- Replace linear `SendProvenance::latest_send` history walk and its1,000,000-step limit with authenticated per-conversation last-wire provenance/index. Current-head ancestry is also linear; the journal has a64MiB bound. Raising limits alone does not solve lifetime scaling.
- Shard/refine the8192-byte global trust/prekey store. The1000 opaque-directory-slot control is not1000 Signal peers. Working set is four active conversations; input admission is bounded64 and not a production refill/queue interface.
- Four retained outboxes and public chosen-cell reuse can falsely backpressure despite another eligible cell. Preserve pending/rejected/uncertain entries. Durable resolution/compaction and unresolved higher-Reserve handling remain incomplete (the latter rejects safely).
- Native stale server ACK injection after cell reuse, never-sent private import and rejected-blocked private activation are not in this positive run; their component/host proofs/tests must not be relabeled native evidence.
- Normal default provider/resolver remains absent. Explicit fixture embedding is not production provisioning, secure storage/key management or actual fresh account/Signal session bootstrap.
- Finish circuit/spec/compiler/source refinement gaps, including private parser/WS and lifecycle composition. No blanket process/OS-copy erasure or mobile-compromise/refresh guarantee.
- Compact Boolean MPC plus checked Fp conversion remains unresolved undert2. Current full-GF128 Boolean backend and every-record epoch policy are slow; the27.8msg/s goal is unmet. Preserve decision frontierd9721df and existing security guards; no silent threshold/statistical change.

No additional optional TLS optimization or broad baseline run is queued. The next separable implementation track is actual Signal fresh-session bootstrap and retained state transitions; crypto retains primitive/wrapper source refinement. Existing prepared-state fixtures, selected-SPQR overrides and file names do not establish that path.
