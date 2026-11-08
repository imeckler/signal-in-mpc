Full MPC transport-epoch renewal candidate (application gate remains closed)

  python3 scripts/prepare_tls_transport_epoch.py
  python3 scripts/check_tls_transport_epoch.py --build

The new source-only runtime layers frozen lifetime candidates without modifying
them or the canonical backend. It renews both per-thread protocols and the host
Player, using unique connection namespaces. Every MPC TLS context requires
TLS1.3, disables tickets and enables SSL_OP_CLEANSE_PLAINTEXT. Sender/Receiver
and generic helper workers use owned stacks that are wiped after join. The
Collector can reacquire machine.get_player() after replacement rather than
retaining a dangling Player reference. Unsupported machine-global shuffle,
external-client, host OT-cache and child-Player state rejects before mutation;
thread OT-cache use also prevents successful retirement acknowledgment.

TLS1.3 avoids static key-exchange modes. Renewing transport keys is necessary:
a retained channel key could decrypt captured old MPC share traffic. Read-buffer
cleansing follows the installed OpenSSL option contract:
https://docs.openssl.org/3.5/man3/SSL_CTX_set_options/
The application still owns and must cleanse SSL_read/write input/output buffers.
OpenSSL internal key cleanup remains a trusted-library assumption, not a proof.

The public synthetic five-party fixture preserves X25519/output shares across
repeated renewal and runs Collective operations after host-Player replacement.
The first transport run passed all native cases but its final source-integrity
check rejected concurrent Makefile additions for the host-stack test. Its logs
are retained under raw/tls-transport-epoch/7c6f2bf96f4be68e; use the final report.

ErasedHostCall is a tested integration building block: successful and throwing
host actions run on fresh owned stacks, destroy TLS/thread-local state, join,
then wipe before returning to the caller. Nesting is refused. It is not yet wired
into production bootstrap/RPC/destruction, so no Session retirement receipt is
issued. Next concrete work: bootstrap and dispatch exclusively through this
runner; bind a profile-restricted lifecycle capability to Session retire/rotate/
abort; return replies only after the host action's stack was wiped. Guard that
all old owned handshake/key copies are discarded before renewal while retaining
application/producer shares. Then run real repeated native application records,
KeyUpdate and failure/abort/replay checks against the local TLS peer.

No complete retirement, application readiness, OS/kernel/persistence/compiler-copy
erasure or throughput claim. Sharing refresh stays paused.
