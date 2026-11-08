Candidate-only OT lifetime boundary

BaseMachine.ot_setup is static thread_local. The tested epoch guard reads the
HOST thread's cache, so an empty result does not establish worker OT retirement.
Worker TLS caches normally destruct after worker exit. No OT-based application
capability is justified by the existing guard alone.

OTTripleSetup normally deletes BaseOT objects after setup and deletes temporary
VirtualTwoPartyPlayer objects in close_connections. Its setup jobs use raw
pthread_create/join; exceptions/partial starts are not covered by the tested
ErasingThreadStack mechanism. BaseOT has BitVector seed/choice storage and PRNG
vectors, partly covered by existing capacity/PRNG cleanup, plus secret local
sender/receiver state on those helper stacks. OT::Matrix uses an aligned vector
whose allocator currently frees without wiping capacity. Extension matrices and
any SoftSpoken/libOTe state require explicit ownership treatment. No OT cleanup
or renewal pass has been executed here.

A future isolated candidate should pin USE_KOS=1 to a reviewed supported path
before excluding SoftSpoken state, give every base-OT job a guarded/wiped stack,
join/reap all successful starts on failure, capture job exceptions without
escaping pthread entry, wipe aligned matrix capacity on deallocation, and audit
cached setup/extension objects through thread exit. MAC key shares alphapi,
alpha2i and alphabi are machine-owned persistent authentication state: renewing
them while retaining shares would invalidate those shares. Define retention and
terminal wipe explicitly; do not wipe live keys then continue. Live-prep key
creation and all failure paths need source-bound tests. Refresh remains paused.

These notes refine the earlier audit's conditional nonemptyot_setup guard
observation. They neither assert that Tinier is128-statistical-secure in this
pin (it is rejected by ShuffleSacrifice), nor authorize a production backend.
