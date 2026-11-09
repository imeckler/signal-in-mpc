# Fresh public sharded-account fixture

Run `python3 signal_backend/RecoveryWork/FreshShardedFixtureWork/prepare.py` after building the NEW `signal-sharded-session-fixture-oracle` Rust binary in `signal_backend/Oracle` with the pinned offline toolchain/lock. No old account or fixture is modified.

`client.json` is PUBLIC disposable initializer/oracle material: two genuinely distinct recipient sessions, one sender identity/certificate, six actual nonempty Content/DataMessage texts per conversation, 59-byte text-builder inputs, and actual sender/recipient serialized records. Use `account_global_store` (conversation zero's actual store) for account-global keys; both peers are trusted and round-trip checked. Per-conversation global stores have different generated prekey RNG and must not be merged as account state.

`recipient.json` contains only the disposable recipient secrets/records, root public key, public test credentials/UAKs and expected events. It omits sender private identity, sender session snapshots and account-global private stores. Events bind actual inner messages; a new MPC execution may use different fresh outer sealed-sender ephemerals.

The new Rust source directly calls the pinned actual libsignal session/global-store APIs. This fixture extends the prior public source harness to sixteen messages and up to four trusted peers. Its selected established SPQR-phase override remains explicit. It does not establish MPC PQXDH/bootstrap, general session support, private import authorization, durability or deployed service interoperability.

The focused test replays all twelve messages into actual serialized recipient sessions, verifies UTF8 text/timestamp/80-byte padding, and rejects final replays while preserving state. No production account or network side effects occur. Existing head3 account and historical fixtures remain unchanged.
