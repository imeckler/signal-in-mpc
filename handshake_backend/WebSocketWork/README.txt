Private WebSocket receive work (isolated candidate, application gate unchanged)

HTTP101 checkpoint:
TlsWebSocketUpgrade validates status101, case-insensitive header names and
Upgrade/Connection tokens, OWS, reordered fields and additional field syntax.
It rejects duplicate critical fields, wrong/missing accept, obs-fold, malformed
field names/values and unoffered extensions/subprotocols. The accept value is
public SHA1/base64 of the fresh public client nonce+RFC6455 GUID. Neither
credentials nor response bodies become host bytes. Completion and consumed
position stay shared; coalesced WebSocket bytes are retained by activity masks.

NativeUpgradeResponse uses the pinned180-byte initial state and a constant-cost
byte function. Input activity is a computed0/255 mask from the authenticated
chunk's private length, not a host length opening. Before completion it permits
65536 public byte-work slots (including inactive padding); caller must also bound
receive time. It authenticates only validity/completion at chunk boundaries.
NativeSession's take_private_payload and shared-length comparison must supply
the active-byte mask before actual TLS integration. This connection is still
unfinished. The standalone native fixture uses disposable public synthetic
activity masks; it is not evidence for the full private chunk/TLS integration.

Evidence:
- check_websocket_upgrade.py:598 streaming cases, every header split and byte
  chunks, private-length/padding/codec checks, coalesced frames, malformed fields,
  duplicate headers, missing/wrong accept and unoffered extension negatives.
- Six map/compiler endpoints audited with only propext/Classical.choice/Quot.sound.
  These map proofs are not a full HTTP grammar/refinement theorem.
- Five actual pinned tungstenite::client probes. Connection token lists are an
  intentional RFC6455 acceptance superset to its exact-value verifier. Duplicate
  critical headers/extensions are deliberately rejected by this implementation.
- check_native_websocket_upgrade.py:five parties all0,25.440s; real pinned MPC
  state across partial chunks, inactive slots and coalesced frame activity; wrong
  accept rejection and idempotent terminal runtime abort. No actual service run.
- Reports tls-websocket-upgrade-checks.json and tls-native-websocket-upgrade.json.

Build with lake build websocket_upgrade_emitter websocket_upgrade_checks;
WebSocketWork/prepare.py compiles a separate .deps/tls-websocket-upgrade-native
cache, with explicit exact descriptor and initial state pinned in upgrade.manifest.
Never copy artifacts into canonical or earlier frozen runtime candidates.

Next critical integration:
Frame machine must validate fragmentation/control/close semantics, collect
bounded private messages/control payloads, correlate ChatConnection response IDs
and statuses, send masked private pong/close as needed, and carry actual private
upgrade+sealed-sender requests through persistent HTTP1.1 TLS against a local
protocol-faithful server. NativeSession wrappers for the crypto-owned upgrade,
service and typed901-to903 result adapters are compiled, not a service milestone.
Variable-length service producer/counter transitions remain crypto-owned.
