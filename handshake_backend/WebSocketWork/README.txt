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
NativeSession's take_private_payload supplies chunks; TlsWebSocketActivity now
proves exact bounds/source validity and each0/255 activity predicate. The native
feed method authenticates that status before invoking the byte consumer. Its
five-party fixture passes private-length chunks50/41/remainder padded to128,
including inactive bytes and coalesced frame data. Actual Session receive/TLS
connection remains unfinished; no received body is opened by the API.

Evidence:
- check_websocket_upgrade.py:598 streaming cases, every header split and byte
  chunks, private-length/padding/codec checks, coalesced frames, malformed fields,
  duplicate headers, missing/wrong accept and unoffered extension negatives.
- Six map/compiler endpoints audited with only propext/Classical.choice/Quot.sound.
  These map proofs are not a full HTTP grammar/refinement theorem.
- Five actual pinned tungstenite::client probes. Connection token lists are an
  intentional RFC6455 acceptance superset to its exact-value verifier. Duplicate
  critical headers/extensions are deliberately rejected by this implementation.
- check_native_websocket_upgrade.py:five parties all0,66.852s; real pinned MPC
  private-length activity and state across padded chunks and coalesced frame
  activity; wrong accept and terminal abort. Prior byte-only run25.440s retained.
- Reports tls-websocket-upgrade-checks.json and tls-native-websocket-upgrade.json.
- check_websocket_activity.py:183 independent mask cases, capacities0/1/16/128/
  900/16385, five foundational-only bounds/map/compiler endpoints. The compiled
  native cap128 artifact matches a fresh proved-emitter export byte for byte.
- Frame algorithm now passes67 public cases and seven pinned tungstenite probes;
  map/compiler theorems plus8-bit and positive16-bit decrement proofs check.
  The binary profile supports bounded canonical16-bit frames, continuation and
  interleaved control, valid close codes/UTF8, and terminal close. Invalid close
  codes reject directly; pinned tungstenite converts them to close1002. Native
  frame/control integration and a full grammar refinement theorem are pending.

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

Actual persistent service candidate (2026-11-08):
NativeWebSocket.h composes authenticated private HTTP101/frame/control/response
machines. NativeSession accepts only authenticated incoming handles for RPC18;
validity/completion/control kinds are explicit public decisions. Body,headers,
request IDs and true application lengths stay shared. Selected partial state
survives declared epoch checkpoints; discarded inputs/runtime history precede
the host-stack barrier. Producer slots unlock only after correlated2xx, not send.
Local preparation failures join a public collective gate before producerVM work.

check_native_websocket_service.py passed allfive parties547.301s,raw
7c7d8288524507fb: privateBasic upgrade,two actual variableSSv1 relay requests,
actual targetlibsignal server decrypt/cert/inner checks,fragmentedresponses,
interleaved3pongs,private requestcorrelation,clientKeyUpdate,terminalabort.
Sources+worker snapshots and hashes are inraw; canonical runtime unchanged.
This uses disposable publicfixture initialstate/recipient and local endpoint,
never a live account. Canonical application gate remainsclosed; refreshpaused.

Bounds are firstintegration profiles: incomingpublicbacking1..128, frame/message
4096, max4controlresponses/chunk, onependingresponse. Later production requires
bounded multiplexed conversations/correlation and broaderrecord profiles.
ASCII-bounded responseheader validation is an explicit narrower profile; actual
fixture service headers are ASCII. No wholeRustresponse refinement, recoverable
ratchet persistence, fullmobilecompromise/OS-erasure,or throughput claim follows.
Peerclose guard permits only its tagged close response; dedicated negative
close/reservationfailure integrated tests remain pending.
