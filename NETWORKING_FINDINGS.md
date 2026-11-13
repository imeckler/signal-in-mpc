# Networking findings: proxies, transport, ClientHello, server-side limits

Written 2026-11-12 from sources on disk only (no network, nothing built, nothing run):
libsignal v0.106.1 (`.deps/libsignal-v0.106.1`), the vendored crates (`.deps/libsignal-vendor`:
h2 0.4.16, hyper 1.10.1, hyper-util 0.1.20, tungstenite 0.29, the `boring` Rust wrapper; BoringSSL's
C sources are NOT on disk), Signal-Server (`/Users/izzy/repos/Signal-Server`) and this repository's
Lean client. It answers sections 3, 4 and 5 of `NETWORKING_TODO.md`.

Paths below are relative to `.deps/libsignal-v0.106.1/rust/` (libsignal), `.deps/libsignal-vendor/`
(vendored crates), `Signal-Server/service/src/main/java/org/whispersystems/textsecuregcm/` (server,
shortened to `S/`) or this repository, unless they are absolute.

Confidence labels:
- **verified**: read in the source on disk, with the lines cited.
- **inferred**: follows from the source plus general knowledge of a library or a deployment that is
  not on disk (said which).
- **unknown**: needs a live capture, a probe of the real service, or BoringSSL's sources.

## Summary

| # | Question | Answer | Confidence |
|---|---|---|---|
| A1 | How does libsignal 0.106.1 connect through a Signal TLS proxy? | Outer TLS to the proxy's own host (SNI = proxy host, no ALPN, system trust store), then **the unchanged direct route inside it**: inner TLS with SNI `grpc.chat.signal.org`, ALPN `h2`, Signal's pinned roots, TLS 1.3 minimum, and the WebSocket over **HTTP/2 extended CONNECT**. The proxy route only replaces the TCP leaf of the route. | verified |
| A2 | Can the server learn our real address through the proxy? | Not from anything in Signal-Server: the h2 front takes the address from a PROXY-protocol header (written by Signal's own load balancer) or the TCP peer, and **overwrites** `x-forwarded-for` itself. Through a TLS proxy that address is the proxy's. | verified (server code); inferred (production load balancer, proxy software) |
| A3 | Does the server treat proxied connections differently? | No code path distinguishes them. Open WebSockets are counted per ASN region and per user agent (metrics only). The closed-source spam filter sees each send's request context (address, user agent) and could. | verified (open source); unknown (spam filter) |
| A4 | SOCKS and HTTP-CONNECT proxies? | Same inner route as direct (`grpc.chat.signal.org`, `h2`); the proxy is asked for `grpc.chat.signal.org:443` (by name by default). A user-configured system proxy falls back to direct if it fails. | verified |
| A5 | Does domain fronting expose request paths to the CDN? | **Yes for classic fronting** (TLS ends at the CDN, HTTP/1.1, `Host: reflector-…`, path prefix `/service`), but that route is **switched off** in the 0.106.1 app bridge. Its replacement, the **reflector**, tunnels an end-to-end inner TLS session (to `grpc.chat.signal.org`, `h2`) inside a WebSocket to the CDN: the CDN does **not** see paths. NETWORKING_TODO's "ruled out" holds for classic fronting only. | verified |
| B | Is HTTP/1.1 to `chat.signal.org` normal through a proxy? | **No.** In libsignal 0.106.1 *every* chat route (direct, Signal TLS proxy, SOCKS, HTTP proxy, reflector) uses `grpc.chat.signal.org` + `h2` + extended CONNECT. No current libsignal route speaks HTTP/1.1 to `chat.signal.org`. Worse: our user agent claims `libsignal/0.107.0`, a version that never uses that route, so the combination is impossible for a genuine client. CLIENT_FINGERPRINT.md and NETWORKING_TODO section 4 should be corrected. | verified (libsignal); inferred (who else still uses it) |
| C | HTTP/2 inside the MPC client: what, and how much? | All HTTP/2 framing, SETTINGS, flow control, PING/GOAWAY handling and the send-side HPACK of the unauthenticated CONNECT are **public** and can run in the controller. Circuits only change shape (9-byte DATA header, maybe a 1024-byte record split). Per-message AND overhead **well under 1 %** of today's ≈2.9M. The cost is Lean code and proofs: an HTTP/2 layer under the reveal policy (whose WebSocket layer has about 540 theorems today). gRPC sends (libsignal's default on h2 connections) are a separate, larger project. The local server already exposes the h2 endpoint (`127.0.0.1:18051`, h2c, the same Netty front as production). | inferred (estimate); verified (what libsignal/h2 send, local config) |
| D | ClientHello parity with least MPC work? | Official: suites 1301,1302,1303 (order depends on AES hardware), groups x25519,P-256,P-384 with **one** X25519 key share, **no post-quantum share** (libsignal says the chat server does not support ML-KEM in TLS yet), no GREASE/ECH/ALPS, no padding at this length. Minimal plan: list P-256/P-384 in `supported_groups` without key shares (no circuits, fails closed on a HelloRetryRequest); list 1302/1303 **only if** a TLS-only probe shows the server picks 1301 for libsignal's list, otherwise build AES-256-GCM-SHA384 first; SNI/ALPN parity needs the HTTP/2 layer (the h2 front only speaks h2). | verified (libsignal config, server ALPN); derived (BoringSSL internals, via CLIENT_FINGERPRINT.md); unknown (server cipher preference) |
| E | The small fingerprint items: where and how big? | Ping keepalive and WebSocket Close are controller-only (no new circuit except possibly one tiny public-seal size). Request ids from 0 changes request shapes (two id widths) but the layout theorems are already parametric. Canonical (unpadded) ids need a new kernel and restated request theorems. Our sessions also end with a TCP abort and no TLS `close_notify`. | verified (code locations); inferred (proof impact) |
| F | Operator warnings | Sealed sends have **no per-sender or per-IP limit** in open-source code; only a per-destination byte bucket (128 MiB, refilling about 2 KB/s). Prekey fetches with an access key are unlimited (authenticated ones: 6 per 10 min). The spam filter (closed) sees address and user agent of every send, can return 428, and a 428 can only be cleared by **our authenticated account** solving a captcha. Recipients can report our account (with a server token minted at send time). An old user-agent version gets 499. | verified (open source); unknown (production dynamic config, spam filter) |

---

## A. Signal's proxy routes, the other proxies, and domain fronting

### A.1 How a route is built (background for everything below)

libsignal describes a connection as nested "route" values: TCP → TLS → HTTP → WebSocket. The chat
route provider is built in the app bridge:

- `bridge/shared/types/src/net/chat.rs:622-657` (`make_route_provider`): the chat routes are
  `env.chat_domain_config.connect.route_provider_with_options(...)`, wrapped in a
  `DirectOrProxyProvider` whose `mode` comes from the connector's proxy setting. **verified**
- `net/src/env.rs:42-64` (`DOMAIN_CONFIG_CHAT`): hostname `grpc.chat.signal.org`, port 443,
  Signal's own root certificates, `min_tls_version: TLS1_3`, `http_version: Http2`. The `proxy`
  field (path prefix `/service`, Fastly and Google front configurations) is for domain fronting
  only; the comment at line 58 says "This won't use H2, but we still want it as a fallback". **verified**
- `net/src/env.rs:534-604` (`route_provider`): an `HttpsProvider` whose direct routes use the
  configured HTTP version, plus a `DomainFrontRouteProvider` forced to `HttpVersion::Http1_1`
  (lines 592-596). **verified**
- `net/infra/src/route/http.rs:171-205`: the direct routes get `set_alpn(Alpn::from(Http2))`
  (`h2`), host header `grpc.chat.signal.org`, empty path prefix; fronted routes follow. **verified**

### A.2 Signal TLS proxy (`sgnl://` links, scheme `org.signal.tls`)

How it is made (**verified**):

1. `net/infra/src/route/proxy.rs:238-262`: a TLS proxy has a host, a port (default 443) and
   `RootCertificates::Native`, i.e. the system trust store ("Proxies that use TLS are permitted to
   use any valid certificate, not just our pinned ones", lines 234-236). No usernames.
2. `net/src/connect_state.rs:907-916`: a Signal TLS proxy is `ProxyOnly` (never falls back to a
   direct connection); SOCKS and HTTP proxies are `ProxyThenDirect` because they may have been set
   system-wide.
3. `proxy.rs:363-409` and `484-514`: for every route the inner provider produced, **only the TCP
   leaf is replaced**: `route.replace(|tcp_route| DirectOrProxyRoute::Proxy(...))`. The new leaf is
   a TLS route to the proxy: SNI = the proxy's host name, **`alpn: None`**, `min_protocol_version:
   None`, system roots (lines 500-513).
4. `net/infra/src/tcp_ssl/proxy.rs:43-65`: connect TCP to the proxy, run the outer TLS handshake
   (same `ssl_config` as everything else, so libsignal's signature algorithms and curve list, but no
   ALPN and no TLS 1.3 minimum), and hand the outer TLS stream up as the "TCP" stream of the
   original route.
5. The original route above the leaf is untouched: inner TLS with SNI `grpc.chat.signal.org`, ALPN
   `h2`, Signal's pinned roots, TLS 1.3 minimum; then HTTP/2 and the extended-CONNECT WebSocket
   (`net/infra/src/ws.rs:170-173` picks `connect_http2` because the HTTP fragment says `Http2`).
   The test `net/infra/src/route.rs:877-934` (`tls_proxy_route`) shows exactly this shape: inner
   fragment kept, proxy TLS route as its leaf.

So **the route through a Signal proxy is the direct route with a different leaf**: same inner SNI,
same ALPN `h2`, same HTTP/2 extended CONNECT, same `:authority grpc.chat.signal.org`.

What the proxy operator sees (**inferred** from the route shape; the proxy software,
Signal-TLS-Proxy, is not on disk): our IP address; the outer handshake; after decrypting the outer
layer, the **inner ClientHello in the clear** (SNI `grpc.chat.signal.org`, our TLS fingerprint,
and the seconds-long gap before our Finished); every inner record's size and timing. Not requests,
recipients or contents. An on-path observer between us and the proxy sees the outer SNI (the proxy
domain) and TLS-inside-TLS size patterns.

**Unknown, and important:** whether the proxy software forwards SNI `grpc.chat.signal.org`. The
published Signal-TLS-Proxy reads the inner SNI and relays only allow-listed Signal host names
(from memory of that project; not on disk). If a volunteer proxy runs an old allow-list without
`grpc.chat.signal.org`, current apps cannot use it at all. Check the current upstream
configuration before relying on public proxies.

### A.3 What Signal-Server can learn of the original address

The h2 front (what `grpc.chat.signal.org` reaches) is `S/grpc/net/OmnibusH2Server.java`
(**verified**):

- `OmnibusH2Server.java:111-144`: per TCP connection, in order: idle timer, connection counter,
  **`ProxyProtocolHandler`** (line 123), `ProxyMessageAttributeSetterHandler`, then (unless h2c) an
  SNI handler and ALPN negotiation that accepts **only `h2`** (lines 128-139).
- `S/grpc/net/ProxyProtocolHandler.java:24-45`: if the connection starts with a PROXY-protocol
  header (HAProxy v1/v2) it is decoded and its source address kept; otherwise the bytes go on to
  TLS. A metric counts both cases (line 36, 41). Only one header is consumed.
- `S/grpc/net/OmnibusH2StreamHandler.java:104-110`: for every new stream the front **sets**
  (replaces) `x-forwarded-for` with the PROXY-protocol address, or else the TCP peer address, before
  forwarding the stream to the WebSocket server (`/v1/websocket`, `/v1/provisioning`) or the gRPC
  server (`S/WhisperServerService.java:1043-1048`).
- `S/grpc/RequestAttributesInterceptor.java:49-63`: gRPC services take the last entry of that
  header, "set by a trusted intermediate proxy … from a PPv2 header that comes from a trusted
  load-balancer" (comment, lines 51-52).

Consequences:
- A client-supplied `x-forwarded-for` is discarded on this path (the front overwrites it); and on a
  TLS proxy route there is no HTTP layer the proxy could add one to anyway. **verified**
- The PROXY-protocol header is written by Signal's own load balancer in front of the h2 server
  (**inferred** from the comment and from the static addresses in `env.rs:43-47`, which look like
  AWS Global Accelerator). It carries the address that connected to Signal: the proxy's. A Signal
  TLS proxy cannot inject its own PROXY header: Signal's load balancer's header comes first and the
  handler only consumes one, so a second one would break the TLS handshake. **inferred**
- On the HTTP/1.1 path (`chat.signal.org`) Jetty trusts forwarded headers
  (`useForwardedHeaders: true` in upstream `service/src/test/resources/config/test.yml:554-557`;
  production's front for that host is unknown). Not relevant to an h2 client.

Whether proxied connections are treated differently (**verified** for open source):
- Nothing in the open-source server identifies "came through a proxy". There is no flag, no
  separate rate limit, no route-specific code.
- Metrics only: `S/metrics/OpenWebSocketCounter.java:58-74` counts open WebSockets per **ASN
  region** of the remote address and per parsed user agent (platform, version); PROXY-protocol
  detection is counted (above).
- The spam filter is loaded at runtime from a closed-source module (`S/WhisperServerService.java:898-950`,
  `ServiceLoader.load(SpamFilter.class)`, no-op if absent). For HTTP/WebSocket sends it receives the
  whole request context (`S/spam/SpamChecker.java:27-32`), which includes the remote address and
  user agent. What it does in production is **unknown**.

### A.4 SOCKS and HTTP(S) proxies

**verified**, `net/infra/src/route/proxy.rs`:
- Parsing (lines 264-302): `http` (port 80, no TLS to the proxy), `https` (port 443, TLS to the
  proxy with system roots and ALPN `http/1.1`, lines 583-592), `socks4`/`socks4a`,
  `socks`/`socks5`/`socks5h`. HTTP proxies always let the proxy resolve the name
  (`resolve_hostname_locally: false`); `socks5`/`socks4` resolve locally, `socks5h`/`socks4a`
  remotely.
- `to_proxy_route` (lines 528-597): the target is the original TCP leaf's host and port, i.e.
  `grpc.chat.signal.org:443`. HTTP proxies get `CONNECT grpc.chat.signal.org:443` with a `Host`
  header and an optional `Proxy-Authorization` (`tcp_ssl/proxy/https.rs:194-221`).
- Everything above the leaf is the direct route again: inner TLS to `grpc.chat.signal.org` with
  `h2`.
- Mode `ProxyThenDirect` (`connect_state.rs:907-916`): if the proxy fails, the app connects
  directly.

What the proxy sees: our address, the target name, the inner ClientHello, sizes and timing. What
the server sees: the proxy's exit address.

### A.5 Domain fronting and the reflector

Classic domain fronting (**verified**):
- `env.rs:254-287`: fronts are Fastly (`http_host: reflector-signal.global.ssl.fastly.net`, SNI one
  of `github.githubassets.com`, `pinterest.com`, `www.redditstatic.com`) and Google
  (`reflector-nrgwuv7kwq-uc.a.run.app`, SNI one of five Google names).
- `route/http.rs:113-168`: TLS **to the CDN** with the innocuous SNI and ALPN `http/1.1`; HTTP/1.1
  with `Host: <http_host>` and the path prefix (`/service` for chat). The CDN terminates TLS and
  sees the full HTTP traffic: paths (recipient UUIDs), headers (access keys), bodies.
  NETWORKING_TODO's reason for ruling it out is **confirmed** for this route.
- But in 0.106.1 the app bridge never enables it: `bridge/shared/types/src/net.rs:67-89` sets
  `enable_fronting` from `use_fallbacks`, and the only construction is
  `EndpointConnections::new(&env, false, EnforceMinimumTls::Yes)` (line 165). **verified**

The reflector (new censorship-circumvention route, **verified**):
- Enabled by `set_censorship_circumvention_enabled` (`bridge/shared/types/src/net.rs:201-220`);
  used as `DirectThenProxy` when no explicit proxy is set (`net/infra/src/tcp_ssl.rs:74-88`).
- `proxy.rs:599-640` and `net/infra/src/tcp_ssl/proxy/reflector.rs:203-251`: outer TLS to the CDN
  (fronted SNI, ALPN `http/1.1`), an HTTP/1.1 WebSocket upgrade to `/tls-tunnel` with `Host:
  reflector-…`, the app's `user-agent`, and `x-signal-host: grpc.chat.signal.org` (line 31,
  221-230); then the **original route's TLS session runs end to end inside WebSocket binary
  frames** (`ReflectorStream`, lines 90-195; at most 64 KB per frame).
- So the CDN and the reflector see our address, the outer upgrade, the inner ClientHello and
  sizes/timing, **not** request paths. Signal sees the reflector's egress address (Fastly / Google
  Cloud; shared with censored-region users). Whether the reflector adds anything identifying is
  **unknown** (its code is not on disk).
- Caution: this is infrastructure Signal runs for censored users; bulk traffic from a
  non-censored client over it would be conspicuous and arguably abusive. Listed for completeness,
  not recommended.

---

## B. What distinguishes our transport, route by route

### B.1 What the official client sends (libsignal 0.106.1)

| Route | Outer layer | Inner TLS SNI | Inner ALPN | HTTP | WebSocket set-up |
|---|---|---|---|---|---|
| Direct | none | `grpc.chat.signal.org` | `h2` | HTTP/2 | extended CONNECT (RFC 8441) |
| Signal TLS proxy | TLS to proxy host, no ALPN, system roots | `grpc.chat.signal.org` | `h2` | HTTP/2 | extended CONNECT |
| SOCKS / HTTP proxy | SOCKS5 or `CONNECT grpc.chat.signal.org:443` | `grpc.chat.signal.org` | `h2` | HTTP/2 | extended CONNECT |
| Reflector | TLS + HTTP/1.1 WebSocket to CDN | `grpc.chat.signal.org` | `h2` | HTTP/2 | extended CONNECT |
| Classic fronting (disabled in 0.106.1) | none | CDN name | `http/1.1` | HTTP/1.1, `Host: reflector-…`, `/service` prefix | HTTP/1.1 upgrade |

Evidence (**verified**): A.1-A.5 above; `net/infra/src/ws.rs:177-252` (HTTP/1.1 upgrade, used only
when the route says HTTP/1.1) and `254-426` (HTTP/2).

The HTTP/2 CONNECT request (**verified**, `net/infra/src/ws.rs:314-325`,
`net/infra/src/http_client.rs:78-98`, `net/src/chat.rs:240-264` and `312-319`):
- `:method CONNECT`, `:protocol websocket`, `:scheme https`, `:authority grpc.chat.signal.org`,
  `:path /v1/websocket/` (`env.rs:920`); h2 writes pseudo-headers in the order method, scheme,
  authority, path, protocol (`h2-0.4.16/src/frame/headers.rs:713-743`).
- Then libsignal's headers in insertion order: authenticated socket `authorization`,
  `x-signal-receive-stories`, (languages if any), then `user-agent`; unauthenticated socket only
  `user-agent` (Android passes no languages, per CLIENT_FINGERPRINT.md).
- Then **`sec-websocket-version: 13` last** (it is appended after the route's headers,
  `ws.rs:317-323`). Correction to CLIENT_FINGERPRINT.md (c), which puts it before libsignal's
  headers. No `Sec-WebSocket-Key`, no `Connection`/`Upgrade` (RFC 8441).
- Any 2xx is accepted (`ws.rs:356-376`).

On an h2 connection, typed API calls go over **gRPC on the same connection** unless remote config
says `ws` (`net/chat/src/ws.rs:173-185`: default `UseGrpc`; keys at
`bridge/shared/types/src/net/remote_config.rs:109-119`, including
`grpc.MessagesAnonymousSendSingleRecipientMessage`). Over HTTP/1.1 there is no shared h2 connection,
so everything uses the WebSocket. Whether Signal's remote config currently sends sealed sends over
gRPC or WebSocket is **unknown** (server-side remote config).

### B.2 Ours today

`TlsWire.Config` default `alpn := ["http/1.1"]` (`TlsMpc/TlsWire.lean:76-82`), SNI `chat.signal.org`
(configuration), HTTP/1.1 upgrade `GET /v1/websocket/` with `Host: chat.signal.org`,
`Sec-WebSocket-Key`, and the libsignal-profile header order (CLIENT_FINGERPRINT.md (c)).

### B.3 Is HTTP/1.1 normal anywhere?

**No route of libsignal 0.106.1 produces it** (**verified**: B.1). The belief that "proxied
clients use HTTP/1.1" came from the `env.rs:58` comment, which is about the domain-fronting routes,
and those are disabled in the app bridge. HTTP/1.1 WebSockets to `chat.signal.org` come only from
(**inferred**): apps with libsignal before 0.97.1 (released 2026-07-10, so builds about four months
old; Signal apps expire old builds, and the server can block versions by user agent with status 499,
`S/filters/RemoteDeprecationFilter.java:83-88, 117-170`), and third-party clients with their own
network code (for example signal-cli-style tools), i.e. mostly automation. Whether Signal-Android's
own OkHttp code still sends anything to `chat.signal.org` is **unknown** (app sources not on disk).

The sharpest point: we send `user-agent: Signal-Android/8.36.0 Android/35 libsignal/0.107.0` over
HTTP/1.1 to `chat.signal.org`. A genuine client with that libsignal never does this, so the server
can single us out with one log line, on any route, proxy or not. Until the HTTP/2 layer exists,
weigh a user agent consistent with HTTP/1.1 (an older version, near or past expiry) against this
contradiction; neither is good.

---

## C. HTTP/2 inside the MPC client: plan and cost

### C.1 What the official client puts on the wire (from the vendored crates)

All **verified** from source unless marked; exact record boundaries are **unknown** without a
capture (see C.6).

1. Connection preface `PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n` (24 bytes), written on its own with
   `write_all` before anything else (`h2-0.4.16/src/client.rs:1286-1298`), so in its own TLS
   record (**inferred**: one `SSL_write`, one record).
2. SETTINGS (`h2/src/client.rs:1322-1325`; values from hyper's defaults,
   `hyper-1.10.1/src/proto/h2/client.rs:48-52, 83-135`; encode order
   `h2/src/frame/settings.rs:229-258`): `ENABLE_PUSH = 0`, `INITIAL_WINDOW_SIZE = 2097152`,
   `MAX_FRAME_SIZE = 16384`, `MAX_HEADER_LIST_SIZE = 16384`. No HEADER_TABLE_SIZE, no
   MAX_CONCURRENT_STREAMS. 9 + 4 × 6 = 33 bytes. libsignal uses `http2::Builder::new(...)` with no
   options (`net/infra/src/http_client.rs:395-398`).
3. WINDOW_UPDATE on stream 0 raising the connection window to 5 MiB: increment 5242880 − 65535 =
   5177345 (`h2/src/client.rs:1346-1348`, hyper `DEFAULT_CONN_WINDOW`). 13 bytes.
4. HEADERS on stream 1, END_HEADERS, not END_STREAM: the CONNECT request of B.1, HPACK-encoded:
   every string literal **Huffman-coded** (`h2/src/hpack/encoder.rs:239-247`); pseudo-headers and
   `user-agent`, `sec-websocket-version`, `x-signal-receive-stories` are added to the dynamic table
   ("literal with incremental indexing"); `authorization` is **never indexed** (literal without
   indexing, name index 23) because h2 skips value indexing for it
   (`h2/src/hpack/header.rs:189-201`, `h2/src/hpack/table.rs:134-145`). The dynamic table starts
   empty, so the bytes are a deterministic function of the header values.
5. After the server's SETTINGS: a SETTINGS ACK (9 bytes). No client PINGs (hyper's
   `keep_alive_interval: None`, no timer given). Server PINGs are answered automatically.
6. Every WebSocket frame becomes the payload of DATA frames on stream 1 (9-byte header: length,
   type 0, flags 0, stream id 1). WebSocket messages are still masked client frames (tungstenite,
   unchanged).
7. Record split (**verified** h2 logic, **inferred** composition): h2 copies a DATA payload into its
   write buffer only below a threshold; at or above it, it writes the 9-byte header plus the first
   bytes up to the threshold, then the rest separately (`h2/src/codec/framed_write.rs:72-77, 85-90,
   232-263`). The threshold is 1024 bytes because nothing in the stack (tokio-boring, hyper-util,
   libsignal's stream wrappers) reports vectored writes. Through `tokio-boring` each write becomes
   its own TLS record, so **a WebSocket frame of 1015 bytes or more leaves as two TLS records: one of
   1024 bytes (DATA header + first 1015 bytes) and one with the rest**. Sealed sends (≈2–3 KB) are in
   this case. Today we send one record per frame.
8. Flow control: h2 sends WINDOW_UPDATE when the unclaimed receive window reaches half the target
   (stream: 1 MiB of 2 MiB; connection: 2.5 MiB of 5 MiB) (**inferred** from h2's flow-control
   module; reach it only on long receive sessions). The sender must stay within the server's windows
   (Netty's defaults, 65535 per stream and connection, **inferred**), which the server tops up with
   its own WINDOW_UPDATE frames.
9. Closing: WebSocket Close inside DATA; what libsignal then does at the h2 level (END_STREAM,
   RST_STREAM, GOAWAY) was not traced; **unknown** until a capture.

### C.2 Public versus secret

| Piece | Who knows it | Where it runs |
|---|---|---|
| Preface, SETTINGS, WINDOW_UPDATE, SETTINGS ACK, PING ACK, GOAWAY handling | public constants and server-chosen numbers | controller, in the clear; sealed as public records (as `sendPublic` does today, `TlsMpc/Node/Session/Common.lean:40-44`) |
| CONNECT HEADERS, unauthenticated socket (all send sessions) | entirely public (host, path, user agent) | controller: a Lean HPACK encoder producing a fixed template; **no kernel** |
| CONNECT HEADERS, authenticated socket | everything except the `authorization` value | if the account password must stay secret from the nodes: a small kernel Huffman-codes `Basic base64(aci.1:password)`; choose the password at registration so its Huffman length is a fixed public number (rejection sampling), then the block's length and every offset after it are public. If the password may be in the clear on the nodes (the privacy rule allows our own credentials there: confirm), it is all controller work. |
| DATA frame headers we send | public (length is the public frame length) | prepended to the request template as public bytes; kernels unchanged in logic, new shapes |
| Server frames: frame headers, SETTINGS, WINDOW_UPDATE, PING, GOAWAY, RST_STREAM, the CONNECT response HEADERS (`:status 200`, possibly `x-signal-timestamp`) | server framing, no contact data | revealed and parsed in the controller, like today's 101 response |
| DATA payloads (the WebSocket stream) | as today | the existing WebSocket reveal policy, applied to the DATA-payload stream |

The request header block **can** be a fixed public template with secret parts in slots, as today:
for send sessions it has no secret parts at all; for the authenticated socket only the
`authorization` value is secret, and because h2 never indexes it, it does not perturb the dynamic
table.

Receiving: `TlsMpc/Node/Policy/Receive.lean` classifies server bytes one at a time
(`step`, `frameByte`, `payloadByte`, `mayReveal`, `budget`: lines 411-611) on top of the upgrade
and WebSocket-frame parsers. HTTP/2 needs a new layer **under** it: a byte transducer that reads
9-byte frame headers (revealed), routes DATA payload bytes of stream 1 to the existing WebSocket
policy, parses HEADERS (HPACK decoding with the server's dynamic table and Huffman) and control
frames in the clear, and fails closed on anything else (PUSH_PROMISE is disabled by our SETTINGS;
CONTINUATION only if headers are large). Bodies the policy passes over unrevealed
(`Common.record`, `TlsMpc/Node/Session/Common.lean:102-158`) may now be split by DATA headers; the
pass-over and `Flow.Receive.take` / `Flow.Refresh.take` already work range by range per record, so
splitting at frame headers fits the existing mechanism.

### C.3 New circuits and AND-gate estimate (rough)

Today's per-message cost is about 2.9M AND: send circuit 2.18M, request frame and sealing its
record 0.31M + 0.07M, opening the response 0.13M, storing state 0.09M (`PERFORMANCE.md:75-88`); a
handshake is about 3.1M (`PERFORMANCE.md:66`).

| Change | New circuit? | AND estimate |
|---|---|---|
| WebSocket over h2, request: 9 more public bytes per frame | no new kernel; new size classes of `signal-request-ctr`, `bundle-request-ctr`, `bundle-fetch-ctr` (offsets +9) | one more AES block at most: a few thousand AND |
| Mimicking the 1024-byte record split | sealing one request as two records: either the kernel emits two records or a second seal call | one more tag block and record overhead: ≈10–20k AND, one more engine round per send |
| Response records with DATA headers | new size classes of the record-opening circuits (+9 bytes per DATA frame) | ≈ +5–10k AND per response |
| Connection set-up: preface, SETTINGS+WINDOW_UPDATE, CONNECT HEADERS, SETTINGS ACK as public records | existing public-seal path; new small sizes | ≈20 AES blocks, ≈0.1M AND per connection; the HPACK-compressed CONNECT is smaller than today's HTTP/1.1 upgrade, so roughly a wash |
| Authenticated CONNECT `authorization` Huffman (if kept secret) | one new small kernel, once per receive session | ≈0.1–0.3M AND (table lookups per base64 character and bit packing) |
| **gRPC sends** (if official sends use gRPC) | new request kernel family: protobuf body (`IndividualRecipientMessageBundle`: raw envelope bytes instead of base64 JSON, registration id as a varint of private width 1 or 2), 5-byte gRPC length prefix, a HEADERS frame per request; new response handling (HEADERS, DATA, trailers) | request circuit probably cheaper than today's (no base64); the cost is design and proofs |

So for the WebSocket-over-h2 variant the per-message overhead is **under 1 %** of today's AND
count (**inferred** estimate). The real cost is Lean code and proofs: CLIENT_FINGERPRINT.md
estimated 1–2k lines for the controller side; add an HPACK decoder (server responses) and the
proofs below, plausibly another 2–4k lines.

### C.4 Proof obligations

- Request side (`TlsMpc/Node/Policy/RequestProofs.lean`): `build_reference`, `buildFetch_reference`,
  `buildDevices_reference`, `build_public`, `buildFetch_public`, `buildDevices_public`,
  `build_two_contacts`, the `*_layout` theorems and `signalRequestCtr_reference`,
  `bundleFetchCtr_reference`, `bundleRequestCtr_reference` (lines 840-1361) need analogues with a
  public DATA-header prefix (best: generalize `assemble`, `Policy/Request.lean:103-118`, to take a
  public prefix, so the existing statements gain one parameter). New: an RFC 9113 frame-header
  encode/decode theorem in the style of `buildHeader_frame`/`decode_clientFrame`.
- Upgrade: the `RelayUpgrade.request` / `signal-upgrade` statements get HEADERS-block analogues; new
  HPACK lemmas: Huffman encode/decode round trip, and "decoding our block yields exactly the
  intended header list" (RFC 7541 Appendix C vectors as tests).
- Receive side: the reveal-policy proof stack (`Policy/ReceiveStream.lean`, `ReceiveSim*.lean`,
  `ReceiveProofs.lean`, `ReceiveInvariant.lean`, `ReceiveEnvelope.lean`, `ReceiveComplete.lean`,
  `ReceiveLoop.lean`, `ReceiveHead.lean`, `ReceiveFrame.lean`; about 540 theorems). Ideally one
  composition theorem: "the h2 layer reveals exactly the frame headers, control frames and response
  HEADERS, and on the concatenated stream-1 DATA payloads it reveals exactly what the existing
  WebSocket policy reveals", so the WebSocket theorems are reused unchanged. The reference
  classifier `ReceiveSpec.classify` needs an h2 counterpart, and `classify_stream` its analogue.
- gRPC, if built: a new request and response specification and the analogues of all of the above.

### C.5 Staged order and local testing

The local server already runs the production h2 front: upstream `test.yml:524-527` sets
`grpc: port 50051, websocketPort 8080, h2c: true`, and `local_signal_server/scripts/make_config.py:44-48`
moves it to `127.0.0.1:18051` (README line 69). In h2c mode `OmnibusH2Server` skips TLS
(`OmnibusH2Server.java:125-127`) but is otherwise the same code: same SETTINGS (connect protocol
enabled, line 166), same routing of `/v1/websocket` to the Jetty connector, same `x-forwarded-for`.
So: point a TLS terminator offering ALPN `h2` at `127.0.0.1:18051`. That Jetty accepts the
forwarded extended CONNECT is **inferred** (production apps depend on it); stage 1 confirms it.

1. Reference bytes without BoringSSL: a tiny Rust harness using the vendored `hyper`/`h2`/`tungstenite`
   exactly as `net/infra/src/http_client.rs:395` and `ws.rs:314-325` do, over plain TCP (h2c) to the
   local front. h2 and hyper do not need BoringSSL, so this gives the exact preface, SETTINGS,
   WINDOW_UPDATE, HEADERS bytes and DATA write pattern now. (A build: outside this read-only task.)
2. Lean HPACK encoder/decoder and frame codec, pure, tested against RFC 7541 Appendix C and the
   reference bytes of step 1.
3. Controller: h2 connection set-up and the unauthenticated CONNECT on send sessions; request
   templates with the DATA header; circuit production with a new profile value (new shapes). Test
   with `check_signal_service_local.py` through an `h2` terminator to 18051.
4. Receive side: the h2 layer under the reveal policy, then its proofs.
5. Authenticated CONNECT (receive session).
6. Fingerprint regression: `fingerprint_terminator.py --alpn h2` and an h2 reference.
7. Only if a capture shows official sealed sends use gRPC: the gRPC send path.

### C.6 Risks

- Record segmentation of the official client is a mix of h2 buffering, tokio scheduling and BoringSSL
  record writes; parts can be derived (C.1 items 1 and 7), but whether SETTINGS, WINDOW_UPDATE and
  the CONNECT HEADERS share a record is timing-dependent. **unknown** without a capture.
- Timing stays distinguishing whatever the bytes: our Finished leaves seconds after the server's
  flight (CLIENT_FINGERPRINT.md (b)).
- Whether official sealed sends travel over gRPC (remote config) is **unknown**; if they do, a
  WebSocket-over-h2 client still differs from official clients in every send.
- Server behaviours not exercised locally: production may send PINGs, GOAWAY on idle (the front
  closes idle connections after 5 minutes by default, `S/configuration/GrpcConfiguration.java:33-35`),
  different SETTINGS. All must fail closed or be handled.
- Proof debt is the largest cost; the reveal policy is the part that must not regress.

---

## D. ClientHello parity

### D.1 What BoringSSL as configured by libsignal offers

libsignal's configuration (**verified**, `net/infra/src/tcp_ssl.rs:208-251`): a fresh `SslConnector`
per connection (so no session resumption across connections), ALPN from the route (one value),
`set_min_proto_version(TLS1_3)` for chat, `set_verify_algorithm_prefs` = Ed25519, ECDSA-P256-SHA256,
RSA-PSS-SHA256, RSA-PKCS1-SHA256, ECDSA-P384-SHA384, RSA-PSS-SHA384, RSA-PKCS1-SHA384,
RSA-PSS-SHA512, RSA-PKCS1-SHA512 (0807 0403 0804 0401 0503 0805 0501 0806 0601), and
`set_curves_list("X25519:P-256:P-384")` with the comment "before boring-rs adds support for the
combined X25519_MLKEM768 … chat-server doesn't support MLKEM in TLS yet" (lines 237-240). The
`boring` wrapper's connector adds only options and a TLS 1.2 cipher string
(`boring/src/ssl/connector.rs:27-78`). Nothing enables GREASE, extension permutation, ECH, ALPS,
OCSP stapling or SCTs (grep of `net/infra/src`, **verified** absence).

What BoringSSL builds from that (**derived** in CLIENT_FINGERPRINT.md from BoringSSL `427ec40`
sources on GitHub; not re-checkable here):
- Cipher suites: TLS 1.3 only: 1301, 1302, 1303 on devices with AES instructions; ChaCha20 first
  without them.
- `supported_groups`: x25519, secp256r1, secp384r1. `key_share`: **one** share, X25519.
- **No post-quantum hybrid key share** (X25519MLKEM768 is excluded by the explicit curve list).
  So the handshake circuits need no ML-KEM today. Watch libsignal releases: when the comment's
  condition changes, the share (1,216 bytes of ML-KEM-768 public key) and its decapsulation would
  have to run in MPC; the repository's ML-KEM kernels (for PQXDH) would be a starting point.
- Extensions and order: server_name, supported_groups, ALPN, signature_algorithms, key_share,
  psk_key_exchange_modes, supported_versions (cookie after a HelloRetryRequest).
- Padding: BoringSSL's F5 workaround pads only when the ClientHello is between 256 and 511 bytes; the
  official hello with SNI `grpc.chat.signal.org` and ALPN `h2` is about 208 bytes, so **no padding**
  (my count: 79 bytes before extensions + 129 bytes of extensions; **derived**).
- First record version 0x0301, 32-byte legacy session id.

### D.2 Differences from ours (libsignal profile, `TlsMpc/TlsWire.lean:96-112`)

| Field | Official | Ours | Can we only OFFER it? |
|---|---|---|---|
| Cipher suites | 1301,1302,1303 | 1301 | Yes, bytes only, **if the server picks 1301**. `serverHello` already aborts on any other suite (`TlsWire.lean:143`), so a different choice fails closed (an outage, not a weakness; reword the error, it says "unoffered"). |
| supported_groups | x25519,P-256,P-384 | x25519 | Yes. The server can only choose a group we sent a share for, or ask with a HelloRetryRequest; ours aborts on an HRR for any group but X25519 (`TlsWire.lean:152`) and on a non-X25519 share (line 164). Every official client sends only an X25519 share, so a server asking for P-256 would cost every client a round trip: implausible. |
| key_share | X25519 | X25519 | same |
| ALPN | `h2` | `http/1.1` | **No.** The h2 front advertises only `h2` and its negotiation handler falls back to `h2` when nothing is agreed (`S/grpc/net/SniMapper.java:88-96`, `OmnibusH2Server.java:129-139`; verified), so an HTTP/1.1 request to `grpc.chat.signal.org` would meet an h2 server (inferred from Netty's fallback behaviour). Offering `h2,http/1.1` is itself non-official (libsignal sends one value). Needs the HTTP/2 layer (section C). |
| SNI | `grpc.chat.signal.org` | `chat.signal.org` | Only together with `h2` (same reason). |
| Everything else | — | matches (CLIENT_FINGERPRINT.md (a)) | — |

### D.3 What the server chooses today, and what would break

- The first production handshake (`real_signal/REAL_TEST_PLAN.md:195-209`) was with
  `chat.signal.org`, ALPN `http/1.1`, offering only 1301 and X25519: the server used them and an
  Ed25519 certificate. That says nothing about which suite it **prefers** when offered three.
- The h2 front's TLS is Netty's `SslContextBuilder.forServer(...)` with `protocols("TLSv1.3")`
  and default ciphers (`SniMapper.java:88-96`); no `netty-tcnative` appears in the server's poms, so
  it likely uses the JDK provider (**inferred**; production may add a native provider). JDK servers
  honour their own order by default, and their default TLS 1.3 order puts AES-256-GCM first; Netty
  may narrow the list to its own defaults (AES-128 first). Result: **unknown**. If it is
  "server order, AES-256 first", every official client gets 1302 and offering 1302 would make all
  our handshakes abort.
- Locally: `tls_terminator.py` is Python/OpenSSL with server preference (Python's default), whose
  TLS 1.3 order starts with AES-256-GCM, so offering 1302 locally would fail unless started with
  `--require-aes128` (`local_signal_server/scripts/tls_terminator.py:27-37`) (**inferred** from
  OpenSSL/Python defaults).

### D.4 Recommended minimal set and residual risk

1. Now, no new circuits: add secp256r1 and secp384r1 to `supported_groups` (no shares). Fails
   closed on an HRR.
2. Settle the cipher preference with one **TLS-only probe** of `grpc.chat.signal.org` (no Signal
   request, no account; still the owner's go-ahead for the real service): offer 1301,1302,1303 with
   x25519/P-256/P-384, ALPN `h2`, and record the chosen suite; repeat with ChaCha20 first to learn
   whether the server follows its own order. `measure_handshake.py` (REAL_TEST_PLAN.md B3) is the
   tool to extend.
   - Server picks 1301: list all three suites; done (JA3/JA4 cipher part then matches).
   - Server picks 1302: build TLS_AES_256_GCM_SHA384 first (SHA-384 key schedule, AES-256 records;
     "medium" in CLIENT_FINGERPRINT.md: about +40 % AND per record block and +1.5–2.5M AND per
     handshake), then list all three. ChaCha20-Poly1305 only if the server prefers it (large).
3. SNI and ALPN with the HTTP/2 layer (section C).

Residual risk: the server's choice can change without notice; a change would make every connection
fail closed at once. Keep a switch back to the 1301-only hello, and alert on "server selected …".
Timing (seconds to Finished) remains a fingerprint the ClientHello cannot fix.

---

## E. The small fingerprint items: where they change now

| Item | Where (file, function) | Circuit shape? | Theorems to restate |
|---|---|---|---|
| **Space-padded ids** (replace with canonical JSON at a private length, CLIENT_FINGERPRINT.md (d) option 2) | `TlsMpc/Node/Policy/Request.lean` `officialJson`, `sendMessage`, `devicesMessage` (lines 53-74, 133-145: the 3- and 10-byte slots); kernels `HybridKernels.paddedDecimal` / `signalRequestCtr` (`TlsMpc/HybridKernels.lean:496, 581`) and `BundleKernels.bundleRequestCtr` (`TlsMpc/BundleKernels.lean:179-187`) replaced by a new `signal-request-canonical`; its worker operation; `Session/Send.lean` `sendMessage`/`sendDevices` | **Yes**: new kernel, new circuits (re-lowering), record capacity padding | `RequestProofs.lean`: `sendMessage_reference`, `devicesMessage_reference`, `build_reference`, `buildDevices_reference`, `build_public`, `buildDevices_public`, `build_two_contacts`, `build_layout`, `buildDevices_layout`, `signalRequestCtr_reference`, `bundleRequestCtr_reference`; `KernelSpecs/RequestCtr.lean` (`paddedDecimal_map`, `paddedDecimal_eval`), `KernelSpecs/RequestFrame.lean` (`paddedDecimal_length` uses), `KernelSpecs/SlotDecimal.lean` (`paddedDecimal_value`, `paddedDecimal_parse`); `RequestSpec.IncomingMessage.json` (ids become canonical decimals); `Security.lean` section 2d restatements; a new theorem for TLS record padding in the sealed record. |
| **Request ids from 0 per connection** | `Session/Common.lean` `nextId` (lines 77-78, `2^63 + 2^32 + n`); `Session/Pool.lean:104-119` (`2^63 + sent`); `Session/Send.lean:255, 473`; `Session/Receive.lean:162, 179` (`2^63 + pings`); the counters in `Session/State.lean:48`; `Main.lean` `request-shape` mode (an id-width argument). libsignal uses **one** counter per connection for every request, from 0 (`net/src/chat.rs:51-56`, `net/src/chat/ws.rs:347-365`); proto2 `optional uint64 id` encodes 0 as `20 00` (`net/src/proto/chat_websocket.proto:6, 15`), which `32 :: varint 0` already produces. | **Yes**: the id varint shrinks from 10 bytes to 1 (< 128) or 2 (< 16384), so every request shape gets two widths (about twice the request shapes) | The layout theorems are already parametric in the id's varint length (`build_layout`, `buildDevices_layout`, `buildFetch_layout`, hypothesis `hid`, `RequestProofs.lean:1178-1290`): no restatement. The models that hard-code `2^63 + …` must change with the code: `Session/DeliverProofs.lean:181` and `Session/LoopProofs.lean:112`, and any theorem relying on send ids and extra ids never colliding (one counter removes that argument). |
| **WebSocket Close at session end** | `Session/Receive.lean` `run` (lines 216-219) and `Main.lean` `kind` (line 117), `Session/Ceremony.lean:259`: before `TlsApplication.abort`, send a masked Close 1000 (a new `close` builder beside `ping` in `Policy/Receive.lean:947-948`; the specification's `RequestSpec.clientFrame` already covers opcode 8, and `replies` already answers a server Close), await the server's Close, then `TlsApplication.close` (sends `close_notify`, `TlsMpc/TlsApplication.lean:138-145`) instead of `abort` (lines 147-150). Today **neither** a Close nor a TLS `close_notify` is sent. The receive session's final `GET /v1/keepalive` (`Receive.lean:153-165`, kept so acknowledgements are known to be read) can be replaced by this Close exchange: the server's Close also comes after everything sent before. | Controller only; at most one new public-seal size (an 8-byte frame) | New `close_reference`/`close_decode` beside `ping_reference`/`ping_decode` (`RequestProofs.lean:583-590, 749-754`); the reveal policy currently treats a server Close as an error before completion (`Receive.lean:190`, `Common.lean:171`), so the closing state and the theorems about `replies` and completion (`ReceiveComplete.lean`, `ReceiveLoop.lean`) need a "closing" case. |
| **Ping instead of a request for the send-session keepalive** | `Session/Common.lean` `keepAlive` (185-195) and `keepAliveSoft` (253-261): send `PublicReceive.ping` and do not await a response (the pong is a control frame the parser skips); libsignal pings after 31 s without sending or receiving (`net/infra/src/timeouts.rs:38-40`, `lib.rs:289-293`), ours waits 20 s | Controller only; the 7-byte ping frame is already sealed by the receive session | `Session/RefreshProofs.lean` `refreshContact_deployed`, `refreshSoft_deployed` stay `rfl` if the signatures stay; the guarded `RefreshOps` instances used by `LoopProofs.lean` (`deliverJob_sendsAgreed'`, `deliverJob_commitsAgreed`, `loop_sendsAcked`, `loop_commitsAgreed`) must be re-shown to keep their invariants with a ping event in place of a request (probably simpler: a ping is not a request). |

---

## F. Other things an operator should know

All from Signal-Server open source (**verified**); production overrides any limiter through dynamic
configuration and runs a closed spam filter (**unknown**).

Rate limiters (`S/limits/RateLimiters.java:19-64`; a `RateLimiterConfig` is a token bucket: size,
then one permit back per duration, `S/limits/RateLimiterConfig.java:12-16`):

| Limiter | Default | Keyed by | Applies to us? |
|---|---|---|---|
| `messages` | 60, then 1 per second | (sender account, destination) | **Identified** sends only (`S/controllers/MessageController.java:298-316`). Not sealed sends. |
| `inboundMessageBytes` | 128 MiB, then 1 byte per 0.5 ms (≈2 KB/s, ≈7 MB/h) | **destination** | every send to a contact (`MessageController.java:411-419`; gRPC `S/grpc/MessagesAnonymousGrpcService.java:179`) |
| `stories` | 5,000, then 1 per 8 s | destination | story sends only |
| `prekeys` | 6, then 1 per 10 min | (account, device, target, target device, registration id) | **authenticated** prekey fetches only; fetches with an access key are not limited (`S/controllers/KeysController.java:347-375, 418-433`) |
| `checkAccountExistence` | 1,000, then 1 per 4 s | IP | if ever used |
| per-IP limiters (`@RateLimitedByIp`) | username lookup 100/15 min, username link 100/15 s, key transparency 100/15 s, batch identity check 100/min, … | IP | none on sends or prekey fetches |
| `captchaChallengeAttempt` / `Success` | 10 per 144 min / 2 per 12 h | account | when a 428 is answered |
| `pushChallengeAttempt` / `Success` | 10 per 144 min / 2 per 12 h | account | needs a push token (we have none) |
| `rateLimitReset` | 2 per 12 h | account | |

Sealed sends (`MessageController.java:338-366, 390-419`): checked only by the access key, the spam
filter and the per-destination byte limiter. There is **no open-source limit per sender or per
address**. The spam filter gets the HTTP request context (address, user agent, headers) for
WebSocket sends (`S/spam/SpamChecker.java:27-32`); its gRPC variant gets no context argument but can
read the address the interceptor stored (`RequestAttributesInterceptor.java:49-63`). Its verdict can
be a response (in practice a 428 "complete a challenge") and a token placed in the delivered
envelope (`MessageController.java:398-407, 432`).

428 challenges (`S/controllers/ChallengeController.java:77`, `S/limits/RateLimitChallengeManager.java:55-103`):
a challenge is answered on `/v1/challenge` by an **authenticated** account (captcha or push).
Answering one from our account ties the challenged sealed traffic to it. Our client treats a 428
on a send as a fault and stops (`TlsMpc/Node/Policy/Recovery.lean:240`), which is the right
default; an operator must decide whether anyone may solve captchas for the account.

Spam reports (`MessageController.java:848-899`): a recipient, who unseals the sender certificate,
can report our account (`/v1/messages/report/{our ACI}/{guid}`), optionally with the spam token
minted at send time. Reports go to the closed filter's listener (`S/WhisperServerService.java:949`).
Unwanted broadcasts can therefore get the account flagged regardless of exits.

Other:
- User-agent version blocking: a version below the configured minimum, or on a block list, gets 499
  (`S/filters/RemoteDeprecationFilter.java:83-88, 117-170`). `RelayUpgrade.userAgent` must follow
  Android releases.
- Metrics per ASN region and per user agent on every WebSocket open
  (`S/metrics/OpenWebSocketCounter.java:58-105`): many sockets from one unusual ASN (a Tor exit, a
  cloud provider) are visible in aggregate even without per-client code.
- Prekey fetches consume each target device's one-time prekeys (`KeysController.java:379-386`); the
  contacts' devices notice depletion and refill. Normal for first messages, unusual in bursts.
- Idle limits: the h2 front closes idle connections after 5 minutes by default
  (`GrpcConfiguration.java:33-35`); libsignal pings after 31 s idle and gives up after 45 s without
  hearing from the server (`timeouts.rs:38-40`).

---

## What only a live capture, a probe, or vendored BoringSSL can settle

1. **Server cipher-suite preference** on `grpc.chat.signal.org` when offered 1301,1302,1303 (and with
   ChaCha20 first): a TLS-only probe, owner's go-ahead (D.4).
2. **Whether Signal TLS proxies forward SNI `grpc.chat.signal.org`** (current Signal-TLS-Proxy
   allow-list; volunteer proxies may run old versions).
3. **Whether official sealed sends use gRPC or the WebSocket** on h2 connections (Signal's remote
   config value for `grpc.MessagesAnonymousSendSingleRecipientMessage`).
4. **Exact record segmentation of the official h2 client**: preface alone, whether SETTINGS +
   WINDOW_UPDATE + CONNECT HEADERS share a record, the 1024-byte DATA split, the closing sequence
   (needs libsignal-net built, i.e. BoringSSL vendored at `427ec40`, against the local terminator).
   The h2-layer bytes alone can be reproduced earlier with the vendored hyper/h2 over h2c (C.5 step 1).
5. **BoringSSL's ClientHello bytes** (cipher order with and without AES instructions, extension
   order, the padding rule): today derived from BoringSSL sources read on GitHub; vendoring
   BoringSSL makes it checkable offline.
6. **Production h2 front behaviour**: its SETTINGS, PINGs, GOAWAY timing, CONNECT response headers,
   record sizes; and which TLS provider it runs.
7. **Production rate-limit overrides and the spam filter**: what triggers 428, and whether Tor, VPN,
   proxy or reflector exits are treated differently.
8. **Who still speaks HTTP/1.1 to `chat.signal.org`** (server metrics only) and whether
   Signal-Android's own HTTP code contacts it (app sources).
9. **What the reflector adds or logs** (its code is not public on disk).
