# Networking: open questions and work parked for later

Written 2026-11-12 from a conversation with the owner ("record this in a networking-todo … we'll
figure it out later"). Nothing here is decided unless it says so. Related documents:
`ROTATION.md` (the rotation planner and its integration to-do), `PRODUCT_TODO.md` section 8
(privacy: the proxy), 11a (stock for spikes), 11b (prepare a contact's devices ahead),
`handshake_backend/EmpHybridWork/CLIENT_FINGERPRINT.md` (how we differ from an official client).

## 0. Corrections from the source review (2026-11-12, `NETWORKING_FINDINGS.md`)

A read of libsignal v0.106.1 and Signal-Server on disk (no network) changed several statements
below. Where this section and a later one disagree, this section is right.

- **HTTP/1.1 is not normal on any route.** Every chat route in libsignal 0.106.1 (direct, Signal
  TLS proxy, SOCKS, HTTP proxy, reflector) uses HTTP/2 to `grpc.chat.signal.org`. Going through
  a Signal proxy does NOT make our HTTP/1.1 transport look normal (sections 3–5 said it might).
- **We are distinguishable today on any route:** our user agent claims libsignal 0.107.0, which
  never speaks HTTP/1.1. HTTP/2 is therefore the first fingerprint item, not an optional one.
- **Signal's proxy route, verified:** outer TLS to the proxy's own host (no ALPN, system trust
  store); inside it the unchanged direct route (SNI `grpc.chat.signal.org`, ALPN `h2`). The
  server takes the client address from the TCP peer or a PROXY-protocol header and overwrites
  any forwarded-for header itself, so through a proxy it sees the proxy's address. No code path
  in the open-source server treats proxied connections differently; the closed-source spam
  filter sees each send's address and user agent.
- **Domain fronting** (CDN terminates TLS, sees paths) is switched off in 0.106.1; its
  replacement, the "reflector", tunnels end-to-end TLS through a CDN and does not expose paths.
  It is Signal's censorship infrastructure; still not recommended for us.
- **ClientHello:** official offers suites 1301/1302/1303 and groups x25519/P-256/P-384 with only
  an X25519 key share; no post-quantum share, GREASE, ECH or padding. Listing P-256/P-384 as
  supported groups needs no new circuits (a retry request for them fails closed). Listing the
  other two suites is safe only if the server picks AES-128-GCM when offered all three — unknown
  without a probe.
- **Server limits (open-source defaults):** no per-sender or per-IP limit on sealed sends; a
  per-recipient byte bucket (128 MiB, about 2 KB/s refill); prekey fetches with an access key
  unlimited, authenticated ones 6 per 10 minutes. A 428 challenge can only be cleared by our own
  logged-in account, which ties that traffic to the account. Recipients can report the account.
  An outdated user-agent version gets status 499.
- **HTTP/2 cost:** framing, settings and flow control are public and can run in the controller;
  circuits only change shape (under 1% per message). The real cost is Lean: a new HTTP/2 layer
  under the reveal policy, whose WebSocket layer has about 540 theorems. Sending over gRPC (what
  h2 clients may default to) would be a separate, larger project. The local server already runs
  the production h2 front, so it can be tested locally.

**Decided (owner, 2026-11-12):** HTTP/2 is the first fingerprint item but waits until the
reorganisation is done ("we can wait til the reorg is done for http 2"). Until then the client
stays distinguishable by transport.

## 1. What the server can link, and what each measure addresses

| Signal the server has | Measure | State |
|---|---|---|
| Source IP of a broadcast's sends | an exit that is not ours (section 3) | Tor works today; less conspicuous exits not chosen |
| Messages arriving on one connection | rotation (section 2) | planner built and proved; not wired into the session |
| Timing: a burst of sends, one after another | spreading sends in time; concurrent connections | nothing built |
| Our client looking unlike an official one | fingerprint work (section 5) | first pass done; transport and ClientHello open |
| A key fetch or send right after a signup | delay and batch (PRODUCT_TODO 11b) | planned, not built |

## 2. Rotation (X2)

Built: `TlsMpc/Node/Policy/Rotation.lean` (pure planner; plan depends only on the joint-random
seed, the message count, the settings and a generation counter; every message sent once; pool
bound; no generation reused), `RotationTest.lean`, `ROTATION.md`. SHA-256 is used only to
stretch the one agreed seed into the plan's random numbers, in the clear, identically on both
nodes; the planner's proofs do not depend on it, uniformity of the shuffle assumes it behaves as
a PRF keyed by the seed.

Not built: the integration (ROTATION.md section 6, with line references), op 92 on the Lean
side, concurrent handshakes.

Cost, from the real run's handshake time (about 4 s with connect and upgrade, malicious) and the
local per-message rates; NOT measured through Tor:

| | Direct, one connection | Rotation (mean 10, pool 4) |
|---|---|---|
| Added per message | — | about 0.4 s |
| Per message, malicious | about 1.4 s | about 1.8 s |
| Per message, semi-honest | about 0.8 s | about 1.2 s |
| 48 recipients, malicious | about 70 s | about 95 s |
| 14,000 recipients, malicious | about 5.4 h | about 7 h |

Open:
- [ ] The worker runs one operation at a time, so the pool spreads handshakes but does not hide
      them. Decide: handshakes concurrent with sends on other slots (`nextOpen` allows it), or
      several sessions in parallel (needed for the spike anyway; then handshakes overlap).
- [ ] Rotation does not address timing: sends are serial and a new connection opens right after
      the previous one closes, so a batch can probably be chained. Decide how far to spread sends
      in time and what delay the application accepts.
- [ ] A fresh circuit can leave from the same exit; check `IsolateSOCKSAuth` and whether to
      require distinct exits.
- [ ] Mean 10 / pool 4 / uniform length on 1..19 were chosen without measurement. Revisit with
      real numbers.
- [ ] Measure: per-message latency through a local Tor instance (the harness can delay the
      node-to-node link but not the server leg).

## 3. Exits less conspicuous than Tor (ideas, none verified)

What a proxy sees in every case: destination, timing, sizes, and our TLS ClientHello; never
requests, recipients or content (TLS ends inside the MPC).

| Option | For | Against |
|---|---|---|
| Mobile carrier exits (own LTE modems with SIMs, or a mobile-proxy vendor) | carrier NAT: one IP shared by thousands of real Signal phones; closest to an official client | hardware to run, or a vendor who sees our timing; a spike needs many |
| Signal's own proxy route (section 4) | made for Signal traffic; our HTTP/1.1 transport may look normal there | operator sees our IP and timing; must confirm what the server learns |
| Commercial VPN exits | many real users run Signal over a VPN; shared IPs; far less flagged than Tor | datacenter addresses; provider sees all timing |
| Residential proxy networks | home IPs | often built on users' devices with doubtful consent; avoid |
| Cloud addresses we rotate | cheap, ours | plainly not phones; IPv6 usually grouped by /64 |
| Nym, I2P | different exit set | small identifiable exit sets, same problem as Tor |
| Domain fronting through a CDN | — | RULED OUT: the CDN terminates TLS and would see request paths, which hold recipient identifiers |

Engineering: the worker speaks SOCKS5 to its proxy. Modems, VPNs and cloud boxes can sit behind
a local SOCKS endpoint; Signal's proxy route needs a small adapter (outer TLS in the clear by one
node).

- [ ] Choose which to evaluate first. Suggested order: Signal's proxy route, own mobile modems,
      a VPN as fallback.
- [ ] For whichever is chosen: terms of use, cost at 14,400 messages a day and at a 14,000
      spike, and how addresses rotate.

## 4. Signal's proxy: what it sees (from memory of Signal's published design, NOT re-checked)

TLS inside TLS. The client makes an outer TLS connection to the proxy's own domain; inside it, an
ordinary TLS handshake addressed to Signal's host; the proxy reads only the server name of the
inner ClientHello, checks it is a Signal host, and then pipes bytes both ways over plain TCP.

- Proxy sees: our IP, the inner ClientHello in the clear (server name, our TLS fingerprint), the
  inner records as ciphertext with sizes and timing.
- Signal sees: the proxy's IP, and the same inner handshake and traffic as on a direct
  connection. TCP-level relay, so there is no HTTP layer for a forwarded-for header.
- For us: the outer TLS needs no MPC (one node does it in the clear, like SOCKS today).

To verify from the sources on disk (libsignal v0.106.1 under `.deps/`, Signal-Server), no network:
- [ ] Whether the proxy route's inner connection is HTTP/1.1 or HTTP/2 in current libsignal (the
      fingerprint document says HTTP/1.1 is what proxied clients use; that is what would make our
      transport look normal).
- [ ] That nothing in the route tells the server the original IP, and whether the server treats
      proxied connections differently.
- [ ] Whether using public volunteer proxies is acceptable, or we run our own (then the exits are
      only as inconspicuous as their addresses).

## 5. Looking like an official client (state as of CLIENT_FINGERPRINT.md, 2026-11-11)

Done behind the `libsignal` profile: envelope length, headers, JSON field order and path,
send-time timestamps, ping keepalive on the receive socket, no client key update; regression
stage `--fingerprint`.

Open, largest first:
- [ ] Transport: we speak HTTP/1.1 to `chat.signal.org`; current apps use HTTP/2 extended
      CONNECT to `grpc.chat.signal.org`. Needs an HTTP/2 layer inside the MPC client. Plan and
      cost estimate owed. (May not matter on a proxied route: section 4.)
- [ ] ClientHello: one cipher suite and one group where BoringSSL offers several. Needs new
      capability. Plan and cost estimate owed.
- [ ] Small ones, to do with the send-path work: space-padded device and registration ids,
      request ids from 0 per connection (changes a size class), WebSocket Close at session end,
      ping instead of a request for the send-session keepalive during a device refresh.
- [ ] Message timestamps 1.3–2 s older than the server's receipt in malicious mode.
- [ ] Things official clients do and we never do: certificate refresh and prekey checks are cheap
      and needed anyway; receipts and profile fetches of contacts stay ruled out.
- [ ] The reference is derived from sources, not a capture: vendor BoringSSL so libsignal's
      network crate builds, and replace the synthetic reference with a real capture.

## 6. Spikes (14,000 recipients in about ten minutes)

Not a networking problem alone: a single session is hours at today's rates with or without
rotation. Needs the stock of preprocessing (X1, `STOCK.md` when written, PRODUCT_TODO 11a),
several sessions in parallel, contacts prepared ahead (11b), and the database client and field
engine limits listed in 11a. Networking's share: enough exits and connections in parallel, and
whatever time-spreading is decided in section 2.
