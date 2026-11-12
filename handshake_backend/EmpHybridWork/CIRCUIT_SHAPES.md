# Circuit shapes: what a deployment can ask for, and how the set is fixed before it starts

Every circuit ("kernel") is defined in Lean and named by its family and PUBLIC shape parameters
(`flat_kernel_emitter kernel NAME PARAMETERS`). A parameter the worker learns only during a
session used to mean a circuit produced during the session (seconds to a minute, up to 10 GB),
while the server waits. This file lists every family, what determines each parameter, and how the
set a deployment needs is made finite, produced ahead and pinned.

- Enumeration: `circuit_inventory` (Lean, `CircuitInventory.lean`), from a deployment description.
- Production and manifest: `scripts/produce_circuits.py DEPLOYMENT.json OUT`.
- Strict mode: a worker started with `CIRCUIT_MANIFEST=OUT/manifest.txt` uses only the manifest's
  kernels and never produces one (`kernel.h`).
- Proof: `local_signal_server/check_signal_service_local.py --strict` (deployment
  `local_signal_server/deployment.json`).

## How a parameter is determined

- **constant**: fixed by the protocol or by this code.
- **deployment**: fixed for a deployment (our certificate's length, the server's handshake records);
  a setting of the deployment description.
- **bounded**: takes a few values that the protocol bounds (varint widths, digit counts, flags);
  the description lists the values to cover.
- **data**: any value in a wide range, known only when the data arrives (the size of a record, of
  a response, of an envelope).

Nothing here is secret: every parameter is something both nodes already see (sizes on the wire,
or shapes the kernels open on purpose). Size classes therefore reveal nothing new: a class is a
function of a size the nodes have.

## Size classes (the fix for the data-dependent sizes of TLS records)

`RecordClass.capacity` (`TlsMpc/RecordClassKernels.lean`; the same function is
`TlsKernels::record_capacity` in `tls_kernels.h`): a size up to 32 is class 32; above that it is
rounded up to a multiple of a quarter of the power of two below it: 40, 48, 56, 64, 80, 96, 112,
128, 160, 192, 224, 256, 320, … Four classes per doubling; padding under 25% of the size, 12% on
average; 37 classes cover every TLS record (up to 20480).

- `tls-open-application-class CAP` replaces `tls-open-application-ctr SIZE` in the worker
  (`TlsKernels::open_application`). Inputs: the record followed by zero bytes up to `CAP`, and
  `size`, the record's length field, as a public value. The kernel requires the header to be the
  encoding of that length, masks every decrypted byte beyond it, and then runs the same inner
  parser and post-handshake parser. Proved (`TlsMpc/RecordClassProofs.lean`, `open_padded`):
  its output is the exact-size kernel's output for the record alone (same opened event, parser
  state and private length) with the private content followed by `CAP − SIZE` zero bytes.
  The length is enforced in the circuit, not by the padding.
- `tls-reveal-masked N` already took a capacity and a private length; it now only ever sees
  `N = CAP − 21`.
- `tls-seal-class CAP` replaces `tls-seal-ctr 23 SIZE 0` (`TlsKernels::seal_application`, content of
  public size: upgrade requests, replies to server requests, keepalives, close frames). Inputs:
  the content followed by zero bytes up to `CAP`, and `size`, the record's length field. Proved
  (`sealCiphertext_padded`): the opened ciphertext is the CTR encryption of the content and its type
  byte, exactly what `tls-seal-ctr 23 SIZE 0` opens, followed by zero bytes whatever followed the
  content. No TLS padding is added: the record on the wire is byte for byte the exact-size one.
- `bundle-shape CAP`: the same kernel as before, run on the prekey response body followed by zero
  bytes up to its class (`BundleItemKernel.shape_padded`: the extra flags are zero).

Cost in AND gates, measured (class kernel against the exact-size kernel of the same record):

| Record (bytes → class) | Exact-size kernel | Class kernel | Overhead |
|---|---|---|---|
| open 160 → 160 (masking alone) | 129,989 | 131,780 | +1.4% |
| open 2560 → 2560 (masking alone) | 2,357,161 | 2,383,123 | +1.1% |
| open 153 → 160 (reply to a send) | 125,302 | 131,780 | +5.2% |
| open 246 → 256 (upgrade response) | 210,638 | 220,697 | +4.8% |
| open 98 → 112 | 72,726 | 87,159 | +19.8% |
| open 695 → 768 | 624,683 | 698,341 | +11.8% |
| open 2502 → 2560 (a signup's record) | 2,304,929 | 2,383,123 | +3.4% |
| open 2742 → 3072 | 2,527,730 | 2,865,341 | +13.4% |
| seal 256 → 256 (masking alone) | 77,717 | 84,912 | +9.3% |
| seal 242 → 256 (authenticated upgrade request) | 73,783 | 84,912 | +15.1% |
| seal 345 → 384 (upgrade request) | 99,644 | 122,252 | +22.7% |
| seal 27 → 32, 41 → 48 (replies, keepalives) | 14,676; 18,866 | 19,209; 23,922 | +31%, +27% |
| bundle-shape 5092 → 5120 | 229,140 | 230,400 | +0.5% |

Opening costs about 920 AND gates per record byte (decryption 320, the post-handshake parser the
rest), so padding costs in proportion: at most 25%, 12% on average over sizes, and what the
length masks add is 1.1–1.4%. Sealed public-size contents are small (the largest here is 122K AND
gates, once per connection); the relative overhead is higher because the masks cost about 27 AND
gates per byte beside 300 for the encryption, and a small content can cross an AES block. Eight
classes per doubling would halve the padding (at most 12.5%) and double the number of record
kernels; the ladder is one function in Lean and one in `tls_kernels.h`.

`bundle-item` costs the same as `bundle-device` did (about 101K AND gates); it reads the same bytes.

## Families

Profile: the product runs the public-receive profile (server bytes that are not contact data are
revealed to the controllers). Families used only by the older private-receive profile are listed
last and are not in a deployment's manifest.

### TLS connection

| Kernel | Parameter | Determined by | Range / handling |
|---|---|---|---|
| `tls-derive`, `tls-verify-finished`, `tls-update`, `tls-parser-initial` | none | constant | 1 each |
| `gcm-key-share`, `gcm-multiply`, `gcm-tag`, `gcm-check` | none | constant | 1 each |
| `tls-finish C` | client certificate message bytes | deployment (`client_certificate`, 0: none) | 1 |
| `tls-open-handshake N` | size of each encrypted server handshake record | deployment (`handshake`): the server's certificate chain, signature algorithm and how it splits its flight | one per record (4 locally: 43, 58, 94, 922; chat.signal.org, measured 2026-11-12: ONE record of 1122 bytes, the whole flight coalesced and padded, Ed25519; the compact local instance reproduces that shape: 621). **Data-dependent if the server signs with ECDSA** (DER signatures vary by a byte or two): list each size, or give this kernel classes too (it authenticates with in-circuit GHASH, so that is a larger change than for application records). Must be measured against the real server before a real run. |
| `tls-seal-ctr 22 5 0`, `tls-seal-ctr 21 2 0` | KeyUpdate, close_notify | constant | 2 |
| `tls-open-application-class CAP` | record size class | **data** → ladder | every class up to `record_max` |
| `tls-reveal-masked CAP−21` | content capacity | follows the record's class | one per class |
| `tls-seal-class CAP` | content size class | **data** (request ids, ping payloads) → ladder | every class up to `seal_max` |

### Socket and sends

| Kernel | Parameter | Determined by | Range / handling |
|---|---|---|---|
| `ws-initial` | none | constant | 1 |
| `signal-upgrade P`, `signal-upgrade-shared P` | password bytes | deployment (`password`, 22) | 1 each |
| `signal-conversation-view CERT`, `signal-widths CERT` | our sender certificate's bytes | deployment (`certificate`); changes if the server issues a certificate of another length on refresh: list each length as its own deployment | 1 each |
| `signal-seal-built CERT CLASS CW PW EW IW` | message size class (1–4: 80 bytes of padded content each); varint widths of the sending counter, previous counter, post-quantum epoch and next post-quantum counter | CLASS: the application's message sizes (`sends`). Widths: **bounded**, and slow-moving: contacts' replies are ignored, so a chain is never replaced; `PW = EW = 1`, and `CW`, `IW` are 1 up to 127 messages to a contact, 2 up to 16383, 3 beyond; at 127 and 16383 one message has `IW = CW + 1` | per class: 2 kernels for the first 127 messages (`1:1:1:1`, `1:1:1:2`), 2 more up to 16383 |
| `signal-request-ctr CERT SIZE U K D R` | frame size and the four slot offsets | a function of the envelope size alone (`PublicRequest.build`: 13-digit timestamp, request ids from 2^63), i.e. of the `signal-seal-built` row | one per row; named by `public_service_controller request-shape send` |
| `contact-key` | none | constant | 1 |
| `contact-seal N`, `contact-open N` | stored state bytes | constant 319 for a contact; `70 + CERT` for the account; `319·d + 1616·p` for a list of `d` devices of which `p` are unanswered | 2 + (d² + 3d)/2 sizes for up to `d` devices |

### Receiving a signup (sealed sender, PreKey message)

Only a new user's first message is processed; any other delivered message is refused (its shape is
not in the manifest), exactly as a message that fails a check is refused. The signup token is fixed width (108 characters),
which fixes the padded content: 176 bytes of ciphertext. What still varies between senders is
bounded and public:

| Kernel | Parameters | Determined by |
|---|---|---|
| `receive-envelope-point E`, `receive-unseal-static E`, `receive-unseal-message E` | envelope bytes | all of the below |
| `receive-content-shape U C0 C1`, `receive-content U C0 C1 HINT` | content bytes; the SENDER's certificate length (two varint bytes); whether a hint field follows | **bounded**: the certificate has a few lengths (with or without a phone number of 8–15 digits, embedded signer or reference) |
| `receive-certificate C0 C1 PRESENT LENGTH`, `receive-certificate-verified` | certificate length, phone-number field | as above |
| `receive-prekey-shape N`, `receive-prekey-open N P R S K`, `receive-signal-shape N P R S K` | message bytes; varint widths of the one-time prekey id (0: none), the sender's registration id, our signed and Kyber prekey ids | P, S, K: OUR ids — a deployment that numbers its prekeys below 128, or in one width, fixes them (0 and one width for P). R: 1 or 2 (ids below 16384) |
| `receive-session CERT N P R S K CW PW L0 L1 ADDR JUMP` | plus counter widths (1 for a first message), ciphertext length, whether addresses are present (client version), skipped messages | CW = PW = 1; L from the token width; ADDR 0 or 1; JUMP 0 |
| `receive-text L L−6`, `receive-access-key CERT L OFFSET` | ciphertext bytes; where the profile key starts (text start 4, 5 or 6 + text length) | constant for a fixed-width token (3 offsets covered) |

Sizes follow from the parts (`CircuitInventory.lean`, `signup`, checked there against the kernels'
own arithmetic): signal message = header + ciphertext + 8 + addresses + post-quantum field;
PreKey message `N` = keys + signal + ids; content `U` = 5 + certificate + hint + `N` framed;
envelope `E` = 81 + (`U` + 10) framed. The post-quantum field's body (`signup_pq`, 37 bytes from
libsignal 0.106) is a deployment setting: **a client version that sends another size is refused
until its size is added**.

Shapes per deployment: (sender certificate lengths) × (hint) × (P values) × 2 (R) × (ADDR values);
each costs about 5.6M AND gates of circuits to produce (unseal 2.7M, session 2.2M, the rest small).
The test deployment covers 4. A real deployment with, say, 6 certificate lengths, P ∈ {0, 1 width}
and both ADDR values needs 48: finite, but the right fix is to give these kernels capacities as
well (see "Not done").

### A contact's other devices (prekey fetch, establishment, multi-device sends)

| Kernel | Parameters | Determined by | Range / handling |
|---|---|---|---|
| `bundle-fetch-ctr SIZE P U K` | frame layout | constant (request ids from 2^63) | 1; named by `request-shape fetch` |
| `bundle-shape CAP` | response body size class | **data** → ladder | classes from 2560 up to `bundle_max` (about one per 2.5 KB device, 6 for two devices) |
| `bundle-item FIRST LAST D R S P K` | whether the item is first / last in the response; digit counts of its device id, registration id, signed prekey id, one-time prekey id (0: none), Kyber prekey id | **bounded**, but a product: D 1–3, R 1–5, S, K 1–10, P 0–10 | the description lists the combinations to cover (`bundle_items`). Replaces `bundle-device SIZE START D R S P K`, which also depended on the body size and the item's offset (unbounded). See "Not done" for the digit counts. |
| `establish-points F`, `establish-session CERT F`, `establish-challenges`, `establish-verified`, `bundle-rebind` (was `bundle-bind`) | one-time prekey present | constant / flag | 7 |
| `kem-hash kyber`, `kem-ntt`, `kem-matrix 0–3`, `kem-u 0–3`, `kem-v`, `kem-finish kyber` | none | constant | 12 |
| `bundle-seal CERT F CONTENT CW PW EW IW` | as `signal-seal-built`, for a device that has not answered | as there (counters start at 0) | 2 per `sends` row |
| `bundle-request-ctr SIZE P U K (D R)…` | frame layout for one message per device | the devices' envelope sizes: per device, established or pending without / with a one-time prekey, at one of the covered counter-width rows | (3·rows)^1 + … + (3·rows)^d for up to `d` devices (12 for two devices and one row); named by `request-shape devices`. Each is large (1.8M AND for two PreKey messages). See "Not done". |

### Not in a deployment's manifest

- Private-receive profile (the older design, no worker of the product uses it): `tls-open-application`,
  `tls-seal`, `tls-seal-private`, `tls-seal-private-ctr N`, `tls-seal-control`, `tls-reveal N`,
  `ws-activity N`, `ws-upgrade-byte`, `ws-idle-byte`, `ws-response-byte`, `ws-control-status`,
  `ws-control-reply I`, `signal-send`, `signal-send-open`, `signal-seal`, `signal-seal-fixed`,
  `signal-request-seal`, `establish-seal`.
- Superseded: `tls-open-application-ctr N`, `tls-seal-ctr 23 N 0`, `bundle-device …` (still defined;
  the worker no longer asks for them).
- Measurement only: `signal-seal-probe`, `kem-sample`.
- **Landed while this was written** (another engineer; not measured here): a second way to open
  received records, `tls-open-typed CAP` and `tls-frame CAP` (`TlsMpc/TypedOpenKernels.lean`), now
  the worker's default (`TLS_WORKER_TYPED_OPEN`, `TlsKernels::typed_open`). They take the same
  capacities (`RecordClass.capacity`). The setting `typed_records: 1` lists both for every record
  class up to `record_max`, beside `tls-open-application-class` (still used with
  `TLS_WORKER_TYPED_OPEN=0`); the test deployment sets it. Also since then: `bundle-rebind`
  replaces `bundle-bind` in the inventory. The numbers below were taken before both.

## The deployment description

`{"settings": {...}}`, the settings of `circuit_inventory` (each documented at the top of
`CircuitInventory.lean`): `profile`, `certificate`, `password`, `client_certificate`, `handshake`,
`record_max`, `seal_max`, `sends`, `devices`, `bundle_items`, `bundle_max`, and the `signup_*`
lists. `local_signal_server/deployment.json` is the test deployment;
`local_signal_server/deployment-compact.json` the compact-certificate local one (libsignal profile,
the second server instance); `real_signal/deployment-production.json` the real account's.
`profile` (`legacy` or `libsignal`) must be the sessions' `SIGNAL_CLIENT_PROFILE`: with `libsignal`
the sends are `signal-seal-official` and `bundle-seal … 80c−1`, and `produce_circuits.py` names
the request kernels with the same profile (the frames differ).

## Producing and pinning

`python3 scripts/produce_circuits.py DEPLOYMENT.json OUT [--max-gb 16]` (run it under
`scripts/guarded.py`):

1. names from `circuit_inventory`; 2. each produced alone, under the memory cap, by
`circuit_cache.py` (resumable: what is in the cache is not produced again); 3. the request
kernels named from the produced seal kernels' envelope sizes by the controller's own frame builder;
4. `OUT/manifest.txt` (`SHA256 LAYOUT_SHA256 NAME PARAMETERS` per kernel), `OUT/manifest.json` (plus
AND gates, gates, input and output bits, bytes, time and peak memory per kernel and in total), and
the gate lists and layouts.

The manifest belongs to one emitter binary. Any change to a Lean kernel changes the binary, the
cache key and every pin: produce again.

## Strict mode

`CIRCUIT_MANIFEST=OUT/manifest.txt` in the worker's environment (`kernel.h`, `KernelCache`):

- the parties exchange the SHA-256 of the manifest before the first kernel and stop if it differs;
- `get` serves only names in the manifest, from the manifest's directory, checked against its pins
  (gate list and layout); the per-kernel pin exchange, the cache lookup and the emitter are not used;
- a name outside it is refused: reported on stderr and in `CIRCUIT_REFUSED_LOG`; the operation fails,
  or — for a kernel whose parameters came from a received message or response — that message is
  refused and the session carries on;
- without `CIRCUIT_MANIFEST` nothing changes: kernels are found in the cache or produced on demand.

## Numbers

The test deployment (`local_signal_server/deployment.json`: certificate 244, records up to 6144
bytes, one message class at counter widths 1, up to two devices, 30 bundle width combinations in
two positions plus alone, 4 signup shapes), produced 2026-11-11 on this machine, one kernel at a
time under a 16 GB cap:

| | |
|---|---|
| Kernels | 284 in 53 families |
| AND gates in all | 116.1M (461.9M gates) |
| Gate lists on disk | 7.8 GB of text |
| Production time | about 17 minutes on an empty cache (944 s for 248 kernels in one run, 36 found cached; a second run after an emitter change: 582 s for 195) |
| Peak memory | 9.0 GB (`tls-open-application-class 6144`, 5.75M AND, which also took longest: 50 s); `receive-session` 7.5 GB |
| Rate | about 7.5 s and 1.4 GB per million AND gates |

With `typed_records: 1` (the test deployment as it is now: 62 more record kernels, `tls-open-typed`
and `tls-frame` for each of the 31 classes): **346 kernels, 151.5M AND gates (568M gates), 9.6 GB of
gate lists, 22.5 minutes on an emitter whose cache held only what other runs had produced (958 s
for 240 kernels), peak 9.0 GB.**

By family, without the typed kernels (kernels, AND gates): record opening 31, 34.8M; `bundle-request-ctr` 12, 14.5M;
`bundle-item` 90, 9.2M; `receive-unseal-message` 4, 9.0M; `receive-session` 4, 8.7M; `bundle-seal`
2, 7.2M; Kyber 12, 12.5M; stored state 12, 5.1M; `signal-seal-built` 1, 2.2M; the TLS handshake
8, 3.5M; everything else under 2M each.

A send-only deployment with one message class (no signups, no other devices) is 104 kernels;
each further message class or counter-width row adds one `signal-seal-built` (2.2–2.6M AND) and
one `signal-request-ctr` (0.3–0.4M).

### Strict mode against the local server (2026-11-11)

`check_signal_service_local.py MODE --strict-produced …` (the manifest produced beforehand; `--strict`
produces it first), one stage per run, nothing refused in any:

| Stage | Semi-honest | Malicious |
|---|---|---|
| Sends (`--runs 2`: admitted contacts, then contacts loaded from the store) | pass, 160 s | pass, 122 s |
| Database nodes and signup (`--runs 0 --db`: broadcasts, a signup with the fixed-width token, broadcast to the new contact, a second signup with the account from the database, delete) | pass, 304 s | pass, 203 s |
| Multi-device (`--runs 0 --multi-device`: 409, prekey fetch, two establishments, sends to both devices, reload) | pass, 186 s | pass, 223 s |

The sends and database runs used the 284-kernel manifest and the worker of that moment; the
multi-device runs used the 346-kernel manifest and the worker with typed opening. The first
multi-device attempt failed as strict mode should: a kernel added by another change that day
(`bundle-rebind`) was not in the older manifest, the worker reported
`kernel not in the circuit manifest: bundle-rebind`, and the session ended without producing anything.

The multi-device stage passes only when the linked device's numbers have the digit counts listed in
`deployment.json` (`bundle_items`); a registration id under 100, a linked device's key id under
1,000,000 or a one-time prekey id of another width would be refused (by the ids' ranges, an
estimated one run in eight; not observed in these two). That is "Not done" 3.

### Loading

In strict mode a send session's workers spend 0.9–1.1 s loading circuits (semi-honest, two contacts,
two broadcasts; `scripts/session_profile.py`). Sessions of the same kind without a manifest, the
same day, showed 1.0–3.6 s (other engineers' profiles; not a controlled comparison, and the kernel
sets differ). What strict mode removes per kernel: the pin exchange between the parties and the
hashing of the emitter binary to find the cache directory. What remains is reading, hashing and
parsing the text gate lists, already made direct in `lean_circuit.h` by the performance work
(`PERFORMANCE.md` recorded 6.8 s before it). A binary gate-list form is not done.

## Not done, and what each needs

1. **`tls-open-handshake`** is per record size (deployment constants today). Against a server
   whose handshake record sizes vary it needs classes; measure the real server first.
2. **Receive kernels** (`receive-*`) are per exact size. The set is finite for a fixed-width token
   (the product of the bounded parameters above) but each shape costs two 2M-gate kernels. Giving
   them capacities means making `ReceiveFirst`'s HMAC and CBC work on a length inside a capacity
   and its field offsets values rather than parameters: a rewrite of that module and its proofs.
   Until then: enumerate (cheap to list, about 40 s and 10 GB to produce per shape), and anything
   else is refused.
3. **Digit counts in `bundle-item`**: realistic ranges (registration ids of 1–5 digits, key ids of
   1–8) multiply to thousands of 100K-gate kernels. The fix is fixed-width number slots: the body's
   punctuation is public, so the worker can splice public `0` characters in front of each number
   (a generic "splice" binding) and one kernel per (FIRST, LAST, one-time present) remains; the
   number parser must then accept leading zeros while the canonical-form check moves to the first
   real digit. Not done: it changes `BundleResponse.device` and its theorems.
4. **`bundle-request-ctr`** (and `signal-request-ctr`): one kernel per combination of envelope
   sizes. The fix is to seal request frames with `tls-seal-class` after a small fixed kernel has
   formatted the private slots (UUID, access key, device and registration ids), with the worker
   placing those slot wires at the controller's public offsets. Not done: it changes how every
   send is sealed, in files two other engineers were editing.
5. **Loading**: gate lists are still text, hashed and parsed once per worker process. Strict mode
   removes the per-kernel pin exchange and the per-kernel hashing of the emitter binary; a binary
   gate-list form pinned by the manifest is not done.
6. `record_max` bounds what can be received: a record above it is refused (the session fails at
   that record). The largest class (20480) is about 19M AND gates and well over 16 GB to produce
   with today's lowering; classes up to 8192 fit under the cap.
