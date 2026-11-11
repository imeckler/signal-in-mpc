# Contacts with several devices

Status 2026-11-11: **live against the local Signal-Server.** A contact that links a second device is
found by the 409 to the next send; the client fetches the contact's prekey bundles, establishes a
session per device in the engines, stores the device list and sends one message per device. Both
devices decrypt (a conventional libsignal client per device), in that session and in the next one
with the list read back from the database nodes: `check_signal_service_local.py --multi-device`
passes in semi-honest and in malicious mode. Section 7 says what is bound and what is not; section 6
has the measured cost. Never run against Signal's own service.

Files: `TlsMpc/Signal/BundleResponse.lean` (definitions), `TlsMpc/BundleKernels.lean` (kernels, `find`),
`TlsMpc/BundleProofs.lean` (theorems), `check_bundle_kernels.py` (check), `bundle-kernels-report.json`.

## 1. What a node may see

A node can fetch anyone's prekey bundle itself (`GET /v2/keys/{uuid}/*` as any registered account).
Whatever it sees of a contact's bundle that it can also see in such a fetch is a test for "is person X
a contact". So:

| Value | Decision | Why |
|---|---|---|
| Identity key, signed prekey, Kyber prekey, their signatures | private | stable, served to anyone |
| Signed prekey id, Kyber prekey id | private | random 24–31 bit numbers, stable for weeks (the last-resort Kyber key's id for good) |
| One-time prekey id | private | ids of one device are consecutive, so a node's own fetch before or after brackets it |
| Registration id | private | 14 random bits per device, stable, served to anyone |
| Device ids (409/410 bodies, bundle items) | private | assigned as the smallest free id from 2, so a set with gaps (`{1,3,7}`) is close to a fingerprint and anyone can list X's devices |
| Number of devices | public (unavoidable) | the send request has one message per device and its length is public |
| Digit counts of the five numbers per device; whether a device has a one-time prekey | public | see below |
| Response status (200/401/404/409/410) | public | as today |

Consequences:

* **No response body is ever revealed**, including the 409/410 bodies. The controllers reveal the
  WebSocket framing and the response's id, status, message and headers, and pass over field 4 (the body).
  (A response used to be revealed to the end of its frame; since 2026-11-11 its body is passed
  over, section 7.)
* Because the 409/410 body is not read, recovery does not target the missing devices. It fetches
  `/v2/keys/{uuid}/*` and **replaces every session of the contact** (section 3). This is also the
  session reset. It costs one establishment per device instead of per missing device; if that is too
  dear, the alternative is to open the device ids (one more shape kernel over the 409 body, per-device
  fetch `/v2/keys/{uuid}/{id}`) and accept the leak in the table.
* **The opened shape.** The body's length is public, and with it the sum of all digit counts. The
  kernels open more than the sum: each count separately (via one flag per body byte, "is JSON
  punctuation"). That is about two bits per device that a node could compare with its own fetch of X
  (mainly: is the registration id five digits, is the signed prekey id eight). It can make X less
  likely to be this contact, never confirm it. The receive path opens the same kind of widths. If it
  is not acceptable, the fix is a parser with private offsets (select each field among the layouts
  consistent with the public length); estimated under 1M AND gates per device, not built.
* **Not avoidable by any parser:** a node sees *when* a contact's device list changed (the 409/410
  and the fetch that follows) and can compare that with when X linked or removed a device.

## 2. The response

`{"identityKey":"<44>","devices":[ITEM,...]}` with

    ITEM = {"deviceId":D,"registrationId":R,"signedPreKey":{"keyId":S,"publicKey":"<44>","signature":"<86>"},
            "preKey":null | {"keyId":P,"publicKey":"<44>"},
            "pqPreKey":{"keyId":K,"publicKey":"<2092>","signature":"<86>"}}

(`entities/PreKeyResponse.java`, `PreKeyResponseItem.java`, `ECSignedPreKey.java`, `ECPreKey.java`,
`KEMSignedPreKey.java`; keys are padded base64 of `05‖key` / `08‖key`, signatures are base64 *without*
padding, `util/ByteArrayAdapter.java`). Only the digit counts of `D R S P K` and `null` vs object vary,
so the punctuation flags determine the layout. One device is 2465 bytes plus its digits.

**Confirmed on the local server (2026-11-11).** Raw bodies of `GET /v2/keys/{uuid}/*` for accounts
with one, two and three devices (`lss-provision keys-dump`) have exactly this form: the field order
above, no whitespace, `"preKey":null` for a device without one-time prekeys, unpadded signatures. On
each of them the Lean `layout?` gave the layout a JSON parse gives, and `bundle-shape` and
`bundle-device` gave the flags and every field (`.deps/agent-bind/check_real_bodies.py`, which uses
`check_bundle_kernels.py`'s references). No change to the Lean template was needed. Two things the
source reading had not shown:

* **Devices are not in id order.** A device linked later can come first (`{2, 1}`). Nothing here
  depends on the order: the request's messages are in the response's order, and each names its own
  device id.
* **The response is one WebSocket message of about 2.6 KB per device** (5,095–5,162 bytes for two
  devices, 7,646 for three). The controllers' frame and response parsers accepted 4,096 bytes;
  `PublicReceive.capacity` is now 16,384 (six devices, the server's limit, are under 15,000).

The 409 to a send is `{"missingDevices":[2],"extraDevices":[]}` in field 4 of the response, after
the id and the status, as section 1 assumes. It is passed over unread.

## 3. Refreshing a contact's sessions (after 409 or 410, or to reset)

Kernels are named as `find` takes them. "Establish step n" is the list in `TlsMpc/EstablishKernels.lean`.

 1. Controllers build the masked frame of `GET /v2/keys/{uuid}/*` with header
    `Unidentified-Access-Key:{key}`, with zero bytes in the two slots.
    `bundle-fetch-ctr SIZE PAYLOAD UUID KEY` (input `record`: any record of the contact) inserts the
    UUID and access key and encrypts the record. Opens `accepted`, `header`, `ciphertext`.
 2. The response arrives. Controllers reveal its framing, id and status; the body is passed over and,
    if the status is 200, collected unopened for the engines (as a delivered envelope's content is).
    Any other status: nothing is collected; 404 means the account is gone.
 3. `bundle-shape SIZE`: opens `shape`, one flag per body byte.
 4. Controllers, in the clear: `BundleResponse.layout? flags` gives the devices' widths or refuses;
    `BundleKernel.arguments SIZE widths` gives one `bundle-device` parameter list per device.
 5. For each device, `bundle-device SIZE START D R S P K`: private `valid`, `identityKey`, `deviceId`,
    `registrationId`, `signedPrekeyId`, `signedPrekey`, `signedPrekeySignature`, `kyberPrekeyId`,
    `kyberPrekey`, `kyberPrekeySignature`, and with a one-time prekey `oneTimePrekeyId`,
    `oneTimePrekey`: the input names of the establishment kernels. Opens nothing.
 6. Establish steps 1–5 on those fields (the identity key is the same for every device, so
    `xeddsa-recover` runs once per response): private `verified`.
 7. `bundle-bind` (inputs `record`, `valid`, `verified`, `identityKey`): the private `verified` for
    `establish-session` — now also requiring that the body parsed and that the identity key is the
    one stored for this contact — and the contact's private `uuid` and `accessKey`.
 8. Establish steps 6–8. Field engine: `dh1`, `dh2`, `dh3`, (`dh4`), `ratchetAgreement`, `basePublic`,
    `ratchetPublic` with a fresh shared base scalar and ratchet scalar per device. The twelve
    `kem-*` kernels (variant `kyber`, `ML_KEM_ENCAPSULATION.md`) on `kyberPrekey`, with 32 private
    bytes from each party. `establish-session` with `deviceId`, `registrationId` and the key ids from step 5,
    `uuid`, `accessKey` from step 7, our certificate, our registration id and the connection's request
    id as public constants. It opens the **one status byte**; failure does not say why (bad JSON,
    bad signature, changed identity key, zero agreement and failed KEM look the same).
 9. Only if every device's status is 255: the contact's device list becomes the new one (section 4),
    is written to the database nodes, and the message is sent again. Otherwise the old state is kept
    and the contact is reported as failed. Retry the whole refresh at most twice (a device can be
    linked between the fetch and the send; a device with no prekeys is left out of the response and
    produces another 409). *As built:* one refresh and one resend per message; a second refusal,
    a failed fetch or a failed establishment ends the session with an error (section 7).

One establishment is about 90 seconds of engine time in malicious mode and the server drops a socket
that is silent for 90 seconds, so the worker runs it in nine steps and the controllers send a
`GET /v1/keepalive` before a step whenever 20 seconds have passed, on a clock they agree on, since
the last request.

A changed identity key (the contact re-registered) therefore shows up as "refresh failed". Accepting a
new identity is a separate decision (PRODUCT_TODO section 3) and needs its own rule; it must not be
automatic.

## 4. Stored state

`establish-session`'s `conversation` output is our certificate followed by the 319-byte record the
send kernels read, so the record needs no conversion (`keep` in `service_kernels.h` already drops the
certificate). But a record is not all a new session needs:

* A session we started is unacknowledged until that device answers, and until then every message must
  be a PreKeySignalMessage built from the 1616-byte `pending` output. Messages from contacts are ignored
  today, so in practice: always. **Each such device stores record ‖ pending = 1935 bytes.**
* The sessions created by a signup (we were the responder) stay 319 bytes.

Blob plaintext (as built): the devices' entries one after the other, each 319 bytes (kind 0), or 1935
(kind 1: no one-time prekey was used; kind 2: one was). The kinds are stored in the clear after the
ciphertext, as `kinds ‖ count` (they are visible in every send's length anyway), and give the count
and the offsets; a contact that is one established record is stored as before, without them, so
existing blobs stay valid. **The kinds are not authenticated** (the check value covers the
ciphertext only). Today every entry of a device list is kind 1 or 2, which have the same size, so
wrong kinds cannot shift where an entry starts; they can only make a device's messages malformed
(1 and 2 swapped). Once kind 0 entries can be mixed in (when replies are processed), a wrong order
would misalign records, and a misaligned record's bytes would be used as UUID and keys. Before
that, the kinds must be sealed with the content and compared inside a kernel. Not built.
`contact-seal` / `contact-open` take the total size (six pending devices are 11,610 bytes; the kernels'
limit is 16,384). Per contact, not per device: the recipient point, the static agreement and the
offset table, since all devices share the identity key.

When replies are handled one day, `establish-session`'s `receiver` output (192 bytes) is what turns a
kind 1/2 entry into kind 0; it is dropped today, like the receive path's.

## 5. Sending to a contact with n devices

 1. For each device: open the counter widths (`signal-widths CERT`), then
    kind 0: `signal-seal-built` as today; kind 1/2: `bundle-seal CERT ONETIME CONTENT CW PW EW IW`
    (`establish-seal` for a text built in the clear; inputs as `establish-seal` plus `pending`,
    `localAddress`; `CONTENT` is the padded content size). A fresh ephemeral pair per device. All
    devices get the same built text (one timestamp). Keep the new records only when every status is 255.
 2. Controllers build one frame for `PUT /v1/messages/{uuid}` with
    `"messages":[{"type":6,"destinationDeviceId":___,"destinationRegistrationId":__________,"content":"..."},...]`
    and zero bytes in the slots. `bundle-request-ctr SIZE PAYLOAD UUID KEY (DEVICE REGISTRATION)×n`
    (input `records`: the n records concatenated) fills them — ids space padded to 3 and 10 characters,
    so their digits stay private — and encrypts the record.
 3. 200: done. 409/410: section 3, then send again (new sessions, so `bundle-seal`). 404: the account
    is gone. 401: the access key no longer matches (the profile key changed).

A PreKey envelope is about 2.0 KB plus the certificate (2,001 bytes at a 40-byte certificate and 80
content bytes), roughly 1.7 KB more than an established one. In base64 that is about 3 KB per device,
so about five unanswered devices fill a 16 KB TLS record (fewer with longer texts), and both request
kernels are limited to one record: more devices than that need a request split over records.

## 6. Cost per new device

### Measured live (2026-11-11, local server, two devices, one worker log per run)

Busy seconds are time inside the worker for circuits that were already cached; a circuit shape seen
for the first time is produced on demand and adds its lowering time once (below).

**Establishing one device's session** (operation 60, nine steps):

| | AND gates | Field products | Busy, semi-honest | Busy, malicious |
|---|---|---|---|---|
| Step 0: fields, two signatures, binding | 2.09M (3.12M malicious) | 23,400–28,000 | 0.9 s | 2.3–3.0 s |
| Step 1: six agreements (seven with a one-time prekey) | 5k | 18,288 (21,084) | 0.1 s | 1.1–1.5 s |
| Steps 2–7: encapsulation | 12.52M | 0 | 0.4 s | 4–6 s |
| Step 8: session | 0.92M (0.94M) | 0 | 0.2 s | 0.4 s |
| **One device** | **15.55M (16.6M malicious)** | **about 44,000–49,000** | **about 2–3 s** | **8–10 s** |

The first device of a response carries the identity key's lift (about 2,500 products). The step 0
gate count differs by mode because the conversions between the engines do.

**Once per refresh**, besides the devices: receiving the response (a 5.1 KB TLS record: 10.4M AND
gates, most of it the authentication of a record that long), `bundle-shape` 229k, the fetch request
45k, storing the new list 1.04M (3,870 bytes for two unanswered devices).

**Each message to a contact with two unanswered devices**, against one established device:

| | Two unanswered devices | One established device |
|---|---|---|
| Seal (operation 61 / 41) | 7.21M AND, 15,200 products | 2.19M AND, 14,600 products |
| State stored before the send | 1.04M | 0.09M |
| Request record (two PreKey envelopes, a 6.4 KB frame) | 4.49M | 0.3–0.8M |
| **Total** | **12.7M AND; 0.8 s semi-honest, 4.5 s malicious** | **about 3M AND; 0.3 s, 1.3 s** |

So each unanswered device adds about 6.3M AND gates per message (3.6M seal, 0.5M state, 2.2M of
request record), about 640 field products, and 0.4 s (semi-honest) or 2 s (malicious). (Most of a
message's field products are the per-contact preparation after its state is loaded, not the device.)

**Whole sessions** (two contacts, two broadcasts): one device each 4.7 s / 12.8 s (semi-honest /
malicious); the session with the 409, the refresh and the resend 131 s / 134 s, of which about 85 s
is first-time production of circuits for sizes that depend on the response (the 5.1 KB record, the
6.4 KB request, the 3,870-byte state); the next session, device list read from the database nodes,
8.4 s / 21 s.

**First-time circuit production** that a refresh can trigger while the socket is open: `bundle-seal`
is 3.60M AND gates and takes about 60 s and 10.4 GB to lower (it is produced ahead of a run for the
usual widths `1 1 1 1`; other widths would not fit the 90 seconds); `establish-session` 15 s;
`establish-challenges` and each `kem-*` kernel 3–7 s; the record-sized kernels above together about
45 s and 30 s.

**The single-device path** changed in one way: a response is revealed in about 16 steps instead of
about 4 (its body, formerly revealed, is passed over). A step is one RPC that opens a few wires;
134 such steps in a whole session take 0.1 s of worker time in either mode.

### From the kernels

AND gates (measured by lowering, `bundle-kernels-report.json` and `establish-kernels-report.json`):

| Kernel | AND gates |
|---|---|
| `bundle-shape` | 45 per body byte: 118,440 for one device, 340,740 for three (once per response) |
| `bundle-device` | 100,308 – 104,098 |
| `establish-challenges` | 1,940,431 |
| `establish-verified`, `bundle-bind` | 771, 535 |
| `establish-session` | 918,035 (940,793 with a one-time prekey), at a 40-byte certificate |
| the twelve `kem-*` kernels (replacing `establish-kem`, about 190M) | 12,521,696 |
| `bundle-fetch-ctr` | 57,549 for a 164-byte frame (once per response) |

So about 3.0M AND gates plus the KEM's 12.5M. Field products: six ladders at 2,794 (seven with a one-time
prekey) and two `xeddsa-check` at 9,402, that is 35,568 (38,362) per device, plus `xeddsa-recover`
2,537 once per response; and the conversions around them (about a dozen words to or from the field,
and 1,020 challenge and scalar bits into it).

Afterwards, each message to a device that has not answered: `bundle-seal`, the same circuit as
`establish-seal` (3,491,525 AND gates at 80 content bytes). `bundle-request-ctr` was 201,771 for two
devices in a 482-byte frame: AES over the frame plus about 21k per device.

### ML-KEM encapsulation

**It cannot leave the engines.** Whoever encapsulates holds the Kyber public key, and that key is
linkable: when a device's one-time Kyber prekeys run out the server serves its *last-resort* key, the
same one to every caller, and a caller cannot tell which kind it got. A node can also force that case
by fetching X's bundle until the one-time keys are used up. The key cannot be blinded either: it
contains the 32-byte seed `ρ` of the matrix, unique per key. (Its signature and id are linkable too,
but those could stay inside; the key itself is the problem.) Revealing the key to one node only is
still revealing it to a node.

**Done: alternative 2 below**, as twelve kernels of 12.5M AND gates together
(`ML_KEM_ENCAPSULATION.md`), run inside `bundleEstablish` steps 2–7. The alternatives as they were
considered:

1. **Run it as it is.** 190M AND gates per new device, only when a device list changes. Whether that
   is tolerable depends on the engines' AND rate and on how often 409s occur across thousands of
   contacts; it can run while other contacts are being served only if the worker allows it.
   Note `establish-kem` has never been lowered or run, so it is also untested as a circuit.
2. **Rewrite the arithmetic for q = 3329.** The 190M comes from a generic 32-bit multiply and
   remainder per coefficient operation. With 12-bit multipliers, Barrett reduction and constant
   multiplications in the NTT, an operation count gives about 22k modular multiplications (11M),
   about 100 Keccak permutations (3.8M), rejection sampling by compaction (about 1M), additions and
   compression (2M): **roughly 15–20M AND gates**, an estimate, not a measurement.
3. **Arithmetic shares modulo q.** The NTT is linear with public constants and becomes free; about
   13k products modulo q remain, plus Keccak and sampling in the Boolean engine (about 5M) and the
   conversions. This needs a third engine (the field engine's prime is 2^255 − 19) and its review.
4. Not available: skipping the KEM (the server requires `pqPreKey` and libsignal requires the Kyber
   ciphertext), or having the contact's device start the session (a newly linked device does not
   write to us, and the server rejects sends that omit it).

## 7. The live binding (done 2026-11-11) and what it leaves out

**Kernels registered**: `BundleKernel.find` and `MlKemFastKernel.find` are in `EmitFlatKernel.lean`
and `EmitHybridKdf.lean`; `establish-kem` is no longer offered by `EstablishKernel.find`.
`flat_kernel_emitter layout MASK_FILE` runs `layout?` (for the checks).

**Worker** (`service_kernels.h`, operation codes in `tls_worker_v3.cpp` / `TlsWorkerPipe.lean`):

| Code | Operation | What it does | Opens |
|---|---|---|---|
| 56 | `bundleFetch` | retains the fetch frame with sealer `bundle-fetch-ctr`, input `record` | the sealed record |
| 57, 58 | `bundleTake`, `bundleDrop` | collects the response body unopened (up to 65,536 bytes); drops it | nothing |
| 59 | `bundleShape` | `bundle-shape` | the flags |
| 60 | `bundleEstablish` | one of nine steps of one device: 0 fields, signatures, binding; 1 agreements; 2–7 encapsulation; 8 session | step 8: the status byte |
| 61 | `devicesSend` | per device an ephemeral pair and `bundle-seal` (kind 1, 2) or `signal-seal-built` (kind 0) | status, timestamp, envelope per device |
| 62 | `devicesRequest` | retains the request frame with sealer `bundle-request-ctr`, input `records` | the sealed record |
| 63 | `devicesOpen` | `contact-open` on a stored device list, split by the public kinds | the key check |
| 38 | `contactSeal` (existing) | for a device list: seals its entries one after the other | check, ciphertext |

The device list replaces the contact's state only when every device's status is 255.

**Controllers** (`PublicServiceController.lean`):

* *Reveal policy.* A response is no longer revealed to the end of its frame. `replyScan` walks its
  fields in the clear, `replyBudget` bounds each reveal step to bytes that cannot be body content,
  and the body (field 4) is passed over with `stepPassed`, as a request's body is. It is handed to
  the engines only if it belongs to the `200` answering the pending prekey fetch
  (`State.fetch`, `collect`). This holds for every response, also on the single-device path, whose
  responses now take about 16 reveal steps instead of 4 (each opens a few wires; section 6).
* *409/410.* On the send socket of a local-server session a response that is not a success completes
  instead of ending the session (`State.lenient`), and the loop reads its status: 409 or 410 starts
  `refreshContact` (fetch, `bundleShape`, `layout?`, the establishment steps with keepalives, store),
  then the same message is sent again by `sendDevices` and must be answered 2xx.
* *Sends.* `sendMessage` goes to `sendDevices` for a contact with a device list:
  `devicesSend`, store (`storeAdvanced`, before anything leaves), `PublicRequest.buildDevices`,
  `devicesRequest`.
* *Storage.* `sealState` / `openState` add and read the kinds after the ciphertext (section 4), for
  the database nodes and the test store alike.

**Not done:**

* Failure handling is "end the session": a second 409 after the resend, a fetch answered 401/404,
  a refused layout and an establishment status other than 255 all throw. The design's "report the
  contact as failed and carry on" and "retry the refresh twice" are not built.
* A device list with an established entry (kind 0) is never produced (replies are not processed),
  so `devicesSend`'s kind 0 branch has not run, and the kinds are not authenticated (section 4).
* The request is one TLS record: at most about five unanswered devices; more are refused by the
  controllers before anything is sent.
* A keepalive is sent between establishment steps but not inside `devicesSend`; with more than
  about four unanswered devices one send would be silent for more than 90 seconds in malicious
  mode.
* Accepting a changed identity key (section 3), targeted recovery from the 409 body (section 1).
* Tested with two devices on the local server only (one device with and one without a one-time
  prekey); three or more devices, 410, and a device removed (extra device) have not been run.

The lists below are the plan this was built from.

**Worker operations** (`service_kernels.h`, `tls_worker_v3.cpp`); a contact holds a list of
(record, pending, kind) instead of one record:

1. `bundle_fetch(id, payload_at, uuid_at, key_at, mask, frame)`: retain a private buffer with sealer
   `bundle-fetch-ctr SIZE PAYLOAD UUID KEY`, extra input `record` = the contact's first record.
2. `bundle_take(handle, offset, count)` / `bundle_drop()`: collect the response body unopened (as
   `envelope_take`; allow 65,536 bytes).
3. `bundle_shape()`: run `bundle-shape`, open `shape`, reply with the flags.
4. `bundle_establish(id, parameter lists, our registration id, request id)`: steps 5–8 of section 3
   for every device, with each party's private 32-byte KEM entropy; reply with the statuses; replace
   the contact's device list only if all are 255.
5. `seal_open` for n devices: per device the kernel for its kind; reply timestamp, then each envelope.
6. `request` for n devices: sealer `bundle-request-ctr ...`, extra input `records`.
7. `contact_seal` / `contact_open`: the blob of section 4, split by the public kinds.

**Controller steps** (`PublicServiceController.lean`):

1. Reveal policy: in a response (`08 02`) never reveal field 4 (body); pass it over, and collect it
   only when the response's id is that of a pending prekey fetch and its status is 200. (Fields are
   written in number order: id, status, message, body, headers — the status is known before the body.)
2. On 409 or 410 to a send: start the refresh; build the fetch frame; keep the request id.
3. On the body: `bundle_shape`, then `BundleResponse.layout?` and `BundleKernel.arguments` (Lean, in
   the clear, both controllers), then `bundle_establish`. Refuse if `layout?` refuses.
4. Build the multi-message request and its slot offsets; send again; bound the retries.
5. Keep each contact's kinds with its stored blob; write the new blob before the resend.

## 8. What is checked and what is not

`check_bundle_kernels.py` (run under `scripts/guarded.py`) builds responses for one device and for
three (ids of 1 to 10 digits, with and without a one-time prekey) independently in Python, and
compares: the opened flags; the Lean `layout?` on them; every output of `bundle-device` against a
`json.loads` parse; 32 altered bodies or wrong layouts, each of which must release nothing;
`bundle-bind` and six rejections; and both request kernels against AES-GCM (`cryptography`) applied to
the real WebSocket frame. It also asserts from the layout files that `bundle-device` and `bundle-bind`
open nothing. Result on 2026-11-11: all pass.

**Live check** (`local_signal_server/check_signal_service_local.py MODE --runs 0 --multi-device`,
under `scripts/guarded.py 24 ...`; contact state on five database nodes):

* A. Broadcast twice to two contacts with one device each; their state is created in the database.
* B. `lss-provision link recipient` registers device 2 on the local server (its own registration id,
  signed prekey and Kyber key; no one-time prekeys, so its bundle has `"preKey":null`, while device
  1 still has one). Broadcast twice: the first send to that contact is answered 409, then the
  refresh and the resend. `lss-provision receive recipient` and `receive recipient.2` must each
  decrypt both texts, sealed (no source fields), and the other contact both as well.
* C. A new session, the device list read from the database nodes. Both devices must decrypt both
  broadcasts again.

Result on 2026-11-11: passes in semi-honest and in malicious mode. This is the first run of
`bundle-seal`, of the establishment kernels fed from `bundle-device`, of the `kem-*` kernels in the
engines, and of the two request kernels against a server; the recipients are libsignal clients, so
a wrong session, PreKey message or Kyber ciphertext would not have decrypted.

Not checked: more than two devices; 410; a removed device; a device list with an established entry;
a refresh that fails. Proof status: `TlsMpc/BundleProofs.lean`, header. The controllers' reveal
policy (`replyScan`, `replyBudget`, `stepPassed`) is code with run-time checks, not theorems, like
the policy for request bodies before it.
