# Contacts with several devices

Status 2026-11-11: **live against the local Signal-Server.** A contact that links a second device is
found by the 409 to the next send; the client fetches the contact's prekey bundles, establishes a
session per device in the engines, stores the device list and sends one message per device. Both
devices decrypt (a conventional libsignal client per device), in that session and in the next one
with the list read back from the database nodes: `check_signal_service_local.py --multi-device`
passes in semi-honest and in malicious mode. Section 7 says what is bound and what is not; section 6
has the measured cost; section 9 is what happens when something fails (per-contact results,
retries, a changed identity key, the delivery guarantee). Never run against Signal's own service.

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
 7. `bundle-rebind` (inputs `record`, `valid`, `verified`, `identityKey`): the private `verified` for
    `establish-session` — now also requiring that the body parsed — and the contact's private
    `uuid` and `accessKey`. It does **not** require the identity key to be the one stored for the
    contact: a contact that registered again is accepted (owner's decision, 2026-11-11). It opens
    one byte, `changed`: 255 when the bundle parsed, both signatures verified under the bundle's
    own identity key, and that key is not the stored one; otherwise 0 (section 9).
    (`bundle-bind`, which requires the stored identity key, is still defined and no longer used.)
 8. Establish steps 6–8. Field engine: `dh1`, `dh2`, `dh3`, (`dh4`), `ratchetAgreement`, `basePublic`,
    `ratchetPublic` with a fresh shared base scalar and ratchet scalar per device. The twelve
    `kem-*` kernels (variant `kyber`, `ML_KEM_ENCAPSULATION.md`) on `kyberPrekey`, with 32 private
    bytes from each party. `establish-session` with `deviceId`, `registrationId` and the key ids from step 5,
    `uuid`, `accessKey` from step 7, our certificate, our registration id and the connection's request
    id as public constants. It opens the **one status byte**; failure does not say why (bad JSON,
    bad signature, zero agreement and failed KEM look the same).
 9. Only if every device's status is 255: the new device list, held as scratch in the worker, is
    sealed, written to the database nodes as the contact's next version, and once they acknowledged
    it becomes the contact's state (section 9, "scratch, then commit"); the message is sent again.
    Otherwise the scratch is dropped, the contact is exactly as before and is reported as failed.
    A refusal of the resend (a device was linked between the fetch and the send; a device with no
    prekeys is left out of the response) is refreshed again, at most twice more per message.
    *As built* (section 9): all of this, as per-contact outcomes; the session carries on.

One establishment is about 90 seconds of engine time in malicious mode and the server drops a socket
that is silent for 90 seconds, so the worker runs it in nine steps and the controllers send a
`GET /v1/keepalive` before a step whenever 20 seconds have passed, on a clock they agree on, since
the last request.

A changed identity key (the contact registered again) is accepted automatically, by the owner's
decision of 2026-11-11: the sessions are replaced under the new key and the id is reported as
"delivered after identity change". What that trusts and reveals is in section 9 and in
`NEEDS_REVIEW.md`.

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
| 60 | `bundleEstablish` | one of nine steps of one device: 0 fields, signatures, binding; 1 agreements; 2–7 encapsulation; 8 session. The result is scratch, not the contact's state | step 0 of the first device: `changed`; step 8: the status byte |
| 64, 65 | `scratchSeal`, `scratchCommit` | seals the scratch device list for storage; makes it the contact's state (58 `bundleDrop` discards it) | 64: check, ciphertext |
| 61 | `devicesSend` | per device an ephemeral pair and `bundle-seal` (kind 1, 2) or `signal-seal-built` (kind 0) | status, timestamp, envelope per device |
| 62 | `devicesRequest` | retains the request frame with sealer `bundle-request-ctr`, input `records` | the sealed record |
| 63 | `devicesOpen` | `contact-open` on a stored device list, split by the public kinds | the key check |
| 38 | `contactSeal` (existing) | for a device list: seals its entries one after the other | check, ciphertext |

The device list replaces the contact's state only when every device's status is 255 **and** the
database nodes acknowledged the sealed list (operation 65, section 9).

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

**Done since (section 9):** failure handling as per-contact outcomes, the refresh retried, a
changed identity key accepted, three devices, a removed device, 410.

**Not done:**

* A device list with an established entry (kind 0) is never produced (replies are not processed),
  so `devicesSend`'s kind 0 branch has not run, and the kinds are not authenticated (section 4).
* The request is one TLS record: at most about five unanswered devices. Splitting it is not
  cheap (both request kernels seal exactly one record, and the 16 KB limit is the TLS record's),
  so it was not done: such a contact is reported "retry later" with the reason "a message to N
  devices does not fit one request", after the engines sealed the message and before anything is
  stored or sent, and is not tried again in that session. Not run (it needs six linked devices).
* A keepalive is sent between establishment steps but not inside `devicesSend`; with more than
  about four unanswered devices one send would be silent for more than 90 seconds in malicious
  mode. (The connection would then be closed by the server and replaced, section 9.)
* Targeted recovery from the 409 body (section 1).

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

Not checked: a device list with an established entry; more than five devices (section 9 has what
was added). Proof status: `TlsMpc/BundleProofs.lean`, header. The controllers' reveal
policy (`replyScan`, `replyBudget`, `stepPassed`) is code with run-time checks, not theorems, like
the policy for request bodies before it.

## 9. Failures as per-contact results (2026-11-11)

A send session with the database nodes no longer ends when something goes wrong for one contact.
Code: `PublicServiceController.lean` (`Recovery`: the table, limits and result names; `deliver` in
`main`: the session), `service_kernels.h`, `tls_worker_v3.cpp` (operations 17, 37, 41, 61, 63 and
the new 64, 65, 91), `TlsMpc/BundleKernels.lean` (`bundle-rebind`). `SIGNAL_RECOVERY=0` on both
nodes runs the previous loop. Sessions without the database nodes (the test store, the fixture)
run the previous loop as before: without a store written before each send, sending again is not
safe across sessions.

### What ends the session and what does not

Still the session's failure (the worker is terminal, as before): an engine or MAC failure; a
request the two workers were not handed identically; a TLS record that does not authenticate or
a fatal alert; a handshake or proxy connect that fails; a commitment that does not open; an
opened shape that is not what Lean declares; the database client failing on a read; no record
from the server for 30 seconds while a response is awaited.

Now one contact's result. Each is a value both nodes already saw (before, as the reason the
session ended):

| Status | Seen as | What it shows |
|---|---|---|
| a send cannot be sealed | `contactSend` / `devicesSend` reply `0` | the seal kernel's gated status was not 255 (the byte Lean marks as openable), or the opened counter widths name no kernel |
| stored state does not open | `contactOpen` / `devicesOpen` reply `0` | the key check of the stored blob failed (`contact-open`'s `accepted`) |
| a device does not verify | `bundleEstablish` status not 255, or layout refused | one byte, not the reason (unchanged) |
| the identity key changed | `bundleEstablish` reply 254 at the first step | `bundle-rebind`'s `changed`: the bundle parsed and verified, under another identity key |
| response status, `Retry-After` | revealed status and headers | as before; a body is never revealed |
| connection closed | `pollRecord` reply `[0]` | the leader's socket was closed by the server or the proxy |
| database did not take a write | each party's own client result, exchanged | whether the nodes acknowledged this contact's blob |

### Scratch, then commit

`bundleEstablish` builds the new sessions in a scratch slot (`Establishing` in
`service_kernels.h`) and never touches the contact. When every device's status is 255 the
controllers call `scratchSeal` (the scratch sealed under the contact's key), submit that blob to
the database nodes as the contact's next version, tell each other whether the nodes acknowledged
it, and only if both saw it call `scratchCommit`; otherwise `bundleDrop`. On any failure before
that — fetch refused, connection closed, layout refused, a device not verifying — the scratch is
dropped. Either the contact has its new list in the engines and on the nodes, or it has exactly
what it had. (A write the nodes took only partly is the nodes' matter: PRODUCT_TODO section 6.)

### Policy

| Signal | Action |
|---|---|
| 409 / 410 to a send | refresh, send again; refused again: refresh again, at most 2 more times, then "retry later" |
| 429 or 5xx, to a send or the prekey fetch | wait `Retry-After` seconds if the response says so (at most 60 s; longer gives the contact up), else 1 s, 3 s, 9 s; the contact goes to the end of the queue; 3 retries, then "retry later" |
| connection closed | `resetConnection` and a new handshake and upgrade on that connection (the others are kept), then the message is sealed and sent **again**: the first copy may have arrived, so a duplicate is possible (owner's decision). At most 2 per message, then "retry later" |
| 401, to a send or the prekey fetch | "needs re-signup"; no further sends to the contact in the session |
| 404 | "gone" |
| bundle under a new identity key | accepted, sessions replaced, "delivered after identity change" |
| bundle does not parse or verify | "fault"; nothing stored |
| the send cannot be sealed; the stored state does not open | "fault" |
| more devices than one request holds | "retry later", reason "does not fit one request" |
| the database nodes did not acknowledge | "retry later" |
| any other status | "fault", with the status in the reason |

**The Signal server answers 401, not 404, for a sealed send or fetch to an account that does not
exist** (`OptionalAccess.verify`: a 404 "would provide a free exists check"). So a deleted
account is reported "needs re-signup", like a rotated profile key; "gone" can only come from a
server that answers 404. Never falls back to an unsealed send; never sends a receipt.

### Results

At the end the controller's JSON has `results`: for every id of every message of the notify,
`{"message": k, "id": "...", "result": R, "reason": "..."}` with R one of `delivered`,
`delivered after device refresh`, `delivered after identity change`, `retry later`,
`needs re-signup`, `gone`, `fault`. Both controllers compute the list from agreed values, exchange
the SHA-256 of its canonical text (`Recovery.canonical`) through the worker, and report it only
if the digests are equal (otherwise the session fails). `recovery` lists the public events in
order (refreshes, replaced connections, retries).

### Delivery guarantee, and where "confirmed" is recorded

At least once, with possible duplicates; never two ciphertexts under one message key.

* A contact's state is stored on the database nodes, acknowledged, before its message leaves.
  Every send, first or repeated, seals under the next keys, so repeating a send can duplicate a
  message and cannot reuse a key. A message stored for and not sent leaves a gap in the counter,
  which the recipient's ratchet skips.
* "Delivered" is reported only after a 2xx that both nodes saw.
* Across sessions: each computation node appends every settled result (delivered, needs
  re-signup, gone) to its own journal (`SIGNAL_NOTIFY_JOURNAL`, under the notify's id
  `SIGNAL_NOTIFY_ID`), as it is reached. A later session for the same notify reloads every contact
  from the database nodes, the two nodes exchange their journal entries for that notify, and an
  entry is skipped only when **both** have it; everything else is sent. The journal holds public
  values only (message number, id, result).
* Duplicates happen when: a connection closed after a request left and before its response;
  the session died after a 2xx and before both journals had the line; a node lost its journal
  (then everything it had settled is sent again); the application retries a notify under a new
  id. The blob version on the database nodes is not used for this: it counts sends attempted,
  not sends confirmed, and writing a confirmation there would double the writes per message.
* Not provided: exactly-once; ordering between a contact's messages when one of them backs off.

### Live checks

`check_signal_service_local.py MODE --runs 0 --recovery STAGE[,STAGE]`, each stage with its own
accounts and five database nodes. A stage runs a session that creates the contacts, a session in
which something goes wrong (usually between its two broadcasts; the controllers pause there on
request, `SIGNAL_LOCAL_PAUSE_AFTER`), and a plain session afterwards. Required of each session:
both controllers end normally with the same results, the results are the expected ones, the
recipients (libsignal clients) decrypt what was reported delivered, sealed.

| Stage | What goes wrong | Result for the affected contact | Also checked |
|---|---|---|---|
| `classify` | (unit check, `public_service_controller recovery-check`: the table, the back-off, the response parser on 429 with `Retry-After`, 503, and a 409 whose body is passed over) | 29 checks | |
| `devices` | a device is linked between the broadcasts; in the next session it is removed | 409, refresh: `delivered after device refresh` both times | the new device decrypts; after the removal one session is established; plain session after |
| `refresh-retry` | a third device is linked after the first refresh was stored and before the resend | second 409, refresh 2 (three sessions): `delivered after device refresh` | all three devices decrypt, and again in the next session |
| `identity` | the contact registers again (new identity key, same account id and access key) | 410, refresh under the new key: `delivered after identity change` | the new installation decrypts, and again in the next session |
| `unauthorized` | the contact's profile key (so its access key) changes | 401: `needs re-signup`, also in the next session | nothing more reaches it |
| `drop` | two circuits; the SOCKS test proxy closes one right after a send left on it | connection replaced, sent again: `delivered` | the other connection is kept; that text arrived twice (the expected duplicate) |
| `throttle` | test proxy: one send answered 429 with `Retry-After: 2`; one contact always 503; one always 404 | `delivered` on the retry; `retry later` after 3 retries; `gone` | the 503 and 404 contacts receive nothing; in the next session, direct, all three are delivered (the state stored for sends that never arrived is consistent) |
| `bundle-fault` | test proxy: a prekey response that is not a bundle; one that is well formed with random keys and signatures | `fault` for both, nothing stored | in the next session, direct, both are refreshed from the real bundles and delivered |
| `resume` | one node (worker and controller) is killed after the first broadcast | the session fails; both journals have two lines | a new session for the same notify skips those two, sends the rest; each text arrives exactly once |

In every faulted session the other contacts were delivered and neither controller ended early.

Results on 2026-11-11: all nine stages pass in semi-honest and in malicious mode (two or three
stages per harness run, each run under `scripts/guarded.py 24 900`). Session times with the
fault, semi-honest / malicious: link 36 s / 59 s, unlink 30 s / 51 s, second 409 with three
devices 179 s / 161 s (34 s of it the test's pauses; not broken down further),
identity change 45 s / 44 s (16 s of it the test's pause), dropped circuit 5 s / 13 s, the
429/503/404 session 19 s / 31 s (13 s of back-off), bad bundles 33 s / 59 s.

What these do not show: an account that was deleted (the local server answers 500 to the
deletion; by its source a sealed send to a missing account gets 401); 429, 5xx, 404 and bad
bundles as the server itself would produce them (they are injected on the plain side of a second
TLS terminator by `local_signal_server/scripts/fault_proxy.py`, which answers the chosen request
instead of forwarding it); a connection lost during a refresh; a lost connection that cannot be
re-established; more than three devices; a cheating party. A node whose controller dies or hangs
while its worker stays alive no longer leaves the other node waiting without limit: the workers
give up on each other at the next request after `TLS_WORKER_PEER_WAIT` seconds (default 180;
stage `hang`, 2026-11-11: party 1's controller stopped, party 0's session ended 20 s after its
next request with "the other party did not reach operation 39 within 20 s", and the next
session resumed from the journals). The `resume` stage still kills both.
