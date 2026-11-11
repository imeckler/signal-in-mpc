# Contacts with several devices

Status 2026-11-11: design, Lean kernels, proofs and a kernel check exist. Nothing is bound into the
worker or the controllers yet (the last section lists what to add). Nothing here was run against a
Signal server, local or real: the response format was read from the Signal-Server source.

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
  Today a response is revealed to the end of its frame; that rule has to change (section 7).
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

**Assumption to confirm on the local server:** the field order above (Jackson writes fields in
declaration order) and `"preKey":null` for a device without one-time prekeys. If either differs the
kernels reject the body; nothing leaks, but nothing works until the template is corrected
(`BundleResponse.header`, `item`, `widthsAt`).

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
    `ratchetPublic` with a fresh shared base scalar and ratchet scalar per device. `establish-kem` on
    `kyberPrekey`. `establish-session` with `deviceId`, `registrationId` and the key ids from step 5,
    `uuid`, `accessKey` from step 7, our certificate, our registration id and the connection's request
    id as public constants. It opens the **one status byte**; failure does not say why (bad JSON,
    bad signature, changed identity key, zero agreement and failed KEM look the same).
 9. Only if every device's status is 255: the contact's device list becomes the new one (section 4),
    is written to the database nodes, and the message is sent again. Otherwise the old state is kept
    and the contact is reported as failed. Retry the whole refresh at most twice (a device can be
    linked between the fetch and the send; a device with no prekeys is left out of the response and
    produces another 409).

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

Proposed blob plaintext: the devices' entries one after the other, each 319 bytes (kind 0), or 1935
(kind 1: no one-time prekey was used; kind 2: one was). The kinds are stored in the clear next to the
ciphertext (they are visible in every send's length anyway), and give the count and the offsets;
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

AND gates (measured by lowering, `bundle-kernels-report.json` and `establish-kernels-report.json`):

| Kernel | AND gates |
|---|---|
| `bundle-shape` | 45 per body byte: 118,440 for one device, 340,740 for three (once per response) |
| `bundle-device` | 100,308 – 104,098 |
| `establish-challenges` | 1,940,431 |
| `establish-verified`, `bundle-bind` | 771, 535 |
| `establish-session` | 918,035 (940,793 with a one-time prekey), at a 40-byte certificate |
| `establish-kem` | about 190,000,000 (never lowered; from the Lean definition) |
| `bundle-fetch-ctr` | 57,549 for a 164-byte frame (once per response) |

So about 3.0M AND gates plus the KEM. Field products: six ladders at 2,794 (seven with a one-time
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

Alternatives, cheapest change first:

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

## 7. What to add (the live binding is not part of this work)

**Registering the kernels** (each file: one import, one change to the lookup):

    import TlsMpc.BundleKernels
    ... HybridKernel.find rest <|> EstablishKernel.find rest <|> ReceiveKernel.find rest <|> BundleKernel.find rest

in `EmitFlatKernel.lean` and `EmitHybridKdf.lean`. Then `check_bundle_kernels.py` runs without `--emitter`
(but then without the `layout?` comparison, which needs a `layout MASK_FILE` command).

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

Not checked: `bundle-seal` (3.5M AND gates, over the limit for lowering here; it is `establish-seal`
with the text taken as input, and has its refinement theorem); the whole flow against a server; the
establishment kernels fed from `bundle-device` (the field names match by construction; the values
are the ones `check_establish_kernels.py` feeds them). Proof status: `TlsMpc/BundleProofs.lean`, header.
