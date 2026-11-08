# Bounded private text notification candidate

The text-only input is 59 bytes: upstream validity8, private lengthBE16, text
capacity48, timestampBE8. `PrivateTextNotification` validates strict UTF8 and
bounds, constructs Content(field1)/DataMessage(body1,timestamp7), appends0x80 and
zeros to the public80-byte ISO7816 bucket used by relay notify.rs. Invalid inputs
produce90 zero bytes. Successful output is validity255, kind0, padded plaintext80,
and the **same** timestampBE8. The normal embedding must split this output into
its computed validity, kind/payload and timestamp; it must never substitute a
caller-supplied success flag or an independently supplied timestamp.

`NativeTextNotification.h` evaluates the pinned472→720-bit artifact. Its manifest
is `.deps/private-text-notification-native/text.manifest`. The downstream private
service profile is260-80-0-0, with611 input bytes,1290-byte public WS capacity and
1373 output bytes. The complete native output preserves validity, private BE16
length and fixed-capacity wire; TLS must retain and gate it as usual.

`check_recipient.py` evaluates the actual numeric text and complete service
artifacts on public disposable fixtures. It uses actual pinned libsignal SSv1
receive/certificate validation and **message_decrypt_signal**, with a retained
receiving SessionRecord including SPQR state. The recipient derives message keys;
no final cipher/MAC keys are supplied. Both conversations have different identity,
ratchet, Signal-chain and PQ-chain fixture states, and each crosses127→128.
Tampering and replay are rejected. The selected established receiving state is
synthetic; fresh-session establishment/full SPQR epoch transitions remain open.

The oracle compiles actual pinned storage.proto, service.proto and SPQR state
schemas. The minimal DataMessage derive copies relay messaging.rs fields1,6,7;
libsignal service.proto itself deliberately treats DataMessage as opaque bytes.
Valid UTF8 agrees with relay String::from_utf8_lossy; malformed UTF8 is rejected
rather than replaced. This is not proof of full application schema or deployed
version compatibility. Existing source/primitive refinement gaps remain explicit.

`prepare_fixtures.py` splits successful public numeric evidence into a client-only
`PublicTextFixture.h` and receiver-only `server-fixtures.json`. Only the client
fixture contains sender initialization. The ordinary local TLS1.3/H1/WS server
retains actual recipient SessionRecords, verifies recovered body and timestamp,
fragments replies around pings, and reverses each independent response pair.
`check_server.py` tests four nonempty texts with standard local TLS and actual
recipient APIs; it does not execute native MPC. The next shared-runtime test must
use this profile/builder via the normal embedding, not the old empty fixture.

Native runtime/conversion and allocation/cleanup remain external trusted/tested
boundaries. Authenticated shared-state bootstrap, recoverable durable snapshots,
full DH/SPQR session transitions and complete source-refinement proofs remain
required. Immutable send tombstones only prevent restart; they are not recovery.
No live service, account or real recipient side effect is performed.
