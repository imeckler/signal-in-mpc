# Optional four-round public fixture

`PublicTextExtendedFixture.h` preserves the original initialized states and first
two text inputs; rounds2/3 repeat their bodies with timestamps advanced by4ms.
The public-capacity domain stays48 UTF8 body bytes and80 ISO7816-padded Content
bytes. `text_input(slot,round)` supports slots0/1, rounds0..3. Existing fixture
headers/JSON and their historical reports are not regenerated.

Run the endpoint with `--rounds 4` (default remains2). It derives extra public
expectations in memory from RECEIVER-owned disposable chain seeds. It reproduces
both frozen inner wires exactly before extending them. This generator uses a
public HMAC/HKDF expectation model plus unchanged pinned SignalMessage/AES APIs;
it is not used by the MPC/client producer or claimed as a source proof. The
endpoint retains an actual libsignal receiving SessionRecord and verifies every
Signal MAC, inner plaintext Content/DataMessage/body/timestamp and sealed sender
certificate. A NEW extended recipient oracle additionally reports actual parsed
Signal counter, stored next receiver counter and stored PQ receive counter.
Only the rounds4 endpoint selects it; the old recipient binary/source remain.

Expected Signal counters are127,128,129,130 with stored next128..131; stored PQ
receive counters127..130. Request IDs remain consecutive relative to the first
legitimately server-observed private random base. Independent response pairs are
reversed, HTTP101/control frames remain fragmented, and9 pongs are checked for8
texts. Default2 still checks4 texts/5 pongs.

`check_extended_server.py` passes both default4 and optional8 ordinary localTLS/WS
texts through actual stateful recipients and compares all8 C++ input byte arrays
with server body/timestamp expectations. This is a public fixture-only test, not
native MPC, steady-state throughput, real account delivery or privacy proof.
For a native run include the NEW executable hash:
`.deps/signal-established-send-oracle-target/debug/signal-text-recipient-extended-oracle`.
