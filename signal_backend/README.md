# Private established-chain send producer

`EstablishedSendStore<tls_mpc_worker::Bits>` binds an already selected Signal/SPQR
sending chain and identities/addresses to a same-worker producer. Every key,
counter, identity, plaintext and output remains an owned share. The host branches
only on public sizes, tickets and execution errors.

A send calls the exact shape-pinned `Worker::signal` function. The circuit selects
next Signal and SPQR keys/counters on acceptance, preserves old state on rejection,
and zeros rejected wire. The store commits those selected shares before returning
wire. It rejects a second outstanding send and stale transport tickets. A runtime
or handoff exception closes the chain, preventing retries with uncertain state.
This is an in-memory transaction, not durable storage or crash recovery.

`programs/signal_export.mpc` exports shared-register functions with no opens.
`prepare.py` compiles a profile in an isolated build tree and creates an exact
function/schedule/bytecode manifest. A native worker must collectively agree that
closure before registration. The compiler/adapter/runtime remain trusted.

`PrivateGrpcRequest.h` frames a shared protobuf request into gRPC DATA and HTTP/2
HEADERS. Header values, credentials and content stay shared; HPACK literals are
never indexed, without Huffman coding. Public dimensions and stream ID determine
the framing. `produce_private_request` composes send, an actual request serializer,
framing and a same-worker opaque TLS retainer, closing the store on any failure.

Validation:

```sh
python3 signal_backend/check.py
python3 signal_backend/request_check.py
# Compile profiles too, without starting native parties:
python3 signal_backend/check.py --compile-backend
# After compiling the minimal profile:
python3 signal_backend/native_check.py
```

`report.json` records fresh Boolean circuit evaluation and C++ store transition
checks. Its Rust oracle invokes unchanged pinned libsignal `SignalMessage::new`,
address serialization and the actual AES-CBC encrypt/decrypt wrappers. The test
KDF keys come from independent Python HMAC; this is not an actual private
`ChainKey` method test or full session interoperability. Two arbitrary-version
fixtures construct matching wire but the actual parser rejects their versions;
these errors are recorded rather than counted as successful message roundtrips.
`request-report.json` checks framing with the unchanged vendored h2 server parser,
including HPACK integer-length boundaries. All test inputs are public synthetic
fixtures. Native fixture evidence, when available, is separate in `native-report.json`.

The caller still needs authenticated established-session initialization, complete
DH/SPQR epoch and chunk state transitions, actual service request protobuf
serialization, recipient-device fanout policy, HTTP/2 settings/flow control/
responses, durable storage and runtime retirement before usable delivery. The
TLS application gate is unchanged. No production, refresh or throughput claim is
made. Full actual `to_edwards` translation remains blocked as recorded in
`SignalReference/XEdDsaToEdwardsWork/`.
