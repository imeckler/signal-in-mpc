# Private request-ID state wrapper

Extends the selected-chain service with a private unsigned64 request counter.
The current ID is encoded; its next value joins the selected candidate state.
Overflow rejects without wrapping and preserves all old chain/request state.
Output is status1 || selected state80 || BE16 length2 || frame capacity.

The component suite reuses actual first output state AND request ID for the
second call across127→128; five rejection cases include request-ID exhaustion.
The three kernel endpoints establish model/compiler agreement. Actual uint64
request arithmetic and complete buffer/hash/packing semantic refinements are
still separate proof work. Functional evidence supplies native-generated DH
and reuses a synthetic ephemeral; native private generation is recorded
separately in signal_backend/VariableServiceWork/native-report.json.
