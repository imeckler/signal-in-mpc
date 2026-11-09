# All-outcome actual message payload validity

`message_byte_valid` factors the actual message-String payload validity guard with UTF transition/live/completion, budget and safe child-boundary conditions. `UtfRunFacts` proves executable grammar dead-state absorption and run concatenation; accepted complete strings have no dead transition. These facts have no axioms.

`message_payload_valid` inducts through the actual Core byte transitions, private child/public budget counters, field kind, mode, opaque skip, and exact grammar phase. Complete accepted payloads preserve valid255, including a payload ending at the child end. No per-byte UTF correctness premise is assumed.

`message_payload_agreement` joins successful and rejecting branches: actual final valid equals the executable UTF8 acceptance mask for every byte list. The entry relation is explicit: message kind, opaque mode, exact copied-payload skip, ready validator, valid/seen255, unfinished, inner response/depth0, and private child/public budget counters bounded4096 and covering the payload. Empty payload satisfies the statement as an identity; the real zero-length header bypasses opaque mode and remains for full-field composition.

The accepted-input theorem alone is not the observation: the all-outcome equality is checked separately. Deriving the entry state from actual String key/length, cache/presence/suffix and source field result, repeated header/HTTP validation, full owned scan/private EOF/correlation/compiler composition remain open. Actual std optimized UTF8 body and static diagnostic-push/content-allocation boundaries remain unchanged. No runtime/generated computational changes.
