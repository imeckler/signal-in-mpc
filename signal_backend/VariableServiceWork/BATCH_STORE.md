# Staged private store batching

`produce_batch_with_checkpoint` accepts1..64 distinct store owners and private
payload/timestamp/request-ID shares. The connection allocator reserves unique IDs
before this call; the helper neither compares nor opens their secret values.
Shapes/lane order/store identities are public. Mixed public shapes are allowed;
the evaluate adapter must choose supported pinned profiles or reject collectively.

1. `stage` all stores: fence, ticket, exact overlaid private call input. No crypto
   evaluation or output release occurs. One staged/pending operation per store.
2. Invoke ONE group Reserve callback on public shapes and const staged tokens.
   A durable adapter freezes the whole account/intent and certifies one account
   slot here, rather than B serial journal/certificate rounds.
3. Move each input once into ONE evaluate callback (no concurrent Machine calls).
   It returns quarantined private outputs in the same public lane order.
4. `preview` all results, validating dimensions and building selected next-state,
   typed outbox and expected-ID candidates without installing any state.
5. Invoke ONE group Commit callback with all const candidates. A durable adapter
   must atomically persist/certify the coherent account and immutable outboxes.
6. Install EVERY selected state, then return the output vector. Any failure,
   including a partial install, closes ALL admitted stores before any vector can
   escape. A runtime/account owner must retire traces after retaining the group;
   one epoch boundary per batch is possible. This helper does not do retirement.

Staged/candidate tokens are move-only, bound to a weak owner lease and ticket.
Destroyed/recreated owners cannot accept old tokens. Taking input twice, replaying
candidate installation and early response completion reject. Abandoning a token
leaves its owner blocked; it cannot silently send again. Only authenticated
correlated response policy may complete a returned ticket. Each conversation can
complete and stage again independently while others remain pending.

Existing single-send methods use the same phases; default calls retain explicit
no-checkpoint hooks and burn-on-restart persistence. No durable recovery or normal
provider admission is established merely by this API. The concrete archive/
certificate/native record/import/retirement binding remains required. In
particular a state COMMIT is independent of remote delivery acknowledgement;
older pending outboxes must survive later unrelated account batch commits.

156 ASAN/UBSAN PUBLIC mock checks cover B1/2/4/8, reserve/eval/result-count/result-
width/commit/partial-install failures, ordering and all-owner closure, duplicate
conversation rejection, stale/moved/destroyed tokens, abandoned stages and
independent response completion.32 default mock profiles and12 existing checkpoint
checks also pass. There is no cryptographic/native MPC or throughput claim here.
