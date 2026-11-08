# Private sender checkpoint boundary

`VariableSendStore::produce_with_checkpoint` is an internal embedding-only path.
The existing private call input (retained keys/recipient plus overlaid payload,
timestamp and globally reserved request ID) reaches `reserve` before evaluation.
After evaluation, `commit` receives the exact selected next sender state, typed
private outbox/status/length/capacity and that request ID. The store installs the
next state and returns a payload only after commit succeeds. Failure at any hook
poisons/closes the store; no uncertain result can roll back and send again.

The existing produce methods delegate with explicit no-checkpoint hooks and keep
the tombstone fence behavior. They do not become recoverable merely because this
new method exists. Neither hooks nor a successful host call prove durable atomic
commit: the recovery adapter must compose the coherent full canonical record,
other conversations/global allocator/credentials, frozen intent and immutable
outbox; AEAD/archive/fsync, actual four-member Reserve/Commit certificates, and
all-party coordination must finish at the correct boundaries. It must close the
whole account on failure, not leave a mutated peer owner active. No normal
provider calls the new path yet, no RPC imports are added, and restart admission
remains closed. This is transaction wiring evidence, not completed persistence.

12 ASAN/UBSAN public-mock checks exercise actual overlaid-input binding, exact
nextstate/outbox/request-ID hook dimensions, success and reserve/eval/commit
failure order, no output after failure and no second send after failure/pending.
All32 existing default mock shape profiles also pass through the delegating path.
No secret reconstruction, native cryptography or filesystem recovery is tested.
