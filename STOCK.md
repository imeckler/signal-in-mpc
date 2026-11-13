# X1: a stock of preprocessing, encrypted on disk, used exactly once

PRODUCT_TODO.md section 11a (the design); REORGANIZATION_PLAN.md section 9 "X1" and T14 in 8.1
(where it fits). Status 2026-11-12: the model, its proofs and a standalone store are built.
Nothing calls the store yet.

**Why.** A broadcast of about 14,000 recipients in about ten minutes is about 23 messages a
second. Live preprocessing cannot keep up with that. So in quiet hours the two nodes make the
message-independent part of each send ahead of time: in semi-honest mode the garbled circuit
(about 85–100 MB a message), in malicious mode the authenticated triples. Each node keeps its
half on disk. A send then needs only a small exchange. The hazard is **reuse**: one item given
to an engine twice breaks security. Everything here exists to make reuse impossible, including
across crashes, restarts, reboots and restored disks.

## What is built

### Lean (`TlsMpc/Node/Stock/`)

These files are pure: no I/O and no escape hatch. No emitter imports them, and
`scripts/lint_node.py` reports 0 findings. `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound`.

- **`Journal.lean`: the consumed journal and how it behaves in a crash.**
  - **Format.** 16-byte records. Each holds a watermark `w`, meaning "every index ≤ w is
    consumed", followed by an 8-byte check.
  - **Crash model.** A crash leaves on disk some prefix of the written bytes, at least as long
    as the synced part. Unsynced bytes can be lost from the end at any byte offset (a torn
    record). Nothing is reordered and nothing is invented.
  - **Reading.** Complete records are read. A torn tail is dropped. A complete record with a
    bad check means corruption, and the stock is refused.
  - **Theorems.**
    - `parse_prefix`: a file cut at any byte reads as exactly the records it fully contains.
    - The abstract journal `Journal`, with `Journal.crash`:
      - `crash_durable`: synced entries are never lost.
      - `crash_prefix`: entries are not reordered or invented.
      - `crash_bytes`: ties the abstract crash to the bytes.
      - `crash_append`: at most the entry in flight is lost.
      - `durableNext_le_crash` and `crash_next_le`: a crash neither loses synced progress nor
        skips forward.
  - **Boot id.** The header's `Hdr` records the boot a stock was made in.
- **`Format.lean`: the bytes.**
  - Shape id: circuit name, size class, client profile.
  - Header: magic, version, shape, manifest hash, boot id, stock id, item length.
  - Item record: index, length, agreed hash, sealed bytes.
  - The item's associated data (AAD), the journal check, the key chain, and the agreement
    claim.
  - Round trips: `parseHeader_encHeader`, `item_enc`, `decClaim_encClaim`.
  - `itemAad_inj`: the AAD fixes the boot, the stock, the manifest, the shape and the item.
- **`Use.lean`: the use rule and T14.** It models one node, for one shape, with three kinds of
  memory:
  - **disk:** the header, the item count and the journal;
  - **boot memory:** the boot id and the stock key (use cursor and producer cursor), lost at
    reboot;
  - **process memory:** the take in progress, lost at a crash.

  A take is four steps: `start j` (append j), `sync` (fsync), `decrypt` (derive the key, move
  the chain past j and erase it), and `hand` (give the item to the engine). The adversary
  controls every event:
  - the index of every round (any `j` ≥ the node's next index, which covers a lying peer);
  - crashes at any step, keeping any number of unsynced bytes;
  - reboots;
  - restores of any earlier disk;
  - rollbacks of boot memory within a boot.

### Theorems (the adversary is the one just described)

| Name | Statement |
|---|---|
| `T14_chain` | With the key chain, in every trace without a boot-memory rollback, no item reaches the engine twice. |
| `T14_journal` | With the journal, in every trace without a disk restore, no item reaches the engine twice. |
| **`T14`** | In production (both barriers), in every trace that does not roll back *both* this node's disk and its boot memory, no item reaches the engine twice. |
| `T14_boot` | In every trace, an item is handed only during the boot in which its stock was made, and a stock is made in exactly one boot. A stock left from before a reboot, or brought back by a restore, is never used. |
| `start_refused_other_boot` | A header with another boot id is refused at `start`. |
| `no_barrier_reuse`, `journal_alone_disk_rollback`, `chain_alone_boot_rollback`, `full_rollback_reuse` | Concrete traces showing that each assumption is needed. Proved with `decide` (not `native_decide`). |
| `production_refuses_after_crash`, `production_disk_rollback`, `production_boot_rollback` | The same traces, refused in production. |
| `agreeIndex_comm`, `agreeIndex_never_back`, `honest_not_behind` | The pair rule. Both honest nodes compute the same index; it is never below this node's next index, whatever the peer claims. |
| `agreeIndex_max_succ` | When the two journals differ, both nodes use max + 1. |
| `agreeIndex_none_left`, `agreeIndex_none_right` | No stock on either side means live preprocessing, never a refusal. |
| `waste_bound` | Each interruption, on either node (a crash, or a lost message), wastes at most one item of each node: next − used ≤ interruptions. A reboot discards that node's stock by design. A lying peer can waste the whole stock, which costs availability only. |
| `stockUse_enc`, `checkStockUse_spec`, `stockUses_nodup` | The specified engine instruction: its encoding, and that within one session no (shape, index) is accepted twice. |

**Which side's reuse is the hazard.** Both sides have one, and each falls on the node that
reuses its *own* item:
- A garbler that evaluates one garbled circuit twice gives the evaluator two label sets for the
  same circuit.
- An evaluator that reuses its precomputed OT correlation lets the garbler learn the XOR of its
  two inputs.
- A reused authenticated triple opens x − x′.

So T14 is stated per node and holds whatever the peer does.

### Rust (`node_stock/`, a standalone crate; not part of `node_worker`)

**Files.** Each shape has a directory `<root>/<shape hash>/` holding three files:
- `header`: written once at create, through a rename;
- `items`: fixed-size records; item i is at offset i × record length;
- `journal`.

**Keys.** All keys live in `BootMemory`, which is held only in memory:
- the boot id: random, and lost with the value;
- per shape: the stock id, the use chain and use cursor, and the producer chain and producer
  cursor.

**API**, shaped for the future engine calls:
- `create(shape, item_len, manifest)`;
- `put(shape, index, bytes, agreed_hash)`: in index order. The producer chain gives the item's
  key and moves past it *before* the record is written, so no key ever encrypts two
  plaintexts, even if the write is cut;
- `take(shape, index)` and `take_expect(…, expected_hash)`. The order is:
  1. checks;
  2. journal append and fsync;
  3. derive the key, move the use chain past the index, zeroize the old value;
  4. decrypt with the AAD and verify, then return the bytes (zeroized on drop).

  `take_expect` refuses a different agreed hash *before* anything is consumed. After
  decryption it checks the hash again, this time authenticated;
- `next_index(shape)`: the claim;
- `skip_to(shape, index)`: forward only;
- `agreed_hash(shape, index)`;
- `agree::agree_index`.

**Open and refuse.** A stock is usable only if all of these hold:
- its header carries the current boot id;
- boot memory holds the key of its stock id;
- the journal parses.

Otherwise every call returns `Unusable`. Opening a journal truncates a torn tail and syncs.

**Crypto.** The production cipher is ChaCha20-Poly1305 from the vendored
`chacha20poly1305 = 0.11.0`. It uses a zero nonce, which is safe because each key encrypts one
item once. `NullCipher` is for tests only: it does no encryption and keeps an HMAC-SHA256 tag.
Other crates: `sha2 0.11.0`, `hmac 0.13.0` and `zeroize 1.9.0`. All are vendored in
`.deps/libsignal-vendor` and build offline. **No crate needs vendoring.**

**Tests:** 23, all passing.
- **Chain.** Keys match the reference. After taking i, the state holds neither c_j nor k_j for
  any j ≤ i, refuses them, and derives only keys above i.
- **Journal.** Every prefix parses as Lean says. Corruption, a foreign journal and zero-filled
  records are refused.
- **Truncation at every byte offset of a journal,** including below the synced length, which a
  crash never does. In every case no taken index can be taken again: the journal refuses it at
  or above the synced length, and the erased key refuses it below.
- **A take cut after each of its three steps,** followed by a crash that keeps 0 to 16 unsynced
  bytes.
- **Boot-id mismatch,** including a header rewritten to the new boot id.
- **Same-boot disk restore.**
- **Wrong item hash:** the early refusal, and a tampered stored hash. Also a tampered
  ciphertext, and a record copied to another index.
- **Put rules.**
- **Cipher:** both ciphers on every tampered byte, plus the RFC 8439 test vector.
- **Lean vectors** (`src/vectors.rs`). These are the format lines byte for byte, plus 312
  schedules generated *from* the Lean model (`node_stock/tests/lean/StockVectors.lean`). Each
  schedule checks the outcome and the next index after every one of 8,775 operations, and
  checks that the same items were handed. The schedules cover:
  - takes behind, at, ahead of and far ahead of the next index;
  - takes cut at every step, followed by a crash keeping 0 to 20 bytes;
  - skips, crashes and reboots;
  - new stocks and refills;
  - restores of disk and boot-memory snapshots.

  The six schedules that restore both disk and boot memory reuse an item in Lean and in Rust
  alike.

**Commands** (repository root, light jobs):
- `python3 .deps/lowering-scratch/x1_check.py TlsMpc/Node/Stock/Use.lean 5 olean`: the Lean
  check, one file at a time, in the order Journal, Format, Use;
- `python3 .deps/lowering-scratch/x1_vectors.py`: regenerates `node_stock/tests/stock_vectors.txt`;
- `python3 .deps/lowering-scratch/x1_cargo.py test test --offline`: the Rust tests.

## Specified, not built

- **The engine's side** (the C ABI `export_preprocessing` / `import_preprocessing`). emp-ag2pc's
  function-independent part would be split out, as `TriplePool::mint` already does for
  triples. In semi-honest mode this means garbling ahead and storing the tables and labels.
  This is the real work 11a needs, and it touches the C++ engines.
- **The `stockUse` instruction.** The spec is the SPECIFICATION section of
  `TlsMpc/Node/Stock/Use.lean`, which also gives standalone definitions:
  - **Opcode:** the next free one, provisionally 22.
  - **Encoding:** shape id, u64 index and a 32-byte agreed hash. All of it is public and goes
    into the skeleton.
  - **Claim exchange:** in the batch before, each node sends `encClaim` of its next index.
  - **check:** `stockUse` arms an item when the index is ≥ the session floor (never back
    within a session). The next `run` of that circuit consumes the item (copies = 1). A batch
    that ends with an item still armed is refused.
  - **Shell:** after the agreement and checkBatch, it calls `take_expect` and then the engine's
    import. If the store refuses, the batch is rejected and the message goes live.

  `Engine.lean` is untouched; the owner adds the instruction after the pending branch is merged.
- **`Channels.stockJournal` (`append`, `sync`, `read`):** the Lean-side binding of the same
  journal, for when the use rule moves into the controller.
- **The boot-memory holder.** `BootMemory` is an in-process value. For a stock to survive a
  worker crash, it needs a holder that outlives the worker, such as a small key-holder process
  or a kernel keyring entry, and that holder must not swap. If the worker holds it itself, a
  worker crash makes the stock unusable, which is safe but wasteful.
- **Refill policy.** A target level per shape, refills when idle and at night, a rate limit,
  and a new stock after every reboot (both nodes; the agreed hash catches mismatched halves).
- **Malicious mode.** Not built: the stock's authenticated triples need each node's MAC key to
  live as long as the stock (the persistent-key question below).
- **The deployment test** that pulls the plug mid-spike.

## The security argument

1. **Nothing in the stock depends on contacts or messages.** Items are made before any message
   exists, from the lowered circuits: the manifest hash is in the header and in every item's
   AAD. What is on disk reveals at most which circuits and how many items. The indices
   exchanged in the agreement are public counters.
2. **Reuse is the hazard, and four independent barriers stop it.**
   - **The journal.** Before an item is used, its index is appended and synced. On restart the
     next index is one past the largest synced entry. A crash loses only unsynced bytes, so it
     can lose at most the entry in flight, and that item was never handed (`T14_journal`).
   - **The key chain.** Every item has its own key, derived from a chain that only moves
     forward. Taking item i keeps only c_{i+1} and zeroizes the rest. A disk restored from a
     snapshot of the same boot brings back an old journal, but not the erased keys
     (`T14_chain`). SSDs do not reliably delete, so this is also what makes used items
     unrecoverable from the disk: their ciphertexts may remain, but their keys exist nowhere.
   - **The boot id.** It is random, held only in memory, and written into every header and
     every AAD. After a reboot, or on a disk restored from another boot, the stock is unusable
     (`T14_boot`). The key for the old stock is gone with boot memory anyway.
   - **The session check.** The specified `check` rule refuses a non-increasing index within a
     session (`stockUses_nodup`).
3. **The pair.** Each node claims its next index and both use the larger one. A node never goes
   back, so a lying peer can only push the honest node forward: it wastes items and the
   messages go live. The skeleton carries the index and the agreed hash, so a mismatch is
   caught before any engine call.
4. **What a single node cannot detect** (`full_rollback_reuse`): its disk *and* its boot memory
   restored together, for example from a VM snapshot with memory. Against that the honest
   peer's claim helps. The peer's next index is past every index it took, so after the
   rollback the agreed index jumps past them. This misses only an index that the rolled-back
   node used and the peer did not journal. That is not proved here and is an open question
   below.

## Open questions for the owner

1. **Stock size per shape.** One spike of about 14,000 messages is about 1.2–1.4 TB a side in
   semi-honest mode and about 13 TB in malicious mode (11a). How often do large broadcasts
   happen, are they announced, and is a sustained 23 messages a second needed or only the
   spike? Both answers set the target level and the disks.
2. **Malicious-mode key lifetime.** Authenticated triples are only valid under the MAC key
   (Δ) they were made with, so that key must live as long as the stock: hours to days, not one
   session. This is the persistent-key question of `SEALED_SENDER_AGREEMENT.md`. Is a MAC key
   in boot memory for the stock's lifetime acceptable? If a reboot always discards the stock,
   then the key need never touch disk.
3. **Where boot memory lives** (holder process or kernel keyring), and whether to mlock it and
   disable swap and core dumps on the nodes.
4. **Full-snapshot rollback** (disk and memory together, as with VM checkpoints): should the
   deployment forbid it, or should the protocol add the peer-based check described above (both
   nodes journal the agreed index before either engine runs)?
5. **A lying peer** can exhaust the stock instantly by claiming a huge index. That is only an
   availability cost, but should a claim more than N beyond our own index be treated as a
   fault and reported?

## Measure first (11a "Measure first"; not run)

Each measurement can be produced from what exists, as follows:

1. **How much of a semi-honest send is message-independent, in bytes.**
   - **Bytes:** about 32 bytes of garbled table per AND gate (half-gates), times the AND gates
     per message. That count, 2.84M, comes from
     `local_signal_server/check_signal_service_local.py semi-honest --runs 0 --sustained 160 --restart-after 80`
     (PERFORMANCE.md "The long-lived send session"), which also reports the traffic between
     the workers per message (117 MB one way over whole sessions).
   - **Time:** today the garbling and the evaluation are one category ("Boolean circuits") in
     `scripts/session_profile.py RUN_DIR`. Splitting garbling from evaluation needs a timer in
     the engine around each, which is not there today.
2. **The evaluator's time per message per core.** `scripts/session_profile.py` reads party 0's
   worker log. The evaluator is party 1, so read party 1's log of the same run (the same
   `boolean circuit:` lines). A harness run gives these logs:
   `check_signal_service_local.py semi-honest --runs 0 --db --broadcasts 6`.
3. **Whether 23 messages a second is reachable on one 16-core pair.**
   - Measure (2) and divide.
   - The other limits are measured by the `--sustained` run: database writes at 0.4 s a
     message, and contact preparation at 0.28 s a contact (PERFORMANCE.md).
   - Use `--link-delay-ms 1` for the 2 ms link between the nodes.
4. **The same split for malicious mode.**
   - `TLS_WORKER_TRIPLE_STOCK=0 TLS_WORKER_FIELD_STOCK=0` already separates the
     circuit-independent AND triples (74% of the Boolean time: 0.57 of 0.77 s per million AND,
     PERFORMANCE.md) from the circuit work.
   - Run `check_signal_service_local.py malicious --runs 0 --db --broadcasts 6` with and
     without those variables, then `scripts/session_profile.py`.
   - Traffic per message one way is 0.96 GB (`--sustained`).
5. **Store throughput** (not in 11a, but cheap). `node_stock`'s tests already exercise
   `put`/`take` with fsync. A timing run with 100 MB items on the target disks would show
   whether one fsync per take (and one per put) matters at 23 a second. It probably does not:
   one 16-byte journal append and one fsync per message.

## Theorems `TlsMpc/Security.lean` should restate (section 5, "state and ordering")

Add `import TlsMpc.Node.Stock.Use`, which also imports Journal and Format. Do not add it to the
`TlsMpc` root module: some emitters import that root (`lint_node.py --report`). No lakefile
change is needed, because the TlsMpcSecurity library builds whatever Security.lean imports.

- `T14`: the main statement.
- `T14_chain`, `T14_journal`: each barrier with its assumption.
- `T14_boot`: the boot id.
- `full_rollback_reuse`: the limit, stated.
- `parse_prefix`, `Journal.crash_bytes`, `Journal.crash_durable`: the journal model.
- `agreeIndex_never_back`, `agreeIndex_max_succ`, `waste_bound`: the pair.
- `itemAad_inj`, `parseHeader_encHeader`: the format.
- `stockUses_nodup`: the specified check rule.
