import TlsMpc.Node.Reveal
import TlsMpc.Node.Flows.Context
import TlsMpc.Node.Flows.TlsLegacy
import TlsMpc.Node.Flows.RandomLegacy
import TlsMpc.Node.Flows.UpgradeLegacy
import TlsMpc.Node.Flows.ContactsLegacy
import TlsMpc.Node.Flows.AccountLegacy
import TlsMpc.Node.Flows.SendLegacy
import TlsMpc.Node.Flows.ReceiveLegacy
import TlsMpc.Node.Flows.RefreshLegacy
import TlsMpc.Node.Flows.CeremonyLegacy

/-!
# The flow API (REORGANIZATION_PLAN.md stage S6)

**The final call sites of every worker operation the controller uses.** A session imports this
module and calls `Flow.<Group>.<function>`; it never names a worker operation. Behind each function
is, today, one worker operation (`TlsMpc/Node/Flows/*Legacy.lean`, through `Legacy.call`); from S9
on, function by function, a Lean script over the engine instruction set. The signatures stay.

## Design (reviewed against every worker call site of the controller before any moved)

At `7bd9aa9` the controller named the worker on 117 lines (the plan's "108 RPC lines" at
`d6c6cd9`, plus the connection views): 72 `.call`, 19 `Secret.inputOwn`, 9 `emptyReply`, 8
`onConnection`, and the TLS backends, transports and `connectVia`. Since S6: none
(`scripts/lint_node.py`, check `flow-calls`).

1. **One context, `Flow.Worker`** (`Flows/Context.lean`), the first argument of every flow. Today
   the worker pipe, the operations used (the final report's check), the selected connection, and
   this party's randomness source (`Channels.random`, unused until the scripts draw from it).
   S9's scripts need the engine interpreter's state and the randomness: they live in this value,
   so switching a flow to a script changes no caller. `w.on i` is the view of connection `i`
   (its operations select `i` first: op 90), as `TlsWorker.onConnection` was.
2. **Typed signatures** (plan S6, rule of thumb):
   - inputs: `ContactId`s and public values (frames built in the clear, masks, offsets, ids),
     `Secret` for own private inputs (key shares, credentials, OWN keys, TEST records);
   - outputs: `Opened r α` for everything opened (`r` a `RevealKind`, made only in `Reveal.lean`),
     `Secret` for what goes to this party only (the ceremony's shares), `TlsWorker.BufferHandle`
     for an engine value that stays there (a request or payload to seal and send; S12 makes it
     `Handle .boolean`), `Unit` otherwise. Contacts are named by id, not handle: the contact table
     is the implementation's (the worker's today, `Flows/ContactsTable.lean` after S9).
   - Parsing and checking of a reply happens in the flow (lengths, status bytes, envelope lists),
     with the controller's error texts, so the caller sees typed results (`Polled`,
     `FirstMessage`, `Received`, `Option` for "refused").
3. **Names.** The API is the namespace `TlsMpc.Node.Flow` (singular). `TlsMpc.Node.Flows.*` is
   taken by S9's scripts (`Flows.Random.joint` is a script today), and the two must be importable
   together. Plan names that are Lean keywords are renamed: `open` → `load` / `openFirst`,
   `public` → `anonymous`.
4. **The TLS backends.** `TlsClient` and `TlsApplication` take a backend record of public
   bytes; `Flow.Tls.legacyBackend` / `legacyApplicationBackend` implement them (ops 1-8, 12-16),
   passing each opening through `Reveal.*`. The session calls `Flow.Tls.handshake` and
   `Flow.Tls.application`; `TlsApplication.send/receive/keyUpdate/abort` stay as they are.
5. **Not flows:** operation 39 (the peer exchange) is a channel, `Channels.exchange` (plan 6.2),
   given `w.link`; the worker spawn stays in the controller (`TlsWorkerProcess`, S8/S9).
6. **Behaviour.** Same operations, same order, same payloads, same checks and error texts as
   before. One difference, on a malformed worker reply only: the non-recovery send paths
   (`sendMessage`, `sendDevices`) now check the envelope lengths of an op 41/61 reply before the
   contact's state is stored, where they checked them after (the session fails either way).

## The functions (plan section 6.2)

| Group | Function | Ops | Returns |
|---|---|---|---|
| `Server` | `connect w host port proxy` | 9 | `Unit` |
| | `poll w` | 17 | `Polled` |
| | `reset w` | 91 | `Unit` |
| | `awaitRecord w kept interval polls` | 17 | `Bool` |
| `Tls` | `handshake w config` | 1-11 | `TlsClient.Session Unit` (`handshakeShare`, `handshakeRecord`, `finishedAccepted`, `clientFinished`) |
| | `application w handshake kept` | 12-17 | `TlsApplication.Session BufferHandle` (`recordEvent`, `sealedRecord`) |
| | `publicBuffer w bytes` | 30 | `BufferHandle` |
| | `recordLength w h`, `revealRange w h offset count` | 43 | `Opened .serverBytes (Nat × Bytes)` |
| | `abortWorker w` | 8 | `Unit` |
| `Random` | `joint w` | 33 | `Opened .jointRandom Bytes` |
| `Upgrade` | `anonymous w` | 45 | `Opened .upgradeNonce (Bytes × Bytes)` |
| | `authenticated w state` | 32 | `BufferHandle × Nat × Opened .upgradeAccept Bytes` |
| `Contacts` | `key w id share` | 36 | `Unit` |
| | `load w id stored`, `loadDevices w id kinds body` | 37, 63 | `Opened .blobAccepted Bool` |
| | `seal w id nonce` | 38 | `Opened .sealedBlob Bytes` |
| | `evict w id` | 40 | `Unit` |
| | `assign w provisional id` | 52 | `Opened .assignStatus Bool` |
| | `admitTest w id record` (TEST) | 44 | `Unit` |
| `Curve` | `prepareContacts w ids` | 66 | `Opened .prepareStatus Bytes` |
| `Account` | `key w share`, `credentials w share` | 53, 47 | `Unit` |
| | `load w stored` | 55 | `Unit` |
| | `seal w nonce` | 54 | `Opened .sealedBlob Bytes` |
| | `admitTest w identity certificate` (TEST) | 46 | `Unit` |
| `Send` | `seal w id built`, `sealDevices w id address built devices` | 41, 61 | `Opened .sealedEnvelope (Option (Nat × List Bytes))` |
| | `request w id offsets mask frame`, `requestDevices …` | 42, 62 | `BufferHandle` |
| `Receive` | `take w h offset count`, `drop w` | 48, 49 | `Unit` |
| | `openFirst w identity now key certificate signer` | 50 | `FirstMessage` |
| | `session w id address signed oneTime secret` | 51 | `Received` |
| `Refresh` | `fetch …` | 56 | `BufferHandle` |
| | `take …`, `drop w`, `scratchCommit w id` | 57, 58, 65 | `Unit` |
| | `shape w` | 59 | `Option (Opened .bundleShape (List Bool))` |
| | `establish …` | 60 | `Opened .deviceStatus Bytes` |
| | `scratchSeal w id nonce` | 64 | `Opened .sealedBlob Bytes` |
| `Ceremony` | `secrets w` | 80 | `Secret Bytes` |
| | `register …` | 81 | `BufferHandle` |
| `Fixture` | `catalogue w` (TEST fixture session; removed in S7) | 19 | `Nat` |

No I/O primitive; no emitter imports this module.
-/
