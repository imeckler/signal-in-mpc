# Deploying the two-party Signal client

Two computation nodes, five database nodes and a monitoring page, deployed by
`python3 deploy/deploy.py` from two small files: `deployment.toml` (shared by everyone, public)
and `operator.toml` (each operator's own, private). Several parts of the product are not ready
for production (Reference, 0.2) and the cloud paths of the tool have never run against a provider
(Status, below).

**Every operator needs:** Docker, Python 3.11+, ssh; this repository at the agreed commit,
fetched by yourself from the repository (never a copy from another operator); an account at
the provider(s) you use, or machines you already have (Ubuntu 22.04+ / Debian 12+).

## Deploying with several operators (the normal case)

| Step | Who | Types | Sends |
|---|---|---|---|
| 1 | coordinator | `python3 deploy/deploy.py init`; edits `deploy/deployment.toml`: name, `security`, `worker_logic`, who operates each node, the application server's public keys | `deployment.toml` to everyone |
| 2 | builder | `python3 deploy/deploy.py build --out images/` (fills the image, circuit and word-dir digests into `deployment.toml`) | `deployment.toml` again, and `images/` |
| 3 | every operator | edits `deploy/operator.toml`: their name, each of their nodes' `provider`/`region`/`size`, credentials as `env:VARIABLE` | nothing: it is private |
| 4 | every operator | `python3 deploy/deploy.py plan`, then `python3 deploy/deploy.py join` | the `*.bundle.json` files `join` prints, to every other operator |
| 5 | every operator | puts every bundle in `bundles/`; `python3 deploy/deploy.py collect bundles/` | nothing |
| 6 | all together | read the printed fingerprint (`12345-67890-...`) aloud on a call or in person: it must be identical for everyone | nothing |
| 7 | every operator | `python3 deploy/deploy.py start bundles/ --fingerprint 12345-67890-...` | nothing |
| 8 | the two computation operators | the account step (below) | |

`join` makes the machines, installs Docker, WireGuard, the firewall, the images, the circuits,
and makes every private key **on the node that uses it**; only public keys leave. `start` builds
the tunnel mesh and the per-sender firewall rules from the bundles, starts the services, the
monitoring page and the certificate timer, and runs pre-flight and the two-node comparison
(it fails loudly on a difference). The database nodes wait until every database operator has
run `start` and then start together (Reference 10, change 19); the page says "waiting" until
then. Afterwards: `status` (each node in one line), `monitor` (opens
your page through ssh), `logs` (redacted), `upgrade`, `destroy` (asks for the name typed back;
keeps data disks unless `--delete-data`). `python3 deploy/deploy.py` alone says what is next.

**Why compare the fingerprint.** Bundles travel by whatever channel you like; whoever relays
them could swap a key for their own. The fingerprint is a hash of `deployment.toml` and every
bundle; comparing it by voice, video or in person is the only step that authenticates the keys
(no PKI, no accounts). It also covers what each node actually runs (image, circuit-manifest and
word-dir digests, field-program pins, agreed-settings digests, the deploy tool's own digest),
and `collect` shows any difference. **What it does not authenticate: that the software is
honest.** It proves everyone runs the same digests, not what they contain.

**Who builds the software.** Builds are not reproducible yet (Reference, 10, proposed change 11).
Either everyone runs the images one builder built from the agreed commit (`builds =
"one-builder"`, the default: image digests are enforced), or each operator builds from that
commit themselves (`builds = "each-operator"`, `join --images build-here`): then the image digests
differ, and only the commit, the circuit manifest, the pins and the agreed settings can be
compared, not the binaries. Reproducible builds are the open item that removes this choice.

## Deploying alone

Write one operator name for every node in `deployment.toml`, then
`python3 deploy/deploy.py up` (= join + collect + start, no fingerprint to compare).
**Trust:** whoever runs this with root on both computation nodes can read both. One operator
gives convenience, not the two-party protection; the tool warns. To rehearse everything on
this computer first, with no cloud account: `provider = "local"` for every node,
`[signal] endpoint = "local-test"`, then `deploy.py testapp up` (a test application server),
`deploy.py up --with-account` (it makes a test account on the local Signal server) and
`deploy.py testapp send` (one signup and one send).

## The account step

The Signal account's registration (SMS code, ban risk) cannot be push-button. `start` leaves
the computation daemons stopped until it is done (the monitoring page says "waiting for the
account step"). The owner registers the account (Reference, 5; CEREMONY.md) and gives each
computation operator a directory with `common/` (the account export, the contacts' signup tokens)
and only their own `party-N/credentials.share`; both run, within a minute of each other,
`python3 deploy/deploy.py account install DIR`. It creates the account's row on the database
nodes (the ceremony's `store` stage, both nodes at once), deletes the share, starts the daemons.
With `endpoint = "local-test"`, `deploy.py account local-test` does all of it against the local
server. With `endpoint = "production"`, `join`/`start` need `--i-have-the-go-ahead`.

## Status of the push-button tool (2026-11-13)

"Tested here" = run on this computer on the `local` provider: containers that stand in for
ssh-reachable Ubuntu machines, reached by ssh and configured by the same Ansible roles as any
machine (the `existing` path). Three simulated operators with separate private files and state
directories exchanged only bundle files.

| Part | State |
|---|---|
| Configuration validation (both files) | tested here: 18 unit checks, `python3 deploy/pushbutton/test_pushbutton.py` |
| Bundles, fingerprint, consistency checks | tested here: the three operators computed the same fingerprint; a swapped WireGuard key gave a different one and `start` refused it |
| `join` on `local` (= the `existing` path: Docker, WireGuard, firewall, data disk, images by digest, circuits and word files copied and checked, keys made on each node) | tested here, 7 machines |
| `start`: WireGuard full mesh, per-sender firewall, database nodes (Postgres + server), daemons' configuration, monitoring page, certificate timer, pre-flight, two-node comparison | tested here: kernel WireGuard inside the machine containers, every handshake up; the comparison reported EQUAL |
| Account step (`account local-test`, `account install` by both computation operators at once) | tested here against the LOCAL Signal server |
| One signup and one 200-byte send | tested here, **intermittent**: in 1 of 3 full runs a signup reached both daemons and a 200-byte text was delivered, agreed and decrypted by the new user from a sealed envelope; in the others every receive session failed at once. Cause found: the database nodes, started minutes apart by different operators, never connected (Reference 10, change 19). The start barrier that fixes it is written and lint-clean but **its end-to-end run was stopped before the send (untested)** |
| `status`, the page (through `monitor`'s ssh tunnel), `logs` | tested here; the page was checked for secrets |
| `upgrade` keeps the database; `destroy` then `join`/`start` restores keys and data from the kept disks | tested here: the database tables survive `upgrade`; after `destroy` + `join` the same keys came back (identical fingerprint) and the tables were restored from the kept volume |
| Certificate timer | tested here as far as it goes: it reads the expiry and, inside the margin, calls the entry point, which only records "refresh due" (the refresh job does not exist: Reference 10, change 15) |
| `existing` on a real remote machine | never run (the local containers stand in; same code) |
| OpenTofu modules `hetzner`, `upcloud`, `ovh` | validated offline: `tofu init` + `tofu validate` pass for both stacks of each; `tofu plan` with dummy credentials plans for hetzner and ovh; upcloud's plugin refuses to plan without valid credentials (one refused login to its API). Never applied: written, validated offline, never run against the provider |
| Ansible | `--syntax-check` passes for all 7 playbooks; ansible-lint passes (one line-length fix) |
| x86-64 images (`build --platform linux/amd64`) | never built (the tested images are arm64, built earlier) |
| `endpoint = "production"` | written, reviewed by reading, never executed |
| `up` (one person, every node) | written, never run (it chains the tested join/collect/start) |
| semi-honest mode, `worker_logic = "lean"` | written, never run (they select the image / environment only) |
| `build` (images for another platform) | written, never run (`build --record` of existing images was run) |

---

# Reference

## 0. Status of the older tooling (deploy/scripts, Dockerfiles, compose), and what is not ready

### 0.1 What was built and run here, and what is only written

| Item | State |
|---|---|
| `deploy/scripts/*.py` | compiled and `--help` checked (`selfcheck.py`: 73 checks pass) |
| `preflight.py` | **run** against the local harness layout (`local_signal_server/state/app/node-{0,1}.json`, `--no-network`): every check ran; it correctly reports the test layout's 4 deviations from a production node (world-readable peer key and database client keys; both parties' TLS keys in one `Player-Data`). The two exports compared equal with `--peer` (settings, manifest, word dir, binaries, mode, port base, peer key) |
| settings digest mirror | `deploylib.agreed_text` **checked equal** to the Lean `Config.agreedText` on 9 environments (3 settings sets x 3 session kinds), with `lake env lean --run` on this tree's `.olean` files |
| `verify_artifacts.py compare` | **run** on the two harness exports: 14 PASS |
| `stack.py status --harness` | **run** (read-only): server ping, terminators, local strict set (464 kernels), lock holder, Docker |
| `collect_logs.py` | **run** on the harness's node-0 state directory: 6 log files taken and redacted, 41 files left out |
| `stack.py up/down/status` (native or compose) | written, **not run** (the rehearsal starts and stops its containers with `docker compose` directly) |
| `build_artifacts.py native` | written, **not run** (it rebuilds binaries a running harness uses) |
| `build_artifacts.py context` | **run** (five times, at successive commits): stages about 1,190 tracked files, the vendored crates, libsignal, the database checkout and the engines bundle in about 10 s |
| `worker.Dockerfile`, malicious | **built** on this machine (linux/arm64, OrbStack) after five fixes found by building (section 12); 299 MB; every binary loads its libraries and starts; runs as uid 10001 |
| `worker.Dockerfile`, semi-honest | **built**; the rehearsal passed with it too (section 12) |
| `dbnode.Dockerfile` | **built** (after one fix); binaries start; **not run** as a database node (section 12) |
| `compose/rehearsal.yml`, `rehearsal.py` | **run, passed in both modes**: both nodes as containers, one signup and one 200-byte send against the local server and five local database nodes (section 12) |
| `compose/*.example` | written; parse and placeholder checks only (`selfcheck.py`) |

### 0.2 Not yet ready (product), in order of how much it blocks a deployment

From PRODUCT_TODO.md, STACK_NOTES.md section 11, NEEDS_REVIEW.md, REAL_TEST_PLAN.md and
NETWORKING_TODO.md. Nothing in this list is fixed by the tooling.

1. **The two nodes have never run on two machines.** Every session so far ran with both nodes on
   one macOS machine (`deployment/vm_pair_test/README.md` section 8: the peer settings were tested
   with one machine's LAN address; nothing ran on x86-64, which was only compiled under
   emulation). The two-machine test kit exists and has not been run. The container rehearsal of
   section 12 ran the two nodes in separate network namespaces of one arm64 Linux VM: closer, not
   the same.
2. **Test scaffolding is still on the production path** (`node_daemon/README.md` "What is still
   scaffolding"; PRODUCT_TODO.md sections 2 and 7): every session reads the account export file
   (prekey private keys, our address, the sealed-sender certificate, the identity key as a
   fallback); Kyber decapsulation runs the test tool `lss-provision`; the account's database row
   is created by a harness-run session from two credential shares; signup tokens of pre-provisioned
   contacts come from a tokens directory. The images and examples therefore still mount an export,
   a tokens directory and the KEM tool.
3. **Links are not authenticated as a deployment needs**: the application-to-daemon link is
   plaintext with an optional bearer token and unsigned replies; the daemon-to-daemon link is
   HMAC over plaintext under one shared key; the Boolean engine's channels are plain TCP; the
   field engine's TLS certificates are self-signed and expire after 30 days
   (`bench_certs.sh`). WireGuard is the only protection planned so far (open decision,
   PRODUCT_TODO.md section 9). The field engine's library listens on all interfaces whatever
   `TLS_WORKER_LISTEN` says: the host firewall must close it.
4. **`SIGNAL_SCRIPTS` must stay unset.** The Lean script flows pass the whole test set but the
   default has not been flipped (STACK_NOTES.md 11.3: parity with the legacy path is reached at a
   2 ms round trip, not on one machine; owner to decide where parity is measured). The legacy C++
   logic inside `node_worker` is what runs. `preflight.py` and the image's entry point refuse a
   non-empty value.
5. **Circuit manifests are hand-appended, not regenerated** (STACK_NOTES.md 11.3 item 2, J27,
   J29, K8): the local set had 23 + 90 kernels appended from the cache (464 now); the compact set
   lacks 142 names non-strict sessions asked for. The production set (414 kernels, 31 GB) was
   produced from `real_signal/deployment-production.json`, which does not list send class 3: **the
   product's texts of at least 200 bytes (owner decision) need class 3 (`"3:1:1:1:1"`), which the
   production set lacks**, so a 200-byte notify would be refused in strict mode until the
   deployment file gets it and the set is regenerated (heavy, alone). Also needed before
   regenerating: `"ceremony": 1` and a CircuitInventory setting for `ceremony-register-ctr`, the
   zero-digit `bundle-slot` shapes, `tls-seal-class 896`, the signup chains the harness and the
   production account use.
6. **Short official texts fail closed** (NEEDS_REVIEW.md 3f item 7): under the libsignal profile a
   text of 89 bytes padded (`classes = 1`) to a contact with an unanswered device aborts the
   session at operation 61 (`bundle-seal` one byte short). Nothing wrong is released. Product texts
   are at least 200 bytes, so the application must never send shorter texts; the daemon itself
   accepts 1 to 256 bytes.
7. **Distinguishable by the server and on the wire** (NETWORKING_TODO.md section 0;
   CLIENT_FINGERPRINT.md): HTTP/1.1 to the chat host while the user agent claims libsignal 0.107
   (official clients use HTTP/2 to the gRPC host since libsignal 0.97.1; HTTP/2 waits on the
   reorganisation, owner decision); one cipher suite and one group in the ClientHello; request ids
   from 2^63; space-padded JSON numbers; a 22-character password (Android: 24); the client Finished
   seconds after the server's flight.
8. **No proxy** (PRODUCT_TODO.md section 8; owner instruction: future work): node A's address
   sends every sealed message of a broadcast, so the Signal server can link a broadcast's
   recipients by source address and timing. Tor through `SIGNAL_TOR_SOCKS` was tested only against
   a local SOCKS stand-in. Connection rotation (ROTATION.md) is a proved planner not wired in.
   The long-lived send session keeps its connections across notifies (NEEDS_REVIEW.md 3d).
9. **The sender certificate expires every 7 days** and the two-party client cannot refresh it
   (REAL_TEST_PLAN.md B4): an owner-only conventional request refreshes it (section 5).
10. **One node pair, one receiving pair.** Several pairs need id partitioning and a receive lease
   (PRODUCT_TODO.md section 7); not built.
11. **Database nodes**: never run on separate machines, never with a node down or restarted during
   a session, never with more than a few rows; `pki` generates all five nodes' keys (and the
   WireGuard keys) in one place; signup tokens carry no expiry; repair of a lagging node is not
   built; a deleted id cannot be dealt again (PRODUCT_TODO.md section 6).
12. **Daemon state is in memory** (requests, results); after a restart the application must ask
   again. No limit on application request rate. The receive session is restarted only when it
   ends (PRODUCT_TODO.md section 7).
13. **Review and proof debt**: `secure_hybrid_backend` stays false until the engine combination is
   reviewed; erasure on retire/abort is not proven; the constant-depth programs
   (`TLS_WORKER_HINTED=1`) await review (NEEDS_REVIEW.md 3b); PROOF_GAPS.md lists the open gaps.
14. **Five or more devices per contact are not covered** (a prekey response record above 12,288
   bytes is refused in strict mode; the contact's message is reported failed).
15. **The account and its keys** (CEREMONY.md section 8, owner decisions): the verification-session
   id and SMS code are visible to both nodes during a registration; the identity private key is in
   the clear on both nodes (by decision: only the password is secret-shared); who holds the SIM;
   registration lock.

### 0.3 Docker build and rehearsal on this machine

Section 12 ("Build attempts on this machine") says exactly what was attempted with Docker and
what came of it. Built on arm64 only: **no x86-64 image has been built**, and the x86-64 engines
have never run anywhere (0.2 item 1).

---

## 1. Topology and trust boundaries

```
                         application server (operator: the product owner)
                         notify(ids, text) / delete(ids), signed with the notify key
                               |  WireGuard, TCP 19700 (+ bearer token)
                 +-------------+--------------+
                 v                            v
        +------------------+  daemon link  +------------------+
        | NODE A (party 0) |<--TCP 19710-->| NODE B (party 1) |
        | node-daemon      |               | node-daemon      |
        | controller(s)    |  workers:     | controller(s)    |
        | node-worker(s) <-+--TCP base..---+- node-worker(s)  |
        |                  |  base+639     |                  |
        +--+------+--------+  (B dials A)  +---------+--------+
           |      |                                  |
           |      +-------------+--------------------+
           |                    |  handoff_client, TCP compute ports (both nodes)
           | TLS 1.3, keys      v
           | inside the MPC   DB 0   DB 1   DB 2   DB 3   DB 4
           | (party 0 only)   secret-shared-db: five operators/providers, each node a
           v                  server with its own Postgres; peer/sync ports among
   Signal chat service :443   themselves; 3 of 5 reconstruct a contact's key; an epoch
                              needs threshold + max_malicious signatures
```

### 1.1 Who operates what

| Component | Runs on | Operator | Must NOT be run by |
|---|---|---|---|
| Application server (calls notify/delete, issues signup tokens) | its own host | product owner | — |
| Node A: daemon, controllers, workers (party 0, the leader) | computation host A | operator A | the operator of node B |
| Node B: daemon, controllers, workers (party 1) | computation host B | operator B | the operator of node A |
| Database node i (server + Postgres), i = 0..4 | database host i | operator i | anyone who also runs two other database nodes (no party may hold 3 of 5) |

- **Nodes A and B**: the security of the contact list rests on these two never colluding.
  Different organisations, different cloud providers, ideally different jurisdictions (owner's
  criterion, PRODUCT_TODO.md section 9; decided pair of locations: Helsinki and Tallinn, about
  2 ms apart). Malicious mode (the default, statistical security 128) is designed against one
  node deviating arbitrarily; semi-honest mode assumes both follow the protocol. The engine
  combination's review is still pending (0.2 item 13).
- **Database nodes**: threshold 3 of 5 (`pki -t 3`): three nodes' shares reconstruct a contact's
  key. No single provider or operator may host three; no realistic pair either. Whether a
  computation node's provider may also host database nodes, and how many, is an open decision
  (PRODUCT_TODO.md section 9): each computation node already holds one additive share of what it
  reads. `max_malicious` decides how many signatures an epoch needs (`threshold + max_malicious`):
  the generator's default 2 needs all five nodes for every epoch; the harness uses 1 (epochs go on
  with one node down).
- **The application server** holds the notify signing key and the signup-token key; it never
  holds a share. Whoever holds the notify key can make the nodes send to any stored id (not read
  who they are).

### 1.2 What each host holds

| Host | Secret (never leaves it, never logged) | Shared secret | Public | Circuits |
|---|---|---|---|---|
| Node A | its XOR share of the account credentials (password); its field-engine TLS key (`Player-Data/P0.key`); its database client key (`compute-nodes/0/key.json`) | the daemon-link key (`peer.key`, also on B); the bearer token (also on the application server) | daemon config, database network config, Signal TLS root, the other node's field-engine certificate | the full manifest set and the word dir (identical to B's) |
| Node B | its credential share; `P1.key`; `compute-nodes/1/key.json` | `peer.key`; bearer token | as A | as A |
| Both nodes, TEST scaffolding | the account export (prekey private keys, identity key fallback, sealed-sender certificate): **in the clear on both, by decision** (only the contact list must stay secret; our own Signal private keys may be in the clear on the nodes) | | | |
| Database node i | its signing key (in its `config.json` from `pki`); its Postgres password | | the network configuration | none |
| Application server | notify key (`notify-key.json`), signup-token configuration (`app-server/config.json`) | bearer tokens | network configuration (to verify delete evidence) | none |

Contacts' keys and ratchet state live only on the database nodes, as shares and sealed blobs;
inside a session they exist only as engine shares. A computation node never writes a contact's
state to its own disk (the journal records only which ids were settled).

### 1.3 Ports and firewall

All traffic between the parties goes through WireGuard (UDP 51820) between the hosts that talk;
the TCP ports below are inside the tunnel and closed on the public interface.

| From | To | Port (TCP unless noted) | What | Configured by |
|---|---|---|---|---|
| application server | node A and node B | 19700 (`listen`) | notify, delete, wait, events, status: one JSON line per request | daemon `listen`, `application.token_file` |
| node A | node B, and B to A | 19710 (`peer_listen`) | daemon link: agree, start, serve, ended, finish (HMAC, replay cache, clocks within 60 s) | `peer_listen`, `peer`, `peer_key_file` |
| node B | node A | `port_base` .. `port_base`+639 (default base 23000 here, daemon default 22400) | per session at port P: P Boolean engine, P+10 field engine (TLS), **P+20 the control link** between the workers. Send sessions at +0..+280, receive sessions at +320..+600. Party 0 listens for everything; nothing dials party 1 | `worker.port_base`, `TLS_WORKER_PEER`, `TLS_WORKER_LISTEN` |
| node A and node B | each database node | its compute port (`pki` non-local layout: 11002+i on 10.0.0.(i+2); read `compute_addresses` in `network-config.json`) | `handoff_client`: read, parity, combine, deal, write-blob, delete | `database.network` |
| database node | the other database nodes | peer, sync and relay ports of `network-config.json` | consensus, epochs, signatures | `pki` |
| **node A only** | the Signal chat service | 443 | the two-party TLS connection (party 0's worker owns the socket; the bytes are encrypted under keys no node holds) | `signal.endpoint`, `signal.port`, `signal.hostname`, `signal.trust_root` |
| node A (optional) | a Tor client on node A | its SOCKS port, localhost only | per-circuit SOCKS credentials; the server is asked for by name | `proxy.socks`, `proxy.circuits` |
| every host | NTP servers | UDP 123 | clock | the OS |
| administrators | every host | 22 | SSH, from the administrators' addresses only | |

Outbound access to Signal: **only node A**, only the chat host on 443 (and only once the owner
has given the go-ahead; section 5). Node B, the database nodes and the application server never
connect to a Signal host. Build machines download toolchains and crates (github.com, crates.io,
static.rust-lang.org, the Ubuntu archive) but contact no Signal service host.

Host firewall on each computation node (as `deployment/vm_pair_test/README.md` section 2):

```sh
sudo ufw default deny incoming
sudo ufw allow from ADMIN_ADDRESS to any port 22 proto tcp
sudo ufw allow from PEER_PUBLIC_ADDRESS to any port 51820 proto udp
sudo ufw allow in on WG_INTERFACE          # then narrow to the table above
sudo ufw enable
```

### 1.4 Hardware

From PERFORMANCE.md ("The long-lived send session", "Rounds") and
`deployment/vm_pair_test/README.md` section 2. Measured on one 12-core macOS machine with both
nodes on it; a real link adds latency and limits bandwidth.

| | Malicious (default) | Semi-honest |
|---|---|---|
| Cores per computation node | 16 vCPU: a node runs two worker pairs at once (the long-lived send session and the receive session), each keeping 8 to 10 threads busy | 8 to 16 vCPU |
| Memory per computation node | 32 GB: a send session 2.8 to 2.9 GB idle, 3.3 to 4.4 GB with contacts loaded (about 0.1 GB more per distinct contact); a receive session's worker about 3 GB; largest benchmark process 2.8 to 3.8 GB | 16 GB (send session 1.0 GB idle, 1.5 to 1.8 GB loaded) |
| CPU features (x86-64) | `aes`, `pclmulqdq`, `avx2` exposed to the guest (the field engine does not compile without AVX) | same |
| Disk | 100 GB: the production circuit set is 31 GB of gate lists (414 kernels); word dir 0.5 GB; logs | same |
| Link between A and B, round trip | 1 to 2 ms. A contact's first send is about 2,800 sequential rounds, a first message received about 11,500: at 10 ms that is 28 s and 2 minutes, past the Signal server's 90 s idle limit | same |
| Link bandwidth | 0.96 GB each way per message: 1 Gbit/s carries one message every 7.7 s; 10 Gbit/s about the one-machine rate. A contact's preparation 0.75 GB each way; a first message received about 3 GB each way | 117 MB per message: 0.94 s at 1 Gbit/s |
| Traffic volume | about 1 PB each way per 1,000,000 messages: price the egress | about 8 times less |
| Throughput of one pair (one machine, local server) | 0.67 messages/s inside the session, 0.63 as the application sees it | 1.25 / 1.14 messages/s |
| Database node | not measured; the test nodes ran with `RAYON_NUM_THREADS=2`; two writes and one read per message per pair; Postgres | |
| Circuit production machine (not a node) | 32 GB or more: `tls-open-typed 12288` peaks at 23.6 GB (`--max-gb 26`); 1.5 to 2 hours from an empty cache, one kernel at a time | |

---

## 2. Build

### 2.1 Pins (2026-11-13)

| What | Pin | Where it is set |
|---|---|---|
| Lean | `leanprover/lean4:v4.31.0` (commit 68218e8), elan 4.2.3 | `lean-toolchain`; `ELAN_VERSION`, `LEAN_TOOLCHAIN` in `worker.Dockerfile` |
| Rust, node_worker | 1.88.0 (`node_worker/build.sh` uses the default toolchain) | `RUST_STABLE` |
| Rust, node_daemon and the KEM tool | `nightly-2025-09-24` | `node_daemon/build.sh`, `local_signal_server/scripts/provision.sh`; `RUST_NIGHTLY` |
| rustup | 1.28.2 | `RUSTUP_VERSION` |
| Crates (worker, daemon, KEM tool) | offline, `.deps/libsignal-vendor`; `Cargo.lock` of each crate (`--locked`) | `deploy/docker/cargo-vendored.toml` |
| libsignal (KEM tool) | v0.106.1 at `.deps/libsignal-v0.106.1` | `local_signal_server/provision/Cargo.toml` |
| Boolean engine | emp-tool 339bde84, emp-ot 5072bdab, emp-ag2pc validated-v3 headers | `deployment/vm_pair_test/make_bundle.py` |
| Field engine | MP-SPDZ 113c4e4 with SimplestOT_C, libOTe and its clones at `.deps/two-party-comparison/dependency-pins.json` | `make_bundle.py` |
| Security parameter | statistical 128 (`EMP_HYBRID_STATISTICAL=128`, `EMP_HYBRID_NATIVE_SECURITY=128`), no `EMP_HYBRID_TEST_FAULTS` | `build_engine_abi.sh`, `build_linux.sh`, `build_hybrid_v3.py --engine-abi` |
| Database client and nodes | `secret-shared-db` branch `two-party-handoff-signup-tool`, commit 229ca66d (`.deps/secret-shared-db-handoff`), `--locked` | `build_artifacts.py context` records it in `context.json` |
| Base images | `ubuntu:24.04` (replace by its digest at the first pull; `build-info.json` records what was used); `postgres:17@sha256:5b96f1a1…a97e4` | Dockerfiles, `db-node.yml.example` |
| Circuits | the manifest's SHA-256; `manifest.json` records the emitter binary's hash (`emitter_sha256`), which keys the circuit cache | `scripts/produce_circuits.py` |
| Word circuits and V3 field programs | the 6 word-circuit pins and 22 field-program pins in `node_worker/src/loader.rs` (`FIELD_PROGRAMS`, `WORD_CIRCUITS`); `pins.json` in the image | `deploylib.parse_loader_pins` |

Values seen on this machine on 2026-11-13 (they change with every rebuild; compare between the
nodes, do not copy): controller `e6b151a2…`, node_worker v3 `d6a7036f…`, local strict manifest
`e090a2b6…` (464 kernels, 14.5 GB), word dir `9f8ee191…` (68 files, 22 V3 programs, 28 pins),
settings digests of the harness's daemons serve `b7cd68aa…`, receive `3c52888d…`, notify
`63ad0bc1…`. The production manifest's digest is in `real_signal/state/` (run `plan.json`), which
this tooling does not read.

### 2.2 The route: one image per security mode

```sh
# on the build machine, from the repository root, at the commit to deploy:
python3 deploy/scripts/build_artifacts.py plan                       # prints every step; does nothing
python3 deploy/scripts/build_artifacts.py context --out /build/ctx --yes
python3 deploy/scripts/build_artifacts.py image --context /build/ctx --mode malicious   --tag tls-mpc-node:malicious   --yes
python3 deploy/scripts/build_artifacts.py image --context /build/ctx --mode semi-honest --tag tls-mpc-node:semi-honest --yes
python3 deploy/scripts/build_artifacts.py image --context /build/ctx --dockerfile deploy/docker/dbnode.Dockerfile --tag tls-mpc-dbnode --yes
```

`context` stages, from **the tracked content at a commit** (`git archive`, not the working tree):
the Lean sources, `handshake_backend/`, the text fixture header, `node_worker/`, `node_daemon/`,
the KEM tool's crate, `deploy/` and the benchmark kit; the vendored crates and libsignal; the
database checkout at its HEAD; and the engines bundle written by `make_bundle.py --with-workers`
(which itself refuses to copy anything that looks like a key, an account, an export, a log or
state). Tracked files whose names or contents look like keys are left out and listed. It writes
`pins.json` and `context.json` (commit, database commit, bundle manifest digest).

The worker image builds, in stages: the engines with the bundle's own `build_linux.sh --portable`
(x86-64-v3 with AES and PCLMUL, or armv8-a with crypto), then `build_engine_abi.sh` (the Linux
counterpart of `build_hybrid_v3.py --engine-abi`) for `v3` and `sh-v3`; the controller with
`lake build public_service_controller` and the certificate checker; `node_worker` in the mode's
production variant (never `-test`), `node-daemon`, `notify-app`, `lss-provision`; the database
client (`handoff_client`, fetched crates, `--locked`). The runtime image runs as uid 10001, holds
no secret and no circuit, and records every binary's SHA-256 in `/opt/tls-mpc/share/build-info.json`
(`docker run --rm IMAGE version`).

**The word-circuit directory is compiled into the worker** (`NODE_WORKER_WORD_DIR`,
`EMP_WORD_CIRCUIT_DIR`): in the image it is `/opt/tls-mpc/word`, and the word volume must be
mounted exactly there.

The native route on the macOS build machine (the one every test so far used) is the same steps
with the repository's scripts directly, each under the heavy-job lock:

```sh
python3 deploy/scripts/build_artifacts.py native --mode both --out .deps/deploy-native --yes
```

### 2.3 Circuits and the word directory

```sh
python3 deploy/scripts/build_artifacts.py circuits --deployment real_signal/deployment-production.json \
    --out /build/circuits-production --max-gb 26 --yes          # alone; 1.5-2 h from an empty cache
python3 deploy/scripts/build_artifacts.py word --out /build/word --yes
```

`circuits` runs `scripts/produce_circuits.py` under `guarded.py --heavy`: kernels are produced one
at a time (parallel lowering crashed the build machine twice), by the Lean emitters, never by
hand; the result is `manifest.txt` (what the workers load in strict mode), `manifest.json` (with
the emitter's hash), and the gate lists. It prints the manifest's SHA-256: that value is
`EXPECTED_MANIFEST_SHA256` on both nodes. The circuits belong to the emitter binaries: after any
change to the Lean kernels, produce them again, and never mix a new worker with old circuits or
the reverse (REAL_TEST_PLAN.md section 3). See 0.2 item 5 for what the production deployment
file must list before the next regeneration.

`word` copies the top-level `*.flat` and `*.v3` files of `.deps/emp-hybrid-word-v1` (the word
circuits and the 22 V3 field programs of FIELD_PROGRAMS_V3.md) and prints their digest
(`EXPECTED_WORD_DIR_SHA256`). Both nodes must hold the same files, all or none of the V3
programs: the workers include them in their start agreement and stop with "circuit manifest
disagreement" otherwise.

### 2.4 Did the two nodes build the same thing?

```sh
# on each node (or inside its container: docker run ... IMAGE preflight --export /srv/tls-mpc/state/facts.json)
python3 deploy/scripts/verify_artifacts.py export --config node.json --word-dir /srv/tls-mpc-host/word --out facts-A.json
# exchange the two files (they hold hashes and public settings text only), then on either node:
python3 deploy/scripts/verify_artifacts.py compare facts-A.json facts-B.json
```

It fails on any difference in: controller, worker (and its mode), database client, certificate
checker; manifest digest; word-dir digest; the agreed-settings digests of the send, receive and
notify sessions; the worker session settings; port base; the salted fingerprint of the shared
peer key. The image digest is the simplest single comparison when both nodes run one image; when
each operator builds independently, compare `build-info.json`'s binary hashes (the builds are not
yet known to be bit-for-bit reproducible across machines; section 10, proposed change 11).

What the software itself checks at every session start, regardless of the above: the controllers
exchange SHA-256 of their agreed settings and end the session on a difference ("the two nodes'
settings differ", with this node's settings text); the workers compare the manifest digest and
the word circuits and field programs they loaded, and a session string with the settings that
change what they compute (`node_worker/src/config.rs`), before the first request.

---

## 3. Configuration reference

### 3.1 The daemon's configuration file (one per node)

The reference is `node_daemon/README.md` "Configuration"; examples with container paths:
`deploy/compose/node-a.json.example`, `node-b.json.example`. Unknown keys are ignored.

| Field | Meaning | Default | Production |
|---|---|---|---|
| `party` | 0 (node A, leads) or 1 | required | 0 on A, 1 on B |
| `listen` | the application's listener | required | the node's WireGuard address:19700; a wildcard needs `application.token_file` |
| `peer_listen`, `peer` | this daemon's link listener; the other's | required | WireGuard addresses:19710 |
| `peer_key_file` | hex, at least 16 bytes, the same on both nodes | required | 32 random bytes, mode 600 |
| `state_directory` | logs/, work/, journal/, events.jsonl | required | on the state volume, mode 700 |
| `controller`, `worker.binary` | executables | required | the image's (`/opt/tls-mpc/bin/...`); never a `-test` worker |
| `worker.send_directory`, `worker.receive_directory` | the workers' working directories: `Player-Data` with this party's field-engine key and the other's certificate | required | writable, mode 700 |
| `worker.hosts` | the two nodes' addresses (node_worker ignores it; the peer comes from `TLS_WORKER_PEER`) | required, 2 entries | both WireGuard addresses |
| `worker.port_base` | sessions use base..base+639 | 22400 | the same on both nodes |
| `circuits.tool` | `circuit_cache.py` (non-strict development only) | required | the image's copy |
| `circuits.manifest` | `CIRCUIT_MANIFEST`: strict mode | null | **required**: the production worker loads only pinned circuits |
| `signal.endpoint`, `port`, `hostname`, `trust_root`, `certificate_checker` | the target and its pinned TLS root | required | owner's go-ahead only for the real service; root `real_signal/signal-root-ca.pem` |
| `proxy.socks`, `proxy.circuits` | `SIGNAL_TOR_SOCKS`, `SIGNAL_TOR_CIRCUITS` | none | unset (no proxy yet) |
| `database.client`, `network`, `key` | `handoff_client`, the network configuration, this node's client key | required | `compute-nodes/0` on A, `/1` on B |
| `application.notify_public_key` | optional pin of the application's key | from the network config | pin it |
| `application.token_file` | bearer token for every application request | none | set (at least 16 bytes) |
| `test.export`, `test.tokens`, `test.kem_tool` | TEST scaffolding still required (0.2 item 2) | none | required until replaced |
| `environment` | passed to every controller as is | {} | section 3.2 |
| `receive` | run the receive session | true | true on exactly one pair |
| `timeouts.*` | agree 30, start margin 30, send 600 + 60 per id, delete 120, peer wait 180 s | | defaults |
| `send_session.*` | long_lived true, max_messages 5000, max_seconds 21600, max_megabytes 0, stall_seconds 900, attempts 3 | | set `max_megabytes` (for example 8000 malicious) |

### 3.2 Environment variables

"Agreed": part of the settings text the controllers compare at every session start
(`TlsMpc/Node/Config.lean` `agreedText`). "Worker session": part of the string the two workers
compare (`node_worker/src/config.rs`). Both kinds must be set identically on the two nodes, or
every session ends before it does anything. Set them in the daemon configuration's `environment`,
never in only one node's shell.

| Variable | Meaning | Default | Agreed / worker | Production value |
|---|---|---|---|---|
| `SIGNAL_SCRIPTS` | flow groups run as Lean scripts instead of the worker's legacy operations | empty | agreed | **unset/empty** (preflight and the entry point refuse anything else) |
| `SIGNAL_WORKER` | `node` (node_worker) or `legacy` (the C++ worker, comparison only) | node | agreed | node |
| `SIGNAL_CLIENT_PROFILE` | `libsignal` (what the server sees follows the official clients) or `legacy` | legacy | agreed | libsignal (as both real runs), and it must equal the circuit set's `profile` setting |
| `SIGNAL_ACK_REFUSED` | `0`: a refused delivered message stays on the server | acknowledged | agreed | 0 (as the real runs) |
| `SIGNAL_RECOVERY` | `0`: old fail-fast loop | on | agreed | unset (on) |
| `SIGNAL_PREPARE_BATCH` | contacts prepared per worker call (with hinted programs) | 32 (max 64) | agreed | unset |
| `SIGNAL_BUNDLE_SLOTS` | `0`: old `bundle-item` layout | on | agreed | unset (on) |
| `SIGNAL_RECEIVE_JUMP` | a first message may be the sender's number 0..N | unset | agreed | 3 (as the real runs; deployment `signup_jump [3]`) |
| `SIGNAL_TOR_SOCKS`, `SIGNAL_TOR_CIRCUITS` | proxy and circuit count (1..16) | none, 0 | agreed (count) | unset |
| `TLS_WORKER_HINTED` | constant-depth curve programs | 0 | agreed and worker | 0 (review pending) |
| `TLS_WORKER_FIELD_BATCH` | field triples per batch | 16 (split agreement) | worker | 3000 (every harness and real run) |
| `TLS_WORKER_TRIPLE_STOCK` | AND-triple factories, batch, reserve | 2,524288,4194304 | worker | default |
| `TLS_WORKER_FIELD_STOCK` | field reserve, generator lines | 8 x batch, 2 | worker | default |
| `TLS_WORKER_FIELD_DIRECT` | both workers send openings at once | 0 | worker | 0 |
| `TLS_WORKER_TYPED_OPEN` | typed record opening | 1 | worker | 1 |
| `TLS_WORKER_KEY_AGREEMENT` | `split` or `ladder` | split | worker | split |
| `TLS_WORKER_PEER` | the other worker's numeric IPv4 address | 127.0.0.1 | per node | the other node's WireGuard address, on both |
| `TLS_WORKER_LISTEN` | address party 0's Boolean listener binds | all interfaces | per node | node A's WireGuard address (A only) |
| `TLS_WORKER_PEER_WAIT` | seconds a worker waits for the other per request | 180 (daemon `timeouts.peer_wait_seconds`) | per node | default |
| `CIRCUIT_MANIFEST` | strict mode | set by the daemon from `circuits.manifest` | (the digest is compared by the workers) | required |
| `CIRCUIT_REFUSED_LOG`, `CIRCUIT_CACHE_LOG` | where refused / requested kernel names are written | unset | per node | set to files in the state directory to see refusals |
| `SIGNAL_RECORD` | one JSON line per exchange with the server (revealed public bytes, sizes, events) | unset | per node | for the first production runs: set (REAL_TEST_PLAN.md "record everything"); see 6.2 |
| `SIGNAL_DB_CLIENT`, `_NETWORK`, `_KEY`, `_WORK`, `_REQUEST`, `_TOKENS` | the database client | set by the daemon | (database present: agreed) | from the configuration |
| `SIGNAL_NOTIFY_*`, `SIGNAL_SERVE_DIR`, `SIGNAL_LOCAL_RECEIVE`, `SIGNAL_LOCAL_EXPECT`, `SIGNAL_LOCAL_EVENTS` | the session's kind | set by the daemon per session, never inherited | agreed (kind) | never set by hand |
| `SIGNAL_LOCAL_EXPORT`, `SIGNAL_LOCAL_KEM` | TEST scaffolding still in use | from `test.*` | agreed (export present) | required until replaced |
| `SIGNAL_LOCAL_CREDENTIALS`, `SIGNAL_LOCAL_CREDENTIALS_FILE` | this party's credential share (ceremony and the account fixture only) | unset | — | **never in a node's environment** |
| `SIGNAL_LOCAL_TIMESTAMP`, `_PAUSE_AFTER`, `_PAUSE_REFRESH`, `_BROADCASTS`, `_EXTRA_CONTACTS`, `_NEW_CONTACT`, `_STORE`, `_TRACE` | TEST hooks, in force only with `--test` | unset | agreed when in force | unset (preflight fails if set) |
| `TLS_WORKER_TEST_LINK_SHIFT`, `TLS_WORKER_TEST_PRODUCER`, `TLS_WORKER_SERVICE_FIXTURE`, `SIGNAL_LINK_DELAY_MS` | test-only | unset | | unset |

Image entry point (`deploy/docker/entrypoint.py`):

| Variable | Meaning | Production |
|---|---|---|
| `EXPECTED_MANIFEST_SHA256` | the agreed manifest digest; the container stops on a difference | required |
| `EXPECTED_WORD_DIR_SHA256` | the agreed word-dir digest | required |
| `TLS_MPC_FULL_HASH=1` | hash every gate list at start (minutes) | after a copy or an upgrade |
| `TLS_MPC_ALLOW_SCRIPTS=1` | accept `SIGNAL_SCRIPTS` | never |
| `TLS_MPC_REHEARSAL=1`, `TLS_MPC_HOST_ALIAS` | rehearsal only | never |

Build time only: `MODE` (malicious, semi-honest), `PORTABLE`, `APT_SNAPSHOT`, the toolchain
arguments; `NODE_WORKER_ENGINE_DIR`, `NODE_WORKER_WORD_DIR` (node_worker's build).

The security mode is chosen by the worker binary (`v3` or `sh-v3`, the image's `MODE`), not by an
environment variable: both nodes must run the same mode, and `preflight.py --peer` and
`verify_artifacts.py compare` check it. Switching to semi-honest is a redeployment of both nodes
with the other image (costs in 1.4).

---

## 4. Bring-up, in order

Each step has a check; do not go on while it fails.

1. **Hosts and tunnels.** Seven hosts (A, B, five database nodes) plus the application server,
   WireGuard between every pair that talks (1.3), the host firewall, NTP.
   *Check:* `wg show` lists a recent handshake for each peer; `ping` between A and B over the
   tunnel: median 1 to 2 ms; `timedatectl` reports synchronised.
   *Failure:* no handshake (keys or UDP 51820 blocked); round trip above 5 ms (the round-bound
   operations will approach the server's 90 s idle limit).
2. **Database network** (`secret-shared-db`). Generate the configuration with `pki` (`-n 5 -t 3
   --max-malicious 1`, non-local mode with the hosts' addresses; it writes every node's directory,
   the compute nodes' client keys `compute-nodes/{0,1}`, and the application's `app-server/`), give
   each operator only its own directory, start Postgres and the node (`db-node.yml.example`).
   *Check:* every node's log shows `Successfully updated database secrets for epoch N` within
   a few epochs (120 s each by default); from A and B each compute port accepts TCP
   (`preflight.py`).
   *Failure:* a node exits (its log; Postgres URL in its `config.json`); no epoch applied (clocks,
   a node down while `max_malicious` requires all).
3. **Images on A and B.** Pull the same image digest on both (or build independently, 2.2).
   *Check:* `docker run --rm IMAGE version` on both; `verify_artifacts.py compare`: no FAIL.
4. **Circuits and word dir** copied to both (2.3).
   *Check:* `preflight.py --full-hash` once after copying; manifest and word digests equal on both.
   *Failure:* "gate list pin differs" (a damaged copy: copy again).
5. **Per-node secrets.** `peer.key`: 32 random bytes in hex, made on one node, carried to the
   other over the tunnel, mode 600. Database client key: `compute-nodes/0` to A, `/1` to B only.
   Field-engine certificates, each key made on its own node (only certificates cross):
   ```sh
   docker run --rm -v /srv/tls-mpc-host/state:/out IMAGE certs init 0 /out/worker-send     # on A (1 on B)
   # copy worker-send/Player-Data/P0.pem to B and P1.pem to A, then on each:
   docker run --rm -v /srv/tls-mpc-host/state:/out -v /tmp/peer:/peer:ro IMAGE certs trust /peer/P1.pem /out/worker-send
   cp -a /srv/tls-mpc-host/state/worker-send /srv/tls-mpc-host/state/worker-receive
   ```
   Compare the printed SHA-256 fingerprints by a second channel. They expire after 30 days.
   Bearer token: from the application operator, one per node.
   *Check:* `preflight.py`: secrets PASS (present, private, exactly one own key per `Player-Data`).
6. **The account** (section 5; owner only where marked). The account's row on the database nodes
   must exist before a receive session can start.
7. **Pre-flight on both nodes**, then compare:
   ```sh
   docker compose -f node.yml --env-file node.env run --rm node preflight --export /srv/tls-mpc/state/facts.json
   # exchange facts.json; then on each node:
   docker compose -f node.yml --env-file node.env run --rm -v /path/facts-other.json:/peer.json:ro node preflight --peer /peer.json
   ```
   *Check:* no FAIL (section 7 lists every item).
8. **Start node B, then node A** (either order works: party 0 starts the sessions once party 1
   answers). For a real Signal endpoint this step contacts the service: owner only.
   ```sh
   python3 deploy/scripts/stack.py up --compose node.yml --env-file node.env --target production --i-have-the-go-ahead
   ```
   *Check:* the container's first lines are the entry point's `manifest … word dir … settings …`
   line, then the daemon's `listening`; within a minute `stack.py status` shows a receive session
   running and the send session ready (`node-daemon: send session … ready` in the log).
   *Failure, by message:* "the two nodes' settings differ" (an agreed variable differs: compare the
   printed text with the other node's); "circuit manifest disagreement" (manifest or word files
   differ); "refused kernel …" (a shape missing from the manifest: 0.2 item 5); field engine
   "handshake failed" (certificate missing, not rehashed, expired, or clocks); party 1 never
   connects (firewall on A, `TLS_WORKER_LISTEN` not A's tunnel address); "the other party did not
   reach operation N within S s" (the other node's controller hung or died).
9. **First real traffic** (owner only, section 5): one signup and one send to a phone the owner
   holds, with everything recorded, before any application traffic.

The local rehearsal of steps 3 to 9 on one machine, against the local Signal-Server and local
database nodes (never Signal's service):

```sh
python3 deploy/scripts/build_artifacts.py context --out .deps/deploy-ctx --yes
python3 deploy/scripts/build_artifacts.py image --context .deps/deploy-ctx --mode malicious --tag tls-mpc-node:malicious --yes
python3 scripts/guarded.py --heavy 24 2400 python3 deploy/scripts/rehearsal.py --yes
```

---

## 5. Account provisioning and the key ceremony

Steps marked **OWNER ONLY** contact Signal's real service and are run by the owner and nobody
else, after the dry run, with the go-ahead given explicitly for that step. Malformed requests to
the real service get accounts and addresses banned; everything is first run against the local
server (`local_signal_server/`, REAL_TEST_PLAN.md section 4).

What exists today (REAL_TEST_PLAN.md):

1. The account was registered by a conventional client (`real_signal/register`, 2026-11-11) and
   its state lives in `real_signal/state/` (git-ignored; never read by this tooling, which only
   checks that a directory you name exists and is private).
2. Offline: `lss-provision export-account ACCOUNT_JSON OUT_DIR production` writes the controllers'
   export, each party's credential share (`credentials-party-0.hex`, `-1.hex`) and the deployment
   hints. **Share 0 goes to node A only, share 1 to node B only**; never both on one host, never
   in a log, a ticket or a chat. Whoever holds both has the account's password.
3. The account's row on the database nodes is created by a session given the two shares (the
   harness's account fixture; `run_real_test.py`'s receive session does it in the real test).
4. The production circuit set is produced from `real_signal/deployment-production.json` (2.3);
   the handshake size in it was measured by `real_signal/measure_handshake.py` (**OWNER ONLY**).
5. Dry run, no connection: `real_signal/run_real_test.py production … --dry-run` must list no
   problems in `plan.json`.
6. **OWNER ONLY**: the real run (`--i-have-the-go-ahead`, typed confirmation).

The two-party registration (CEREMONY.md: the password made inside the engines, each node keeping
an XOR share) has run only against the local server. Running it against the real service is
**OWNER ONLY** and waits on the owner's decisions in CEREMONY.md section 8 (the session id and
SMS code are visible to both nodes; the identity key in the clear; who holds the SIM;
registration lock). With the image it would be, on both nodes with the same NAME:

```sh
docker compose -f node.yml --env-file node.env run --rm node ceremony NAME register      # OWNER ONLY
docker compose -f node.yml --env-file node.env run --rm node ceremony NAME certificate   # OWNER ONLY
docker compose -f node.yml --env-file node.env run --rm node ceremony NAME store
```

**The sender certificate expires every 7 days** (REAL_TEST_PLAN.md B4) and only a conventional
`GET /v1/certificate/delivery?includeE164=false` on the authenticated socket refreshes it:
**OWNER ONLY**, never while a receive session is connected (the server closes the older socket,
4409). `export-account` refuses an expired certificate and warns under 24 hours. Put the expiry in
the calendar and in monitoring.

Cautions that apply to every owner-only step (REAL_TEST_PLAN.md section 3):

- Stop at once and do not retry on: a 428 or 403 to any request, close code 4401 or 4409, an
  `x-signal-alert` header in any revealed response, a refused handshake.
- Record everything: each controller's `SIGNAL_RECORD` (every exchange with the server, with
  time), the launcher's `plan.json` (configuration, binary and manifest hashes, git head) and
  `timeline.jsonl`, the parties' logs and final reports, the kernels requested and refused,
  optionally a packet capture on node A. Write what the phone showed into the run directory.
- Never `SIGNAL_SCRIPTS` for a real run; never a `-test` worker; strict mode only.
- The key ceremony of the infrastructure (PRODUCT_TODO.md section 9) is not built: today `pki`
  generates every database node's key, the compute nodes' client keys and the application's keys
  in one place, and whoever runs it has seen them all. Until each machine makes its own keys, run
  `pki` on an offline machine, distribute each directory to its operator only, and erase the
  machine.

---

## 6. Operations

### 6.1 Start, stop, restart

```sh
python3 deploy/scripts/stack.py up     --compose node.yml --env-file node.env --target production --i-have-the-go-ahead
python3 deploy/scripts/stack.py status --compose node.yml --env-file node.env
python3 deploy/scripts/stack.py down   --compose node.yml --env-file node.env
# native (no Docker): stack.py up|down|status --config node.json
```

A daemon asked to stop ends its sessions and kills their process trees (`stop_grace_period: 90s`).
A notify in flight ends `failed`; resubmitting the same signed request while it is fresh (120 s)
runs a new session that does not resend what both journals show as settled (at least once:
duplicates possible). Restart both daemons together when changing anything agreed. A daemon keeps
requests and results in memory: after a restart the application asks again.

### 6.2 Logs, and what must never be logged

Each daemon writes its own log to standard error and each session's controller and worker log to
`STATE/logs/` (several lines a second even when idle: rotate). The application gets statuses and
results, never a controller's error text.

Never logged, copied into tickets or collected: credential shares and the password, the recovery
password share, `peer.key`, the bearer token, database client keys, `Player-Data/*.key`, the
export file (prekey private keys, identity key), the application's notify and signup keys, the
account's phone number, captcha tokens and SMS codes (they are in a ceremony's `SIGNAL_RECORD`),
work and journal files. `SIGNAL_LOCAL_TRACE` (it prints revealed bytes) is a TEST hook and stays
off. `SIGNAL_RECORD` files hold only what both nodes may see, but they describe the account's
traffic: keep them on the node, mode 600, and treat them like logs with contact ids.

```sh
python3 deploy/scripts/collect_logs.py --state-dir /srv/tls-mpc-host/state/daemon --out /tmp/case-123 --compose node.yml --env-file node.env
```

takes only `logs/*.log` and `events.jsonl` (and `docker compose logs`), redacts keys, tokens,
shares, PEM blocks, UUIDs, phone numbers, long hex and base64-looking strings and contact ids, and
never reads work/, journal/, keys, shares, records or exports. Review its output before sending
it anywhere.

### 6.3 The stock journal and connection rotation

Neither is deployed yet. The preprocessing stock (STOCK.md) is a standalone, proved store that
nothing calls; when it is wired in, its rules become operational ones: the journal must be on
storage that honours `fsync`; a reboot discards the stock by design (boot memory); never restore a
node from a snapshot that includes memory (`full_rollback_reuse`); never back up or copy a stock.
Connection rotation over Tor (ROTATION.md) is a proved planner not wired into the session.

### 6.4 Upgrades

Both computation nodes change together; nothing supports mixed versions.

1. Build the new image and, if any Lean kernel or emitter changed, produce the circuits again
   (2.3): the new manifest digest and word-dir digest replace the old ones in both `node.env`.
2. `verify_artifacts.py compare` on the new artefacts of both nodes.
3. Drain: stop submitting notifies; wait until `stack.py status` shows no job running on either.
4. `stack.py down` on both; switch both `node.env` files; `preflight.py --peer`; `stack.py up` on
   both.
5. Re-agreement is automatic: at the first session start the controllers compare their settings
   digest and the workers their manifest, word files and session string; a difference ends the
   session before any request, with the reason in the log.

A change of the database protocol needs all five database nodes and both computation nodes
together. Do not mix circuits of one emitter build with a worker of another (every device
establishment would be refused).

### 6.5 Backup

| What | Where | How |
|---|---|---|
| Contacts' shares and blobs | each database node's Postgres | each operator separately, encrypted, never two nodes' backups in one place (three nodes' data reconstruct keys). Restoring a node to an older state is not supported yet (no repair of a lagging node) |
| Credential share (one per node) | node A, node B | each operator separately; losing one share loses the password (re-registration) |
| `peer.key`, database client key, field-engine keys, bearer | each node | each operator; all can be regenerated (with the other side's cooperation) |
| Account export, deployment hints (scaffolding) | both nodes | as the shares (private keys in the clear) |
| Daemon configuration, image digest, manifest digest | both | version control without secrets |
| Circuit set and word dir | any build machine | keep the produced directory: regenerating takes hours |
| Journals, events.jsonl | each node | not needed after the application has read the events; journals matter only for a notify in flight |

### 6.6 Monitoring and health checks

With the push-button tool: every node runs a health endpoint (`deploy/node/pb_health.py`, port
9100 on its tunnel address and localhost; the firewall admits only the other mesh members). It
exposes, by design, only public status: node and role, unit and container states, image digests,
circuit / word-dir / settings digests and the pre-flight facts (hashes and the agreed settings
text), tunnel handshake ages, disk and memory use, the daemon's `status` reduced to numbers and
yes/no (no ids), the sender certificate's and the field-engine certificates' expiry dates, the
database's last epoch. Never keys, shares, the export's private parts, journals, work files or
contact ids. Each operator's page (port 8088, localhost; `deploy.py monitor` opens an ssh tunnel
to it) shows that operator's nodes; the node named in `[monitoring] combined_page_on` also
serves a page of every node, pulled over the tunnel. Why not Uptime Kuma or Grafana: they need
an account and set-up and cannot show this system's own checks (the two nodes' agreed-settings
digests equal, certificate expiry); the page is one file on the nodes. Prekey replenishment and
signed-prekey rotation are not automated jobs (PRODUCT_TODO.md section 1: open items), so the page
has nothing to show for them yet.

- `stack.py status`: the daemon answers; a receive session is running; requests by state.
- Daemon log: `send session … ready`, `send session memory` (every 10 s), session restarts and
  their reasons, notifies `failed` / `rejected` / `expired`.
- Alerts: daemon not answering; receive session not running for more than a few minutes; send
  session restarted more than a few times an hour; the sender certificate within 48 hours of
  expiry; field-engine certificates within 7 days of expiry; memory near `send_session.max_megabytes`;
  disk; clock not synchronised; WireGuard handshake older than 3 minutes; a database node not
  applying epochs.
- Never alert on, or ship to a monitoring service, anything from 6.2's list.

### 6.7 Capacity

One pair: 0.67 messages/s malicious, 1.25 semi-honest, measured on one machine (1.4); on real
machines the link decides (malicious: 1 Gbit/s gives 0.13 messages/s). The owner's volume (about
1,000,000 messages a month, US daytime) averages 0.77 messages/s with peaks of 4 to 8. Levers, in
order (PERFORMANCE.md): a long-lived release-build database client (about 0.4 s per message), 10
Gbit/s between the nodes, semi-honest mode (8 times less traffic), several pairs (not built:
partitioned ids, one receiving pair; PRODUCT_TODO.md section 7), the preprocessing stock for
spikes (not wired in). A notify of thousands of ids must be split into requests that each start
within 120 s; each loaded contact costs about 0.1 GB until the session ends.

---

## 7. Pre-flight checklist

`deploy/scripts/preflight.py` checks every item marked (P); run it on both nodes with `--export`,
then each with `--peer` on the other's file.

- [ ] (P) Controller, worker, certificate checker, database client present; the worker is a
      production build (not `-test`), mode as intended, identical on both nodes.
- [ ] (P) `circuits.manifest` set; every gate list present, every layout matching (`--full-hash`
      once after copying); the manifest digest identical on both nodes and equal to
      `EXPECTED_MANIFEST_SHA256`.
- [ ] (P) The word dir matches the worker's pins (all 22 V3 programs or none), identical on both.
- [ ] (P) `SIGNAL_SCRIPTS` empty; no TEST hook; no credential in the environment.
- [ ] (P) The agreed-settings digests (send, receive, notify) and the worker session settings
      identical on both nodes; `SIGNAL_CLIENT_PROFILE` equal to the circuit set's profile.
- [ ] (P) Peer key, database client key, bearer token: present, mode 600; each `Player-Data` holds
      exactly this party's key, mode 600; the peer key's fingerprint equal on both.
- [ ] (P) Account state directory (`--account-state`) exists, mode 700 (contents never read).
- [ ] (P) The other daemon's link port and at least four database compute ports reachable; this
      node's ports free; party 0's worker range open to party 1 only.
- [ ] (P) Clock synchronised (`--ntp HOST` for the offset).
- [ ] (P) Memory, cores, disk, CPU flags.
- [ ] Sender certificate valid for more than 48 hours; field-engine certificates for more than 7 days.
- [ ] WireGuard handshakes recent; round trip A to B 1 to 2 ms.
- [ ] Every database node applied a recent epoch.
- [ ] The previous image digest, configuration and circuit directory kept for rollback.
- [ ] For a real endpoint: the owner's explicit go-ahead for this start, and recording on.

## 8. Rollback

1. Keep, for every deployment: the previous image digest, both `node.env`/`node.json` files, the
   previous circuit directory and word dir (their digests are in the old `node.env`).
2. To roll back: drain (6.4 step 3); `stack.py down` on both nodes; restore both nodes' previous
   `node.env` and configuration; `preflight.py --peer`; `stack.py up` on both.
3. Never roll back one node alone (every session would end on a settings or manifest difference,
   which is safe but stops service).
4. Contacts' state written by the newer version stays on the database nodes: a rollback is safe
   only if the stored formats did not change between the versions (check the changes between the
   two commits for `contact-seal`, record layouts and the database client). If they changed, roll
   forward instead.
5. A rollback never touches the account's credential shares or the database nodes' keys.

---

## 9. Files of this tooling

```
DEPLOYMENT.md                      this document
deploy/deploy.py                   THE push-button tool (init, build, plan, join, collect, start, account,
                                   status, monitor, logs, upgrade, destroy, up, testapp, next)
deploy/deployment.example.toml     the shared deployment file, commented
deploy/operator.example.toml       an operator's private file, commented
deploy/.gitignore                  .state/ (tofu state, ssh keys, bundles, logs), the two real files
deploy/pushbutton/                 the tool's Python (standard library only): config, providers, bundles,
                                   tofu, local, tools, flow; test_pushbutton.py (unit checks)
deploy/providers/{hetzner,upcloud,ovh}/{disk,machine}/main.tf   OpenTofu modules (one pair per provider)
deploy/providers/local/machine.Dockerfile   the local provider's stand-in machine (systemd + sshd)
deploy/tools/ansible.Dockerfile    the pinned Ansible the tool runs (no host install)
deploy/ansible/                    playbooks (join, start, account, status, logs, stop, testapp) and roles
                                   (base, datadisk, firewall, software, identity, wireguard, meshfw,
                                   dbnode, mpcnode, health, certrefresh)
deploy/node/pb_node.py             on each node: keys made there, digests, daemon-link key, certificates
deploy/node/pb_health.py           on each node: health endpoint (:9100), monitoring page (:8088), verdicts, logs
deploy/node/pb_certificate.py      on the computation nodes: the sender-certificate timer's check
.dockerignore                      the repository root is never a build context (sends nothing)
deploy/scripts/deploylib.py        shared helpers: manifests, pins, settings digest mirror, redaction
deploy/scripts/preflight.py        pre-flight checks of one node; --export / --peer
deploy/scripts/verify_artifacts.py export / compare the two nodes' artefact digests
deploy/scripts/build_artifacts.py  plan / native / circuits / word / context / image (plan-only without --yes)
deploy/scripts/stack.py            up / down / status (native or compose); status --harness
deploy/scripts/collect_logs.py     redacted logs
deploy/scripts/rehearsal.py        the local two-node rehearsal (containers + local server + local database nodes)
deploy/scripts/selfcheck.py        checks this tooling (compile, --help, examples, redaction, pins)
deploy/docker/worker.Dockerfile    computation-node image (MODE=malicious|semi-honest)
deploy/docker/build_engine_abi.sh  the engine library for node_worker on Linux
deploy/docker/entrypoint.py        the image's start-up checks and commands
deploy/docker/cargo-vendored.toml  offline crate source inside the image
deploy/docker/dbnode.Dockerfile    database-node image (server, pki, handoff_client)
deploy/docker/*.dockerignore       per-Dockerfile ignore files
deploy/compose/rehearsal.yml       the local rehearsal
deploy/compose/node.yml.example    one computation node (A or B), with node-a/node-b .env and .json examples
deploy/compose/db-node.yml.example one database node with its Postgres, with db-node.env.example
```

Every script answers `--help`, prints its plan without `--yes` where it would change anything, and
contacts no Signal host by default (`preflight.py --probe-signal-endpoint` opens one TCP connection
and says so first; `stack.py up` refuses a non-local endpoint without `--i-have-the-go-ahead`).

---

## 10. Proposed changes to existing files

Not made here (another engineer is working in these files); each is small.

1. `node_worker/.cargo/config.toml`, `node_daemon/.cargo/config.toml`,
   `local_signal_server/provision/.cargo/config.toml`: the vendored source is the build machine's
   absolute path (`/Users/…/.deps/libsignal-vendor`). Make it relative to the repository, so
   `node_worker/build.sh` and `node_daemon/build.sh` can be used inside the image instead of the
   Dockerfile's own cargo lines.
2. `handshake_backend/EmpHybridWork/build_hybrid_v3.py --engine-abi` is macOS-only (Homebrew
   paths, `-lc++`, replayed macOS commands). Add a Linux path; `deploy/docker/build_engine_abi.sh`
   is a working description of it.
3. node_worker: the word-circuit directory is compiled in (`NODE_WORKER_WORD_DIR`,
   `EMP_WORD_CIRCUIT_DIR`). Take it at run time (checked against the same pins), so a mount point
   is not fixed by the build.
4. Controller: a `settings-digest` mode that prints `Config.agreedText` and its digest for a given
   session kind, so `preflight.py` can use the controller's own definition instead of its mirror
   (checked equal on 9 cases today).
5. Daemon: set `SIGNAL_RECORD` per session (one file per session and party) instead of relying on
   one `environment` value for every session; rotate its logs; persist requests and results.
6. Daemon: mutually authenticated TLS (or signed replies) on the application link and the daemon
   link; per-node keys (PRODUCT_TODO.md section 7).
7. secret-shared-db `pki`: each node makes its own keys; the network configuration assembled from
   public parts (PRODUCT_TODO.md section 9).
8. `deployment/vm_pair_test/bench_certs.sh`: certificate lifetime as a parameter (30 days today)
   and a command that prints the expiry, for monitoring.
9. `deployment/vm_pair_test/make_bundle.py`: an option that adds node_worker's engine library
   sources (`engine-abi-*.d`), so the bundle alone can build it (the context adds them from the
   repository today).
10. The field engine (MP-SPDZ) binds its listeners to all interfaces: bind `TLS_WORKER_LISTEN`.
11. Reproducible builds: `SOURCE_DATE_EPOCH`, `--remap-path-prefix` for Rust, fixed build paths,
    so two operators building independently get identical binaries and need not trust one build.
12. `real_signal/deployment-production.json` and `local_signal_server/deployment*.json`: the
    settings STACK_NOTES.md 11.3 item 2 lists (send class 3, ceremony, zero-digit bundle slots,
    `tls-seal-class 896`, the signup chains), then regenerate the sets instead of appending.
13. The daemon accepts texts of 1 to 256 bytes; the product decision is at least 200 bytes and
    NEEDS_REVIEW.md 3f item 7 fails closed below that: refuse shorter texts at the daemon (or fix
    `bundle-seal` and regenerate).
14. A release-build, long-lived database client (PERFORMANCE.md: about 0.4 s per message).
15. **P-CERT, the joint sender-certificate refresh** (the push-button path needs it; its timer is
    wired to a TODO entry point, `deploy/node/pb_certificate.py` `refresh()`). Today nothing
    refreshes the certificate in a way a session would use: sessions take it from the account's
    row on the database nodes (`Start.lean` 74-81) and no code rewrites that row once it exists
    (`Start.lean` 160-167, create-if-missing only). The ceremony's `certificate` stage is not a
    safe substitute: it re-uploads the one-time prekeys (`Ceremony.lean` 254-257), needs the
    registration's credentials share (deleted after the account step), uses port_base+140, which
    overlaps the daemon's send sessions at +40k, displaces the receive session's socket (4409), and
    writes the certificate to a side file no session reads. Proposed: a daemon job kind
    (`{"op":"refresh-certificate"}`, party 0 leads over peer-start, or inside the receive session as
    PRODUCT_TODO.md section 7 intends) that opens the authenticated socket from the row's
    credentials, does only `GET /v1/certificate/delivery?includeE164=false`, requires the
    deployment's certificate length (circuits exist only for it), re-seals and rewrites the row (a
    versioned overwrite in the database client), updates the export's `certificate_hex` /
    `certificate_expires_ms` while the export is still read, uses its own port block, and ends the
    long-lived send session so it reloads. Then `refresh()` becomes one request to the local daemon.
16. secret-shared-db `pki`, non-local mode: the peer and sync ports in `network-config.json`
    (8000, 10001) differ from what each node's `config.json` binds (8002+i, 10002+i), and the
    WireGuard files' ListenPort/Endpoint disagree; `-d` copies the Postgres password into the shared
    network configuration. The push-button path does not use `pki`'s layout: each database node
    runs a throwaway `pki` on its own machine and keeps only its own seed (public keys derived
    from it), and `deploy.py` assembles the network configuration from the public parts with
    one port per role (worked around; the fix belongs in `pki`, with change 7).
17. Daemon `status`: add the time of the last successful send and receive (numbers only), so the
    monitoring page can show them; today it shows the counts `status` returns.
18. A refresh of the field engine's 30-day certificates without a restart (with change 8):
    today the page shows their expiry and renewing means `certs init`/`trust` again on both nodes
    and new bundles (a new fingerprint).

19. secret-shared-db `server`: it dials its peers once, 10 s after it starts, and never again
    ("Client N not connected, skipping" for ever). Found by the push-button test: database nodes
    started minutes apart by different operators never connected, no epoch reached consensus
    (an epoch needs threshold + max_malicious = 4 signatures), and every receive session then
    failed while loading the account ("operation 8 local abort"). Proposed: reconnect to peers
    with back-off. Worked around in the tooling: each database node's start waits (up to 30
    minutes) until every other database node is waiting or running, then all start at the same
    30-second boundary (`pb_health.py db-barrier`). A node restarted alone later (reboot,
    upgrade) still depends on whether its peers reconnect to it: not tested.

Which of these the push-button path depends on: 19 (database peers reconnecting; worked around
for a coordinated start only), 15 (certificate refresh: the timer only alerts until it exists)
and 8/18 (field-engine certificates expire after 30 days: the page warns 7
days ahead; renewal is manual). Worked around in the tooling: 3 (the word dir is mounted at the
compiled-in path), 4 (the settings-digest mirror), 7 and 16 (per-node database keys), 10 (the
field engine's ports are closed by the per-sender firewall on the tunnel). Needed for the
`each-operator` build mode to compare binaries: 11.

---

## 11. Open questions for the owner

1. Who operates node B, and node A: two separate legal entities? Which providers (Helsinki and
   Tallinn are the decided locations)?
2. Who operates the five database nodes, at which providers; may a computation node's provider
   host one (and how many)? `max_malicious` 1 or 2?
3. Where does the application server run, who holds the notify and signup keys, and how does it
   reach the two daemons (WireGuard into both)?
4. Is WireGuard the only authentication between the nodes, or do the daemon link, the Boolean
   engine's channels and the application link get mutually authenticated TLS (0.2 item 3)?
5. Secrets management: files on the nodes as today, or a key store; who generates the shared
   `peer.key`; where the credential shares are backed up.
6. Images: one builder whose image both operators run, or independent builds compared
   (proposed change 11)?
7. Malicious (default) or semi-honest in production, given the traffic (about 1 PB each way per
   million messages in malicious mode)?
8. The sender-certificate refresh every 7 days: who does it, until the two-party client can.
9. `SIGNAL_RECORD` in production: always (the "record everything" rule of the real tests) or only
   for the first runs; retention of records and logs.
10. A monitoring stack, and who is alerted.
11. Release of the first deployment: after the two-machine test (`deployment/vm_pair_test`),
    after the next real-service run, or both?
12. Push-button tool: who is the coordinator and who builds the images (one builder whose images
    everyone runs, or each operator building from the agreed commit, which cannot be compared
    binary for binary until builds are reproducible)?
13. The research's cheapest computation pair is dedicated or VPS machines (Hetzner AX102, OVH
    VPS-6), which no OpenTofu module creates: deploy those with `provider = "existing"` after
    ordering them, or prefer cloud VMs (`hetzner`, `upcloud`, `ovh` Public Cloud) for push-button
    creation?
14. Monitoring: the per-operator page and an optional combined page exist; nobody is alerted. Is
    a page enough, or should failures send mail / a push notification (to whom)?
15. Until the joint certificate refresh (proposed change 15) exists, the timer only alerts: who
    refreshes by hand every 7 days, and is building P-CERT the next priority?
16. The application server must join the tunnel mesh (its WireGuard key in deployment.toml): who
    operates it and does it need to reach the database nodes too (today: only the two daemons)?

---

## 12. Build attempts on this machine (2026-11-13)

Docker 29.4 under OrbStack, linux/arm64, 12 CPUs and 16.8 GB for the VM. Every build ran under
`scripts/guarded.py --heavy` (queued behind the timing runs of the same afternoon). Logs:
`.deps/deploy-logs/`.

| Attempt | What | Result |
|---|---|---|
| 1 | `--target engines` | **passed** (388 s, mostly packages): `build_linux.sh --portable` built emp-tool, emp-ot, libOTe, the field engine's library, both field engine objects, the benchmark fixtures and both C++ workers; `build_engine_abi.sh` built `libengine-abi-v3.a` and `libengine-abi-sh-v3.a`: the first Linux build of node_worker's engine library |
| 2 | full image | node_worker link failed: `__stack_chk_guard` (SimplestOT, glibc's dynamic loader on aarch64): rustc's `-lc` comes before the link arguments. Fixed: `-lm -lc` at the end |
| 3 | full image | the Lean controller built (`lake build public_service_controller`, 546 jobs, 152 s with 4 jobs); node_worker link failed on `__aarch64_cas4_acq_rel` (libgcc's outline atomics). Fixed: `-lgcc` at the end |
| 4 | full image | node_worker linked; node_daemon failed offline on libsignal's git dependency SparsePostQuantumRatchet. Fixed: the image's cargo configuration replaces the two git sources as the provisioning tool's own does |
| 5 | full image | node_daemon built; lss-provision failed: its `#[path]` module `signal_backend/Oracle/src/session_send_projection.rs` was not staged. Fixed in `build_artifacts.py context` |
| 6 | full image | **built** (299 MB). `version` lists every binary's hash; uid 10001; the entry point refuses to start without a configuration. But node-worker could not load `libSPDZ.so`: linked by path, the build tree's path was recorded (the library has no SONAME). Fixed: linked by name, found through the rpath |
| 7 | full image | **built**; `ldd` finds every library; node-worker, node-daemon, notify-app, handoff_client, the controller and lss-provision all start and print their usage |

Image `tls-mpc-node:malicious` (context commit 5cce36f): node-worker `9de0c2a7…`, controller
`67ab4655…`, node-daemon `d216d2ba…`, handoff_client `2d5cd8ea…`, public_auth `7605d08c…`,
libSPDZ.so `1089a2f7…`. These Linux binaries are not the macOS build machine's (different
platform): compare images with images.

**The local rehearsal passed** (`python3 scripts/guarded.py --heavy 24 2400 python3
deploy/scripts/rehearsal.py --yes`, malicious, 204 s, report in
`.deps/deploy-rehearsal/report.json`): the local Signal-Server and five real database nodes
(Postgres, 20 s epochs) on the host; the account's row by the harness's native fixture session
(3.9 s); then both computation nodes as containers of `tls-mpc-node:malicious` on a private
bridge network (172.29.0.10 and .11, `TLS_WORKER_PEER`/`TLS_WORKER_LISTEN` set, each worker's
field-engine key made by `bench_certs.sh` in its own directory, only certificates exchanged),
strict mode with the local 464-kernel set, the word dir mounted at the compiled-in path. Both
entry points printed the same manifest, word-dir and settings digests (serve `b7cd68aa…`,
receive `3c52888d…`: the same as the native harness daemons'), both daemons answered `status`
3 s after `docker compose up`, the long-lived send session was ready 12 s after start; a new local
user signed up with the application's token and both daemons reported the id (26 s); a notify of
a 200-byte text to that id was agreed `delivered` by both daemons and the user decrypted it from
an envelope without source fields (64 s, including a database epoch). Containers, database
nodes and server were stopped at the end. What this is not: two machines, a real link, x86-64,
WireGuard, or Signal's service.

Not run here: the database node image as a node; `compose/*.example` (placeholders; split
deployment); `stack.py up/down/status`; `build_artifacts.py native`, `circuits` and `word`.

**Semi-honest**: `tls-mpc-node:semi-honest` built from the same context (250 s with the shared
stages cached; 299 MB; node-worker `2cc5207c…`, every other binary identical to the malicious
image's), and **the same rehearsal passed in semi-honest mode** (`rehearsal.py --mode
semi-honest`, 159 s: signup reported by both daemons, the 200-byte text delivered, agreed and
decrypted from a sealed envelope).

**Database node image**: `dbnode.Dockerfile` failed once (with `--bin` filters, cargo built no
`pki`; fixed: `--bin pki` too), then **built** (156 MB, uid 10002, the database checkout's
crates fetched with `--locked`, 1 min 46 s of compilation): `server`, `pki` and `handoff_client`
start and print their usage. **Not run as a database node** (no Postgres container, no network
of five containers): the rehearsal used the harness's native database nodes.
