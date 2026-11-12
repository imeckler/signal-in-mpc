# Two cheap rented machines: test kit and plan

The two computation nodes have only ever run on one macOS machine over 127.0.0.1. This kit
measures whether a pair of cheap rented Linux virtual machines at two different providers can
carry the work, before anything is committed. You rent the two machines; the kit does the rest.
Nothing here creates an account, rents anything or contacts a provider.

Read first: `PERFORMANCE.md` (what a message costs), `deployment/PROVIDERS.md` and
`deployment/PROVIDERS_CHEAP.md` (candidates, and what could not be verified from outside).

Contents of this directory:

| File | What it does | Where it runs |
|---|---|---|
| `make_bundle.py` | assembles the source bundle (sources, engines, pinned circuits; no keys) | build machine (macOS) |
| `build_linux.sh` | builds the benchmark on Linux from the bundle | both rented machines |
| `selftest.sh` | one-machine check of the build | both rented machines |
| `net/wg_setup.sh` | WireGuard between the two machines | both, as root |
| `net/machine_check.py` | CPU, memory, disk; 30-minute all-core load with steal time | both |
| `net/rtt_log.py` | round-trip time over hours | machine a |
| `net/iperf_run.py` | iperf3 in both directions, logged per second | a (client), b (server) |
| `net/volume_test.py` | N GB each way with the rate over time | a (run), b (serve) |
| `net/sysmon.py` | steal time, memory, tunnel counters during the benchmark | both (started by `run_pair.sh`) |
| `bench_certs.sh` | the field engine's certificates, each key made on its own machine | both |
| `run_pair.sh`, `run_bench.py` | one party's side of the benchmark | both |
| `collect.py` | both machines' logs into one report with pass/fail | anywhere with Python 3 |

Everything except `build_linux.sh --packages` and `wg_setup.sh` runs without root. The network
and machine tests need none of our software: Python 3, `ping`, `iperf3`, `wireguard-tools`.

## 1. What the test answers

1. **Per-message time and throughput of one worker pair, in each security mode, over the real
   link.** `run_pair.sh` stage 1: N messages per mode, each the per-message field program and
   the eight per-message circuits (2.65M AND gates, 638 field products), triple stocks on.
2. **Is the smaller machine's CPU throttled under sustained load?** `machine_check.py load`
   (30 minutes, all cores, a fixed benchmark's rate and steal time once a minute), and
   `sysmon.py` beside the benchmark; the benchmark's own per-message time, early against late.
3. **Sustained throughput in each direction, and does either provider throttle after a large
   volume?** `iperf_run.py` (five tests of 30 minutes) and `volume_test.py` (200 GB each way).
4. **Round-trip time and its tail over hours.** `rtt_log.py`, summarised per hour.
5. **Memory actually needed per party.** Largest process per pair, and the machine's lowest
   available memory during the run.
6. **How throughput scales with a second worker pair on the same machines.** `run_pair.sh`
   stage 2.
7. **The round-bound operations over the real round trip**: a contact's first-send preparation
   (about 2,800 sequential rounds) and the field programs of a first message received (about
   11,500), with the default programs and with the constant-depth ones (`TLS_WORKER_HINTED=1`).

## 2. What to rent

Two machines at two different providers, x86-64, **Ubuntu 24.04 LTS**, one public IPv4 address
each. Requirements, from what was measured here:

- **CPU**: must expose `aes`, `pclmulqdq` and `avx2` to the guest (`machine_check.py info`
  prints them). Without AVX the field engine does not compile at all (seen in an emulated
  x86-64 container here). One worker pair keeps about 8 to 10 threads busy (four for the Boolean
  session, two AND-triple factories of two threads each, two field generator lines), so
  **8 vCPU is the least that makes sense for one pair; 16 for two**.
- **Memory**: the benchmark's largest process was 3.8 GB per party on macOS and 2.8 GB on
  Linux (one pair, malicious); the real worker loads more circuits. **16 GB for one pair,
  32 GB or more for two.**
- **Disk**: 20 GB is plenty (the archive is 72 MB, unpacks to 0.3 GB, and is 0.65 GB after the build).

Sizes from the provider reports (prices excluding VAT, as read on 11 November 2026; "not
verified" items are marked there). Pick one per side.

| Side | Option | Size | Billing | Price | 3-hour test | 24-hour test |
|---|---|---|---|---|---|---|
| A: Hetzner Cloud, Helsinki | CCX43 | 16 dedicated vCPU, 64 GB | hourly | €0.3766/hour | €1.13 | €9.04 |
| A | CPX42 | 8 shared vCPU, 16 GB | hourly, capped at €59.49/month | about €0.10/hour (the hourly figure was not read from the page; it is the monthly price in Hetzner's usual ratio) | about €0.30 | about €2.30 |
| A | CX43 | 8 shared vCPU, 16 GB | hourly, capped at €16.49/month | was "currently unavailable" | cents | under €1 |
| B: OVHcloud public cloud, Strasbourg | b3-64 | 16 vCores, 64 GB, 4 Gbit/s not guaranteed | hourly | €0.4092/hour | €1.23 | €9.82 |
| B: OVHcloud VPS, Strasbourg | VPS-4 or VPS-5 (2026 range) | 12 vCores, 48 GB, or 16 vCores, 64 GB; shared cores | monthly | €36.99 or €54.99 | a month's price | a month's price |
| B: WaveCom, Tallinn | KVM VPS built to order | 8 vCPU, 16 GB, 80 GB, or 16 vCPU, 32 GB | not stated (assume monthly) | €8 + €3 per vCPU + €2 per GB + €0.10 per GB of disk: €72, or €128 | a month's price | a month's price |
| B: Infomaniak, Geneva | a16-ram64 | 16 vCPU, 64 GB | hourly | about €0.081/hour plus a disk (third-party figure, not verified) | about €0.25 | about €2 |

**Recommended.** Side A: a Hetzner Cloud **CCX43** in Helsinki, and beside it for the CPU
question a **CPX42** (shared cores) for the same hours: both hourly. Side B: whichever
provider you would actually use. If that is Tallinn, a **WaveCom VPS with 16 vCPU and 32 GB**
(about €128 for the month; ask about traffic terms when ordering, their page states none). For a
first look that costs almost nothing, an **OVHcloud b3-64** by the hour.

Expected cost: **a 3-hour test on two hourly machines is about €2.50, a 24-hour test about
€19**. With a monthly-billed machine on side B it is that machine's month (€37 to €128) plus
the Hetzner hours. Traffic: the full plan moves about 1.5 TB each way (iperf3 at 1 Gbit/s is
225 GB per 30-minute test). Hetzner Cloud includes 20 TB or more outbound; check side B's
terms before the volume test, and shorten the tests (`--seconds`, `--gb`) if it meters.

Hetzner says of its cloud network "you can expect about 300-500 Mbits". If the CCX43 shows
that, it is the cloud product, not the dedicated server with a 10 Gbit/s uplink.

### Ports

- **Provider firewall, both machines**: inbound UDP 51820 from the other machine's public
  address (WireGuard); inbound TCP 22 from your own address. Nothing else.
- **Inside the tunnel** (no public port): TCP 5201 (iperf3), 5301 (volume test), 26000 to 26799
  (benchmark; party 0 listens, party 1 dials), 27000 to 27199 on loopback (`selftest.sh`).
- The Boolean engine's listener binds the tunnel address you give it. The field engine's
  library binds its listeners to all interfaces and has no setting for that (its connections
  are TLS with the two certificates of `bench_certs.sh`). So also close the machine itself:

      sudo ufw default deny incoming
      sudo ufw allow 22/tcp
      sudo ufw allow from OTHER_PUBLIC_IP to any port 51820 proto udp
      sudo ufw allow in on vmpair
      sudo ufw enable

## 3. Step by step

Machine **a** runs party 0 (it listens) and drives the network tests; machine **b** runs
party 1. Tunnel addresses: a = 10.77.0.1, b = 10.77.0.2.

### 3.1 On the build machine, before renting

    python3 scripts/guarded.py 16 2400 python3 handshake_backend/EmpHybridWork/build_hybrid_v3.py pair-bench pair-bench-sh rounds rounds-sh
    python3 scripts/guarded.py 12 3600 python3 deployment/vm_pair_test/make_bundle.py

The first command writes the compiler's dependency records the bundle is assembled from. The
second writes `.deps/vm-pair-bundle/vm-pair-bundle.tar.gz` and prints its SHA-256. See
"The bundle" below for exactly what is in it.

### 3.2 Rent, log in, copy

Rent the two machines (section 2). Copy the archive to both and unpack it in the home
directory:

    scp .deps/vm-pair-bundle/vm-pair-bundle.tar.gz USER@MACHINE:
    ssh USER@MACHINE 'tar xzf vm-pair-bundle.tar.gz && cd vm-pair && sha256sum -c --quiet MANIFEST.sha256'

### 3.3 Packages and build (both machines; the build took 3 minutes on six cores here)

    sh vm-pair/kit/build_linux.sh --packages
    sh vm-pair/kit/selftest.sh

`--packages` installs with apt: build-essential clang cmake make git python3 pkg-config
ca-certificates openssl libssl-dev libsodium-dev libgmp-dev libboost-dev
libboost-filesystem-dev libboost-iostreams-dev libboost-thread-dev libboost-system-dev
wireguard-tools iproute2 iputils-ping iperf3 mtr-tiny sysstat procps. `selftest.sh` runs both
parties on the one machine over loopback (needs about 8 GB free). If the build fails, see
"Building on Linux".

### 3.4 Machine checks (both machines, 35 minutes, can run at the same time on both)

    mkdir -p vm-pair/logs && cd vm-pair/logs
    python3 ../kit/net/machine_check.py info --out machine.json
    python3 ../kit/net/machine_check.py load --minutes 30 --out cpu-load.csv

### 3.5 WireGuard

On each machine, as root:

    sh vm-pair/kit/net/wg_setup.sh keygen            # prints this machine's PUBLIC key

Exchange the two public keys and public addresses by any channel, then:

    sh vm-pair/kit/net/wg_setup.sh up a B_PUBLIC_KEY B_PUBLIC_IP     # on machine a
    sh vm-pair/kit/net/wg_setup.sh up b A_PUBLIC_KEY A_PUBLIC_IP     # on machine b
    ping -c 3 10.77.0.2                                              # from a

Record the path once, from a: `mtr -rwzc 100 B_PUBLIC_IP > vm-pair/logs/mtr.txt`.

### 3.6 Network tests (driven from machine a)

Round-trip time, for the whole test, in the background on a:

    cd vm-pair/logs && nohup python3 ../kit/net/rtt_log.py run 10.77.0.2 --hours 24 --out rtt.csv &

iperf3: server on b, client on a (2.5 hours; `--seconds 600` for the 3-hour test):

    python3 vm-pair/kit/net/iperf_run.py server 10.77.0.2                                     # on b, leave running
    cd vm-pair/logs && python3 ../kit/net/iperf_run.py client 10.77.0.2 --bind 10.77.0.1 --logs .   # on a

Volume, 200 GB each way (`--gb 50` for the 3-hour test):

    python3 vm-pair/kit/net/volume_test.py serve 10.77.0.2                                    # on b, leave running
    cd vm-pair/logs && python3 ../kit/net/volume_test.py run 10.77.0.2 --bind 10.77.0.1 --gb 200 --out volume.csv   # on a

Do not run iperf3, the volume test and the benchmark at the same time: each wants the whole
link. The ping log may run beside all of them (its tail then also shows what load does to it).
After the volume test look at both providers' traffic graphs, invoice previews and mailboxes.

### 3.7 Our software across the two machines

Certificates for the field engine (each key is made on its own machine; only the `.pem`
certificates cross):

    sh vm-pair/kit/bench_certs.sh init 0 vm-pair/work        # on a; prints the path of P0.pem
    sh vm-pair/kit/bench_certs.sh init 1 vm-pair/work        # on b; prints the path of P1.pem
    # copy P0.pem to b and P1.pem to a (scp), then:
    sh vm-pair/kit/bench_certs.sh trust P1.pem vm-pair/work  # on a
    sh vm-pair/kit/bench_certs.sh trust P0.pem vm-pair/work  # on b

The benchmark: start party 0 first, party 1 within a minute. 100 messages per mode by default
(for the 24-hour test pass 2000 as the last argument on both sides: several hours in malicious
mode on a slow link, which is the sustained-load evidence).

    sh vm-pair/kit/run_pair.sh 0 10.77.0.2 10.77.0.1        # on a (party 0; listens on its tunnel address)
    sh vm-pair/kit/run_pair.sh 1 10.77.0.1 -                # on b (party 1; dials)

Each side prints one line per step, for example
`[pair 0] bench malicious: ok in 25.3 s  0.907 s/message (median), 2.65M AND, 638 products, sent 0.777 GB/message`.
To try other settings use `run_bench.py` directly (`--help`): `--triple-stock 4,524288,4194304`
gives the Boolean engine four AND-triple factories instead of two, which `PERFORMANCE.md`
expects to matter on machines with cores to spare; both sides must pass the same value.

### 3.8 Collect

Copy `vm-pair/logs/` from each machine to one place (`logs-a/`, `logs-b/`), then, with the
monthly price of each machine:

    python3 deployment/vm_pair_test/collect.py --a logs-a --b logs-b --eur-month-a 234.99 --eur-month-b 128 --out report.md

`--eur-per-tb-a` / `--eur-per-tb-b` add a metered traffic price.

### 3.9 Tear down

1. On both machines, as root: `sh vm-pair/kit/net/wg_setup.sh down` (removes the tunnel, its
   configuration and the key).
2. Copy off `vm-pair/logs/` if you have not. Nothing else on the machines is worth keeping; the
   certificates' keys in `vm-pair/work/Player-Data/` are test keys and go with the machine.
3. Delete both servers in the providers' consoles, and what does not go with them: volumes,
   snapshots and backups, extra IP addresses, firewall rules, SSH keys you uploaded for this.
4. For a monthly-billed machine, cancel it so that it does not renew.
5. A day later, check both invoices and mailboxes for traffic charges or notices.

## 4. Pass criteria: "a cheap pair is good enough"

The thresholds are the constants at the top of `collect.py`. The stability criteria follow
`PROVIDERS_CHEAP.md` section 8. **The two throughput floors are a proposal, not a requirement
anyone has stated: change them to the demand you have.**

Both modes:

| Criterion | Threshold |
|---|---|
| CPU features | `aes`, `pclmulqdq`, `avx2` on both machines |
| CPU keeps its speed | over the 30-minute load: lowest minute at least 90 % of the first; steal median at most 2 %, worst minute at most 5 % |
| No steal during the benchmark | steal median at most 2 %, 95th percentile at most 5 % |
| Round-trip time is steady | in at least 95 % of the hours the 99th percentile is within 1.5 times that hour's median; loss at most 0.01 % |
| No throttle after volume | each direction: last tenth of the transfer at least 80 % of the first tenth; slowest minute at least half the mean; no notice or charge |
| Memory | at least 2 GB stayed available on each machine through the run |
| Round-bound operations | first-send preparation and the receive sequence's field programs each within 60 s (the Signal server drops an idle connection after 90 s) |
| No upward drift | late median per-message time at most 1.25 times the early median (needs 50 messages or more) |

Per mode:

| | Malicious | Semi-honest |
|---|---|---|
| Per-message time, one pair, median | at most **15 s** (240 messages an hour) | at most **3 s** (1,200 an hour) |
| Sustained iperf3 throughput | at least **400 Mbit/s each way at once** (`both-4`), no step down | at least **250 Mbit/s in the better direction**, no step down |

Where the floors come from. A malicious-mode message moves about 1.5 GB, half each way:
6 Gbit each way, so at B Mbit/s each way the link alone takes 6000 / B seconds. Hetzner's own
expectation for its cloud network (300 to 500 Mbit/s) gives 12 to 20 s; 400 Mbit/s gives 15 s.
A semi-honest message moves about 0.09 GB, almost all from the garbling party (party 0):
0.72 Gbit, 2.9 s at 250 Mbit/s. On this machine the engines need about 0.9 s (malicious) and
0.1 s (semi-honest) per message, so on any realistic cheap link malicious mode is bound by the
network and semi-honest mode by whichever is slower.

The arithmetic `collect.py` prints:

    messages per hour  = 3600 / (median seconds per message)      x the measured two-pair ratio, for two pairs
    machines, EUR per 1,000 messages = (price_a + price_b per month) / 730 / messages per hour x 1,000
    metered traffic, EUR per 1,000   = GB sent per message x EUR per TB        (each side with its own price)
    TB per month at full use         = messages per hour x 730 x GB per message / 1,000

Example with the local figures and a €363 pair (CCX43 + WaveCom 16 vCPU): malicious at 15 s is
240 an hour, 175,000 a month at full use, €2.07 per 1,000 messages, and 131 TB a month sent by
each side, which no allowance in the reports covers: at full use the traffic terms, not the
machines, decide. Semi-honest at 3 s is 1,200 an hour, €0.41 per 1,000, 79 TB a month from the
garbling side. A pair that is idle most of the month costs proportionally more per message.

For the round-bound operations the rule of thumb is rounds x round trip: at 2.1 ms, 2,800
rounds are 6 s and 11,500 are 24 s; at 6.5 ms, 18 s and 75 s. The benchmark measures it
rather than assuming it, including the constant-depth programs (a few dozen rounds).

## 5. The worker setting this needed

The workers assumed the other party at 127.0.0.1 in two places: the Boolean engine's channel
(and through it every sibling channel: the engine's second channel and the AND-triple
factories' channels), and the field engine's player names (and through them its triple-stock
lines). There is no other socket between the two workers; the controllers do not talk to each
other. New, in `handshake_backend/EmpHybridWork/peer_link.h`, used by `tls_worker_v3.cpp`,
`rounds_fixture.cpp` and the benchmark:

- `TLS_WORKER_PEER=A.B.C.D`: the other worker's address. Unset or 127.0.0.1: exactly as
  before. Set it on both workers: party 1 dials it; on both it switches the field engine to its
  direct connection (party 0 listens on PORT+10, party 1 dials the peer there), which both
  must use alike.
- `TLS_WORKER_LISTEN=A.B.C.D`: the address party 0's Boolean listener binds. Unset: all
  interfaces, as before. The field engine's listeners cannot be restricted (above).
- A value that is not a numeric IPv4 address is refused rather than falling back to localhost.
  When either is set the worker logs `tls-worker-v3 peer=... listen=...`.

Party 0 listens for everything and nothing dials party 1, so only machine a needs to accept
connections from b.

## 6. The bundle

`make_bundle.py` writes `vm-pair/` with:

- `repo/`: our sources the four benchmark binaries are compiled from, taken from the compiler's
  dependency records: `pair_bench_fixture.cpp`, `rounds_fixture.cpp`, `field_engine.cpp` and
  the 14 headers of `handshake_backend/EmpHybridWork/` they include.
- `pins/word/`, `pins/curve/`: the pinned Lean field programs and small circuits (`.flat`,
  each under 2 MB) and the pin headers, from `.deps/emp-hybrid-word-v1` and
  `.deps/emp-hybrid-curve-v1`.
- `engines/`: `emp-tool` and `emp-ot` source trees, the 13 headers of the validated-v3 Boolean
  engine, and the field engine's library source (MP-SPDZ at commit 113c4e4 with
  `deps/SimplestOT_C`, `deps/simde`, `deps/sse2neon`, `deps/libOTe2` and the three trees
  libOTe's build cloned: coproto, macoro, function2, at their pinned commits, without git
  history). Its `CONFIG` is the tree's with the macOS-only last block removed.
- `circuits/`: eight gate lists and `circuits.list` with their SHA-256 pins (below).
- `kit/`: this directory.
- `MANIFEST.sha256`.

It contains no keys, test accounts, exports, logs or state. Never copied: any `Player-Data/`
(the local test certificates and keys), `.git`, logs, build products, the upstream libraries'
own test certificates (`cert/`, `certs/`). The script stops if any file it is about to copy has
a key, certificate, database, log or environment-file extension, a name with words such as
secret, password, credential, export, account or state (for anything that is not program
source), or contains a PEM private key. `--with-workers` adds the two workers' sources so that
`build_linux.sh` also builds them; they include
`signal_backend/TextNotificationWork/PublicTextFixture.h`, hex records of a throwaway test
conversation marked "PUBLIC DISPOSABLE FIXTURES ONLY". That is why it is off by default.

The circuits, and how they are produced. Each is written by the Lean executable
`flat_kernel_emitter` (no hand-built gate logic), through
`handshake_backend/EmpHybridWork/circuit_cache.py kernel NAME ARGUMENTS`, which `make_bundle.py`
calls for each (they come from its cache when already there; all eight were):

| Kernel | AND gates | File |
|---|---|---|
| `signal-widths 244` | 444 | `kernel-signal-widths-244.flat` |
| `signal-seal-built 244 1 1 1 1 1` (the send circuit, smallest size class) | 2,183,965 | `kernel-signal-seal-built-244-1-1-1-1-1.flat` (194 MB) |
| `signal-request-ctr 244 1000 33 976 797 829` (request frame and its record) | 313,825 | `kernel-signal-request-ctr-244-1000-33-976-797-829.flat` |
| `gcm-tag` | 0 | `kernel-gcm-tag.flat` |
| `gcm-check` | 6,426 | `kernel-gcm-check.flat` |
| `tls-open-typed 160` (the response record) | 52,961 | `kernel-tls-open-typed-160.flat` |
| `tls-reveal-masked 139` | 1,929 | `kernel-tls-reveal-masked-139.flat` |
| `contact-seal 314` (storing the contact's state) | 91,781 | `kernel-contact-seal-314.flat` |
| **Per message** | **2,651,331** | |

To produce one by hand: `python3 handshake_backend/EmpHybridWork/circuit_cache.py kernel signal-seal-built 244 1 1 1 1 1`
prints the path of the gate list and its SHA-256.

## 7. What the benchmark is, exactly

`handshake_backend/EmpHybridWork/pair_bench_fixture.cpp` (built as `pair-bench` and
`pair-bench-sh` by `build_hybrid_v3.py`). It drives the same layers as the worker and adds no
engine code: `DynSession` (malicious statistical 128, or the semi-honest build) with its
AND-triple stock, the field engine with its triple stock, the pinned circuits and programs.

- Before the messages: one contact's first-send preparation as the worker does it by default
  (the offset agreement's `prepare` program, then the long-term agreement by the ladder).
- One iteration: the per-message field program (the offset agreement's sum: 638 products, 23
  multiplication rounds and 9 openings, one of the openings being the fixture's own check of
  the result against X25519), then each of the eight circuits once on private all-zero inputs
  from party 0, opening the first output byte. A circuit's cost does not depend on its inputs.
- Not in an iteration: the conversion of the agreement into the Boolean engine, the openings
  and exchanges between circuits in the real sequence, the controllers, the Signal server's
  response. So it is the engines' share of a message, and a lower bound on the real time.
- It reports per iteration: seconds (field and Boolean parts), AND gates, field products,
  rounds, and bytes sent by this party in each engine (triple stocks included). Each party
  logs its own side; `collect.py` puts them together.

The rounds fixture (`rounds_fixture.cpp`, already in the tree) supplies the other two steps:
`prepare 1` (a contact's first send with both program families) and `receive 1` (the field
programs of a first message received, both families, checked equal).

## 8. Building on Linux

`build_linux.sh` does, in order: emp-tool and emp-ot with CMake into `vm-pair/install`; the
field engine's library with its own Makefile (`libSPDZ.so`, six OT objects, SimplestOT, libOTe)
after writing its `CONFIG.mine` (compiler, `-march=native`, no AVX base OT, SoftSpoken OT
through libOTe 2, as on the build machine); our `field_engine.cpp` at statistical 128 in both
modes; the fixtures. The flags are those of `build_hybrid_v3.py` and the recorded field build,
with Homebrew paths replaced by the distribution's packages and `-mcpu=native` by what
emp-tool's own CMake chooses for the machine.

### What was verified on the build machine (11 and 12 November 2026)

| What | How | Result |
|---|---|---|
| Default still works (no setting) | both workers rebuilt; one harness session, `check_signal_service_local.py semi-honest --runs 1` | passed |
| The worker with the peer setting | `check_tls_worker_v3.py` (two controllers, two workers, a full TLS 1.3 handshake against a local OpenSSL server; no Signal server), with `TLS_WORKER_PEER` and `TLS_WORKER_LISTEN` set to this machine's non-loopback address, malicious and semi-honest | passed in both; both workers logged the peer and listen address |
| The benchmark and the rounds fixture with the peer setting | both parties on this machine through `bench_certs.sh` and `run_bench.py`, peer and listen address non-loopback, all three steps, both modes | passed |
| Linux build, arm64 | Ubuntu 24.04 container (clang 18.1.3, 6 CPUs, 12 GB): `build_linux.sh --packages --portable` from a bundle with the workers, then `selftest.sh`; and again from the final default archive (unpacked, manifest checked, built, self-tested) | all six binaries built (the two workers included); self-test passed in both modes both times |
| Linux build, x86-64 | the same container image for x86-64 under emulation: `build_linux.sh --packages`, then `--portable` | with `--portable` everything **compiled and linked**, the workers included. **Nothing was run**: the emulator has no AVX |
| The kit's scripts on Linux | machine check, ping log, iperf3 (five tests of 25 s), volume test (30 GB each way), `run_pair.sh` (both stages, 6 messages), `collect.py`, in the arm64 container over loopback | all ran and the report was produced; its verdicts mean nothing at those durations (it correctly marks the short tests as failed or not run) |

Local benchmark figures (macOS, 12 cores shared with other work, both parties on the one
machine, loopback): malicious 0.85 to 0.91 s per message, 0.78 GB sent by party 0 and 0.69 GB
by party 1 per message; semi-honest 0.14 s, 0.10 GB and 0.015 GB; first-send preparation 1.1 s
(2,306 multiplication rounds and 486 openings); largest process 3.8 GB. In the arm64
container (6 CPUs, portable flags): malicious 1.85 s, semi-honest 0.19 s, largest process
2.85 GB; field triples were made about four times slower than on macOS, the rounds themselves
no slower.

### What is not tested

- **Any run on x86-64.** The build is proved to compile and link there, not to run. `-march=native`
  on a real x86 CPU was not tried (under emulation it selects a CPU without AVX, and the field
  engine then does not compile).
- **Two machines.** Everything ran on one machine; the non-loopback runs used one machine's
  own LAN address. No real round trip, no WireGuard, no packet loss.
- **`net/wg_setup.sh`** was never executed (it needs root and a kernel with WireGuard), nor the
  `ufw` commands. They follow the tools' documented usage.
- The network scripts ran only on loopback and for seconds, not for hours.
- Debian, other Ubuntu releases, GCC.

### Most likely failure points on the rented machines, and what to do

1. **The CPU does not expose AVX2 to the guest.** `build_linux.sh` warns, and the field engine
   fails with "requires target feature 'avx'" in `Tools/BitVector.h`. There is no fix on that
   machine (`--portable` would build something that stops with an illegal instruction): rent
   a different instance type.
2. **`-march=native` picks too little** (seen on arm64 in a container: emp-tool fails with
   "requires target feature 'aes'"). Use `--portable`: x86-64-v3 with AES and PCLMUL.
3. **libOTe's build wants git.** It runs `git checkout PIN` in the three source trees shipped
   with the bundle; `build_linux.sh` puts a small wrapper named `git` first in the path for that
   one step, which answers for those trees and passes everything else to the real git. If the
   step still tries the network (see `build/logs/libote.log`), it needs outbound HTTPS to
   github.com and will fetch the same pinned commits.
4. **Out of memory while compiling** on a 16 GB machine with many cores: `--jobs 4`.
5. **Link errors.** The four static libraries of libOTe are in one linker group; if a Boost
   library is missing on a newer distribution (`-lboost_system` is header-only in recent Boost),
   remove it from `FIELD_LIBS` in `build_linux.sh`.
6. **"handshake failed" from the field engine**: the other side's certificate is missing or
   was not rehashed (`bench_certs.sh trust`), it expired (30 days), or the clocks differ.
7. **Party 1 never connects**: party 0 was not started first (party 1 gives up after 60 s);
   the firewall on machine a does not allow the tunnel interface; the listen address is not
   machine a's tunnel address.
8. **Step out of step**: both sides must pass the same iterations, modes, steps and pairs.
   After a failure on one side stop the other and start both again.

## 9. What this does not tell you

- **The real application.** The benchmark has no controllers, no Signal server and no database
  nodes. Per message the application adds the server's response (0.26 s locally), the
  controllers (0.1 to 0.3 s) and openings that each cost a round trip. A whole session (TLS
  handshake, WebSocket upgrade, loading circuits) is not measured here at all.
- **The real Signal service**: its latency, rate limits, and how it treats a connection that
  is slow to answer. By the standing rule that needs an explicit go-ahead (ban risk).
- **Where the database nodes sit** and what their round trips add to loading and storing a
  contact; and the application server's placement.
- **Long-term provider behaviour**: a day does not show monthly fair-use enforcement,
  noisy-neighbour weeks, maintenance, or a provider's reaction to a month of this traffic
  pattern. The reports' advice stands: tell support in advance.
- **The dedicated products.** A cloud instance's network is not the dedicated server's port.
- **Security of the link.** WireGuard here is test plumbing. Whether WireGuard alone
  authenticates the nodes to each other is still an open decision (`PRODUCT_TODO.md` section 9);
  the field engine's certificates here are self-signed test certificates.
- **x86 tuning.** The field engine is built as on the build machine: without the AVX base-OT
  code and with libOTe's portable AES. On x86-64 those are two known ways to make field triples
  faster that this kit does not use, so its field-triple rate on x86 is a floor.
- **Mixed architectures and other operating systems**: only Ubuntu 24.04 was built.

## 10. The follow-up test, once this one passes

The full application on the same two machines: the two controllers and workers (built from a
bundle made with `--with-workers`, with `TLS_WORKER_PEER` and `TLS_WORKER_LISTEN` set), the
circuit manifest produced ahead of time (`scripts/produce_circuits.py`, `CIRCUIT_MANIFEST`) so
that neither machine needs Lean, the local Signal-Server on a third machine or on one of the
two, and the five database test nodes. Run the harness's send, receive and signup flows and
compare `scripts/session_profile.py` with the single-machine figures in `PERFORMANCE.md`:
steady-state send to send, a contact's first send, a first message received against the 90 s
limit, and a sustained broadcast of several hundred messages (never measured anywhere yet).
What that needs and does not exist: a way to start the two controllers on two machines in step
(today one script starts both), the controllers' and the database client's addresses from
configuration, and the manifest's hash compared between the nodes at start. Only after that,
and on an explicit go-ahead, the real Signal service.
