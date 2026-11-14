# Hand-over: the push-button deploy tool (2026-11-13)

Resumed and completed the previous handover's three next steps: the full local multi-operator
run, single-operator `up`, semi-honest mode, and a commit of the tested fixes and evidence.
DEPLOYMENT.md's status table remains authoritative. See LOCAL_TEST_RESULTS.md for evidence.

## Completed this session

- Malicious, three simulated operators, separate private files and state directories, only
  public bundles exchanged: **61 checks, zero failures**. All three signup + 200-byte sends
  passed (initial deployment, after same-version upgrade, after replacing Alice's machines
  while keeping data disks). Every send report confirms delivery and sealed-envelope decryption.
- All five database nodes applied epochs. After replacing Alice's two database nodes while the
  other three stayed running, all five applied the same new epoch (89730784 was checked directly).
- Both single-operator `up --with-account` runs passed, including signup/send/decryption:
  malicious **16 checks**, semi-honest **18 checks**, zero failures in either. Legacy worker logic.
- **28 unit tests pass**: configuration, bundles, account readiness, command results and timeout
  coverage. Account playbook syntax-check and production-profile ansible-lint pass.

## Fixes made

1. The database start barrier worked, but `start` returns before it finishes. Account installation
   raced it and both store ceremonies failed with database connection refused. The account
   playbook now waits for threshold + max_malicious reachable database nodes that are running,
   are no longer at the barrier, and have applied an epoch. A timeout fails before the ceremony
   and explains how to retry. Its duration and the outer Ansible timeout include epoch settling.
2. `up --with-account` used to retain an earlier waiting-status exit code even after successful
   account installation. It now returns the account step's result, matching the standalone
   account command (daemon startup remains asynchronous).
3. The ignored test harness now checks database epoch evidence before sends and uses unique
   per-run account staging directories. One retry had an unavailable account bind mount after
   reusing a deleted/recreated path; a fresh container could read it. This was not established
   as a deployment-tool defect.

An initial attempt also exposed an execution-environment issue: the sandbox blocked `ps`, so
scripts/guarded.py crashed after spawning its child and released the heavy lock. That child was
stopped, and all reported passing runs used an elevated guard with working `ps` access. Do not
run this harness if its guard cannot monitor processes; never bypass the heavy lock.

## Evidence and reruns (local files, ignored by Git)

- `.deps/lowering-scratch/pb_results/malicious-multi.jsonl` (61 checks)
- `.deps/lowering-scratch/pb_results/malicious-single.jsonl` (16 checks)
- `.deps/lowering-scratch/pb_results/semi-honest-single.jsonl` (18 checks)
- `.deps/lowering-scratch/pb_e2e.py`: original multi-operator harness, now with epoch checks.
- `.deps/lowering-scratch/pb_single.py`: single-operator harness; second argument selects mode.
- State/logs: `deploy/.state/pbtest/`, `deploy/.state/pbsingle/`.

The full multi-operator command (first remove the current single-operator machines, below):

```sh
python3 scripts/guarded.py --heavy 8 5000 python3 .deps/lowering-scratch/pb_e2e.py resume,teardown,setup,join,exchange,collect,tamper,start,account,send,cert,status,upgrade,send2,destroy-up,send3,quiesce,pause
```

A single-operator run, once no other local deployment owns the fixed Docker subnet:

```sh
python3 scripts/guarded.py --heavy 8 3600 python3 .deps/lowering-scratch/pb_single.py resume,teardown,setup,up,send,cert,status,quiesce,pause semi-honest
```

The original multi-operator script records FAIL rows but can exit 0: inspect results.jsonl.
The single-operator script exits nonzero if any of its checks failed. Archive results before
another setup/run, since setup replaces the multi-operator results directory.

## Left on this computer

- **8 paused** `pb-pbsingle-*` containers (7 machines + application server), network `pb-pbsingle`,
  and data/docker/containerd volumes. The final run is semi-honest.
- The old `pb-pbtest-*` machines, network and volumes were removed after their successful run.
  Their state directories and archived results remain.
- Both computation daemons and the local Signal server were stopped before pausing.
- Existing deployment/Ansible/machine images and both arm64 computation images remain.

To remove the current test machines and data under the heavy lock:

```sh
python3 scripts/guarded.py --heavy 8 600 python3 .deps/lowering-scratch/pb_single.py resume,teardown
```

## Still open / not tested

- P-CERT joint sender-certificate refresh (proposed change 15): timer only records refresh due.
  The existing ceremony certificate stage is not a safe automated refresh job.
- Field-engine 30-day certificate renewal (changes 8/18), reproducible builds, prekey
  replenishment and signed-prekey rotation (PRODUCT_TODO.md section 1).
- `build` for linux/amd64, lean worker logic through push-button, real remote `existing`, cloud
  applies and production Signal. OpenTofu's earlier offline validation remains unchanged.
- General database reconnect/partition-recovery behavior (change 19). Coordinated initial start
  and replacement of one operator's two databases passed; this is not a proof of every recovery case.
- Same-version upgrade passed; an upgrade to genuinely different binaries was not exercised.
- Owner questions remain in DEPLOYMENT.md section 11: builder, provider/`existing` route, alerts,
  manual certificate refresh responsibility, application-server WireGuard ownership.
