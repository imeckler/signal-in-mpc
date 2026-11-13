# Hand-over: the push-button deploy tool (2026-11-13)

Stopped early (out of credits). DEPLOYMENT.md "Status of the push-button tool" is the
authoritative table; this is the short version.

## Done and tested here (local provider: containers standing in for ssh machines)
- Config validation of deployment.toml / operator.toml: `python3 deploy/pushbutton/test_pushbutton.py` (18 checks).
- Multi-operator flow with 3 simulated operators, separate state dirs, only bundle files exchanged:
  join (Docker, WireGuard, ufw, data disk, images by digest, circuits + word files checked, keys made
  on the nodes), collect (same fingerprint for all three), tampered bundle -> different fingerprint
  and `start` refuses, start (WireGuard mesh, per-sender firewall, Postgres + db server, daemon
  config, health endpoints, monitoring page, certificate timer, preflight, two-node comparison EQUAL),
  account local-test + account install by both MPC operators, status/monitor/logs, upgrade keeps
  db tables, destroy + join restores keys (same fingerprint) and db data.
- Signup + 200-byte send: passed once (run 2, after a restart); failed in other runs (below).
- OpenTofu modules hetzner/upcloud/ovh: init + validate pass offline; never applied.
- Ansible: syntax-check of 7 playbooks and ansible-lint (production profile) pass.

## Written but untested
- The database start barrier (`pb_health.py db-barrier`, ssdb-node.service ExecStartPre): the fix for
  the db nodes never connecting when started minutes apart (DEPLOYMENT.md Reference 10, change 19).
  Its run was stopped right after start(carol).
- `up`, `build` for linux/amd64, semi-honest / lean, `existing` against a real remote machine, every
  cloud apply, `endpoint = "production"` (reviewed by reading only).

## Not started
- The joint sender-certificate refresh (change 15, P-CERT): the timer only records "refresh due".
- Field-engine certificate (30-day) renewal; reproducible builds.

## Next steps, in order
1. Rerun the local end-to-end under the heavy lock (it pauses the test machines at the end):
   `python3 scripts/guarded.py --heavy 8 5000 python3 .deps/lowering-scratch/pb_e2e.py resume,teardown,setup,join,exchange,collect,tamper,start,account,send,cert,status,upgrade,send2,destroy-up,send3,quiesce,pause`
   Check in pb_e2e/results.jsonl that the db nodes apply epochs (status shows "epoch N", not None)
   and that all three sends pass. If not, look at `docker logs ssdb-node` on a db machine
   ("Client N not connected").
2. Then `up` with one operator file (all nodes local), then semi-honest.
3. Commit the then-tested state; update the status table.

## Leftover state on this computer
- 8 PAUSED containers `pb-pbtest-*` (7 machines + application-server), network `pb-pbtest`,
  volumes `pb-pbtest-*-{data,docker,containerd}` (about 30 GB). Remove all with
  `python3 .deps/lowering-scratch/pb_e2e.py resume,teardown`.
- Images: `tls-mpc-deploy-ansible:1`, `tls-mpc-deploy-machine:1`, `ghcr.io/opentofu/opentofu:1.10.6`.
- deploy/.state/pbtest/ (git-ignored: ssh keys of the test, bundles, logs, image tars ~0.5 GB).
- Test scripts: .deps/lowering-scratch/pb_*.py, pb_cmds/, pb_e2e/, pb_tofu/.
- The local Signal server is stopped.
