# Push-button local validation — 2026-11-13

These runs used arm64 images and the `local` provider: systemd/SSH machine containers configured
by the same Ansible roles as `existing`. Signal traffic went only to the local test server.
Legacy worker logic was used throughout. No cloud resources or production Signal were used.

| Run | Checks | Failures | Result |
|---|---:|---:|---|
| Malicious, three independent operator state directories | 61 | 0 | Initial deployment, same-version upgrade, replacement of Alice's computation node and two databases with kept disks; all three signup/send/decryption checks passed |
| Malicious, single-operator `up --with-account` | 16 | 0 | Command returned 0, pair EQUAL, all five databases applying epochs, signup/send/decryption passed |
| Semi-honest, single-operator `up --with-account` | 18 | 0 | Command returned 0, pair EQUAL, all five databases applying epochs, signup/send/decryption passed |

Each send created a new signup and sent a 200-byte message. Each report had `signup`, `delivered`,
`decrypted_sealed` and `passed` equal to true. Database tables and the deployment fingerprint were
unchanged by the same-version upgrade and restored from kept disks after machine replacement.
A direct check after replacement found all five databases applying epoch 89730784, newer than
all pre-replacement epochs. Status, logs and certificate-timer checks passed in all three runs;
the multi-operator run also checked the monitoring page through its SSH tunnel and tamper rejection.

The first resumed run found an account-startup race: `start` returns while database nodes are
still at their start barrier, so both account store ceremonies could reach connection refused.
`account.yml` now waits for a reachable quorum with epoch evidence. Its helper is covered by six
unit tests. Four command-flow tests cover `up` result handling and account timeout budgets.
Together with the existing eighteen tests, all **28 tests pass**:

```sh
python3 -m unittest discover -s deploy/pushbutton -p 'test_*.py'
```

`account.yml` also passes Ansible syntax-check and ansible-lint's production profile. The final
semi-honest run exercised the complete account playbook with the adjusted timeout budget.

Raw JSONL results are retained locally under `.deps/lowering-scratch/pb_results/`:
`malicious-multi.jsonl`, `malicious-single.jsonl`, `semi-honest-single.jsonl`. Harnesses and cleanup
commands are documented in [HANDOVER.md](HANDOVER.md). The final eight single-operator machine
containers are paused; both computation daemons and the local Signal server were stopped first.

These results establish the local scenarios above. Different-version upgrades, other CPU
architectures, real remote machines, provider applies, production Signal, lean worker logic,
general partition recovery, and automated certificate renewal remain outside these runs.
