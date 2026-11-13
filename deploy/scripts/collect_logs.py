#!/usr/bin/env python3
"""Collect a node's logs for diagnosis, redacted, into a new directory.

    collect_logs.py --state-dir STATE --out DIR [--since HOURS] [--compose FILE [--env-file F]]
                    [--account-state DIR] [--keep-ids] [--max-mb N]

Takes from the daemon's state directory (node_daemon/README.md): logs/*.log (the daemon's and each
session's controller and worker standard error) and events.jsonl; with --compose, `docker compose
logs` of that stack. Every line is redacted before it is written (deploylib.redact): PEM blocks,
Authorization headers, any `password` / `token` / `secret` / `share` / `key` / `captcha` / `code`
value, SIGNAL_LOCAL_CREDENTIALS, phone numbers, UUIDs (Signal service ids), long hex and
base64-looking strings, and, unless --keep-ids, the application's contact ids.

NEVER collected, whatever the options: work/ (requests, message texts, the database client's
scratch files), journal/, the workers' Player-Data and any *.key / *.share / *.pem file, export
files, SIGNAL_RECORD files (record-*.jsonl: revealed server bytes and, for a ceremony, the captcha
and SMS code), anything under real_signal/state/. --account-state DIR is only checked to exist and
be private (stat); nothing in it is listed or read.

The output directory must not exist or be empty; it gets MANIFEST.txt (SHA-256 of each redacted
file) and README.txt (what was taken and what was not). Review it before sending it anywhere.
"""
import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import deploylib as dl  # noqa: E402

SKIP_DIRS = {'work', 'journal', 'Player-Data', 'ceremony', 'send', 'serve'}
SKIP_SUFFIXES = {'.key', '.share', '.pem', '.p12', '.der', '.hex'}
SKIP_NAMES_START = ('record-', 'credentials', 'password', 'recovery', 'mpc-export', 'export')


def wanted(path, state):
    rel = path.relative_to(state)
    if any(part in SKIP_DIRS for part in rel.parts[:-1]):
        return False
    if path.suffix in SKIP_SUFFIXES or path.name.startswith(SKIP_NAMES_START):
        return False
    return (rel.parts[0] == 'logs' and path.suffix in ('.log', '.txt', '.out')) or rel.as_posix() == 'events.jsonl'


def redact_file(source, target, keep_ids, max_bytes, since):
    written = 0
    with open(source, errors='replace') as f, open(target, 'w') as out:
        for line in f:
            text = dl.redact(line, keep_ids=keep_ids)
            out.write(text)
            written += len(text)
            if written > max_bytes:
                out.write(f'\n[truncated at {max_bytes} bytes]\n')
                break
    return written


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--state-dir', required=True, help="the daemon's state_directory")
    p.add_argument('--out', required=True, help='a new or empty directory')
    p.add_argument('--since', type=float, default=72.0, help='only files modified in the last HOURS (default 72)')
    p.add_argument('--compose', help='also `docker compose logs` of this stack')
    p.add_argument('--env-file')
    p.add_argument('--account-state', help='checked to exist and be private; never read')
    p.add_argument('--keep-ids', action='store_true', help='do not redact contact ids')
    p.add_argument('--max-mb', type=float, default=50.0, help='per file, after redaction')
    a = p.parse_args()
    os.umask(0o077)
    state = Path(a.state_dir).resolve()
    if dl.is_forbidden(state):
        sys.exit('refusing: that is account state')
    out = Path(a.out)
    if out.exists() and any(out.iterdir()):
        sys.exit(f'{out} is not empty')
    out.mkdir(parents=True, exist_ok=True)
    os.chmod(out, 0o700)
    notes = [f'collected {time.strftime("%Y-%m-%d %H:%M:%S %Z")} from {state}', f'redaction: deploylib.redact (ids {"kept" if a.keep_ids else "redacted"})']
    if a.account_state:
        acc = Path(a.account_state)
        if acc.is_dir():
            mode, _ = dl.mode_string(acc)
            notes.append(f'account state {acc}: exists, {mode}, {"private" if dl.private_enough(acc) else "NOT private (chmod 700)"} (not read)')
        else:
            notes.append(f'account state {acc}: MISSING')
    cutoff = time.time() - a.since * 3600
    manifest, taken, left = [], 0, 0
    if state.is_dir():
        for path in sorted(state.rglob('*')):
            if not path.is_file() or path.is_symlink():
                continue
            if not wanted(path, state) or path.stat().st_mtime < cutoff:
                left += 1
                continue
            target = out / ('state-' + '-'.join(path.relative_to(state).parts))
            redact_file(path, target, a.keep_ids, int(a.max_mb * 1e6), cutoff)
            manifest.append(f'{dl.sha256_file(target)}  {target.name}')
            taken += 1
    else:
        notes.append(f'{state} is not a directory')
    if a.compose:
        docker = dl.docker_binary()
        command = [docker or 'docker', 'compose', '-f', a.compose] + (['--env-file', a.env_file] if a.env_file else []) + \
                  ['logs', '--no-color', '--timestamps', '--since', f'{int(a.since * 60)}m']
        try:
            r = subprocess.run(command, capture_output=True, text=True, timeout=120)
            target = out / 'compose.log'
            target.write_text(dl.redact(r.stdout + r.stderr, keep_ids=a.keep_ids))
            manifest.append(f'{dl.sha256_file(target)}  compose.log')
            taken += 1
        except (OSError, subprocess.TimeoutExpired) as e:
            notes.append(f'docker compose logs: {e}')
    notes.append(f'taken {taken} files; left out {left} (work/, journal/, keys, shares, records, exports, older files)')
    (out / 'MANIFEST.txt').write_text('\n'.join(manifest) + '\n')
    (out / 'README.txt').write_text('\n'.join(notes) + '\nReview before sharing: redaction is pattern-based.\n')
    print('\n'.join(notes))
    print(f'output: {out}')


if __name__ == '__main__':
    main()
