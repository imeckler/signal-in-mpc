#!/usr/bin/env python3
"""Did the two computation nodes build and install the same thing? (DEPLOYMENT.md, "Build")

    verify_artifacts.py export --out FILE [--config NODE.json] [--manifest manifest.txt]
                               [--word-dir DIR] [--binary NAME=PATH ...] [--full-hash]
    verify_artifacts.py compare A.json B.json

`export` writes, for this node, the SHA-256 of each named binary (from --binary and, with
--config, the controller, worker, certificate checker and database client the daemon is
configured with), the circuit manifest's digest and file check, the word-circuit directory's
digest (word circuits and the 22 V3 field programs), the agreed-settings digests (with --config),
the git commit of this checkout when there is one, and the image build information when run in
the worker image. No secrets: hashes and public settings text only. It reads nothing but those
files (and the shared peer key, for a salted fingerprint, with --config).

`compare` puts two exports side by side and exits 1 if anything that must be equal differs:
controller, worker (same mode), database client, certificate checker, manifest digest, word-dir
digest, settings digests, worker session settings, port base, peer-key fingerprint. Files may also
be preflight.py --export output (same fields).

Expected values (2026-11-13, this tree; they change with every rebuild): see DEPLOYMENT.md "Pins".
"""
import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import deploylib as dl  # noqa: E402

MUST_MATCH_BINARIES = ['controller', 'worker', 'database_client', 'certificate_checker']


def git_head():
    try:
        r = subprocess.run(['git', '-C', str(dl.ROOT), 'rev-parse', 'HEAD'], capture_output=True, text=True, timeout=20)
        head = r.stdout.strip()
        d = subprocess.run(['git', '-C', str(dl.ROOT), 'status', '--porcelain', '--untracked-files=no'], capture_output=True, text=True, timeout=60)
        return dict(head=head or None, tracked_files_modified=len([l for l in d.stdout.splitlines() if l.strip()]))
    except (OSError, subprocess.SubprocessError):
        return None


def export(a):
    facts = dict(format='tls-mpc-node-facts-v1', exported_at=int(time.time()), binaries={}, problems=[])
    if a.config:
        config = dl.load_json(a.config)
        facts['party'] = config.get('party')
        facts['port_base'] = (config.get('worker') or {}).get('port_base')
        named = dict(controller=config.get('controller'), worker=(config.get('worker') or {}).get('binary'),
                     certificate_checker=(config.get('signal') or {}).get('certificate_checker'),
                     database_client=(config.get('database') or {}).get('client'))
        for name, path in named.items():
            if path and Path(path).is_file():
                facts['binaries'][name] = dl.sha256_file(path)
            else:
                facts['problems'].append(f'binary {name} missing: {path}')
        try:
            facts['settings'] = dl.settings_digests(config)
        except ValueError as e:
            facts['problems'].append(f'settings: {e}')
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        from preflight import peer_key_fingerprint, worker_mode
        facts['peer_key_fingerprint'] = peer_key_fingerprint(config)
        facts['worker_mode'] = worker_mode(named['worker'] or '')
        a.manifest = a.manifest or (config.get('circuits') or {}).get('manifest')
    for item in a.binary or []:
        name, _, path = item.partition('=')
        if not path or not Path(path).is_file():
            facts['problems'].append(f'binary {name} missing: {path}')
            continue
        facts['binaries'][name] = dl.sha256_file(path)
    if a.manifest:
        try:
            problems, stats = dl.check_manifest_files(a.manifest, full=a.full_hash)
            facts['manifest'] = stats
            facts['problems'] += problems
        except (OSError, ValueError) as e:
            facts['problems'].append(f'manifest: {e}')
    if a.word_dir:
        problems, stats = dl.word_dir_summary(a.word_dir)
        facts['word_dir'] = stats
        facts['problems'] += problems
    if dl.IMAGE_BUILD_INFO.exists():
        facts['image'] = json.loads(dl.IMAGE_BUILD_INFO.read_text())
    facts['git'] = git_head()
    Path(a.out).write_text(json.dumps(facts, indent=1, sort_keys=True) + '\n')
    print(f'wrote {a.out}: {len(facts["binaries"])} binaries, manifest {(facts.get("manifest") or {}).get("manifest_sha256", "-")}, '
          f'word dir {(facts.get("word_dir") or {}).get("word_dir_sha256", "-")}, problems {len(facts["problems"])}')
    for problem in facts['problems']:
        print('  problem:', problem)
    return 1 if facts['problems'] else 0


def compare(a):
    one, two = json.loads(Path(a.a).read_text()), json.loads(Path(a.b).read_text())
    r = dl.Report()
    for name in sorted(set(one.get('binaries', {})) | set(two.get('binaries', {}))):
        x, y = one.get('binaries', {}).get(name), two.get('binaries', {}).get(name)
        if x == y:
            r.ok(f'binary {name}', (x or '')[:16])
        elif name in MUST_MATCH_BINARIES:
            r.fail(f'binary {name}', f'{(x or "missing")[:16]} vs {(y or "missing")[:16]}')
        else:
            r.warn(f'binary {name}', f'{(x or "missing")[:16]} vs {(y or "missing")[:16]} (not required equal)')
    pairs = [
        ('manifest digest', ('manifest', 'manifest_sha256')),
        ('word dir digest', ('word_dir', 'word_dir_sha256')),
    ]
    for label, (group, key) in pairs:
        x, y = (one.get(group) or {}).get(key), (two.get(group) or {}).get(key)
        if x is None and y is None:
            r.skip(label, 'in neither export')
        else:
            r.check(x == y, label, x or '', f'{x} vs {y}')
    for kind in ('serve', 'receive', 'notify'):
        x = ((one.get('settings') or {}).get(kind) or {}).get('sha256')
        y = ((two.get('settings') or {}).get(kind) or {}).get('sha256')
        if x is None and y is None:
            r.skip(f'settings {kind}', 'in neither export')
        else:
            r.check(x == y, f'settings {kind}', x or '', f'{x} vs {y}')
    for label, key in (('worker session settings', None), ('worker mode', 'worker_mode'), ('port base', 'port_base'),
                       ('peer key fingerprint', 'peer_key_fingerprint')):
        if key is None:
            x, y = (one.get('settings') or {}).get('worker_session'), (two.get('settings') or {}).get('worker_session')
        else:
            x, y = one.get(key), two.get(key)
        if x is None and y is None:
            r.skip(label, 'in neither export')
        else:
            r.check(x == y, label, str(x), f'{x} vs {y}')
    if one.get('party') is not None and one.get('party') == two.get('party'):
        r.fail('parties', f'both exports are party {one.get("party")}')
    gx, gy = (one.get('git') or {}).get('head'), (two.get('git') or {}).get('head')
    if gx or gy:
        (r.ok if gx == gy else r.warn)('git commit', f'{gx} vs {gy}' if gx != gy else gx)
    for name, facts in (('A', one), ('B', two)):
        for problem in facts.get('problems') or []:
            r.warn(f'{name} reported', problem)
    return r.summary()


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='command', required=True)
    e = sub.add_parser('export', help="this node's artefact digests")
    e.add_argument('--out', required=True)
    e.add_argument('--config', help="the node daemon's configuration")
    e.add_argument('--manifest', help='manifest.txt (default: the configuration\'s circuits.manifest)')
    e.add_argument('--word-dir', help='the word-circuit directory')
    e.add_argument('--binary', action='append', metavar='NAME=PATH', help='another binary to hash (repeatable)')
    e.add_argument('--full-hash', action='store_true', help='hash every gate list (minutes)')
    c = sub.add_parser('compare', help='compare two exports')
    c.add_argument('a')
    c.add_argument('b')
    a = p.parse_args()
    sys.exit(export(a) if a.command == 'export' else compare(a))


if __name__ == '__main__':
    main()
