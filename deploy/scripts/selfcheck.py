#!/usr/bin/env python3
"""Check the deployment tooling itself (light; no network, no Docker, no build).

    selfcheck.py

  - every Python file under deploy/ compiles (py_compile, to a temporary directory);
  - every script under deploy/scripts/ answers --help with status 0;
  - the example JSON files parse; the agreed-settings digests of node-a and node-b examples are
    equal (a mirror of TlsMpc/Node/Config.lean, deploylib.agreed_text);
  - the *.example files and the compose files carry no real identifier: no phone number, no
    UUID, no Signal host name, no key material (PEM, 64-hex strings other than the pinned image
    digest), and SIGNAL_SCRIPTS is not set anywhere;
  - deploylib.redact removes a sample of secrets;
  - deploylib.parse_loader_pins finds the 22 V3 field programs and the word circuits in
    node_worker/src/loader.rs.
Exit status 1 on any failure.
"""
import json
import py_compile
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import deploylib as dl  # noqa: E402

DEPLOY = dl.DEPLOY
ALLOWED_HEX = {'5b96f1a16bd9768b060dd2ffe55cb6225c4d9ef4d214a8b21eb08134869a97e4'}   # postgres:17 image digest


def main():
    if '--help' in sys.argv or '-h' in sys.argv:
        print(__doc__)
        return 0
    r = dl.Report()
    with tempfile.TemporaryDirectory() as tmp:
        for path in sorted(DEPLOY.rglob('*.py')):
            try:
                py_compile.compile(str(path), cfile=str(Path(tmp) / (path.stem + '.pyc')), doraise=True)
                r.ok('compiles', str(path.relative_to(dl.ROOT)))
            except py_compile.PyCompileError as e:
                r.fail('compiles', f'{path}: {e.msg[:300]}')
    for path in sorted((DEPLOY / 'scripts').glob('*.py')):
        if path.name in ('deploylib.py', 'selfcheck.py'):
            continue
        out = subprocess.run([sys.executable, str(path), '--help'], capture_output=True, text=True, timeout=60)
        r.check(out.returncode == 0 and 'usage' in out.stdout.lower(), '--help', path.name, f'{path.name}: exit {out.returncode} {out.stderr[-200:]}')
    configs = {}
    for path in sorted(DEPLOY.rglob('*.json.example')):
        try:
            configs[path.name] = json.loads(path.read_text())
            r.ok('example parses', path.name)
        except ValueError as e:
            r.fail('example parses', f'{path.name}: {e}')
    a, b = configs.get('node-a.json.example'), configs.get('node-b.json.example')
    if a and b:
        da, db = dl.settings_digests(a, base_env={}), dl.settings_digests(b, base_env={})
        for kind in ('serve', 'receive', 'notify'):
            r.check(da[kind]['sha256'] == db[kind]['sha256'], f'example settings agree ({kind})', da[kind]['sha256'][:16], 'node-a and node-b differ')
        r.check(da['worker_session'] == db['worker_session'], 'example worker settings agree', 'equal', f'{da["worker_session"]} vs {db["worker_session"]}')
        r.check(a['party'] == 0 and b['party'] == 1, 'example parties', '0 and 1')
    patterns = {
        'phone number': re.compile(r'\+\d{8,15}'),
        'uuid': re.compile(r'\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b', re.I),
        'signal host': re.compile(r'signal\.org|whispersystems', re.I),
        'pem': re.compile(r'-----BEGIN'),
        'SIGNAL_SCRIPTS set': re.compile(r'SIGNAL_SCRIPTS\s*[:=]\s*["\']?[a-z]'),
    }
    for path in sorted(list(DEPLOY.rglob('*.example')) + list((DEPLOY / 'compose').glob('*.yml'))):
        text = path.read_text()
        for name, pattern in patterns.items():
            r.check(not pattern.search(text), f'no {name}', path.name, f'{path.name}: {pattern.search(text).group(0) if pattern.search(text) else ""}')
        hexes = set(re.findall(r'\b[0-9a-f]{64}\b', text)) - ALLOWED_HEX
        r.check(not hexes, 'no key-like hex', path.name, f'{path.name}: {sorted(hexes)[:2]}')
    sample = ('Authorization: Basic dXNlcjpwYXNzd29yZA== password=hunter2hunter2 "token": "abcdefABCDEF0123456789abcdefABCDEF012345" '
              '+15555550100 0f1e2d3c4b5a69788796a5b4c3d2e1f00f1e2d3c4b5a69788796a5b4c3d2e1f0 "id":"123456789012345678901234"')
    redacted = dl.redact(sample)
    leaked = [s for s in ('dXNlcjpwYXNzd29yZA', 'hunter2', 'abcdefABCDEF0123456789', '5555550100','0f1e2d3c4b5a6978', '123456789012345678901234') if s in redacted]
    r.check(not leaked, 'redaction', 'sample secrets removed', f'still present: {leaked}')
    if dl.LOADER_RS.exists():
        pins = dl.parse_loader_pins()
        v3 = [k for k in pins if k.endswith('.v3')]
        flat = [k for k in pins if k.endswith('.flat')]
        r.check(len(v3) == 22, 'loader pins: V3 field programs', f'{len(v3)}', f'{len(v3)} (expected 22)')
        r.check(len(flat) >= 6, 'loader pins: word circuits', f'{len(flat)} files', f'{len(flat)}')
    else:
        r.skip('loader pins', 'node_worker/src/loader.rs not here')
    return r.summary()


if __name__ == '__main__':
    sys.exit(main())
