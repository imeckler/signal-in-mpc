#!/usr/bin/env python3
"""Entry point of the computation-node image (deploy/docker/worker.Dockerfile).

    daemon                  (default) start-up checks, then exec node-daemon CONFIG
    preflight [ARGS...]     deploy/scripts/preflight.py --config CONFIG ARGS... (e.g. --export /srv/tls-mpc/state/facts.json)
    ceremony NAME STAGE     public_service_controller ceremony CONFIG NAME STAGE (CEREMONY.md; OWNER ONLY against the real service)
    certs init PARTY DIR | certs trust PEER.pem DIR      the field engine's certificates (bench_certs.sh)
    notify-app ARGS...      the application stand-in (node_daemon/README.md), for rehearsals
    version                 the image's build information (binary hashes, toolchains, mode)

Start-up checks (each failure stops the container before anything connects anywhere):
  - the configuration exists and names this image's binaries;
  - strict mode: circuits.manifest is set; its SHA-256 equals EXPECTED_MANIFEST_SHA256 (required
    unless TLS_MPC_REHEARSAL=1); every listed kernel's gate list exists and every layout matches
    its pin (TLS_MPC_FULL_HASH=1: every gate list hashed too);
  - the word-circuit directory (/opt/tls-mpc/word) matches the worker's pins (pins.json written at
    build time) and, when EXPECTED_WORD_DIR_SHA256 is set, its digest;
  - SIGNAL_SCRIPTS is empty (TLS_MPC_ALLOW_SCRIPTS=1 to override, never in production) and no TEST
    hook or credential is in the environment.
Rehearsal only (TLS_MPC_HOST_ALIAS=host.docker.internal): loopback addresses in the configuration
(Signal endpoint, database nodes' compute addresses) are rewritten to that host's address, into
copies under the state directory; the mounted files are not changed.
"""
import json
import os
import socket
import sys
from pathlib import Path

SHARE = Path('/opt/tls-mpc/share')
sys.path.insert(0, str(SHARE / 'deploy/scripts'))
import deploylib as dl  # noqa: E402

BIN = Path('/opt/tls-mpc/bin')
CONFIG = Path(os.environ.get('TLS_MPC_CONFIG', '/srv/tls-mpc/config/node.json'))
STATE = Path('/srv/tls-mpc/state')
WORD = Path('/opt/tls-mpc/word')


def die(message):
    print(f'entrypoint: {message}', file=sys.stderr, flush=True)
    sys.exit(1)


def rehearsal_rewrite(config):
    """Loopback addresses -> the host alias's address (copies in the state directory)."""
    alias = os.environ.get('TLS_MPC_HOST_ALIAS')
    if not alias:
        return CONFIG
    try:
        address = socket.gethostbyname(alias)
    except OSError as e:
        die(f'TLS_MPC_HOST_ALIAS {alias}: {e}')
    signal = config.get('signal') or {}
    if signal.get('endpoint') in ('127.0.0.1', 'localhost'):
        signal['endpoint'] = address
    network = (config.get('database') or {}).get('network')
    if network:
        data = json.loads(Path(network).read_text())
        for key, value in list(data.items()):
            if isinstance(value, list) and value and all(isinstance(v, str) for v in value):
                data[key] = [v.replace('127.0.0.1:', f'{address}:') for v in value]
        copy = STATE / 'rehearsal-network.json'
        copy.write_text(json.dumps(data))
        config['database']['network'] = str(copy)
    out = STATE / 'rehearsal-node.json'
    out.write_text(json.dumps(config, indent=1))
    print(f'entrypoint: rehearsal: loopback -> {alias} ({address}); using {out}', flush=True)
    return out


def checks():
    if not CONFIG.is_file():
        die(f'{CONFIG} missing (mount the daemon configuration read-only at /srv/tls-mpc/config)')
    config = json.loads(CONFIG.read_text())
    for key, want in (('controller', BIN / 'public_service_controller'),):
        if Path(config.get(key, '')) != want:
            die(f'{key} must be {want} in this image, not {config.get(key)}')
    if Path((config.get('worker') or {}).get('binary', '')) != BIN / 'node-worker':
        die(f'worker.binary must be {BIN / "node-worker"} in this image')
    manifest = (config.get('circuits') or {}).get('manifest')
    if not manifest:
        die('circuits.manifest is null: the production worker loads only pinned circuits')
    try:
        problems, stats = dl.check_manifest_files(manifest, full=os.environ.get('TLS_MPC_FULL_HASH') == '1')
    except (OSError, ValueError) as e:
        die(f'circuit manifest {manifest}: {e}')
    if problems:
        die('circuit files: ' + '; '.join(problems))
    expected = os.environ.get('EXPECTED_MANIFEST_SHA256')
    if expected:
        if expected != stats['manifest_sha256']:
            die(f'manifest digest {stats["manifest_sha256"]} is not EXPECTED_MANIFEST_SHA256 {expected}')
    elif os.environ.get('TLS_MPC_REHEARSAL') != '1':
        die('EXPECTED_MANIFEST_SHA256 is not set (the digest both operators agreed on; DEPLOYMENT.md "Bring-up")')
    problems, words = dl.word_dir_summary(WORD)
    if problems:
        die('word circuits / field programs: ' + '; '.join(problems[:6]))
    expected = os.environ.get('EXPECTED_WORD_DIR_SHA256')
    if expected and expected != words['word_dir_sha256']:
        die(f'word dir digest {words["word_dir_sha256"]} is not EXPECTED_WORD_DIR_SHA256 {expected}')
    env = dl.daemon_session_env(config)
    if (env.get('SIGNAL_SCRIPTS') or '').strip() and os.environ.get('TLS_MPC_ALLOW_SCRIPTS') != '1':
        die('SIGNAL_SCRIPTS must stay unset/empty in production for now (STACK_NOTES.md 11.3)')
    hooks = [h for h in dl.TEST_HOOKS + ['SIGNAL_LOCAL_CREDENTIALS', 'SIGNAL_LOCAL_CREDENTIALS_FILE', 'TLS_WORKER_TEST_LINK_SHIFT'] if os.environ.get(h)]
    if hooks:
        die('TEST settings or credentials in the environment: ' + ', '.join(hooks))
    try:
        digests = dl.settings_digests(config)
    except ValueError as e:
        die(f'settings: {e}')
    print('entrypoint: manifest %s (%d kernels), word dir %s, settings serve=%s receive=%s, mode %s' % (
        stats['manifest_sha256'], stats['kernels'], words['word_dir_sha256'][:16], digests['serve']['sha256'][:16],
        digests['receive']['sha256'][:16], os.environ.get('TLS_MPC_MODE')), flush=True)
    return config


def main():
    args = sys.argv[1:] or ['daemon']
    command, rest = args[0], args[1:]
    if command == 'daemon':
        config = checks()
        path = rehearsal_rewrite(config)
        os.execv(str(BIN / 'node-daemon'), [str(BIN / 'node-daemon'), str(path)])
    elif command == 'preflight':
        os.execv(sys.executable, [sys.executable, str(SHARE / 'deploy/scripts/preflight.py'), '--config', str(CONFIG), '--word-dir', str(WORD), *rest])
    elif command == 'ceremony' and len(rest) == 2:
        checks()
        os.execv(str(BIN / 'public_service_controller'), [str(BIN / 'public_service_controller'), 'ceremony', str(CONFIG), *rest])
    elif command == 'certs' and rest:
        os.execv('/bin/sh', ['/bin/sh', str(SHARE / 'bench_certs.sh'), *rest])
    elif command == 'notify-app':
        os.execv(str(BIN / 'notify-app'), [str(BIN / 'notify-app'), *rest])
    elif command == 'version':
        print((SHARE / 'build-info.json').read_text())
    else:
        print(__doc__)
        sys.exit(2)


if __name__ == '__main__':
    main()
