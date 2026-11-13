#!/usr/bin/env python3
"""Start, stop and inspect a computation node (native or Docker Compose), or look at the local harness.

    stack.py up     --config NODE.json [--i-have-the-go-ahead] [--skip-preflight] [--account-state DIR]
    stack.py up     --compose FILE [--env-file F] --target local|production [--i-have-the-go-ahead]
    stack.py down   --config NODE.json | --compose FILE [--env-file F]
    stack.py status --config NODE.json [--bearer-file F] | --compose FILE [--env-file F] | --harness

up (native): runs preflight.py on the configuration first and stops on any FAIL; starts
  `node-daemon NODE.json` in the background (its standard error to STATE/logs/daemon.log, its pid
  in STATE/daemon.pid) and waits for its "listening" line. Idempotent: a running daemon is left
  alone. A daemon connects to the Signal server as soon as it starts (its receive session and its
  long-lived send session), so a configuration whose Signal endpoint is not a loopback/private
  address is refused without --i-have-the-go-ahead (owner only; REAL_TEST_PLAN.md).
up (compose): `docker compose up -d` (production target likewise needs --i-have-the-go-ahead).
down: SIGTERM to the daemon (it ends its sessions and kills their process trees), waits 60 s;
  compose: `docker compose down` (volumes are never removed here).
status: the daemon's own `status` reply (node_daemon/README.md: requests by state, whether a
  receive session and a send session run), its pid; compose: `docker compose ps`.
status --harness: read-only look at the LOCAL test set-up of local_signal_server/ (server ping,
  terminators, database nodes, daemons' ports, the heavy-job lock, Docker). Starts nothing.
"""
import argparse
import json
import os
import signal
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import deploylib as dl  # noqa: E402

HARNESS = dl.ROOT / 'local_signal_server'


def pid_alive(pid, word='node-daemon'):
    if not pid:
        return False
    out = subprocess.run(['ps', '-p', str(pid), '-o', 'command='], capture_output=True, text=True).stdout
    return word in out


def state_paths(config):
    state = Path(config['state_directory'])
    return state, state / 'daemon.pid', state / 'logs' / 'daemon.log'


def read_pid(path):
    try:
        return int(path.read_text().strip())
    except (OSError, ValueError):
        return None


def production_gate(endpoint, go_ahead):
    if dl.is_local_address(endpoint or ''):
        return True
    print(f'The Signal endpoint {endpoint} is not local: starting the daemon connects to the REAL Signal service as the account.')
    if not go_ahead:
        print('Refused. Only the owner starts a production node (--i-have-the-go-ahead), after the dry run and the pre-flight checklist.')
        return False
    print('--i-have-the-go-ahead given: continuing.')
    return True


def up_native(a):
    config = dl.load_json(a.config)
    state, pid_file, log_file = state_paths(config)
    pid = read_pid(pid_file)
    if pid_alive(pid):
        print(f'already running: pid {pid}')
        return 0
    if not production_gate((config.get('signal') or {}).get('endpoint'), a.i_have_the_go_ahead):
        return 1
    if not a.skip_preflight:
        command = [sys.executable, str(Path(__file__).resolve().parent / 'preflight.py'), '--config', a.config]
        if a.account_state:
            command += ['--account-state', a.account_state]
        if subprocess.run(command).returncode:
            print('pre-flight failed: not starting (fix the FAIL lines, or --skip-preflight for a rehearsal)')
            return 1
    log_file.parent.mkdir(parents=True, exist_ok=True)
    os.chmod(state, 0o700)
    daemon = Path(os.environ.get('NODE_DAEMON') or (dl.ROOT / 'node_daemon/target/debug/node-daemon'))
    if not daemon.is_file():
        print(f'{daemon} missing (NODE_DAEMON=PATH, or build_artifacts.py native)')
        return 1
    with open(log_file, 'a') as log:
        process = subprocess.Popen([str(daemon), a.config], stdout=subprocess.PIPE, stderr=log, stdin=subprocess.DEVNULL, text=True,
                                   cwd=str(dl.ROOT), start_new_session=True)
    pid_file.write_text(f'{process.pid}\n')
    deadline = time.time() + 30
    line = ''
    while time.time() < deadline and process.poll() is None:
        line = process.stdout.readline()
        if line:
            break
    if line.startswith('listening'):
        print(f'started: pid {process.pid}: {line.strip()}; log {log_file}')
        return 0
    print(f'the daemon did not report "listening" (exit {process.poll()}); see {log_file}')
    return 1


def down_native(a):
    config = dl.load_json(a.config)
    _, pid_file, log_file = state_paths(config)
    pid = read_pid(pid_file)
    if not pid_alive(pid):
        print('not running')
        pid_file.unlink(missing_ok=True)
        return 0
    os.kill(pid, signal.SIGTERM)
    for _ in range(120):
        if not pid_alive(pid):
            pid_file.unlink(missing_ok=True)
            print(f'stopped pid {pid}')
            return 0
        time.sleep(0.5)
    print(f'pid {pid} did not stop within 60 s; its sessions may still be ending (see {log_file}). Not killed from here.')
    return 1


def status_native(a):
    config = dl.load_json(a.config)
    _, pid_file, log_file = state_paths(config)
    pid = read_pid(pid_file)
    print(f'daemon pid: {pid} ({"running" if pid_alive(pid) else "not running"}); log {log_file}')
    bearer = Path(a.bearer_file).read_text().strip() if a.bearer_file else None
    try:
        reply = dl.daemon_call(config['listen'], {'op': 'status'}, bearer=bearer)
        print('status: ' + json.dumps(reply, sort_keys=True))
        return 0 if reply.get('ok') else 1
    except OSError as e:
        print(f'status: {config.get("listen")} not answering ({e})')
        return 1


def compose(a, *args):
    docker = dl.docker_binary()
    if not docker:
        print('docker not found')
        return 1
    command = [docker, 'compose', '-f', a.compose] + (['--env-file', a.env_file] if a.env_file else []) + list(args)
    print('+ ' + ' '.join(command), flush=True)
    try:
        return subprocess.run(command, timeout=a.timeout).returncode
    except subprocess.TimeoutExpired:
        print(f'docker compose did not return within {a.timeout} s. Not retrying and not restarting Docker from here.')
        return 124


def harness_status(_):
    r = dl.Report()
    try:
        with urllib.request.urlopen('http://127.0.0.1:18081/ping', timeout=3) as response:
            body = response.read().decode().strip()
        r.check(body == 'pong', 'local Signal-Server admin ping', '127.0.0.1:18081 pong', f'answered {body!r}')
    except OSError as e:
        r.warn('local Signal-Server admin ping', f'127.0.0.1:18081 not answering ({e}); start: bash local_signal_server/scripts/start_server.sh')
    # Ports are tested by trying to bind them (no connection: a run in progress sees nothing).
    for name, port in (('TLS terminator', 18443), ('compact instance terminator', 19443), ('fingerprint terminator', 18445)):
        listening = not dl.port_free('127.0.0.1', port)
        (r.ok if listening else r.skip)(name, f'127.0.0.1:{port} ' + ('listening' if listening else 'closed'))
    built = (HARNESS / 'state/classpath.txt').exists()
    (r.ok if built else r.warn)('server build', 'state/classpath.txt present' if built else 'not built: bash local_signal_server/scripts/build_server.sh')
    for label, path in (('database nodes (harness, real)', HARNESS / 'state/db/real/nodes.json'),):
        if path.exists():
            nodes = json.loads(path.read_text())
            alive = [pid_alive(pid, '/server') for pid in nodes.get('pids', [])]
            ports = [not dl.port_free('127.0.0.1', nodes['base'] + 40 + j) for j in range(5)]
            r.ok(label, f'{sum(alive)}/5 processes, {sum(ports)}/5 compute ports listening (base {nodes.get("base")})')
        else:
            r.skip(label, 'none recorded (the harness starts and stops its own)')
    for label, port in (('application listener party 0', 19700), ('application listener party 1', 19701), ('daemon link 0', 19710), ('daemon link 1', 19711)):
        listening = not dl.port_free('127.0.0.1', port)
        (r.ok if listening else r.skip)(label, f'127.0.0.1:{port} ' + ('listening (a harness run with --app/--sustained in progress?)' if listening else 'closed'))
    circuits = HARNESS / 'state/circuits/manifest.txt'
    if circuits.exists():
        digest, rows = dl.read_manifest(circuits)
        r.ok('local strict circuit set', f'{len(rows)} kernels, manifest {digest[:16]}…')
    else:
        r.skip('local strict circuit set', 'state/circuits/manifest.txt missing (check_signal_service_local.py --strict produces it)')
    lock = dl.ROOT / '.deps/heavy.lock'
    try:
        holder = json.loads(lock.read_text() or '{}')
        held = pid_alive(holder.get('pid'), 'guarded.py') or pid_alive(holder.get('pid'), 'python')
        (r.warn if held else r.ok)('heavy-job lock', (f'held by pid {holder.get("pid")} since {holder.get("since")}: '
                                                     f'{" ".join(holder.get("command", []))[:120]}') if held else 'free')
    except (OSError, ValueError):
        r.skip('heavy-job lock', 'no lock file')
    docker = dl.docker_binary()
    if docker:
        try:
            out = subprocess.run([docker, 'version', '--format', '{{.Server.Version}}'], capture_output=True, text=True, timeout=20)
            (r.ok if out.returncode == 0 else r.warn)('docker', out.stdout.strip() or out.stderr.strip()[:200])
        except subprocess.TimeoutExpired:
            r.warn('docker', 'no answer within 20 s (OrbStack has hung before: do not restart it from a script)')
    else:
        r.skip('docker', 'not installed')
    return r.summary()


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('action', choices=['up', 'down', 'status'])
    p.add_argument('--config', help="the node daemon's configuration (native)")
    p.add_argument('--compose', help='a docker compose file')
    p.add_argument('--env-file', help='its environment file')
    p.add_argument('--target', choices=['local', 'production'], help='compose up: what the stack connects to')
    p.add_argument('--harness', action='store_true', help='status of the local test set-up (read-only)')
    p.add_argument('--bearer-file', help='the application bearer token file, when the daemon requires one')
    p.add_argument('--account-state', help='passed to preflight (existence and permissions only)')
    p.add_argument('--skip-preflight', action='store_true')
    p.add_argument('--i-have-the-go-ahead', action='store_true', help='OWNER ONLY: allow a non-local Signal endpoint')
    p.add_argument('--timeout', type=int, default=300, help='seconds for a docker compose command')
    a = p.parse_args()
    if a.action == 'status' and a.harness:
        sys.exit(harness_status(a))
    if bool(a.config) == bool(a.compose):
        p.error('give exactly one of --config (native) or --compose')
    if a.compose:
        if a.action == 'up':
            if not a.target:
                p.error('compose up needs --target local|production')
            if a.target == 'production' and not production_gate('a production Signal endpoint', a.i_have_the_go_ahead):
                sys.exit(1)
            sys.exit(compose(a, 'up', '-d'))
        sys.exit(compose(a, 'down') if a.action == 'down' else compose(a, 'ps'))
    sys.exit(dict(up=up_native, down=down_native, status=status_native)[a.action](a))


if __name__ == '__main__':
    main()
