#!/usr/bin/env python3
"""Pre-flight checks for one computation node (DEPLOYMENT.md, "Pre-flight checklist").

    preflight.py --config NODE.json [--word-dir DIR] [--export OUT.json] [--peer PEER.json]
                 [--account-state DIR] [--full-hash] [--no-network] [--ntp HOST]
                 [--allow-scripts] [--probe-signal-endpoint]

NODE.json is the node daemon's configuration (node_daemon/README.md, "Configuration"). Checks,
each printed as PASS / WARN / FAIL / SKIP; exit status 1 if any FAIL:

  binaries      controller, worker, certificate checker, database client (and the scaffolding KEM
                tool) exist and are executable; the worker is a production build (not `-test`);
                their SHA-256 are recorded for the comparison with the other node
  circuits      `circuits.manifest` is set (strict mode), parses, every kernel's gate list exists
                and every layout matches its pin (--full-hash: every gate list too; minutes)
  word dir      the word circuits and the 22 V3 field programs (FIELD_PROGRAMS_V3.md) match the
                worker's pins; their digest is recorded (both nodes must hold the same files)
  settings      SIGNAL_SCRIPTS is empty (production rule for now; --allow-scripts to override),
                no TEST hook and no credential in the environment, values the controller accepts;
                the agreed-settings digest (a mirror of TlsMpc/Node/Config.lean `agreedText`) for
                the send, receive and notify sessions
  secrets       peer key, database client key, bearer token, the workers' key directories: present
                and not readable by group or others
  account state --account-state DIR: the directory exists and is private. Its contents are
                NEVER listed or read
  network       (skipped with --no-network) the other daemon's peer address and the database
                nodes' compute addresses accept TCP; this node's listen ports are free. The Signal
                endpoint is contacted only if it is a loopback/private address (the local test
                server) or with --probe-signal-endpoint, which prints what it is about to do
  clock         OS synchronisation state; --ntp HOST measures the offset (skew limits: the daemons'
                link accepts 60 s, a notify request 30 s into the future)
  machine       free disk, memory, cores (and on x86-64 Linux the aes/pclmulqdq/avx2 flags)
  peer          --peer PEER.json (the other node's --export): settings digests, manifest digest,
                word-dir digest, binary hashes, worker mode, port base and peer-key fingerprint equal

--export OUT.json writes this node's facts (no secrets: hashes, digests, a salted fingerprint of
the shared peer key) for the other node's --peer.
"""
import argparse
import hashlib
import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import deploylib as dl  # noqa: E402

MIN_FREE_GB = 20.0
MIN_MEMORY_GB = {'malicious': 16.0, 'semi-honest': 8.0}


def worker_mode(path):
    """From node_worker's target layout (target/VARIANT/release/node-worker) or the image's build
    information. 'test' for a -test variant, which must never be deployed."""
    parts = Path(str(path)).parts
    if any(part in ('v3-test', 'sh-v3-test') for part in parts):
        return 'test'
    if 'sh-v3' in parts:
        return 'semi-honest'
    if 'v3' in parts:
        return 'malicious'
    if dl.IMAGE_BUILD_INFO.exists():
        return json.loads(dl.IMAGE_BUILD_INFO.read_text()).get('mode', 'unknown')
    return 'unknown'


def check_binaries(r, config, facts):
    worker = (config.get('worker') or {}).get('binary')
    named = {
        'controller': config.get('controller'),
        'worker': worker,
        'certificate_checker': (config.get('signal') or {}).get('certificate_checker'),
        'database_client': (config.get('database') or {}).get('client'),
    }
    kem = (config.get('test') or {}).get('kem_tool')
    if kem:
        named['kem_tool (scaffolding)'] = kem
    facts['binaries'] = {}
    for name, path in named.items():
        if not path:
            r.fail(f'binary {name}', 'not configured')
            continue
        p = Path(path)
        if p.is_file() and os.access(p, os.X_OK):
            digest = dl.sha256_file(p)
            facts['binaries'][name] = digest
            r.ok(f'binary {name}', f'{p} sha256 {digest[:16]}…')
        else:
            r.fail(f'binary {name}', f'{p} missing or not executable')
    mode = worker_mode(worker or '')
    facts['worker_mode'] = mode
    if mode == 'test':
        r.fail('worker build', f'{worker} is a -test build (unpinned circuits, fault hook): never deploy it')
    elif mode == 'unknown':
        r.warn('worker build', 'mode not recognisable from the path (expected node_worker/target/v3 or sh-v3, or the image build info)')
    else:
        r.ok('worker build', f'production variant, {mode}')
    env = config.get('environment') or {}
    if env.get('SIGNAL_WORKER') == 'legacy' or os.environ.get('SIGNAL_WORKER') == 'legacy':
        r.warn('worker kind', 'SIGNAL_WORKER=legacy: the C++ worker, kept for comparison only')


def check_circuits(r, config, facts, full):
    manifest = (config.get('circuits') or {}).get('manifest')
    if not manifest:
        r.fail('circuits strict mode', 'circuits.manifest is null: the production worker loads only pinned circuits')
        return
    try:
        problems, stats = dl.check_manifest_files(manifest, full=full)
    except (OSError, ValueError) as e:
        r.fail('circuit manifest', f'{manifest}: {e}')
        return
    facts['manifest'] = stats
    expected = os.environ.get('EXPECTED_MANIFEST_SHA256')
    if expected and expected != stats['manifest_sha256']:
        r.fail('manifest digest', f'{stats["manifest_sha256"]} differs from EXPECTED_MANIFEST_SHA256 {expected}')
    detail = f'{stats["kernels"]} kernels, {stats["gate_list_bytes"] / 1e9:.1f} GB, sha256 {stats["manifest_sha256"]}'
    if problems:
        r.fail('circuit files', '; '.join(problems))
    else:
        r.ok('circuit files', detail + (' (gate lists hashed)' if full else ' (layouts hashed; --full-hash for gate lists)'))


def check_word_dir(r, word_dir, facts):
    if not word_dir:
        r.skip('word dir', 'not given (--word-dir); the worker reads the directory compiled into it')
        return
    pins = dl.known_pins()
    if not pins:
        r.warn('word dir pins', 'no pins source (node_worker/src/loader.rs or the image pins.json); digest only')
    problems, stats = dl.word_dir_summary(word_dir, pins)
    facts['word_dir'] = stats
    if problems:
        r.fail('word dir', '; '.join(problems[:6]))
    else:
        r.ok('word dir', f'{stats["files"]} files, {stats["v3_programs"]} V3 programs, {stats["pinned_present"]}/{stats["pinned"]} pinned present, '
                         f'digest {stats["word_dir_sha256"][:16]}…')
    if stats and stats.get('v3_programs', 0) not in (0, 22):
        r.warn('V3 field programs', f'{stats["v3_programs"]} files; the re-export writes 22 (both nodes: all or none)')


def check_settings(r, config, facts, allow_scripts):
    env = dl.daemon_session_env(config)
    scripts = (env.get('SIGNAL_SCRIPTS') or '').strip()
    if scripts and not allow_scripts:
        r.fail('SIGNAL_SCRIPTS', f'set to "{scripts}": must stay unset/empty in production for now (STACK_NOTES.md 11.3)')
    elif scripts:
        r.warn('SIGNAL_SCRIPTS', f'set to "{scripts}" (--allow-scripts): not for production')
    else:
        r.ok('SIGNAL_SCRIPTS', 'empty (every flow legacy, as the golden records)')
    hooks = [h for h in dl.TEST_HOOKS if env.get(h)]
    r.check(not hooks, 'test hooks', 'none set', 'set (ignored without --test, but must not be configured): ' + ', '.join(hooks))
    creds = [n for n in ('SIGNAL_LOCAL_CREDENTIALS', 'SIGNAL_LOCAL_CREDENTIALS_FILE') if (config.get('environment') or {}).get(n) or os.environ.get(n)]
    r.check(not creds, 'credentials in environment', 'none', 'set: ' + ', '.join(creds) + ' (the account comes from the database nodes)')
    # The hinted (constant-depth) curve programs' checks are not yet shown safe against a cheating
    # node (PRODUCT_TODO.md section 11d): refused outright, whatever else is allowed.
    r.check(env.get('TLS_WORKER_HINTED', '0') in ('', '0'), 'TLS_WORKER_HINTED', 'off (the default, reviewed path)',
            '=1 refused: the hinted curve programs are not yet shown safe against a cheating node (PRODUCT_TODO.md 11d)')
    shifted = [n for n in ('TLS_WORKER_TEST_LINK_SHIFT', 'TLS_WORKER_TEST_PRODUCER', 'TLS_WORKER_SERVICE_FIXTURE', 'SIGNAL_LINK_DELAY_MS') if env.get(n)]
    r.check(not shifted, 'test-only worker settings', 'none', 'set: ' + ', '.join(shifted))
    try:
        facts['settings'] = dl.settings_digests(config)
        r.ok('agreed settings', ' '.join(f'{k}={v["sha256"][:12]}…' for k, v in facts['settings'].items() if k != 'worker_session'))
    except ValueError as e:
        r.fail('agreed settings', str(e))
    peer = env.get('TLS_WORKER_PEER')
    listen = env.get('TLS_WORKER_LISTEN')
    hosts = (config.get('worker') or {}).get('hosts') or []
    if peer:
        import ipaddress
        try:
            ipaddress.IPv4Address(peer)
            r.ok('TLS_WORKER_PEER', peer)
        except ValueError:
            r.fail('TLS_WORKER_PEER', f'{peer}: must be a numeric IPv4 address')
    elif hosts and any(h not in ('127.0.0.1', 'localhost') for h in hosts):
        r.fail('TLS_WORKER_PEER', 'unset but worker.hosts is not loopback: node_worker ignores hosts and takes the peer from TLS_WORKER_PEER')
    else:
        r.ok('TLS_WORKER_PEER', 'unset: both workers on this machine (rehearsal only)')
    if config.get('party') == 0 and peer and not listen:
        r.warn('TLS_WORKER_LISTEN', 'unset on party 0: the Boolean listener binds all interfaces (the field engine does regardless): rely on the firewall')
    profile = env.get('SIGNAL_CLIENT_PROFILE') or 'legacy'
    signal = config.get('signal') or {}
    if not dl.is_local_address(signal.get('endpoint', '')) and profile != 'libsignal':
        r.warn('SIGNAL_CLIENT_PROFILE', f'{profile} against a non-local endpoint; the real runs used libsignal')


def check_secrets(r, config):
    paths = {
        'peer key': config.get('peer_key_file'),
        'database client key': (config.get('database') or {}).get('key'),
        'bearer token': (config.get('application') or {}).get('token_file'),
        'send workers key directory': (config.get('worker') or {}).get('send_directory'),
        'receive workers key directory': (config.get('worker') or {}).get('receive_directory'),
        'export (scaffolding)': (config.get('test') or {}).get('export'),
    }
    for name, path in paths.items():
        if not path:
            if name in ('peer key', 'database client key', 'send workers key directory', 'receive workers key directory'):
                r.fail(name, 'not configured')
            else:
                r.skip(name, 'not configured')
            continue
        p = Path(path)
        if not p.exists():
            r.fail(name, f'{p} missing')
            continue
        if name.endswith('key directory'):
            player = p / 'Player-Data'
            if not player.is_dir():
                r.fail(name, f'{player} missing (deploy/scripts: bench_certs.sh init/trust, DEPLOYMENT.md "Key ceremony")')
                continue
            keys = [k for k in player.glob('P*.key')]
            loose = [k.name for k in keys if not dl.private_enough(k)]
            r.check(len(keys) == 1 and not loose, name,
                    f'{player}: exactly one own key, private', f'{player}: {len(keys)} keys (expected this party\'s only){"; readable by others: " + ", ".join(loose) if loose else ""}')
            continue
        mode, _ = dl.mode_string(p)
        if dl.private_enough(p):
            r.ok(name, f'{p} {mode}')
        else:
            r.fail(name, f'{p} {mode}: readable by group or others (chmod 600)')


def peer_key_fingerprint(config):
    path = config.get('peer_key_file')
    if not path or not Path(path).is_file():
        return None
    key = Path(path).read_bytes().strip()
    return hashlib.sha256(b'tls-mpc deploy peer-key check v1\n' + key).hexdigest()[:24]


def check_account_state(r, directory):
    if not directory:
        r.skip('account state', 'not given (--account-state)')
        return
    p = Path(directory)
    if not p.exists():
        r.fail('account state', f'{p} does not exist')
        return
    if not p.is_dir():
        r.fail('account state', f'{p} is not a directory')
        return
    mode, uid = dl.mode_string(p)
    if uid != os.getuid():
        r.warn('account state owner', f'{p} is owned by uid {uid}, not this user ({os.getuid()})')
    r.check(dl.private_enough(p), 'account state permissions', f'{p} {mode} (contents not read)', f'{p} {mode}: chmod 700')


def check_network(r, config, probe_signal):
    party = config.get('party')
    peer = config.get('peer')
    if peer:
        host, port = dl.split_hostport(peer)
        ok, err = dl.tcp_reachable(host, port)
        (r.ok if ok else r.warn)('peer daemon link', f'{peer} ' + ('accepts TCP' if ok else f'not reachable ({err}); fine if the other daemon is not started yet'))
    for key in ('listen', 'peer_listen'):
        address = config.get(key)
        if address:
            host, port = dl.split_hostport(address)
            if host in ('0.0.0.0', '::') and not (config.get('application') or {}).get('token_file') and key == 'listen':
                r.fail(key, f'{address}: a wildcard address needs application.token_file (the daemon refuses it)')
            free = dl.port_free(host if host not in ('0.0.0.0', '::') else '0.0.0.0', port)
            (r.ok if free else r.warn)(f'{key} port', f'{address} ' + ('free' if free else 'in use (the daemon already running?)'))
    base = (config.get('worker') or {}).get('port_base')
    if base:
        busy = [p for p in range(base, base + 640) if p % 10 in (0,) and not dl.port_free('0.0.0.0', p)]
        (r.ok if not busy else r.warn)('worker port range', f'{base}..{base + 639}' + (f'; in use: {busy[:6]}' if busy else ' free (sampled at session ports)'))
        if party == 0:
            r.ok('worker listener', f'party 0 listens on {base}..{base + 639}; party 1 must reach them (firewall)')
    network = (config.get('database') or {}).get('network')
    if network and Path(network).is_file():
        try:
            addresses = dl.load_json(network).get('compute_addresses') or []
        except (OSError, ValueError) as e:
            addresses = []
            r.fail('database network config', str(e))
        reachable = 0
        for address in addresses:
            host, port = dl.split_hostport(address)
            ok, _ = dl.tcp_reachable(host, port, timeout=2)
            reachable += ok
        need = 4 if len(addresses) == 5 else len(addresses)
        (r.ok if reachable >= need else r.fail)('database nodes', f'{reachable}/{len(addresses)} compute ports accept TCP (need at least {need})')
    elif network:
        r.fail('database network config', f'{network} missing')
    signal = config.get('signal') or {}
    endpoint, port = signal.get('endpoint'), signal.get('port')
    if not endpoint:
        r.fail('signal endpoint', 'not configured')
    elif dl.is_local_address(endpoint):
        ok, err = dl.tcp_reachable(endpoint, int(port or 443))
        (r.ok if ok else r.fail)('signal endpoint (local)', f'{endpoint}:{port} ' + ('accepts TCP' if ok else err))
    elif probe_signal:
        if party != 0:
            r.skip('signal endpoint', 'only party 0 (the leader) connects to the Signal server')
        else:
            print(f'about to open ONE TCP connection to {endpoint}:{port} and close it (no TLS, no request)', flush=True)
            ok, err = dl.tcp_reachable(endpoint, int(port or 443), timeout=5)
            (r.ok if ok else r.fail)('signal endpoint (probe)', f'{endpoint}:{port} ' + ('accepts TCP' if ok else err))
    else:
        r.skip('signal endpoint', f'{endpoint}:{port} is not local: not contacted (--probe-signal-endpoint to open one TCP connection)')
        if party == 0:
            r.warn('production target', 'this node will connect to the real Signal service when its daemon starts: owner go-ahead required')


def check_clock(r, ntp):
    state, detail = dl.clock_synchronized()
    if state is True:
        r.ok('clock synchronised', detail)
    elif state is False:
        r.fail('clock synchronised', detail)
    else:
        r.skip('clock synchronised', detail)
    if ntp:
        try:
            offset = dl.sntp_offset(ntp)
            (r.ok if abs(offset) < 1.0 else r.fail)('clock offset', f'{offset:+.3f} s against {ntp} (limit 1 s; the daemons tolerate 60 s, requests 30 s)')
        except OSError as e:
            r.warn('clock offset', f'{ntp}: {e}')


def check_machine(r, config, facts):
    mode = facts.get('worker_mode', 'malicious')
    state = config.get('state_directory') or '.'
    disk = dl.free_gb(state)
    r.check(disk >= MIN_FREE_GB, 'free disk (state)', f'{disk:.0f} GB at {state}', f'{disk:.0f} GB at {state}; at least {MIN_FREE_GB:.0f} GB')
    memory = dl.total_memory_gb()
    need = MIN_MEMORY_GB.get(mode, 16.0)
    if memory is None:
        r.skip('memory', 'unknown')
    else:
        (r.ok if memory >= need else r.fail)('memory', f'{memory:.0f} GB (one pair: {need:.0f} GB or more in {mode} mode; DEPLOYMENT.md "Hardware")')
    cores = os.cpu_count() or 0
    (r.ok if cores >= 8 else r.warn)('cores', f'{cores} (8 or more for one worker pair)')
    flags = dl.cpu_flags()
    if flags is not None:
        missing = [f for f in ('aes', 'pclmulqdq', 'avx2') if f not in flags]
        r.check(not missing, 'CPU flags', 'aes pclmulqdq avx2', 'missing: ' + ' '.join(missing))
    facts['machine'] = dict(memory_gb=round(memory or 0, 1), cores=cores, free_gb=round(disk, 1))


def compare_peer(r, facts, peer_path):
    peer = json.loads(Path(peer_path).read_text())
    me, other = facts, peer
    if me.get('party') == other.get('party'):
        r.fail('peer party', f'both nodes are party {me.get("party")}')
    else:
        r.ok('peer party', f'this {me.get("party")}, other {other.get("party")}')
    for kind in ('serve', 'receive', 'notify'):
        a = ((me.get('settings') or {}).get(kind) or {}).get('sha256')
        b = ((other.get('settings') or {}).get(kind) or {}).get('sha256')
        r.check(a and a == b, f'settings digest ({kind})', a or '', f'this {a} other {b}: the controllers would end every session')
    a, b = (me.get('settings') or {}).get('worker_session'), (other.get('settings') or {}).get('worker_session')
    r.check(a == b, 'worker session settings', 'equal', f'this {a} other {b}: the workers would disagree on their first request')
    a, b = (me.get('manifest') or {}).get('manifest_sha256'), (other.get('manifest') or {}).get('manifest_sha256')
    r.check(a and a == b, 'manifest digest', a or '', f'this {a} other {b}: "circuit manifest disagreement" at start')
    a, b = (me.get('word_dir') or {}).get('word_dir_sha256'), (other.get('word_dir') or {}).get('word_dir_sha256')
    if a or b:
        r.check(a == b, 'word dir digest', a or '', f'this {a} other {b}: both nodes must hold the same word circuits and V3 programs')
    for name in ('controller', 'worker', 'database_client', 'certificate_checker'):
        a, b = (me.get('binaries') or {}).get(name), (other.get('binaries') or {}).get(name)
        if a == b:
            r.ok(f'binary {name} equal', (a or '')[:16])
        else:
            (r.fail if name in ('controller', 'worker') else r.warn)(f'binary {name} equal',
                                                                    f'this {(a or "")[:16]} other {(b or "")[:16]} (rebuild both from one commit; DEPLOYMENT.md "Build")')
    r.check(me.get('worker_mode') == other.get('worker_mode'), 'worker mode', str(me.get('worker_mode')), f'this {me.get("worker_mode")} other {other.get("worker_mode")}')
    r.check(me.get('port_base') == other.get('port_base'), 'port base', str(me.get('port_base')), f'this {me.get("port_base")} other {other.get("port_base")}')
    a, b = me.get('peer_key_fingerprint'), other.get('peer_key_fingerprint')
    r.check(a and a == b, 'peer key', 'same key on both nodes (salted fingerprint)', 'fingerprints differ or missing: the daemons will refuse each other')
    skew = abs((me.get('exported_at') or 0) - (other.get('exported_at') or 0))
    if skew > 3600:
        r.warn('peer export age', f'the two exports were made {skew / 3600:.1f} h apart: re-export both')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--config', required=True, help="the node daemon's configuration (JSON)")
    p.add_argument('--word-dir', help='the word-circuit directory the worker was built for (default: the image\'s /opt/tls-mpc/word, else .deps/emp-hybrid-word-v1)')
    p.add_argument('--export', help="write this node's facts (no secrets) for the other node's --peer")
    p.add_argument('--peer', help="the other node's --export file")
    p.add_argument('--account-state', help='account state directory: existence and permissions only, never read')
    p.add_argument('--full-hash', action='store_true', help='hash every gate list too (tens of GB: minutes)')
    p.add_argument('--no-network', action='store_true', help='no TCP checks')
    p.add_argument('--ntp', help='an NTP server to measure the clock offset against (one UDP exchange)')
    p.add_argument('--allow-scripts', action='store_true', help='accept a non-empty SIGNAL_SCRIPTS (development only)')
    p.add_argument('--probe-signal-endpoint', action='store_true',
                   help='open one TCP connection to a NON-local Signal endpoint (party 0 only). Off by default: owner go-ahead')
    a = p.parse_args()
    config_path = Path(a.config)
    if dl.is_forbidden(config_path):
        sys.exit('refusing: that path is account state')
    r = dl.Report()
    try:
        config = dl.load_json(config_path)
    except (OSError, ValueError) as e:
        r.fail('configuration', f'{config_path}: {e}')
        sys.exit(r.summary())
    r.ok('configuration', f'{config_path} party {config.get("party")}')
    facts = dict(format='tls-mpc-node-facts-v1', party=config.get('party'), exported_at=int(time.time()),
                 port_base=(config.get('worker') or {}).get('port_base'), config_sha256=dl.sha256_file(config_path))
    word_dir = a.word_dir or (Path('/opt/tls-mpc/word') if Path('/opt/tls-mpc/word').is_dir() else (dl.WORD_DIR_REPO if dl.WORD_DIR_REPO.is_dir() else None))
    check_binaries(r, config, facts)
    check_circuits(r, config, facts, a.full_hash)
    check_word_dir(r, word_dir, facts)
    check_settings(r, config, facts, a.allow_scripts)
    check_secrets(r, config)
    facts['peer_key_fingerprint'] = peer_key_fingerprint(config)
    check_account_state(r, a.account_state)
    if a.no_network:
        r.skip('network', '--no-network')
    else:
        check_network(r, config, a.probe_signal_endpoint)
    check_clock(r, a.ntp)
    check_machine(r, config, facts)
    if a.peer:
        compare_peer(r, facts, a.peer)
    if a.export:
        # The settings text is public (no paths, no secrets): kept in the export for diagnosis.
        Path(a.export).write_text(json.dumps(facts, indent=1, sort_keys=True) + '\n')
        print(f'facts written to {a.export}')
    sys.exit(r.summary())


if __name__ == '__main__':
    main()
