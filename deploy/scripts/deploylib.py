"""Shared helpers of the deployment scripts in deploy/scripts/ (no third-party modules).

Nothing here opens a network connection except `tcp_reachable` and `sntp_offset`, which the
scripts call only for addresses the operator configured, and never for a Signal host unless the
operator passed an explicit flag (see preflight.py).

Read-only towards everything it inspects. It never reads real_signal/state/ (or any account
state directory) beyond `stat()` of the directory itself.
"""
import hashlib
import ipaddress
import json
import os
import platform
import re
import shutil
import socket
import stat
import struct
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]          # repository root (or /opt/tls-mpc/share/deploy/.. in the image)
DEPLOY = ROOT / 'deploy'
LOADER_RS = ROOT / 'node_worker/src/loader.rs'
WORD_DIR_REPO = ROOT / '.deps/emp-hybrid-word-v1'
IMAGE_PINS = Path('/opt/tls-mpc/share/pins.json')   # written at image build time (worker.Dockerfile)
IMAGE_BUILD_INFO = Path('/opt/tls-mpc/share/build-info.json')
MANIFEST_FORMAT = 'EMP_HYBRID_CIRCUIT_MANIFEST_V1'

# Paths no script here may open (only stat the directory the operator names).
FORBIDDEN_READ = [ROOT / 'real_signal' / 'state']

# ---------------------------------------------------------------------------------------------
# Output


class Report:
    """PASS / WARN / FAIL / SKIP lines and a summary. FAIL makes the exit status 1."""

    def __init__(self, quiet=False):
        self.rows = []
        self.quiet = quiet

    def add(self, status, name, detail=''):
        self.rows.append((status, name, detail))
        if not self.quiet:
            print(f'{status:4}  {name}' + (f': {detail}' if detail else ''), flush=True)

    def ok(self, name, detail=''):
        self.add('PASS', name, detail)

    def warn(self, name, detail=''):
        self.add('WARN', name, detail)

    def fail(self, name, detail=''):
        self.add('FAIL', name, detail)

    def skip(self, name, detail=''):
        self.add('SKIP', name, detail)

    def check(self, condition, name, detail_ok='', detail_fail=''):
        (self.ok if condition else self.fail)(name, detail_ok if condition else (detail_fail or detail_ok))
        return condition

    def failed(self):
        return [r for r in self.rows if r[0] == 'FAIL']

    def summary(self):
        counts = {}
        for status, _, _ in self.rows:
            counts[status] = counts.get(status, 0) + 1
        text = ', '.join(f'{counts.get(k, 0)} {k}' for k in ('PASS', 'WARN', 'FAIL', 'SKIP'))
        print(f'---- {text}', flush=True)
        return 1 if self.failed() else 0


# ---------------------------------------------------------------------------------------------
# Files and hashes


def sha256_file(path, block=1 << 20):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(block), b''):
            h.update(chunk)
    return h.hexdigest()


def sha256_text(text):
    return hashlib.sha256(text.encode()).hexdigest()


def is_forbidden(path):
    p = Path(path).resolve()
    return any(p == f.resolve() or f.resolve() in p.parents for f in FORBIDDEN_READ if f.exists())


def load_json(path):
    path = Path(path)
    if is_forbidden(path):
        raise SystemExit(f'refusing to read {path}: account state is never read by these scripts')
    return json.loads(path.read_text())


def mode_string(path):
    st = os.stat(path)
    return stat.filemode(st.st_mode), st.st_uid


def private_enough(path):
    """True when neither group nor others can read (or write) the file or directory."""
    st = os.stat(path)
    return (st.st_mode & 0o077) == 0


def free_gb(path):
    probe = Path(path)
    while not probe.exists() and probe != probe.parent:
        probe = probe.parent
    return shutil.disk_usage(probe).free / 1e9


def total_memory_gb():
    try:
        if sys.platform == 'darwin':
            out = subprocess.run(['sysctl', '-n', 'hw.memsize'], capture_output=True, text=True, timeout=10).stdout
            return int(out.strip()) / 1e9
        with open('/proc/meminfo') as f:
            for line in f:
                if line.startswith('MemTotal:'):
                    return int(line.split()[1]) * 1024 / 1e9
    except (OSError, ValueError, subprocess.SubprocessError):
        pass
    return None


def cpu_flags():
    """x86-64 Linux: the flags the engines need. None where it cannot be read (macOS, arm64)."""
    if sys.platform != 'linux' or platform.machine() not in ('x86_64', 'amd64'):
        return None
    try:
        with open('/proc/cpuinfo') as f:
            for line in f:
                if line.startswith('flags'):
                    return set(line.split(':', 1)[1].split())
    except OSError:
        return None
    return None


# ---------------------------------------------------------------------------------------------
# The circuit manifest (scripts/produce_circuits.py, node_worker/src/loader.rs)


def kernel_stem(arguments):
    return 'kernel-' + arguments.replace(' ', '-')


def read_manifest(path):
    """(digest, {name: (sha256, layout_sha256)}) of a manifest.txt; raises ValueError if malformed."""
    data = Path(path).read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    lines = data.decode().split('\n')
    if not lines or lines[0] != MANIFEST_FORMAT:
        raise ValueError('not an EMP_HYBRID_CIRCUIT_MANIFEST_V1 file')
    rows = {}
    for line in lines[1:]:
        if not line:
            continue
        parts = line.split(' ')
        if len(parts) < 3 or not re.fullmatch(r'[0-9a-f]{64}', parts[0]) or not re.fullmatch(r'[0-9a-f]{64}', parts[1]):
            raise ValueError(f'malformed row: {line[:80]}')
        name = ' '.join(parts[2:])
        if name in rows:
            raise ValueError(f'kernel listed twice: {name}')
        rows[name] = (parts[0], parts[1])
    return digest, rows


def check_manifest_files(path, full=False, limit_report=5):
    """Every listed kernel's .flat exists and its .layout matches its pin; with `full`, every .flat
    is hashed too (tens of GB for the production set: minutes). Returns (problems, stats)."""
    digest, rows = read_manifest(path)
    directory = Path(path).parent
    problems, total_bytes = [], 0
    for name, (flat_sha, layout_sha) in sorted(rows.items()):
        stem = kernel_stem(name)
        flat, layout = directory / (stem + '.flat'), directory / (stem + '.layout')
        if not flat.is_file():
            problems.append(f'missing {flat.name}')
            continue
        total_bytes += flat.stat().st_size
        if not layout.is_file():
            problems.append(f'missing {layout.name}')
        elif sha256_file(layout) != layout_sha:
            problems.append(f'layout pin differs: {name}')
        if full and sha256_file(flat) != flat_sha:
            problems.append(f'gate list pin differs: {name}')
    stats = dict(manifest_sha256=digest, kernels=len(rows), gate_list_bytes=total_bytes, full_hash=full)
    return problems[:limit_report] + ([f'... and {len(problems) - limit_report} more'] if len(problems) > limit_report else []), stats


# ---------------------------------------------------------------------------------------------
# Word circuits and V3 field programs (FIELD_PROGRAMS_V3.md; node_worker/src/loader.rs)


def parse_loader_pins(loader_rs=LOADER_RS):
    """{file: sha256} of node_worker's FIELD_PROGRAMS and WORD_CIRCUITS, read from its source."""
    text = Path(loader_rs).read_text()
    consts = dict(re.findall(r'const ([A-Z0-9_]+): &str = "([0-9a-f]{64})";', text))
    pins = {}
    for kind in ('FieldProgramPin', 'WordCircuit'):
        for block in re.findall(kind + r'\s*\{(.*?)\}', text, re.S):
            file = re.search(r'file:\s*"([^"]+)"', block)
            sha = re.search(r'sha256:\s*(?:"([0-9a-f]{64})"|([A-Z0-9_]+))', block)
            if not file or not sha:
                continue
            value = sha.group(1) or consts.get(sha.group(2))
            if value:
                pins[file.group(1)] = value
    return pins


def known_pins():
    """Pins from the image (pins.json) or from the source tree, whichever exists."""
    if IMAGE_PINS.exists():
        return json.loads(IMAGE_PINS.read_text())
    if LOADER_RS.exists():
        return parse_loader_pins()
    return {}


def word_dir_summary(word_dir, pins=None):
    """Digest of the top-level *.flat and *.v3 files of the word-circuit directory (what both
    nodes must hold identically), and every pinned file checked. Returns (problems, stats)."""
    word_dir = Path(word_dir)
    if not word_dir.is_dir():
        return [f'{word_dir} is not a directory'], {}
    pins = known_pins() if pins is None else pins
    files = sorted(p for p in word_dir.iterdir() if p.is_file() and p.suffix in ('.flat', '.v3'))
    lines, problems = [], []
    hashes = {}
    for p in files:
        hashes[p.name] = sha256_file(p)
        lines.append(f'{hashes[p.name]} {p.name}')
    for name, sha in sorted(pins.items()):
        if name not in hashes:
            problems.append(f'pinned file missing: {name}')
        elif hashes[name] != sha:
            problems.append(f'pin differs: {name}')
    v3 = [n for n in hashes if n.endswith('.v3')]
    stats = dict(word_dir_sha256=sha256_text('\n'.join(lines) + '\n'), files=len(files), v3_programs=len(v3),
                 pinned=len(pins), pinned_present=sum(1 for n in pins if n in hashes))
    return problems, stats


# ---------------------------------------------------------------------------------------------
# The agreed settings (TlsMpc/Node/Config.lean). A MIRROR of `Config.agreedText` for the session
# kinds a node daemon starts; the authoritative comparison is the controllers' own at the start
# of every session (they exchange SHA-256 of this text and end the session on a difference).

SCRIPT_NAMES = ['random', 'upgrade', 'contacts', 'account', 'masks', 'tls', 'curve', 'send', 'receive', 'refresh', 'ceremony']
TEST_HOOKS = ['SIGNAL_LOCAL_TIMESTAMP', 'SIGNAL_LOCAL_PAUSE_AFTER', 'SIGNAL_LOCAL_PAUSE_REFRESH', 'SIGNAL_LOCAL_BROADCASTS',
              'SIGNAL_LOCAL_EXTRA_CONTACTS', 'SIGNAL_LOCAL_NEW_CONTACT', 'SIGNAL_LOCAL_STORE', 'SIGNAL_LOCAL_TRACE']
# Settings that change what the two workers compute (folded into node_worker's session string,
# node_worker/src/config.rs): both nodes must set them alike too.
WORKER_SESSION_VARIABLES = ['TLS_WORKER_HINTED', 'TLS_WORKER_FIELD_DIRECT', 'TLS_WORKER_KEY_AGREEMENT', 'TLS_WORKER_TYPED_OPEN',
                            'TLS_WORKER_TRIPLE_STOCK', 'TLS_WORKER_FIELD_BATCH', 'TLS_WORKER_FIELD_STOCK']


def _lean_option_str(value):
    return 'none' if value is None else f'(some {value})'


def agreed_text(env, kind, socks=None):
    """`Config.agreedText` for a daemon-started session of `kind` in {'serve', 'receive', 'notify'}
    under environment `env` (a dict). Raises ValueError where the controller would refuse."""
    profile = env.get('SIGNAL_CLIENT_PROFILE')
    if profile not in (None, 'legacy', 'libsignal'):
        raise ValueError(f'SIGNAL_CLIENT_PROFILE must be libsignal or legacy, not {profile}')
    worker = env.get('SIGNAL_WORKER')
    if worker not in (None, 'node', 'legacy'):
        raise ValueError(f'SIGNAL_WORKER must be node or legacy, not {worker}')
    scripts = []
    for name in (env.get('SIGNAL_SCRIPTS') or '').split(','):
        name = name.strip()
        if name and name not in scripts:
            if name not in SCRIPT_NAMES:
                raise ValueError(f'SIGNAL_SCRIPTS: unknown flow group {name}')
            scripts.append(name)
    socks = socks if socks is not None else env.get('SIGNAL_TOR_SOCKS')
    circuits = env.get('SIGNAL_TOR_CIRCUITS')
    circuits = int(circuits) if circuits not in (None, '') else (1 if socks else 0)
    try:
        prepare = min(64, int(env.get('SIGNAL_PREPARE_BATCH', '32')))
    except ValueError:
        prepare = 32
    receive_jump = env.get('SIGNAL_RECEIVE_JUMP')
    socket_label = {'serve': 'unauthenticated', 'notify': 'unauthenticated', 'receive': 'stored'}[kind]
    expect = 1000000000 if kind == 'receive' else int(env.get('SIGNAL_LOCAL_EXPECT', '1') or 1)
    text = ('settings v1; '
            f'profile={"libsignal" if profile == "libsignal" else "legacy"} '
            f'ack_refused={"false" if env.get("SIGNAL_ACK_REFUSED") == "0" else "true"} '
            f'recovery={"false" if env.get("SIGNAL_RECOVERY") == "0" else "true"} '
            f'prepare_batch={prepare} '
            f'bundle_slots={"false" if env.get("SIGNAL_BUNDLE_SLOTS") == "0" else "true"} '
            f'receive_jump={_lean_option_str(receive_jump)} '
            f'hinted={"true" if env.get("TLS_WORKER_HINTED") == "1" else "false"} '
            f'circuits={circuits} worker={"legacy" if worker == "legacy" else "node"}'
            + (f' scripts={",".join(scripts)}' if scripts else '')
            + f'; socket={socket_label} expect={expect} ceremony=none serve={"true" if kind == "serve" else "false"} '
            f'notify={"true" if kind == "notify" else "false"} export={"true" if env.get("SIGNAL_LOCAL_EXPORT") else "false"} '
            f'database={"true" if env.get("SIGNAL_DB_CLIENT") else "false"}; test=none')
    return text


def daemon_session_env(config, base_env=None):
    """The environment a node daemon gives its controllers (node_daemon/src/channels/controller.rs
    `session_command`), as far as it decides the agreed settings."""
    env = dict(base_env if base_env is not None else os.environ)
    for name, value in (config.get('environment') or {}).items():
        env[name] = str(value)
    db = config.get('database') or {}
    if db.get('client'):
        env['SIGNAL_DB_CLIENT'] = db['client']
    test = config.get('test') or {}
    if test.get('export'):
        env['SIGNAL_LOCAL_EXPORT'] = test['export']   # otherwise whatever the daemon's own environment has passes through
    if (config.get('circuits') or {}).get('manifest'):
        env['CIRCUIT_MANIFEST'] = config['circuits']['manifest']
    proxy = config.get('proxy') or {}
    if proxy.get('socks'):
        env['SIGNAL_TOR_SOCKS'] = proxy['socks']
        env['SIGNAL_TOR_CIRCUITS'] = str(proxy.get('circuits', 1))
    for name in ('SIGNAL_LOCAL_CREDENTIALS', 'SIGNAL_LOCAL_RECEIVE', 'SIGNAL_LOCAL_EXPECT', 'SIGNAL_DB_REQUEST', 'SIGNAL_NOTIFY_ID',
                 'SIGNAL_NOTIFY_JOURNAL', 'SIGNAL_NOTIFY_MESSAGE_FILE', 'SIGNAL_LOCAL_EVENTS', 'SIGNAL_RECOVERY', 'SIGNAL_SERVE_DIR'):
        env.pop(name, None)      # decided by the daemon per session, never inherited
    return env


def settings_digests(config, base_env=None):
    env = daemon_session_env(config, base_env)
    out = {}
    for kind in ('serve', 'receive', 'notify'):
        text = agreed_text(env, kind)
        out[kind] = dict(sha256=sha256_text(text), text=text)
    out['worker_session'] = {name: env.get(name) for name in WORKER_SESSION_VARIABLES}
    return out


# ---------------------------------------------------------------------------------------------
# Network


def is_local_address(host):
    """Loopback or private (RFC 1918 / ULA) numeric address, or localhost."""
    if host in ('localhost', 'host.docker.internal', 'host.orb.internal'):
        return True
    try:
        ip = ipaddress.ip_address(host)
    except ValueError:
        return False
    return ip.is_loopback or ip.is_private


def split_hostport(text):
    host, _, port = text.rpartition(':')
    return host.strip('[]'), int(port)


def tcp_reachable(host, port, timeout=3.0):
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True, ''
    except OSError as e:
        return False, str(e)


def port_free(host, port):
    with socket.socket() as s:
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            s.bind((host, port))
            return True
        except OSError:
            return False


def sntp_offset(server, timeout=3.0):
    """Clock offset in seconds against an (S)NTP server the operator names. One UDP exchange."""
    packet = b'\x1b' + 47 * b'\0'
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
        s.settimeout(timeout)
        t0 = time.time()
        s.sendto(packet, (server, 123))
        data, _ = s.recvfrom(48)
        t3 = time.time()
    seconds, fraction = struct.unpack('!II', data[40:48])
    t2 = seconds - 2208988800 + fraction / 2 ** 32
    return t2 - (t0 + t3) / 2


def clock_synchronized():
    """(state, detail): whether the OS reports its clock as synchronized. None when unknown."""
    if shutil.which('timedatectl'):
        r = subprocess.run(['timedatectl', 'show', '-p', 'NTPSynchronized', '--value'], capture_output=True, text=True, timeout=10)
        value = r.stdout.strip()
        if value in ('yes', 'no'):
            return value == 'yes', f'timedatectl NTPSynchronized={value}'
    if shutil.which('chronyc'):
        r = subprocess.run(['chronyc', 'tracking'], capture_output=True, text=True, timeout=10)
        if r.returncode == 0:
            leap = [l for l in r.stdout.splitlines() if l.startswith('Leap status')]
            return ('Normal' in leap[0]) if leap else None, (leap[0] if leap else 'chronyc tracking')
    if sys.platform == 'darwin':
        return None, 'macOS: not checked (use --ntp HOST to measure the offset)'
    return None, 'no timedatectl or chronyc'


# ---------------------------------------------------------------------------------------------
# Redaction (collect_logs.py). Conservative: anything long and random-looking goes.


def _random_looking(token):
    """Base64-like: mixed case and several digits (a path or a word rarely is)."""
    return sum(c.isdigit() for c in token) >= 4 and any(c.isupper() for c in token) and any(c.islower() for c in token)


REDACTIONS = [
    (re.compile(r'-----BEGIN [A-Z ]+-----.*?-----END [A-Z ]+-----', re.S), '[pem block]'),
    (re.compile(r'(?i)(authorization\s*[:=]\s*)(basic|bearer)\s+\S+'), r'\1\2 [redacted]'),
    (re.compile(r'(?i)("?(?:bearer|token|password|passwd|secret|share|credentials?|key|private[a-z_]*|captcha|code)"?\s*[:=]\s*)("[^"]*"|\S+)'),
     r'\1[redacted]'),
    (re.compile(r'(SIGNAL_LOCAL_CREDENTIALS(?:_FILE)?=)\S+'), r'\1[redacted]'),
    (re.compile(r'\+\d{7,15}\b'), '[phone]'),
    (re.compile(r'\b[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}\b'), '[uuid]'),
    (re.compile(r'\b[0-9a-fA-F]{32,}\b'), lambda m: f'[hex:{len(m.group(0))}]'),
    (re.compile(r'[A-Za-z0-9+/_-]{40,}={0,2}'), lambda m: f'[b64:{len(m.group(0))}]' if _random_looking(m.group(0)) else m.group(0)),
]
ID_REDACTIONS = [
    (re.compile(r'("id"\s*:\s*)"?\d+"?'), r'\1"[id]"'),
    (re.compile(r'("ids"\s*:\s*)\[[^\]]*\]'), r'\1["[ids]"]'),
    (re.compile(r'\b\d{20,39}\b'), '[id]'),
]


def redact(text, keep_ids=False):
    for pattern, replacement in REDACTIONS + ([] if keep_ids else ID_REDACTIONS):
        text = pattern.sub(replacement, text)
    return text


# ---------------------------------------------------------------------------------------------
# Daemon protocol (node_daemon/README.md): one JSON line per request and reply.


def daemon_call(address, request, bearer=None, timeout=10.0):
    host, port = split_hostport(address)
    if bearer:
        request = dict(request, bearer=bearer)
    with socket.create_connection((host, port), timeout=timeout) as s:
        s.sendall((json.dumps(request) + '\n').encode())
        data = b''
        while not data.endswith(b'\n'):
            chunk = s.recv(65536)
            if not chunk:
                break
            data += chunk
    return json.loads(data.decode() or '{}')


def docker_binary():
    for candidate in (shutil.which('docker'), os.path.expanduser('~/.orbstack/bin/docker'), '/usr/bin/docker', '/usr/local/bin/docker'):
        if candidate and os.path.exists(candidate):
            return candidate
    return None


def run_logged(command, log_path, timeout, cwd=None, env=None):
    """Run a command with its output appended to `log_path`; returns (status, tail). Status 124
    on timeout (the process group is killed; nothing else is touched)."""
    log_path = Path(log_path)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with open(log_path, 'a') as log:
        log.write(f'\n+ {" ".join(map(str, command))}\n')
        log.flush()
        try:
            r = subprocess.run([str(c) for c in command], stdout=log, stderr=subprocess.STDOUT, cwd=cwd, env=env, timeout=timeout,
                               start_new_session=True)
            status = r.returncode
        except subprocess.TimeoutExpired:
            status = 124
            log.write(f'\n[timed out after {timeout} s]\n')
    tail = log_path.read_text(errors='replace').splitlines()[-15:]
    return status, tail
