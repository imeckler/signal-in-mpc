#!/usr/bin/env python3
"""Health endpoint, monitoring page and helpers, ON a deployed machine (standard library only).

    pb_health.py serve CONFIG      /health, /facts, /public on the tunnel address and localhost, port 9100
    pb_health.py page CONFIG       the monitoring page on localhost:8088 (and every address if page_public)
    pb_health.py verdict FILE MODE DATA   judge a pre-flight output (MODE strict | relaxed | pair-strict | pair-relaxed)
    pb_health.py logs LINES OUTDIR       redacted logs of this node's services
    pb_health.py db-ready NETWORK TIMEOUT  wait for a database quorum before the account ceremony

What the endpoints expose (public by design, nothing secret, no contact data): node name and role,
container and unit states, image digests, the circuit / word / settings digests and the pre-flight
facts (hashes and the agreed settings text), tunnel handshake ages, disk and memory use, the daemon's
status COUNTS (numbers and yes/no only: no ids), certificate expiry dates, the database's last epoch
number. They never read keys, shares, the account export's private parts, journals or work files.

Why a ~400-line page and not Uptime Kuma or Grafana: it needs no account, no database and no
setup, it runs on the nodes themselves over the tunnel, and it can show this system's own checks
(agreed-settings digests equal on both nodes, certificate expiry) that a generic probe cannot.
"""
import html
import json
import os
import re
import socket
import subprocess
import sys
import threading
import time
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEALTH_PORT, PAGE_PORT, DAEMON_PORT = 9100, 8088, 19700
CONTAINERS = {'mpc': ['tls-mpc-node'], 'db': ['ssdb-node', 'ssdb-postgres'], 'app': []}
UNITS = {'mpc': ['wg-quick@wg0', 'tls-mpc-node', 'pb-certificate.timer'], 'db': ['wg-quick@wg0', 'ssdb-postgres', 'ssdb-node'], 'app': ['wg-quick@wg0']}
EPOCH = re.compile(r'Successfully updated database secrets for epoch (\d+)')


def sh(argv, timeout=10):
    """(exit status, standard output and standard error together: `docker logs` replays a
    container's stderr on stderr)."""
    try:
        r = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=timeout)
        return r.returncode, r.stdout
    except (OSError, subprocess.TimeoutExpired) as e:
        return 1, str(e)


def numbers_only(value, depth=0):
    """Keep numbers and yes/no values only (the daemon's status counts): never strings or lists."""
    if isinstance(value, bool) or isinstance(value, (int, float)):
        return value
    if isinstance(value, dict) and depth < 3:
        out = {k: numbers_only(v, depth + 1) for k, v in value.items()}
        return {k: v for k, v in out.items() if v is not None and v != {}}
    return None


def daemon_status(address):
    try:
        with socket.create_connection((address, DAEMON_PORT), timeout=5) as s:
            s.sendall(b'{"op":"status"}\n')
            data = b''
            while not data.endswith(b'\n') and len(data) < 1 << 20:
                chunk = s.recv(65536)
                if not chunk:
                    break
                data += chunk
        return numbers_only(json.loads(data.decode()))
    except (OSError, ValueError):
        return None


def cert_end(pem):
    code, out = sh(['openssl', 'x509', '-in', str(pem), '-noout', '-enddate'])
    if code:
        return None
    end = out.strip().split('=', 1)[1]
    try:
        return int(time.mktime(time.strptime(end, '%b %d %H:%M:%S %Y %Z')) - time.timezone)
    except ValueError:
        return None


def read_json(path):
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError):
        return None


class Health:
    def __init__(self, config):
        self.c = config
        self.data = Path(config['data_root'])
        self.cache, self.at = None, 0
        self.peer_facts, self.peer_at = None, 0
        self.lock = threading.Lock()

    def collect(self):
        with self.lock:
            if self.cache and time.time() - self.at < 15:
                return self.cache
            self.cache, self.at = self._collect(), time.time()
            return self.cache

    def _collect(self):
        c, now = self.c, time.time()
        role = c['role']
        h = dict(node=c['node'], role=role, deployment=c['deployment'], time=int(now), problems=[], notes=[])
        exp = c.get('expected') or {}
        h['software'] = {k: exp.get(k) for k in ('tool_commit', 'image_id', 'mode', 'manifest_sha256', 'word_dir_sha256', 'pins_sha256', 'settings')}
        # units and containers
        units = {}
        for unit in UNITS.get(role, []):
            code, out = sh(['systemctl', 'is-active', unit])
            units[unit] = out.strip() or 'unknown'
        h['units'] = units
        code, out = sh(['docker', 'ps', '-a', '--format', '{{json .}}'])
        containers = {}
        for line in out.splitlines() if code == 0 else []:
            try:
                row = json.loads(line)
            except ValueError:
                continue
            if row.get('Names') in CONTAINERS.get(role, []):
                containers[row['Names']] = dict(state=row.get('State'), status=row.get('Status'))
        for name in CONTAINERS.get(role, []):
            if name in containers:
                code, out = sh(['docker', 'inspect', name, '--format', '{{.Image}}'])
                containers[name]['image'] = out.strip().removeprefix('sha256:')[:16]
        h['containers'] = containers
        # tunnel
        code, out = sh(['wg', 'show', 'wg0', 'dump'])
        peers = {}
        names = c.get('peers') or {}
        for line in out.splitlines()[1:] if code == 0 else []:
            parts = line.split('\t')
            if len(parts) >= 5:
                last = int(parts[4] or 0)
                peers[names.get(parts[0], parts[0][:8])] = dict(handshake_age=(int(now - last) if last else None))
        h['tunnel'] = peers if code == 0 else None
        if code != 0:
            h['problems'].append('the WireGuard tunnel is down')
        else:
            stale = [n for n, p in peers.items() if p['handshake_age'] is None or p['handshake_age'] > 180]
            if stale:
                h['notes'].append('no recent tunnel handshake with ' + ', '.join(sorted(stale)) + ' (normal for a peer not started yet)')
        # machine
        st = os.statvfs(self.data)
        h['disk'] = dict(used_percent=round(100 * (1 - st.f_bavail / st.f_blocks), 1) if st.f_blocks else None,
                         free_gb=round(st.f_bavail * st.f_frsize / 1e9, 1))
        mem = {}
        try:
            for line in Path('/proc/meminfo').read_text().splitlines():
                k, v = line.split(':', 1)
                mem[k] = int(v.split()[0])
            h['memory'] = dict(total_gb=round(mem['MemTotal'] / 1e6, 1), available_gb=round(mem['MemAvailable'] / 1e6, 1))
            h['load'] = float(Path('/proc/loadavg').read_text().split()[0])
        except (OSError, KeyError, ValueError):
            pass
        if h['disk']['used_percent'] and h['disk']['used_percent'] > 90:
            h['problems'].append(f'data disk {h["disk"]["used_percent"]}% full')
        if role == 'mpc':
            self._mpc(h, units, containers)
        elif role == 'db':
            self._db(h, units, containers)
        h['level'] = 'bad' if h['problems'] else ('warn' if h['notes'] else 'ok')
        h['summary'] = self._summary(h)
        return h

    def _mpc(self, h, units, containers):
        account = (self.data / 'tls-mpc/scaffold/ACCOUNT_READY').exists()
        h['account_installed'] = account
        running = containers.get('tls-mpc-node', {}).get('state') == 'running'
        if not account:
            h['notes'].append('waiting for the account step (the daemon starts after it)')
        elif not running:
            h['problems'].append('the daemon container is not running')
        status = daemon_status(self.c['wg_address']) if running else None
        h['daemon'] = status
        if running and status is None:
            h['problems'].append('the daemon does not answer status')
        cert = read_json(self.data / 'pb/status/certificate.json')
        h['sender_certificate'] = cert
        if cert and cert.get('state') in ('refresh-due', 'expired'):
            (h['problems'] if cert['state'] == 'expired' else h['notes']).append(f'Signal sender certificate: {cert.get("message")}')
        party = self.c.get('party', 0 if self.c['node'] == 'mpc-node-0' else 1)
        own = self.data / f'tls-mpc/state/worker-send/Player-Data/P{party}.pem'
        peer = self.data / f'tls-mpc/state/worker-send/Player-Data/P{1 - party}.pem'
        ends = {'own': cert_end(own) if own.exists() else None, 'peer': cert_end(peer) if peer.exists() else None}
        h['field_certificates'] = {k: dict(expires=v, days_left=round((v - time.time()) / 86400, 1) if v else None) for k, v in ends.items()}
        for k, v in ends.items():
            if v and v - time.time() < 7 * 86400:
                h['problems' if v < time.time() else 'notes'].append(f'field-engine certificate ({k}) expires in {round((v - time.time()) / 86400, 1)} days (30-day lifetime; renew: DEPLOYMENT.md)')
        net = read_json(self.data / 'tls-mpc/config/network.json') or {}
        reach = 0
        for address in net.get('compute_addresses') or []:
            host, port = address.rsplit(':', 1)
            try:
                with socket.create_connection((host, int(port)), timeout=2):
                    reach += 1
            except OSError:
                pass
        total = len(net.get('compute_addresses') or [])
        h['database_reachable'] = f'{reach}/{total}'
        if total and reach < net.get('threshold', 3) + 1:
            h['problems'].append(f'only {reach} of {total} database nodes accept connections over the tunnel')
        elif total and reach < total:
            h['notes'].append(f'{reach} of {total} database nodes accept connections over the tunnel')
        pre = read_json(self.data / 'pb/status/preflight-verdict.json')
        h['preflight'] = pre.get('summary') if pre else None
        mine = read_json(self.data / 'pb/public/preflight-facts.json')
        if time.time() - self.peer_at > 60:
            other = 'mpc-node-1' if self.c['node'] == 'mpc-node-0' else 'mpc-node-0'
            address = '10.77.0.2' if other == 'mpc-node-1' else '10.77.0.1'
            try:
                with urllib.request.urlopen(f'http://{address}:{HEALTH_PORT}/facts', timeout=5) as r:
                    self.peer_facts = json.loads(r.read())
            except (OSError, ValueError):
                self.peer_facts = None
            self.peer_at = time.time()
        h['pair'] = compare_facts(mine, self.peer_facts)
        if h['pair'].get('differences'):
            h['problems'].append('the two computation nodes differ: ' + ', '.join(h['pair']['differences']))

    def _db(self, h, units, containers):
        h['database_waiting'] = bool((read_json(self.data / 'pb/status/db-barrier.json') or {}).get('waiting'))
        if h['database_waiting']:
            h['notes'].append('waiting for the other database nodes to start together (their operators run start)')
        elif containers.get('ssdb-node', {}).get('state') != 'running':
            h['problems'].append('the database node is not running')
        if containers.get('ssdb-postgres', {}).get('state') != 'running':
            h['problems'].append('Postgres is not running')
        code, out = sh(['docker', 'logs', '--since', '30m', 'ssdb-node'], timeout=20)
        epochs = [int(m.group(1)) for m in EPOCH.finditer(out)] if code == 0 else []
        h['database'] = dict(last_epoch=max(epochs) if epochs else None, epochs_applied_30min=len(epochs),
                             no_consensus_30min=out.count('without reaching consensus') if code == 0 else None)
        if containers.get('ssdb-node', {}).get('state') == 'running' and not epochs:
            h['notes'].append('no database epoch applied in the last 30 minutes (normal in the first minutes)')

    def _summary(self, h):
        bits = [h['level'].upper()]
        if h['role'] == 'mpc':
            d = h.get('daemon') or {}
            bits.append('daemon ' + ('up' if d else ('waiting for account' if not h.get('account_installed') else 'DOWN')))
            cert = h.get('sender_certificate') or {}
            if cert.get('hours_left') is not None:
                bits.append(f'sender cert {cert["hours_left"]:.0f} h left')
            if h.get('database_reachable'):
                bits.append(f'database nodes {h["database_reachable"]} reachable')
            pair = h.get('pair') or {}
            bits.append('pair ' + ('EQUAL' if pair.get('equal') else ('DIFFERENT' if pair.get('differences') else 'not compared yet')))
        if h['role'] == 'db':
            db = h.get('database') or {}
            bits.append(f'epoch {db.get("last_epoch")}')
        tunnel = h.get('tunnel') or {}
        up = sum(1 for p in tunnel.values() if p['handshake_age'] is not None and p['handshake_age'] < 180)
        bits.append(f'tunnel {up}/{len(tunnel)} peers')
        bits.append(f'disk {h["disk"]["used_percent"]}%')
        return ', '.join(bits)


PAIR_KEYS = ['settings', 'manifest_sha256', 'word_dir_sha256', 'binaries', 'mode', 'port_base', 'peer_key_fingerprint']


def compare_facts(mine, other):
    if not mine or not other:
        return dict(equal=False, compared=False)
    diffs = []
    for key in PAIR_KEYS:
        a, b = mine.get(key), other.get(key)
        if key == 'settings' and isinstance(a, dict) and isinstance(b, dict):
            for kind in ('serve', 'receive', 'notify'):
                if (a.get(kind) or {}).get('sha256') != (b.get(kind) or {}).get('sha256'):
                    diffs.append(f'settings {kind}')
            if a.get('worker_session') != b.get('worker_session'):
                diffs.append('worker session settings')
        elif a != b and key in mine:
            diffs.append(key)
    if mine.get('party') == other.get('party'):
        diffs.append('both are the same party')
    return dict(equal=not diffs, compared=True, differences=diffs)


def serve(config_path):
    config = json.loads(Path(config_path).read_text())
    health = Health(config)
    data = Path(config['data_root'])

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_GET(self):
            if self.path == '/health':
                body = health.collect()
            elif self.path == '/facts':
                body = read_json(data / 'pb/public/preflight-facts.json') or {}
            elif self.path == '/public':
                body = read_json(data / 'pb/public/facts.json') or {}
            else:
                self.send_error(404)
                return
            raw = json.dumps(body, sort_keys=True).encode()
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)

    def listen(address):
        while True:
            try:
                ThreadingHTTPServer((address, HEALTH_PORT), Handler).serve_forever()
            except OSError:
                time.sleep(10)        # the tunnel address appears once wg0 is up

    threads = [threading.Thread(target=listen, args=(a,), daemon=True) for a in ('127.0.0.1', config['wg_address'])]
    for t in threads:
        t.start()
    while True:
        time.sleep(3600)


def page(config_path):
    config = json.loads(Path(config_path).read_text())
    nodes = config.get('page_nodes') or []
    state = {'rows': {}, 'at': 0}

    def poll():
        while True:
            for n in nodes:
                address = '127.0.0.1' if n['node'] == config['node'] else n['address']
                try:
                    with urllib.request.urlopen(f'http://{address}:{HEALTH_PORT}/health', timeout=8) as r:
                        state['rows'][n['node']] = json.loads(r.read())
                except (OSError, ValueError) as e:
                    state['rows'][n['node']] = dict(node=n['node'], level='bad', summary='UNREACHABLE over the tunnel', problems=[str(e)[:120]])
            state['at'] = time.time()
            time.sleep(30)

    threading.Thread(target=poll, daemon=True).start()

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_GET(self):
            if self.path not in ('/', '/index.html', '/health.json'):
                self.send_error(404)
                return
            if self.path == '/health.json':
                raw, kind = json.dumps(state['rows'], sort_keys=True).encode(), 'application/json'
            else:
                raw, kind = render(config, state).encode(), 'text/html; charset=utf-8'
            self.send_response(200)
            self.send_header('Content-Type', kind)
            self.send_header('Content-Length', str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)

    # localhost only (reached through `deploy.py monitor`, an ssh tunnel), unless the operator
    # listed monitoring_allow_ips: then every address, with the firewall admitting only those.
    ThreadingHTTPServer(('0.0.0.0' if config.get('page_public') else '127.0.0.1', PAGE_PORT), Handler).serve_forever()


def _fmt_time(ts):
    return time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime(ts)) if ts else '-'


def render(config, state):
    e = html.escape
    rows = []
    for node in sorted(state['rows']):
        h = state['rows'][node]
        level = h.get('level', 'bad')
        details = []
        sw = h.get('software') or {}
        if sw.get('image_id'):
            details.append(f'image {e(str(sw["image_id"])[:12])}')
        if sw.get('manifest_sha256'):
            details.append(f'circuits {e(sw["manifest_sha256"][:12])} word {e(str(sw.get("word_dir_sha256"))[:12])}')
        if sw.get('settings'):
            details.append('settings ' + ' '.join(f'{k}={e(str(v)[:8])}' for k, v in sorted(sw['settings'].items())))
        cert = h.get('sender_certificate') or {}
        if cert:
            details.append(f'Signal sender certificate: {e(cert.get("state", "?"))}, expires {_fmt_time((cert.get("expires_ms") or 0) / 1000)}'
                           f' ({cert.get("hours_left", "?")} h); last check {_fmt_time(cert.get("checked_at"))}')
        for k, v in (h.get('field_certificates') or {}).items():
            details.append(f'field-engine certificate ({k}): expires {_fmt_time(v.get("expires"))} ({v.get("days_left")} days)')
        if h.get('daemon'):
            details.append('daemon status ' + e(json.dumps(h['daemon'], sort_keys=True))[:300])
        if h.get('database'):
            details.append(f'database: last epoch {h["database"].get("last_epoch")}, {h["database"].get("epochs_applied_30min")} applied in 30 min')
        if h.get('pair'):
            p = h['pair']
            details.append('two-node comparison: ' + ('equal' if p.get('equal') else (', '.join(p.get('differences') or []) or 'not compared yet')))
        if h.get('memory'):
            details.append(f'memory {h["memory"]["available_gb"]}/{h["memory"]["total_gb"]} GB free, load {h.get("load")}')
        problems = ''.join(f'<li class="bad">{e(p)}</li>' for p in h.get('problems', [])) + ''.join(f'<li>{e(p)}</li>' for p in h.get('notes', []))
        rows.append(f'<tr class="{e(level)}"><td><b>{e(node)}</b><br><span class="dim">{e(h.get("role", ""))}</span></td>'
                    f'<td><span class="pill {e(level)}">{e(level.upper())}</span> {e(h.get("summary", ""))}<ul>{problems}</ul>'
                    f'<div class="dim">{"<br>".join(details)}</div></td></tr>')
    updated = time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime(state['at'])) if state['at'] else 'not yet'
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta http-equiv="refresh" content="30">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>{e(config.get("page_title", "nodes"))}</title>
<style>
:root {{ --bg:#fff; --fg:#1d1d1f; --dim:#6b6b70; --ok:#1a7f37; --warn:#9a6700; --bad:#cf222e; --line:#e5e5ea; }}
@media (prefers-color-scheme: dark) {{ :root {{ --bg:#111214; --fg:#ececf0; --dim:#9a9aa2; --ok:#3fb950; --warn:#d29922; --bad:#f85149; --line:#2a2b2f; }} }}
body {{ background:var(--bg); color:var(--fg); font:15px/1.45 system-ui, sans-serif; margin:0; padding:16px; }}
table {{ border-collapse:collapse; width:100%; max-width:1100px; }} td {{ border-top:1px solid var(--line); padding:10px 8px; vertical-align:top; }}
.dim {{ color:var(--dim); font-size:13px; }} .pill {{ font-weight:600; font-size:12px; padding:1px 6px; border-radius:4px; border:1px solid currentColor; }}
.pill.ok {{ color:var(--ok); }} .pill.warn {{ color:var(--warn); }} .pill.bad, li.bad {{ color:var(--bad); }} ul {{ margin:4px 0; padding-left:18px; }}
</style></head><body><h1 style="font-size:20px">{e(config.get("page_title", "nodes"))}</h1>
<p class="dim">Updated {updated}; refreshes every 30 s. Public status only: no keys, no contacts.</p>
<table>{"".join(rows) or "<tr><td>collecting ...</td></tr>"}</table></body></html>'''


ACCOUNT_FAILS = {'export (scaffolding)', 'signal endpoint (local)', 'signal endpoint', 'signal endpoint (probe)'}
RELAXED_FAILS = {'memory', 'clock synchronised', 'cores', 'disk', 'CPU flags', 'cpu flags'}
# Other operators' nodes may not be started yet: reported as waiting (the page keeps checking).
WAIT_FAILS = {'database nodes'}


def verdict(path, mode, data_root):
    text = Path(path).read_text()
    fails, ignored, waiting = [], [], []
    account = (Path(data_root) / 'tls-mpc/scaffold/ACCOUNT_READY').exists()
    for line in text.splitlines():
        if not line.startswith('FAIL'):
            continue
        name = line[4:].strip().split(':', 1)[0].strip()
        if (not account and name in ACCOUNT_FAILS) or (mode.endswith('relaxed') and name in RELAXED_FAILS):
            ignored.append(line[4:].strip()[:200])
        elif name in WAIT_FAILS:
            waiting.append(line[4:].strip()[:200])
        else:
            fails.append(line[4:].strip()[:300])
    counts = re.findall(r'---- (.*)', text)
    out = dict(fails=fails, ignored=ignored, waiting=waiting,
               summary=(counts[-1] if counts else 'no summary') + (f'; {len(ignored)} expected before the account step or on a test machine' if ignored else '')
               + (f'; waiting for other nodes: {"; ".join(waiting)}' if waiting else ''))
    if not mode.startswith('pair'):
        Path(data_root, 'pb/status/preflight-verdict.json').write_text(json.dumps(out))
    print(json.dumps(out))


def db_ready(network_path, timeout):
    """Wait for a reachable quorum that has applied an epoch, before storing the account.

    `start` returns while the database start barrier is still waiting for other operators.
    An open port alone does not establish that those nodes have reached consensus.
    """
    network = json.loads(Path(network_path).read_text())
    addresses = network['compute_addresses']
    required = network['threshold'] + network['max_malicious_parties']
    if not 0 < required <= len(addresses):
        raise ValueError('invalid database quorum')
    deadline = time.monotonic() + float(timeout)
    while time.monotonic() < deadline:
        ready = 0
        for address in addresses:
            host, port = address.rsplit(':', 1)
            try:
                with urllib.request.urlopen(f'http://{host}:{HEALTH_PORT}/health', timeout=4) as response:
                    health = json.loads(response.read())
                epoch = (health.get('database') or {}).get('last_epoch')
                running = (health.get('containers') or {}).get('ssdb-node', {}).get('state') == 'running'
                if health.get('database_waiting') or not running or epoch is None:
                    continue
                with socket.create_connection((host, int(port)), timeout=2):
                    ready += 1
            except (OSError, ValueError):
                pass
        print(f'db-ready: {ready}/{len(addresses)} nodes ready; need {required}', flush=True)
        if ready >= required:
            return 0
        time.sleep(3)
    print('db-ready: timed out waiting for database consensus; run start on the remaining nodes, then retry the account step', flush=True)
    return 1


def db_barrier(config_path, timeout):
    """ExecStartPre of a database node: wait until every other database node is either waiting
    here too or already running, then start at the next 30-second boundary of the clock. The
    database server dials its peers once, 10 s after it starts, and does not dial again (DEPLOYMENT.md
    Reference 10, change 19): nodes started minutes apart by different operators never connect and
    the database reaches no consensus. Gives up waiting after TIMEOUT seconds and starts alone."""
    config = json.loads(Path(config_path).read_text())
    data = Path(config['data_root'])
    flag = data / 'pb/status/db-barrier.json'
    net = read_json(data / 'ssdb/config/network-config.json') or {}
    peers = [a.rsplit(':', 1)[0] for a in net.get('peer_addresses') or [] if a.rsplit(':', 1)[0] != config['wg_address']]
    flag.write_text(json.dumps({'waiting': True, 'since': int(time.time())}))
    deadline = time.time() + float(timeout)
    try:
        while time.time() < deadline:
            ready = 0
            for address in peers:
                try:
                    with urllib.request.urlopen(f'http://{address}:{HEALTH_PORT}/health', timeout=4) as r:
                        h = json.loads(r.read())
                    if h.get('database_waiting') or (h.get('containers') or {}).get('ssdb-node', {}).get('state') == 'running':
                        ready += 1
                except (OSError, ValueError):
                    pass
            if ready == len(peers):
                time.sleep(30 - time.time() % 30)
                print(f'db-barrier: all {len(peers)} other database nodes ready; starting', flush=True)
                return 0
            time.sleep(3)
        print(f'db-barrier: {timeout} s without every other database node; starting alone', flush=True)
        return 0
    finally:
        flag.write_text(json.dumps({'waiting': False}))


def logs(lines, outdir):
    sys.path.insert(0, str(HERE))
    import deploylib as dl
    out = Path(outdir)
    out.mkdir(parents=True, exist_ok=True)
    for unit in ('wg-quick@wg0', 'tls-mpc-node', 'ssdb-node', 'ssdb-postgres', 'pb-health', 'pb-page', 'pb-certificate'):
        code, text = sh(['journalctl', '-u', unit, '-n', str(lines), '--no-pager'], timeout=30)
        if code == 0 and text.strip() and 'No entries' not in text:
            (out / f'{unit}.log').write_text(dl.redact(text))
    for name in ('tls-mpc-node', 'ssdb-node', 'ssdb-postgres'):
        code, text = sh(['docker', 'logs', '--tail', str(lines), name], timeout=30)
        if code == 0:
            (out / f'container-{name}.log').write_text(dl.redact(text))
    print(json.dumps(sorted(p.name for p in out.iterdir())))


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    command = sys.argv[1]
    if command == 'serve':
        serve(sys.argv[2])
    elif command == 'page':
        page(sys.argv[2])
    elif command == 'verdict':
        verdict(sys.argv[2], sys.argv[3], sys.argv[4])
    elif command == 'logs':
        logs(int(sys.argv[2]), sys.argv[3])
    elif command == 'db-barrier':
        return db_barrier(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 1800)
    elif command == 'db-ready':
        return db_ready(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 600)
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
