"""The guided process. Every command is idempotent and resumable and ends by saying what to do next.

  init            the coordinator: deployment.toml (shared) and operator.toml (private) from the examples
  build           the builder: images for the target platform, digests into deployment.toml
  plan            what join would create and what it costs per month where known; creates nothing
  join            each operator: their machines, software, keys made ON the nodes -> public bundles
  collect DIR     anyone: check the set of bundles, print the deployment fingerprint
  start DIR --fingerprint F   each operator, after comparing F by voice: tunnels, firewall, services
  account ...     the account step (local test: automatic; real service: the owner's manual step)
  status / monitor / logs / upgrade / destroy / next
  up              one person, every node: init(if needed)/join/collect/start in one go
  testapp ...     a TEST application server on this computer (local-test only)
"""
import json
import os
import re
import secrets
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

from . import bundles as B
from . import config as C
from . import local as L
from . import providers as P
from . import tofu as T
from .tools import ANSIBLE_IMAGE, DEPLOY, ROOT, ToolError, docker, docker_ok, run, ansible

sys.path.insert(0, str(DEPLOY / 'scripts'))
import deploylib as dl  # noqa: E402

DEFAULT_OPERATOR = DEPLOY / 'operator.toml'
DEFAULT_DEPLOYMENT = DEPLOY / 'deployment.toml'
STATE_ROOT = DEPLOY / '.state'
DAEMON_PORT, PEER_PORT, PORT_BASE, HEALTH_PORT, PAGE_PORT = 19700, 19710, 23000, 9100, 8088
POSTGRES_IMAGE = 'postgres:17@sha256:5b96f1a16bd9768b060dd2ffe55cb6225c4d9ef4d214a8b21eb08134869a97e4'
SIGNAL_ROOT_CA = ROOT / 'real_signal/signal-root-ca.pem'
PRODUCTION_SIGNAL = dict(endpoint='chat.signal.org', port=443, hostname='chat.signal.org')   # never contacted by any test


class Fail(Exception):
    pass


def say(text=''):
    print(text, flush=True)


def step(text):
    say(f'\n== {text}')


# ---------------------------------------------------------------------------------------------
# context


class Ctx:
    def __init__(self, args, need_operator=True):
        self.args = args
        self.operator_file = Path(getattr(args, 'operator', None) or DEFAULT_OPERATOR).resolve()
        self.o = C.load_operator(self.operator_file) if need_operator else None
        dfile = getattr(args, 'deployment', None) or (self.o['deployment'] if self.o else DEFAULT_DEPLOYMENT)
        self.deployment_file = Path(dfile).resolve()
        self.d = C.load_deployment(self.deployment_file)
        self.mine = C.check_pair(self.d, self.o) if self.o else []
        self.state = Path(getattr(args, 'state', None) or (STATE_ROOT / self.d['name'] / (self.o['operator'] if self.o else '_coordinator'))).resolve()
        self.state.mkdir(parents=True, exist_ok=True)
        os.chmod(self.state, 0o700)
        self.log = self.state / 'logs' / 'deploy.log'
        self.local = bool(self.o) and all(self.o['nodes'][n]['provider'] == 'local' for n in self.mine)

    def warn_all(self):
        for w in C.deployment_warnings(self.d) + (C.operator_warnings(self.d, self.o) if self.o else []):
            say(f'  WARNING: {w}')

    @property
    def progress(self):
        path = self.state / 'progress.json'
        return json.loads(path.read_text()) if path.exists() else {}

    def save_progress(self, **kw):
        p = self.progress
        p.update(kw)
        (self.state / 'progress.json').write_text(json.dumps(p, indent=1, sort_keys=True) + '\n')

    @property
    def outbox(self):
        return self.state / 'outbox'

    def machines(self):
        path = self.state / 'machines.json'
        return json.loads(path.read_text()) if path.exists() else {}


def tool_commit():
    head = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', '-C', str(ROOT), 'status', '--porcelain', '--', 'deploy'], capture_output=True, text=True).stdout.strip()
    return head, bool(dirty)


SKIP_IN_DIGEST = {'.state', '__pycache__', 'bundles', 'operator.toml', 'deployment.toml'}


def tool_digest():
    """SHA-256 over the deploy tool's own files (deploy/, without state and private files): what
    every operator must run identically, whether or not it is committed."""
    import hashlib
    h = hashlib.sha256()
    for path in sorted(DEPLOY.rglob('*')):
        rel = path.relative_to(DEPLOY)
        if path.is_file() and not (set(rel.parts) & SKIP_IN_DIGEST) and path.suffix != '.pyc':
            h.update(str(rel).encode() + b'\0' + hashlib.sha256(path.read_bytes()).digest())
    return h.hexdigest()


def ssh_key(ctx):
    key = ctx.state / 'ssh' / 'id_ed25519'
    if not key.exists():
        key.parent.mkdir(exist_ok=True)
        os.chmod(key.parent, 0o700)
        code, text = run(['ssh-keygen', '-q', '-t', 'ed25519', '-N', '', '-C', f'tls-mpc-deploy-{ctx.d["name"]}', '-f', key], ctx.log, 60)
        if code:
            raise Fail('ssh-keygen failed (ssh is a prerequisite)')
    return key


# ---------------------------------------------------------------------------------------------
# rendering what each node runs (computed here from public data only; secrets are made on the nodes)


def signal_target(ctx):
    ep = ctx.d['signal']['endpoint']
    if ep == 'local-test':
        gateway = ctx.progress.get('local_gateway') or L.host_gateway_address(ctx.d['name'], ctx.log)
        ctx.save_progress(local_gateway=gateway)
        return dict(endpoint=gateway, port=18443, hostname='server.example', trust_root='/srv/tls-mpc/shared/ca.pem')
    if ep == 'production':
        return dict(PRODUCTION_SIGNAL, trust_root='/srv/tls-mpc/config/signal-root-ca.pem')
    return dict(endpoint='192.0.2.1', port=443, hostname='no-endpoint.invalid', trust_root='/srv/tls-mpc/config/no-endpoint.pem')


def node_config(ctx, node):
    """The daemon's configuration (node_daemon/README.md) for a computation node, container paths."""
    d = ctx.d
    party = C.MPC_NODES.index(node)
    me, other = C.wg_address(node), C.wg_address(C.MPC_NODES[1 - party])
    env = dict(SIGNAL_WORKER='node', TLS_WORKER_FIELD_BATCH='3000', TLS_WORKER_PEER=other)
    if party == 0:
        env['TLS_WORKER_LISTEN'] = me
    if d['signal']['endpoint'] == 'production':
        env.update(SIGNAL_CLIENT_PROFILE='libsignal', SIGNAL_ACK_REFUSED='0', SIGNAL_RECEIVE_JUMP='3')
    if d['worker_logic'] == 'lean':
        env['SIGNAL_SCRIPTS'] = C.LEAN_SCRIPTS
    sig = signal_target(ctx)
    return {
        '_comment': f'Rendered by deploy/deploy.py for {node} of deployment {d["name"]}; do not edit on the node (re-run start).',
        'party': party, 'listen': f'{me}:{DAEMON_PORT}', 'peer_listen': f'{me}:{PEER_PORT}', 'peer': f'{other}:{PEER_PORT}',
        'peer_key_file': '/srv/tls-mpc/secrets/peer.key', 'state_directory': '/srv/tls-mpc/state/daemon',
        'controller': '/opt/tls-mpc/bin/public_service_controller',
        'worker': {'binary': '/opt/tls-mpc/bin/node-worker', 'send_directory': '/srv/tls-mpc/state/worker-send',
                   'receive_directory': '/srv/tls-mpc/state/worker-receive', 'hosts': [C.wg_address(n) for n in C.MPC_NODES],
                   'port_base': PORT_BASE},
        'circuits': {'tool': '/opt/tls-mpc/share/circuit_cache.py', 'manifest': '/srv/tls-mpc/circuits/manifest.txt'},
        'signal': {'endpoint': sig['endpoint'], 'port': sig['port'], 'hostname': sig['hostname'], 'trust_root': sig['trust_root'],
                   'certificate_checker': '/opt/tls-mpc/bin/public_auth'},
        'database': {'client': '/opt/tls-mpc/bin/handoff_client', 'network': '/srv/tls-mpc/config/network.json',
                     'key': '/srv/tls-mpc/secrets/db-key.json'},
        'application': {'notify_public_key': d['app']['notify_public_key']},
        'test': {'export': '/srv/tls-mpc/shared/mpc-export.json', 'tokens': '/srv/tls-mpc/shared/tokens',
                 'kem_tool': '/opt/tls-mpc/bin/lss-provision'},
        'environment': env,
        'receive': True,
        'timeouts': {'agree_seconds': 30, 'start_margin_seconds': 30, 'send_seconds': 600, 'send_seconds_per_id': 60,
                     'delete_seconds': 120, 'peer_wait_seconds': 180},
        'send_session': {'long_lived': True, 'max_messages': 5000, 'max_seconds': 21600, 'max_megabytes': 0, 'stall_seconds': 900, 'attempts': 3},
    }


def settings_digests(config):
    s = dl.settings_digests(config, base_env={})
    ws = json.dumps(s['worker_session'], sort_keys=True)
    return {k: s[k]['sha256'] for k in ('serve', 'receive', 'notify')} | {'worker_session': dl.sha256_text(ws)}


def mesh(ctx, bundles):
    """Every member of the tunnel mesh: the nodes, and the application server if it has a key."""
    members = []
    for node in sorted(ctx.d['nodes']):
        b = bundles[node]
        members.append(dict(node=node, address=C.wg_address(node), public_key=b['wireguard']['public_key'],
                            endpoint=b['wireguard']['endpoint'], role=C.role(node)))
    if ctx.d['app']['wireguard_public_key']:
        members.append(dict(node=C.APP, address=C.wg_address(C.APP), public_key=ctx.d['app']['wireguard_public_key'],
                            endpoint='', role='app'))
    return members


def firewall_rules(ctx, node):
    """TCP rules on the tunnel interface (default deny everything else)."""
    me = C.role(node)
    others = [n for n in ctx.d['nodes'] if n != node]
    rules = [dict(src=C.wg_address(n), port=str(HEALTH_PORT), why='health') for n in others]
    app = C.wg_address(C.APP)
    if me == 'mpc':
        peer = C.MPC_NODES[1 - C.MPC_NODES.index(node)]
        rules.append(dict(src=C.wg_address(peer), port=str(PEER_PORT), why='daemon link'))
        if node == 'mpc-node-0':
            rules.append(dict(src=C.wg_address(peer), port=f'{PORT_BASE}:{PORT_BASE + 639}', why='workers (party 1 dials party 0)'))
        rules.append(dict(src=app, port=str(DAEMON_PORT), why='application'))
    elif me == 'db':
        p = B.DB_PORTS
        for n in others:
            if n.startswith(C.DB_PREFIX):
                for port in (p['peer'], p['sync'], p['relay']):
                    rules.append(dict(src=C.wg_address(n), port=str(port), why='database peers'))
        for m in C.MPC_NODES:
            rules.append(dict(src=C.wg_address(m), port=str(p['compute']), why='computation nodes'))
    return rules


def page_hosts(ctx):
    """(this operator's page host, the combined page host if it is ours)."""
    mine = ctx.mine
    own = next((n for n in mine if n in C.MPC_NODES), mine[0])
    combined = ctx.d['monitoring']['combined_page_on']
    return own, (combined if combined in mine else None)


# ---------------------------------------------------------------------------------------------
# machines


def provision(ctx, nodes):
    step('machines')
    key = ssh_key(ctx)
    pub = key.with_suffix('.pub')
    machines = ctx.machines()
    cloud = [n for n in nodes if ctx.o['nodes'][n]['provider'] in P.CLOUD]
    for node in nodes:
        spec = ctx.o['nodes'][node]
        if spec['provider'] == 'local':
            machines[node] = L.up(ctx.d['name'], node, spec, pub, ctx.log)
            say(f'  {node}: local machine {machines[node]["container"]} at {machines[node]["ssh_host"]}')
        elif spec['provider'] == 'existing':
            machines[node] = dict(provider='existing', ssh_host=spec['host'], ssh_port=spec['port'], ssh_user=spec['user'],
                                  ssh_key=str(spec['ssh_key']) if spec['ssh_key'] else None, endpoint=spec['endpoint'],
                                  data_device=spec['data_device'], data_path=spec['data_path'], requirements='strict',
                                  tunnel_host=spec['host'], tunnel_port=spec['port'])
            say(f'  {node}: your machine {spec["user"]}@{spec["host"]}:{spec["port"]}')
    if cloud:
        names = T.env_names(ctx.o, cloud)
        admin = [a for a in ctx.o['admin_ips'] if a != 'auto'] or ['0.0.0.0/0', '::/0']
        stacks = T.render(ctx.state, ctx.d, ctx.o, cloud, pub.read_text().strip(), admin, ctx.o['monitoring_allow_ips'])
        say(f'  creating disks with OpenTofu ({", ".join(cloud)}) ...')
        disks = T.apply(stacks['disks'], ctx.state / 'logs' / 'tofu-disks.log', names)
        stacks = T.render(ctx.state, ctx.d, ctx.o, cloud, pub.read_text().strip(), admin, ctx.o['monitoring_allow_ips'], disks)
        say('  creating machines with OpenTofu ...')
        made = T.apply(stacks['machines'], ctx.state / 'logs' / 'tofu-machines.log', names)
        for node in cloud:
            m = made[node]
            machines[node] = dict(provider=ctx.o['nodes'][node]['provider'], ssh_host=m['public_ip'], ssh_port=22, ssh_user=m.get('ssh_user', 'root'),
                                  ssh_key=None, endpoint=m['public_ip'], data_device=m['device'], data_path='/srv/data', requirements='strict',
                                  tunnel_host=m['public_ip'], tunnel_port=22)
            say(f'  {node}: {ctx.o["nodes"][node]["provider"]} {ctx.o["nodes"][node]["size"]} at {m["public_ip"]}')
    (ctx.state / 'machines.json').write_text(json.dumps(machines, indent=1, sort_keys=True) + '\n')
    return machines


def inventory(ctx, machines, nodes):
    hosts = {}
    mounts = []
    for node in nodes:
        m = machines[node]
        h = dict(ansible_host=m['ssh_host'], ansible_port=m['ssh_port'], ansible_user=m['ssh_user'],
                 ansible_ssh_private_key_file='/state/ssh/id_ed25519', node=node, node_role=C.role(node),
                 party=C.MPC_NODES.index(node) if node in C.MPC_NODES else None, wg_address=C.wg_address(node),
                 data_device=m['data_device'], data_root=m['data_path'], requirements=m['requirements'], provider=m['provider'],
                 local_machine=m['provider'] == 'local', security=ctx.d['security'],
                 mpc_memory=f'{ctx.o["nodes"][node].get("memory_gb", 12)}g' if m['provider'] == 'local' else '28g',
                 ansible_ssh_common_args=('-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null' if m['provider'] == 'local'
                                          else '-o StrictHostKeyChecking=accept-new -o UserKnownHostsFile=/state/ssh/known_hosts'))
        if m.get('ssh_key'):
            inside = f'/keys/{node}'
            mounts.append((m['ssh_key'], inside))
            h['ansible_ssh_private_key_file'] = inside
        hosts[node] = h
    inv = {'all': {'hosts': hosts, 'vars': {'ansible_python_interpreter': '/usr/bin/python3', 'deployment_name': ctx.d['name']}}}
    (ctx.state / 'inventory.json').write_text(json.dumps(inv, indent=1, sort_keys=True) + '\n')
    return mounts


def network_for(ctx):
    return L.network_name(ctx.d['name']) if ctx.local else None


def admin_cidrs(ctx):
    if ctx.local:
        return [P.LOCAL_SUBNET]
    return [a for a in ctx.o['admin_ips'] if a != 'auto']


def play(ctx, playbook, extra, nodes, mounts=(), timeout=7200):
    log = ctx.state / 'logs' / f'{Path(playbook).stem}.log'
    code, summary = ansible(ctx.state, playbook, 'inventory.json', extra, log, timeout=timeout, network=network_for(ctx),
                            mounts=mounts, limit=','.join(nodes))
    for line in summary:
        say('    ' + line)
    if code:
        raise Fail(f'{playbook} failed (exit {code}); the full output is in {log}')
    return log


# ---------------------------------------------------------------------------------------------
# software


def image_ids(ctx, roles):
    sw = ctx.d['software']
    want = {}
    if roles & {'mpc', 'app'}:
        want['node'] = sw['node_image']
    if 'db' in roles:
        want['dbnode'] = sw['dbnode_image']
    mode = ctx.o['software']['images']
    if getattr(ctx.args, 'images', None):
        mode = ctx.args.images
    for kind, ident in want.items():
        if mode == 'build-here':
            raise Fail('images = "build-here": run `deploy.py build` on this computer first, then put the digests it prints into '
                       'your operator.toml as [software] images = "prebuilt" with images_dir (independent builds: see DEPLOYMENT.md)')
        if not ident:
            raise Fail(f'deployment.toml [software] {kind}_image is empty: the builder runs `deploy.py build` (or `build --record` for '
                       'images already built) and shares the updated deployment.toml')
    return want, mode


def image_tars(ctx, want):
    """A `docker save` file per image: from images_dir, or saved from this computer's Docker."""
    out = {}
    (ctx.state / 'images').mkdir(exist_ok=True)
    for kind, ident in want.items():
        target = ctx.state / 'images' / f'{ident[:16]}.tar'
        source = ctx.o['software']['images_dir']
        if source and (Path(source) / f'{ident[:16]}.tar').exists():
            if not target.exists():
                shutil.copy2(Path(source) / f'{ident[:16]}.tar', target)
        elif not target.exists():
            say(f'  saving image {ident[:16]} from this computer\'s Docker ...')
            code, text = run([docker(), 'image', 'save', '-o', target, f'sha256:{ident}'], ctx.log, 1800)
            if code:
                raise Fail(f'image sha256:{ident[:16]} is neither in images_dir nor in this computer\'s Docker (get the image files from the builder)')
        out[kind] = dict(id=ident, tar=f'/state/images/{target.name}')
    return out


def image_pins(image_id, log):
    """The word-circuit and field-program pins the computation image's worker checks (its
    pins.json); the repository's loader.rs if the image is not on this computer."""
    if image_id:
        code, text = run([docker(), 'run', '--rm', '--network', 'none', '--entrypoint', 'cat', f'sha256:{image_id}',
                          '/opt/tls-mpc/share/pins.json'], log, 120)
        if code == 0:
            return json.loads(text[text.index('{'):])
    return dl.parse_loader_pins()


def stage_word(word_dir, pins, dest):
    """The word circuits and field programs: the TOP-LEVEL *.flat and *.v3 files of the word dir
    (what the workers and the engines load, about 0.5 GB, and what the word-dir digest covers), as
    build_artifacts.py `word` copies them. The source directory's subdirectories (build products,
    hundreds of GB) are not copied. Hard links where possible."""
    dest = Path(dest)
    dest.mkdir(parents=True, exist_ok=True)
    names = sorted(p.name for p in Path(word_dir).iterdir() if p.is_file() and p.suffix in ('.flat', '.v3'))
    for old in dest.iterdir():
        if old.name not in names:
            old.unlink()
    for name in names:
        src, dst = Path(word_dir) / name, dest / name
        if dst.exists() and dst.stat().st_size == src.stat().st_size and dst.stat().st_mtime == src.stat().st_mtime:
            continue
        if dst.exists():
            dst.unlink()
        try:
            os.link(src, dst)
        except OSError:
            shutil.copy2(src, dst)
    problems, stats = dl.word_dir_summary(dest, pins)
    if problems:
        raise Fail('word circuits / field programs: ' + '; '.join(problems[:3]))
    return dest, stats['word_dir_sha256']


def software_vars(ctx, nodes):
    roles = {C.role(n) for n in nodes}
    want, mode = image_ids(ctx, roles)
    tars = image_tars(ctx, want)
    mounts = []
    v = dict(images=tars, images_mode=mode, postgres_image=POSTGRES_IMAGE)
    if 'mpc' in roles:
        sw = ctx.o['software']
        for name, path in (('circuits', sw['circuits_dir']), ('word', sw['word_dir'])):
            if not path or not Path(path).is_dir():
                raise Fail(f'[software] {name}_dir {path} is not a directory')
        mounts.append((str(Path(sw['circuits_dir']).resolve()), '/in/circuits'))
        staged, wdigest = stage_word(sw['word_dir'], image_pins(ctx.d['software']['node_image'], ctx.log), ctx.state / 'word')
        expected = ctx.d['software']['word_dir_sha256']
        if expected and wdigest != expected:
            raise Fail(f'the pinned word circuits / field programs of {sw["word_dir"]} have digest {wdigest[:16]}, '
                       f'but deployment.toml expects {expected[:16]}')
        mounts.append((str(staged), '/in/word'))
        manifest = Path(sw['circuits_dir']) / 'manifest.txt'
        digest, rows = dl.read_manifest(manifest)
        expected = ctx.d['software']['manifest_sha256']
        if expected and digest != expected:
            raise Fail(f'your circuit set {manifest} has digest {digest[:16]}, but deployment.toml expects {expected[:16]}')
        v.update(circuits_in='/in/circuits', word_in='/in/word', manifest_sha256=digest)
    return v, mounts


# ---------------------------------------------------------------------------------------------
# commands


def cmd_init(args):
    """Copy the examples (never over existing files) and fill the agreed commit."""
    made = []
    dfile = Path(args.deployment or DEFAULT_DEPLOYMENT)
    if not dfile.exists():
        text = (DEPLOY / 'deployment.example.toml').read_text()
        head, dirty = tool_commit()
        text = re.sub(r'(?m)^commit = ".*"', f'commit = "{head}"', text, count=1)
        dfile.write_text(text)
        made.append(dfile)
    ofile = Path(args.operator or DEFAULT_OPERATOR)
    if not ofile.exists():
        shutil.copy2(DEPLOY / 'operator.example.toml', ofile)
        os.chmod(ofile, 0o600)
        made.append(ofile)
    for f in made:
        say(f'wrote {f}')
    say(f'\nNext:\n  1. edit {dfile}: name, security, who operates which node, the application server\'s keys'
        f'\n  2. edit {ofile}: your nodes\' provider/size and your credentials (PRIVATE: never send it)'
        f'\n  3. send {dfile.name} to every operator; each runs `python3 deploy/deploy.py join`')
    return 0


def cmd_plan(args):
    ctx = Ctx(args)
    ctx.warn_all()
    say(f'deployment "{ctx.d["name"]}": {ctx.d["security"]}, worker logic {ctx.d["worker_logic"]}, Signal endpoint {ctx.d["signal"]["endpoint"]}')
    say(f'you are "{ctx.o["operator"]}" and operate: {", ".join(ctx.mine)}\n')
    total, unknown = 0.0, []
    say(f'  {"node":12} {"provider":9} {"region":14} {"size":14} {"disk":>6}  {"EUR/month":>10}  creates')
    for node in ctx.mine:
        spec = ctx.o['nodes'][node]
        prov = P.PROVIDERS[spec['provider']]
        machine, disk = prov.monthly(spec) if spec['provider'] in P.CLOUD else (None, None)
        price = '-' if spec['provider'] in ('local', 'existing') else (f'{machine + (disk or 0):.2f}' if machine is not None else 'unknown')
        if machine is not None:
            total += machine + (disk or 0)
        elif spec['provider'] in P.CLOUD:
            unknown.append(node)
        creates = {'local': 'a container on this computer + a kept volume', 'existing': 'nothing (your machine)'}.get(
            spec['provider'], f'server, {spec["data_disk_gb"]} GB disk (kept by destroy), firewall, ssh key')
        say(f'  {node:12} {spec["provider"]:9} {spec["region"]:14} {spec["size"]:14} {spec["data_disk_gb"] or "-":>6}  {price:>10}  {creates}')
    say(f'\n  known monthly total: EUR {total:.2f}' + (f'; price unknown for {", ".join(unknown)} (check the provider\'s page; '
                                                         'prices from deployment/PROVIDERS_CHEAP.md, 2026-11-11, excl. VAT and traffic)' if unknown else ''))
    if args.tofu:
        cloud = [n for n in ctx.mine if ctx.o['nodes'][n]['provider'] in P.CLOUD]
        if cloud:
            names = T.env_names(ctx.o, cloud)
            pub = ssh_key(ctx).with_suffix('.pub').read_text().strip()
            stacks = T.render(ctx.state, ctx.d, ctx.o, cloud, pub, ['0.0.0.0/0'], [])
            for name, directory in stacks.items():
                code, text = T.plan(directory, ctx.state / 'logs' / f'tofu-plan-{name}.log', names)
                say(f'  tofu plan {name}: ' + (next((l for l in text.splitlines() if l.startswith('Plan:')), 'see log') if code == 0 else f'failed (log {ctx.state}/logs)'))
    say('\nNothing was created. Next: `python3 deploy/deploy.py join`')
    return 0


def cmd_join(args):
    ctx = Ctx(args)
    ctx.warn_all()
    docker_ok(ctx.log)
    nodes = ctx.mine
    if ctx.d['signal']['endpoint'] == 'production' and not args.i_have_the_go_ahead:
        raise Fail('[signal] endpoint = "production": add --i-have-the-go-ahead (owner only). join itself contacts no Signal host; '
                   'the computation daemons will once the account step is done')
    step(f'join: {", ".join(nodes)} for operator "{ctx.o["operator"]}"')
    machines = provision(ctx, nodes)
    mounts = inventory(ctx, machines, nodes)
    v, more = software_vars(ctx, nodes)
    mounts += more
    configs = {}
    for node in nodes:
        if node in C.MPC_NODES:
            configs[node] = node_config(ctx, node)
    v.update(admin_cidrs=admin_cidrs(ctx), node_configs=configs, deployment=ctx.d['name'])
    step('installing (Docker, WireGuard, firewall, data disk, images, circuits) and making keys on each node')
    play(ctx, 'join.yml', v, nodes, mounts)
    head, dirty = tool_commit()
    digest = tool_digest()
    made = []
    for node in nodes:
        facts = json.loads((ctx.state / 'facts' / f'{node}.json').read_text())
        sw = dict(tool_commit=head, tool_dirty=dirty, tool_digest=digest, images=v['images_mode'], image_id=facts['image_id'], image_arch=facts.get('image_arch'))
        bundle = dict(format=B.FORMAT, deployment=ctx.d['name'], deployment_sha256=B.deployment_digest(ctx.d), node=node,
                      operator=ctx.o['operator'], role=C.role(node), provider=machines[node]['provider'],
                      wireguard=dict(public_key=facts['keys']['wireguard_public_key'], endpoint=f'{machines[node]["endpoint"]}:{C.WG_PORT}',
                                     address=C.wg_address(node)), software=sw)
        if node in C.MPC_NODES:
            mk = facts['keys']['mpc']
            bundle['party'] = C.MPC_NODES.index(node)
            bundle['mpc'] = dict(link_public_key=mk['link_public_key'], db_client_public_key=mk['db_client_public_key'],
                                 field_certificate=mk['field_certificate'], field_certificate_sha256=mk['field_certificate_info']['sha256'],
                                 field_certificate_not_after=mk['field_certificate_info']['not_after'])
            dg = facts['digests']
            if dg['circuit_problems'] or dg['word_problems']:
                raise Fail(f'{node}: circuit / word files are not right after copying: ' + '; '.join((dg['circuit_problems'] + dg['word_problems'])[:4]))
            sw.update(mode=facts.get('mode'), worker_logic=ctx.d['worker_logic'], manifest_sha256=dg['manifest_sha256'],
                      word_dir_sha256=dg['word_dir_sha256'], pins_sha256=dg['pins_sha256'], binaries_sha256=facts.get('binaries_sha256'),
                      settings=settings_digests(configs[node]))
        else:
            bundle['db'] = facts['keys']['db']
            bundle['db_index'] = C.db_index(node)
        made.append(B.write_bundle(bundle, ctx.outbox))
    ctx.save_progress(joined={n: B.bundle_digest(json.loads((ctx.outbox / f'{n}.bundle.json').read_text())) for n in nodes},
                      joined_deployment=B.deployment_digest(ctx.d))
    step('done: your public bundle files')
    for path in made:
        say(f'  {path}   (file digest {B.bundle_digest(json.loads(path.read_text()))[:16]})')
    others = sorted({s['operator'] for n, s in ctx.d['nodes'].items() if s['operator'] != ctx.o['operator']})
    say('\nNext: send these files (public, no secrets) to ' + (', '.join(others) if others else 'nobody: you operate every node') +
        '.\n  Put every bundle you receive, and your own, in one directory (e.g. bundles/), then run'
        '\n    python3 deploy/deploy.py collect bundles/')
    return 0


def load_set(ctx, dirs):
    bundles, problems = B.read_bundles([*dirs, ctx.outbox] if ctx.o else list(dirs))
    errors, warnings, rows = B.check(ctx.d, bundles)
    return bundles, problems + errors, warnings, rows


def print_rows(rows):
    say(f'  {"node":20} {"operator":10} {"deploy tool":20} {"image":13} {"images":10} {"manifest":13} {"word dir":13} {"settings"}')
    for r in rows:
        say(f'  {r[0]:20} {r[1]:10} {r[2]:20} {r[3]:13} {r[4]:10} {r[5]:13} {r[6]:13} {r[7]}')


def cmd_collect(args):
    ctx = Ctx(args, need_operator=Path(args.operator or DEFAULT_OPERATOR).exists())
    bundles, errors, warnings, rows = load_set(ctx, args.dirs)
    step(f'{len(bundles)} bundles for deployment "{ctx.d["name"]}" ({len(ctx.d["nodes"])} nodes)')
    print_rows(rows)
    for w in C.deployment_warnings(ctx.d) + warnings:
        say(f'  WARNING: {w}')
    if errors:
        for e in errors:
            say(f'  PROBLEM: {e}')
        say('\nNot complete or not consistent: fix the problems above (ask the named operator), then run collect again.')
        return 1
    fp = B.fingerprint(ctx.d, bundles)
    (ctx.state / 'collected').mkdir(exist_ok=True)
    for node, b in bundles.items():
        (ctx.state / 'collected' / f'{node}.bundle.json').write_text(json.dumps(b, indent=1, sort_keys=True) + '\n')
    ctx.save_progress(collected=fp)
    say(f'\nDEPLOYMENT FINGERPRINT:   {fp}\n')
    say('Next: compare this fingerprint with EVERY other operator by voice, video or in person (not by the channel the files came by).\n'
        'It covers deployment.toml, every node\'s keys and the digests of the software each node runs. If it matches, run\n'
        f'    python3 deploy/deploy.py start {" ".join(args.dirs)} --fingerprint {fp}\n'
        'If it differs, stop: a file was changed on the way, or someone used another deployment.toml.')
    return 0


def render_start(ctx, bundles):
    """Per-node variables for start.yml (all public)."""
    members = mesh(ctx, bundles)
    netcfg = B.network_config(ctx.d, bundles)
    own_page, combined = page_hosts(ctx)
    per = {}
    for node in ctx.mine:
        peers = [m for m in members if m['node'] != node and (m['role'] != 'app' or C.role(node) == 'mpc')]
        page_nodes = None
        if node == combined:
            page_nodes = [dict(node=n, address=C.wg_address(n)) for n in sorted(ctx.d['nodes'])]
        elif node == own_page:
            page_nodes = [dict(node=n, address=C.wg_address(n)) for n in sorted(ctx.mine)]
        h = dict(node=node, role=C.role(node), deployment=ctx.d['name'], wg_address=C.wg_address(node),
                 peers={m['public_key']: m['node'] for m in members}, expected=dict(bundles[node]['software']),
                 page_nodes=page_nodes, page_title=f'{ctx.d["name"]}: ' + ('all nodes' if node == combined else f'{ctx.o["operator"]}\'s nodes'),
                 page_public=bool(ctx.o['monitoring_allow_ips']) and node == own_page,
                 certificate_margin_hours=ctx.d['signal']['certificate_margin_hours'])
        v = dict(peers=peers, rules=firewall_rules(ctx, node), health=h, image_id=bundles[node]['software']['image_id'])
        if C.role(node) == 'mpc':
            other = C.MPC_NODES[1 - C.MPC_NODES.index(node)]
            v.update(node_config=node_config(ctx, node), peer_link=bundles[other]['mpc']['link_public_key'],
                     peer_certificate=bundles[other]['mpc']['field_certificate'], peer_address=C.wg_address(other),
                     lean=ctx.d['worker_logic'] == 'lean', endpoint=ctx.d['signal']['endpoint'],
                     manifest_sha256=bundles[node]['software']['manifest_sha256'], word_dir_sha256=bundles[node]['software']['word_dir_sha256'])
        if C.role(node) in ('mpc', 'db'):
            v['network_config'] = netcfg
        if C.role(node) == 'db':
            v['db_index'] = C.db_index(node)
            v['db_ports'] = B.DB_PORTS
        per[node] = v
    return per


def cmd_start(args):
    ctx = Ctx(args)
    bundles, errors, warnings, rows = load_set(ctx, args.dirs)
    if errors:
        for e in errors:
            say(f'  PROBLEM: {e}')
        raise Fail('the bundle set is not complete or not consistent: run collect and fix what it says')
    fp = B.fingerprint(ctx.d, bundles)
    if B.normalize_fingerprint(args.fingerprint) != B.normalize_fingerprint(fp):
        raise Fail(f'the fingerprint you typed is not this set\'s ({fp}). Do not start: compare again with the other operators; '
                   'a bundle or deployment.toml differs between you')
    if ctx.d['signal']['endpoint'] == 'production' and not args.i_have_the_go_ahead:
        raise Fail('[signal] endpoint = "production": add --i-have-the-go-ahead (owner only)')
    docker_ok(ctx.log)
    machines = ctx.machines()
    missing = [n for n in ctx.mine if n not in machines]
    if missing:
        raise Fail(f'run `deploy.py join` first ({", ".join(missing)} not prepared)')
    mounts = inventory(ctx, machines, ctx.mine)
    if ctx.d['signal']['endpoint'] == 'production' and any(n in C.MPC_NODES for n in ctx.mine):
        if not SIGNAL_ROOT_CA.exists():
            raise Fail(f'{SIGNAL_ROOT_CA} (the pinned root of the real service) is missing')
        mounts.append((str(SIGNAL_ROOT_CA), '/in/signal-root-ca.pem'))
    step(f'start: tunnels, firewall and services on {", ".join(ctx.mine)} (fingerprint {fp})')
    per = render_start(ctx, bundles)
    play(ctx, 'start.yml', dict(per_node=per, admin_cidrs=admin_cidrs(ctx), monitoring_allow_ips=ctx.o['monitoring_allow_ips'],
                                deployment=ctx.d['name'], postgres_image=POSTGRES_IMAGE), ctx.mine, mounts)
    ctx.save_progress(started=fp)
    return report_status(ctx, after_start=True)


def report_status(ctx, after_start=False, page_out=None):
    machines = ctx.machines()
    if not machines:
        say('nothing deployed yet: run `deploy.py join`')
        return 1
    inventory(ctx, machines, [n for n in ctx.mine if n in machines])
    (ctx.state / 'status').mkdir(exist_ok=True)
    log = play(ctx, 'status.yml', dict(page_out=bool(page_out)), [n for n in ctx.mine if n in machines], timeout=600)
    worst = 0
    step('status')
    for node in ctx.mine:
        path = ctx.state / 'status' / f'{node}.json'
        if not path.exists():
            say(f'  {node:12} no answer')
            worst = 1
            continue
        h = json.loads(path.read_text())
        say(f'  {node:12} {h.get("summary", "?")}')
        for problem in h.get('problems', []):
            say(f'  {"":12}   - {problem}')
        if h.get('level') == 'bad':
            worst = 1
    page = ctx.state / 'status' / 'page.html'
    own, combined = page_hosts(ctx)
    m = machines.get(own) or {}
    say(f'\nMonitoring page: on {own}, at http://127.0.0.1:{PAGE_PORT}/ there. Open it with:\n    python3 deploy/deploy.py monitor'
        f'\n  (an ssh tunnel to {m.get("tunnel_host")}:{m.get("tunnel_port")}; then browse http://127.0.0.1:{PAGE_PORT + 10000}/)')
    if page.exists():
        say(f'  a copy of the page as it is now: {page}')
    if ctx.d['signal']['endpoint'] != 'none' and any(n in C.MPC_NODES for n in ctx.mine) and not ctx.progress.get('account'):
        say('\nRemaining manual step: the Signal account (DEPLOYMENT.md "The account step"). ' +
            ('Local test: `python3 deploy/deploy.py account local-test`.' if ctx.d['signal']['endpoint'] == 'local-test'
             else 'The owner registers the account, then each computation operator runs `deploy.py account install DIR`.'))
    return worst


def cmd_status(args):
    ctx = Ctx(args)
    return report_status(ctx, page_out=True)


def cmd_monitor(args):
    ctx = Ctx(args)
    machines = ctx.machines()
    own, combined = page_hosts(ctx)
    host = combined or own
    m = machines[host]
    local_port = PAGE_PORT + 10000
    argv = ['ssh', '-i', str(ctx.state / 'ssh/id_ed25519'), '-o', 'StrictHostKeyChecking=accept-new',
            '-o', f'UserKnownHostsFile={ctx.state / "ssh/known_hosts"}', '-p', str(m['tunnel_port']), '-N',
            '-L', f'{local_port}:127.0.0.1:{PAGE_PORT}', f'{m["ssh_user"]}@{m["tunnel_host"]}']
    say(f'Monitoring page of {host}: http://127.0.0.1:{local_port}/  (Ctrl-C to close the tunnel)')
    if args.seconds:
        p = subprocess.Popen(argv)
        time.sleep(args.seconds)
        p.terminate()
        return 0
    return subprocess.call(argv)


def cmd_logs(args):
    ctx = Ctx(args)
    machines = ctx.machines()
    nodes = [args.node] if args.node else [n for n in ctx.mine if n in machines]
    inventory(ctx, machines, nodes)
    play(ctx, 'logs.yml', dict(lines=args.lines), nodes, timeout=900)
    for node in nodes:
        say(f'  {node}: {ctx.state / "logs" / "nodes" / node}')
    say('Logs are redacted on the node (keys, tokens, shares, ids, phone numbers); still review them before sending them anywhere.')
    return 0


def cmd_upgrade(args):
    """New images / circuits / settings from an updated deployment.toml: join again (software only
    changes; keys are kept), then start with the bundles of the other operators' upgraded nodes."""
    ctx = Ctx(args)
    say('Upgrade = the same two steps as the first time, with the updated deployment.toml:')
    say('  1. every operator: `deploy.py join` (keeps every key; installs the new software; writes new bundles)')
    say('  2. exchange the new bundles, `collect`, compare the NEW fingerprint, `start` (restarts the services)')
    say('Both computation nodes must change together: a node whose bundle still shows the old digests blocks collect.')
    if args.dirs:
        bundles, errors, warnings, rows = load_set(ctx, args.dirs)
        print_rows(rows)
        for e in errors:
            say(f'  still different: {e}')
    rc = cmd_join(args)
    return rc


def confirm(ctx, what):
    say(what)
    typed = input(f'Type the deployment name ({ctx.d["name"]}) to confirm: ').strip()
    if typed != ctx.d['name']:
        raise Fail('not confirmed; nothing was changed')


def cmd_destroy(args):
    ctx = Ctx(args)
    machines = ctx.machines()
    keep = 'DELETES the data disks too (the database contents and the computation nodes\' keys and shares are lost)' if args.delete_data \
        else 'keeps every data disk (database contents, node keys): `up`/`join` later reattaches them'
    if not args.yes_i_typed_it:
        confirm(ctx, f'destroy removes YOUR machines ({", ".join(ctx.mine)}) and {keep}.')
    for node in ctx.mine:
        spec = ctx.o['nodes'][node]
        if spec['provider'] == 'local':
            gone = L.down(ctx.d['name'], node, args.delete_data, ctx.log)
            say(f'  {node}: container removed; volumes removed: {", ".join(gone)}')
        elif spec['provider'] == 'existing' and node in machines:
            inventory(ctx, machines, [node])
            play(ctx, 'stop.yml', dict(delete_data=args.delete_data), [node], timeout=900)
            say(f'  {node}: services stopped (your machine stays)' + ('; data removed' if args.delete_data else '; data kept'))
    cloud = [n for n in ctx.mine if ctx.o['nodes'][n]['provider'] in P.CLOUD]
    if cloud:
        names = T.env_names(ctx.o, cloud)
        T.destroy(ctx.state / 'tofu' / 'machines', ctx.state / 'logs' / 'tofu-destroy.log', names)
        say(f'  cloud machines removed: {", ".join(cloud)}')
        if args.delete_data:
            T.destroy(ctx.state / 'tofu' / 'disks', ctx.state / 'logs' / 'tofu-destroy.log', names)
            say('  cloud data disks removed')
    if ctx.local:
        L.remove_network_if_unused(ctx.d['name'], ctx.log)
    for node in ctx.mine:
        machines.pop(node, None)
    (ctx.state / 'machines.json').write_text(json.dumps(machines, indent=1) + '\n')
    ctx.save_progress(started=None, joined=None, collected=None, account=None if args.delete_data else ctx.progress.get('account'))
    say('done.')
    return 0


def cmd_next(args):
    try:
        ctx = Ctx(args)
    except C.ConfigError as e:
        say(f'Configuration: {e}')
        say('Start with `python3 deploy/deploy.py init` (or edit deploy/deployment.toml and deploy/operator.toml).')
        return 1
    p = ctx.progress
    say(f'deployment "{ctx.d["name"]}", you are "{ctx.o["operator"]}" ({", ".join(ctx.mine)}); state in {ctx.state}')
    joined_ok = p.get('joined') and p.get('joined_deployment') == B.deployment_digest(ctx.d)
    if not joined_ok:
        say('Next: `python3 deploy/deploy.py join`' + (' (deployment.toml changed since your last join)' if p.get('joined') else ''))
        return 0
    say(f'  joined: bundles in {ctx.outbox}')
    if not p.get('collected'):
        say('Next: send your bundles to the other operators; put all bundles in one directory; `deploy.py collect DIR`')
        return 0
    say(f'  collected; fingerprint {p["collected"]}')
    if p.get('started') != p.get('collected'):
        say('Next: compare the fingerprint by voice with every operator, then `deploy.py start DIR --fingerprint ...`')
        return 0
    say('  started')
    if any(n in C.MPC_NODES for n in ctx.mine) and ctx.d['signal']['endpoint'] != 'none' and not p.get('account'):
        say('Next: the account step (DEPLOYMENT.md "The account step")')
        return 0
    say('Running. `deploy.py status` for the state of your nodes; `deploy.py monitor` for the page.')
    return 0


def cmd_up(args):
    """One person, every node."""
    ctx = Ctx(args)
    if sorted(ctx.mine) != sorted(ctx.d['nodes']):
        raise Fail('`up` is for one person operating every node: deployment.toml must name you for every node '
                   '(otherwise use join / collect / start with the other operators)')
    say('Single-operator deployment. Trust note: whoever runs this with root on both computation nodes can read both;\n'
        'this gives operational convenience, not the two-party protection (DEPLOYMENT.md "Deploying alone").')
    if ctx.d['signal']['endpoint'] == 'local-test' and not ctx.d['app']['wireguard_public_key']:
        say('note: [application-server] has no wireguard_public_key: no application can reach the daemons (run `deploy.py testapp up` first for a test one)')
    rc = cmd_join(args)
    if rc:
        return rc
    args.dirs = [str(ctx.outbox)]
    bundles, errors, warnings, rows = load_set(ctx, args.dirs)
    if errors:
        for e in errors:
            say(f'  PROBLEM: {e}')
        raise Fail('the bundles are not consistent')
    args.fingerprint = B.fingerprint(ctx.d, bundles)
    ctx.save_progress(collected=args.fingerprint)
    say(f'\n(one operator: the fingerprint {args.fingerprint} needs no comparison)')
    rc = cmd_start(args)
    if ctx.d['signal']['endpoint'] == 'local-test' and getattr(args, 'with_account', False):
        rc = cmd_account_local(args) or rc
    return rc


# ---------------------------------------------------------------------------------------------
# the account step


def cmd_account_install(args):
    """Install the account material on this operator's computation node(s), create the account's
    row on the database nodes (the `store` ceremony stage, both nodes at once), start the daemon."""
    ctx = Ctx(args)
    nodes = [n for n in ctx.mine if n in C.MPC_NODES]
    if not nodes:
        raise Fail('you operate no computation node: the account step is for the computation operators')
    source = Path(args.dir).resolve()
    for node in nodes:
        party = C.MPC_NODES.index(node)
        for need in ('common/mpc-export.json', 'common/tokens', f'party-{party}/credentials.share'):
            if not (source / need).exists():
                raise Fail(f'{source / need} is missing (the account directory holds common/ and party-{party}/)')
        if (source / f'party-{1 - party}').exists() and len(nodes) == 1:
            raise Fail(f'{source} holds the OTHER party\'s share too (party-{1 - party}/): each computation operator must receive only their own')
    machines = ctx.machines()
    inventory(ctx, machines, nodes)
    step('the account step: material onto the node(s), the account row on the database nodes, then the daemon')
    ids = {n: json.loads((ctx.outbox / f'{n}.bundle.json').read_text())['software']['image_id'] for n in nodes}
    play(ctx, 'account.yml', dict(name=ctx.d['name'], image_ids=ids, settle_seconds=3 * ctx.d['database']['epoch_seconds']),
         nodes, [(str(source), '/in/account')], timeout=1800)
    ctx.save_progress(account=True)
    say('Account installed; the daemon is starting. `deploy.py status` shows when the receive session runs.')
    return 0


def cmd_account_local(args):
    """local-test: a TEST account on the local Signal server, then install on both nodes (one person)."""
    ctx = Ctx(args)
    if ctx.d['signal']['endpoint'] != 'local-test':
        raise Fail('account local-test is only for [signal] endpoint = "local-test"')
    out = ctx.state / 'account-local'
    make_local_account(ctx, out)
    if sorted(n for n in ctx.mine if n in C.MPC_NODES) == C.MPC_NODES:
        args.dir = str(out)
        return cmd_account_install(args)
    say(f'Made {out}: give common/ and party-0/ to the operator of mpc-node-0, common/ and party-1/ to the operator of mpc-node-1;\n'
        'both then run `deploy.py account install DIR` within a minute of each other.')
    return 0


def make_local_account(ctx, out):
    """The local Signal server (local_signal_server/), a TEST account, its export, the signup tokens
    of its contacts signed by the test application (testapp), the credentials in two XOR shares.
    Contacts only the local server (127.0.0.1)."""
    sys.path.insert(0, str(ROOT / 'local_signal_server'))
    import check_signal_service_local as harness
    app_state =STATE_ROOT / ctx.d['name'] / '_testapp'
    if not (app_state / 'machines.json').exists():
        raise Fail('no test application: `deploy.py testapp up` first (it signs the contacts\' signup tokens)')
    step('local Signal server and a TEST account (fictional numbers, 127.0.0.1 only)')
    if not (harness.HERE / 'state/classpath.txt').exists():
        harness.run(['bash', harness.HERE / 'scripts/build_server.sh'])
    harness.run(['bash', harness.HERE / 'scripts/start_server.sh'])
    harness.lss('provision')
    harness.lss('export-mpc')
    export = json.loads(harness.EXPORT.read_text())
    if out.exists():
        shutil.rmtree(out)
    (out / 'common/tokens').mkdir(parents=True)
    shutil.copy2(harness.EXPORT, out / 'common/mpc-export.json')
    shutil.copy2(harness.STATE / 'tls/ca.pem', out / 'common/ca.pem')
    credentials = bytes.fromhex(export['sender']['upgrade_credentials_hex'])
    share = secrets.token_bytes(len(credentials))
    for party, value in ((0, share), (1, bytes(x ^ y for x, y in zip(credentials, share)))):
        (out / f'party-{party}').mkdir()
        (out / f'party-{party}/credentials.share').write_text(value.hex() + '\n')
        os.chmod(out / f'party-{party}/credentials.share', 0o600)
    ids = [int(c['contact_id_u128_hex'], 16) for c in export['contacts']] + [harness.ACCOUNT]
    testapp_call(ctx.args, 'tokens', dict(ids=[str(i) for i in ids]))
    for f in (app_state / 'fetched').glob('tokens/*.json'):
        shutil.copy2(f, out / 'common/tokens' / f.name)
    say(f'  account material in {out} ({len(ids)} signup tokens)')
    return out


# ---------------------------------------------------------------------------------------------
# the TEST application server (local-test only)


class AppCtx:
    """The test application server's own state (it is not an operator's node)."""
    def __init__(self, args):
        self.args = args
        self.deployment_file = Path(getattr(args, 'deployment', None) or (C.load_operator(Path(args.operator or DEFAULT_OPERATOR))['deployment'])).resolve()
        text = self.deployment_file.read_text()
        import tomllib
        raw = tomllib.loads(text)
        self.name = raw.get('name')
        self.raw = raw
        self.state = STATE_ROOT / self.name / '_testapp'
        self.state.mkdir(parents=True, exist_ok=True)
        os.chmod(self.state, 0o700)
        self.log = self.state / 'logs' / 'deploy.log'


def testapp_call(args, action, extra):
    a = AppCtx(args)
    machines = json.loads((a.state / 'machines.json').read_text())
    m = machines[C.APP]
    hosts = {C.APP: dict(ansible_host=m['ssh_host'], ansible_port=22, ansible_user='root', ansible_ssh_private_key_file='/state/ssh/id_ed25519',
                         ansible_ssh_common_args='-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null',
                         node=C.APP, node_role='app', wg_address=C.wg_address(C.APP), data_root='/srv/data', data_device='',
                         requirements='relaxed', provider='local', local_machine=True, party=None)}
    (a.state / 'inventory.json').write_text(json.dumps({'all': {'hosts': hosts, 'vars': {'ansible_python_interpreter': '/usr/bin/python3'}}}))
    (a.state / 'fetched').mkdir(exist_ok=True)
    log = a.state / 'logs' / f'testapp-{action}.log'
    code, summary = ansible(a.state, 'testapp.yml', 'inventory.json', dict(action=action, **extra), log, timeout=1800,
                            network=L.network_name(a.name))
    for line in summary:
        say('    ' + line)
    if code:
        raise Fail(f'testapp {action} failed; see {log}')
    return a


def cmd_testapp(args):
    a = AppCtx(args)
    if (a.raw.get('signal') or {}).get('endpoint', 'local-test') != 'local-test':
        raise Fail('the test application is only for [signal] endpoint = "local-test"')
    if args.action == 'up':
        key = a.state / 'ssh' / 'id_ed25519'
        if not key.exists():
            key.parent.mkdir(exist_ok=True)
            run(['ssh-keygen', '-q', '-t', 'ed25519', '-N', '', '-C', 'tls-mpc-testapp', '-f', key], a.log, 60)
        m = L.up(a.name, C.APP, dict(memory_gb=2), key.with_suffix('.pub'), a.log)
        (a.state / 'machines.json').write_text(json.dumps({C.APP: m}, indent=1))
        ident = (a.raw.get('software') or {}).get('node_image', '')
        if not ident:
            raise Fail('deployment.toml [software] node_image is empty (the test application runs notify-app from it)')
        (a.state / 'images').mkdir(exist_ok=True)
        tar = a.state / 'images' / f'{ident[:16]}.tar'
        if not tar.exists():
            code, _ = run([docker(), 'image', 'save', '-o', tar, f'sha256:{ident}'], a.log, 1800)
            if code:
                raise Fail('the node image is not in this computer\'s Docker')
        testapp_call(args, 'up', dict(image=dict(id=ident, tar=f'/state/images/{tar.name}')))
        keys = json.loads((a.state / 'fetched' / 'app-public.json').read_text())
        text = a.deployment_file.read_text()
        for field, value in (('notify_public_key', keys['notify_public_key']), ('signup_public_key', keys['signup_public_key']),
                             ('wireguard_public_key', keys['wireguard_public_key'])):
            text, n = re.subn(rf'(?m)^{field} = ".*"', f'{field} = "{value}"', text, count=1)
            if n != 1:
                raise Fail(f'deployment.toml has no line `{field} = "..."` under [application-server] to fill')
        a.deployment_file.write_text(text)
        say(f'test application ready; its three public keys are now in {a.deployment_file} [application-server]')
        return 0
    if args.action == 'start':
        d = C.load_deployment(a.deployment_file)
        bundles, problems = B.read_bundles(args.dirs)
        mpc = [dict(node=n, address=C.wg_address(n), public_key=bundles[n]['wireguard']['public_key'], endpoint=bundles[n]['wireguard']['endpoint'])
               for n in C.MPC_NODES]
        testapp_call(args, 'start', dict(peers=mpc, network_config=B.network_config(d, bundles)))
        say('test application connected to both computation nodes')
        return 0
    if args.action == 'send':
        return testapp_send(args, a)
    raise Fail(f'unknown testapp action {args.action}')


def testapp_send(args, a):
    """One signup and one 200-byte send, against the LOCAL Signal server only."""
    sys.path.insert(0, str(ROOT / 'local_signal_server'))
    import check_signal_service_local as harness
    new = secrets.randbits(100)
    text = ('Push-button deployment test: one message to a contact who signed up a moment ago. ' + 'x' * 200)[:200]
    report = dict(id_bits=100, started=time.time())
    testapp_call(args, 'token', dict(id=str(new)))
    token = json.loads((a.state / 'fetched' / 'token.json').read_text()).get('token', '')
    harness.lss('signup', 'newuser', '+12025550104', 'sender', token)
    testapp_call(args, 'events', dict(id=str(new)))
    events = json.loads((a.state / 'fetched' / 'events.json').read_text())
    report['signup'] = signed = str(new) in (events.get('signups') or []) and bool(events.get('agreed'))
    say(f'  signup reported by both daemons: {signed}')
    # A contact who just signed up is readable once the database nodes have applied the epoch
    # after the deal: the daemons answer "retry later" until then, and the application retries.
    epoch = int((a.raw.get('database') or {}).get('epoch_seconds', 120))
    for attempt in range(8):
        testapp_call(args, 'notify', dict(id=str(new), text=text))
        result = json.loads((a.state / 'fetched' / 'notify.json').read_text())
        rows = (result.get('result') or {}).get('results') or []
        if not rows or any(r.get('result') != 'retry later' for r in rows):
            break
        say(f'  the daemons say "retry later" (the new contact is readable after the next database epoch); again in {epoch} s')
        time.sleep(epoch)
    report['notify_attempts'] = attempt + 1
    seen = harness.receive('newuser', 6)
    attributed = [g for g in seen if g['envelope'].get('source_service_id') or g['envelope'].get('source_device')]
    report['delivered'] = bool(result.get('agreed')) and [r.get('result') for r in rows] == ['delivered']
    report['decrypted_sealed'] = text in [g['text'] for g in seen] and not attributed
    report['passed'] = bool(signed and report['delivered'] and report['decrypted_sealed'])
    (a.state / 'send-report.json').write_text(json.dumps(report, indent=1) + '\n')
    say(f'  delivered and agreed: {report["delivered"]}; decrypted by the new user from a sealed envelope: {report["decrypted_sealed"]}')
    say(f'signup and send {"PASSED" if report["passed"] else "FAILED"} ({a.state / "send-report.json"})')
    return 0 if report['passed'] else 1


# ---------------------------------------------------------------------------------------------
# build (the builder)


def cmd_build(args):
    """Record (or build) the images every operator will run, and the digests, in deployment.toml."""
    import tomllib
    dfile = Path(args.deployment or C.load_operator(Path(args.operator or DEFAULT_OPERATOR))['deployment']).resolve()
    raw = tomllib.loads(dfile.read_text())     # not fully validated: the application's keys may not be known yet
    d = dict(name=raw.get('name', 'deployment'), security=raw.get('security', 'malicious'))
    if not C.NAME.match(d['name']) or d['security'] not in ('malicious', 'semi-honest'):
        raise Fail('deployment.toml: set name and security first')
    log = STATE_ROOT / d['name'] / '_builder' / 'build.log'
    log.parent.mkdir(parents=True, exist_ok=True)
    node_tag = args.node_tag or f'tls-mpc-node:{d["security"]}'
    db_tag = args.db_tag or 'tls-mpc-dbnode'
    if not args.record:
        ctxdir = Path(args.context or (ROOT / '.deps/deploy-ctx')).resolve()
        steps = [[sys.executable, DEPLOY / 'scripts/build_artifacts.py', 'context', '--out', ctxdir, '--replace', '--yes'],
                 [sys.executable, DEPLOY / 'scripts/build_artifacts.py', 'image', '--context', ctxdir, '--mode', d['security'],
                  '--tag', node_tag, '--platform', args.platform, '--yes'],
                 [sys.executable, DEPLOY / 'scripts/build_artifacts.py', 'image', '--context', ctxdir, '--dockerfile',
                  DEPLOY / 'docker/dbnode.Dockerfile', '--tag', db_tag, '--platform', args.platform, '--yes']]
        for argv in steps:
            say('  ' + ' '.join(map(str, argv)))
            if subprocess.call([str(a) for a in argv]):
                raise Fail('build step failed (see .deps/deploy-logs/)')
    ids = {}
    for key, tag in (('node_image', node_tag), ('dbnode_image', db_tag)):
        code, text = run([docker(), 'image', 'inspect', tag, '--format', '{{.Id}} {{.Architecture}}'], log, 30)
        if code:
            raise Fail(f'image {tag} not found')
        ident, arch = text.split()
        ids[key] = ident.removeprefix('sha256:')
        say(f'  {key} = {ident}  ({arch})')
        if args.out:
            out = Path(args.out)
            out.mkdir(parents=True, exist_ok=True)
            target = out / f'{ids[key][:16]}.tar'
            if not target.exists():
                run([docker(), 'image', 'save', '-o', target, ident], log, 1800)
            say(f'    file for the operators: {target}')
    if args.circuits:
        ids['manifest_sha256'] = dl.read_manifest(Path(args.circuits) / 'manifest.txt')[0]
    if args.word_dir:
        problems, stats = dl.word_dir_summary(args.word_dir, image_pins(ids.get('node_image'), log))
        if problems:
            raise Fail('word dir: ' + '; '.join(problems[:3]))
        ids['word_dir_sha256'] = stats['word_dir_sha256']
    head, dirty = tool_commit()
    ids['commit'] = head
    text = dfile.read_text()
    for key, value in ids.items():
        text, n = re.subn(rf'(?m)^{key} = ".*"', f'{key} = "{value}"', text, count=1)
        if n != 1:
            raise Fail(f'deployment.toml has no line `{key} = "..."` under [software]')
    dfile.write_text(text)
    say(f'recorded in {dfile}. Send it, and the image files, to every operator.')
    if dirty:
        say('WARNING: deploy/ has uncommitted changes; commit them so the operators can use the same commit')
    return 0
