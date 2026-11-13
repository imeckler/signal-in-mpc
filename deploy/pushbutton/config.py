"""The two configuration files and their validation.

deployment.toml  SHARED, public, identical for every operator: what is deployed and who operates
                 which node (deploy/deployment.example.toml explains every field).
operator.toml    PRIVATE to one operator: where their nodes run and the credentials to create
                 them (deploy/operator.example.toml).

Every problem is reported as one plain-English line (`ConfigError`); `warnings` lists the trust
consequences the operators must accept knowingly.
"""
import ipaddress
import os
import re
import tomllib
from pathlib import Path

from . import providers as P

MPC_NODES = ['mpc-node-0', 'mpc-node-1']
DB_PREFIX = 'db-node-'
APP = 'application-server'
WG_NET = ipaddress.ip_network('10.77.0.0/24')
WG_PORT = 51820
LEAN_SCRIPTS = 'contacts,account,curve,send,receive,refresh,tls,masks,random,upgrade'   # Flows/Select.lean `closedSet`
LEAN_CEREMONY_SCRIPTS = LEAN_SCRIPTS + ',ceremony'                                      # `ceremonySet`
DB_NODES_RUN_SO_FAR = 5          # the only database size ever run (secret-shared-db docs, the harness)
DB_MAX_NODES = 16                # the database's sync helper gives up with more peers (server/src/main.rs)
B64KEY = re.compile(r'^[A-Za-z0-9+/]{43}=$')     # 32 bytes, standard base64 (WireGuard, ed25519 keys)
HEX64 = re.compile(r'^(sha256:)?[0-9a-f]{64}$')
NAME = re.compile(r'^[a-z][a-z0-9-]{1,30}$')
LABEL = re.compile(r'^[A-Za-z0-9][A-Za-z0-9_.-]{0,40}$')


class ConfigError(Exception):
    """One line, plain English, says what to change."""


def wg_address(node):
    if node == 'mpc-node-0':
        return '10.77.0.1'
    if node == 'mpc-node-1':
        return '10.77.0.2'
    if node == APP:
        return '10.77.0.100'
    return f'10.77.0.{10 + db_index(node)}'


def db_index(node):
    return int(node[len(DB_PREFIX):])


def role(node):
    return 'mpc' if node in MPC_NODES else ('app' if node == APP else 'db')


def _load(path, what):
    path = Path(path)
    if not path.is_file():
        raise ConfigError(f'{what} {path} does not exist (copy the example next to it and edit it)')
    try:
        return tomllib.loads(path.read_text())
    except tomllib.TOMLDecodeError as e:
        raise ConfigError(f'{path} is not valid TOML: {e}') from None


def _unknown(table, allowed, where):
    for key in table:
        if key not in allowed:
            raise ConfigError(f'{where}: unknown setting "{key}" (a typo? allowed: {", ".join(sorted(allowed))})')


def _choice(table, key, choices, default, where):
    value = table.get(key, default)
    if value not in choices:
        raise ConfigError(f'{where}: {key} must be one of {", ".join(repr(c) for c in choices)}, not {value!r}')
    return value


def _int(table, key, default, low, high, where):
    value = table.get(key, default)
    if not isinstance(value, int) or isinstance(value, bool) or not low <= value <= high:
        raise ConfigError(f'{where}: {key} must be a whole number from {low} to {high}, not {value!r}')
    return value


# ---------------------------------------------------------------------------------------------
# deployment.toml


DEPLOYMENT_KEYS = {'name', 'security', 'worker_logic', 'allow_same_provider', 'application-server', 'signal', 'database',
                   'monitoring', 'nodes', 'software'}


def load_deployment(path):
    data = _load(path, 'the deployment file')
    return validate_deployment(data, str(path))


def validate_deployment(data, where='deployment.toml'):
    _unknown(data, DEPLOYMENT_KEYS, where)
    d = {}
    name = data.get('name')
    if not isinstance(name, str) or not NAME.match(name):
        raise ConfigError(f'{where}: name must be 2-31 characters, lower-case letters, digits and "-", starting with a letter (got {name!r})')
    d['name'] = name
    d['security'] = _choice(data, 'security', ['malicious', 'semi-honest'], 'malicious', where)
    d['worker_logic'] = _choice(data, 'worker_logic', ['legacy', 'lean'], 'legacy', where)
    d['allow_same_provider'] = bool(data.get('allow_same_provider', False))

    app = data.get('application-server') or {}
    _unknown(app, {'notify_public_key', 'signup_public_key', 'wireguard_public_key'}, f'{where} [application-server]')
    for key in ('notify_public_key', 'signup_public_key'):
        value = app.get(key, '')
        if not isinstance(value, str) or not B64KEY.match(value):
            raise ConfigError(f'{where} [application-server]: {key} must be the application server\'s 44-character base64 public key '
                              f'(from `handoff_client gen-key`; `deploy.py testapp` makes a test one), got {value!r:.60}')
    wg = app.get('wireguard_public_key', '')
    if wg and not B64KEY.match(wg):
        raise ConfigError(f'{where} [application-server]: wireguard_public_key must be a 44-character WireGuard public key (`wg pubkey`) or empty')
    d['app'] = dict(notify_public_key=app['notify_public_key'], signup_public_key=app['signup_public_key'], wireguard_public_key=wg)

    signal = data.get('signal') or {}
    _unknown(signal, {'endpoint', 'certificate_margin_hours'}, f'{where} [signal]')
    d['signal'] = dict(endpoint=_choice(signal, 'endpoint', ['local-test', 'production', 'none'], 'local-test', f'{where} [signal]'),
                       certificate_margin_hours=_int(signal, 'certificate_margin_hours', 48, 6, 150, f'{where} [signal]'))

    db = data.get('database') or {}
    _unknown(db, {'threshold', 'max_malicious', 'epoch_seconds'}, f'{where} [database]')
    d['database'] = dict(threshold=_int(db, 'threshold', 3, 2, DB_MAX_NODES, f'{where} [database]'),
                         max_malicious=_int(db, 'max_malicious', 1, 0, DB_MAX_NODES, f'{where} [database]'),
                         epoch_seconds=_int(db, 'epoch_seconds', 120, 4, 3600, f'{where} [database]'))

    mon = data.get('monitoring') or {}
    _unknown(mon, {'combined_page_on'}, f'{where} [monitoring]')
    d['monitoring'] = dict(combined_page_on=mon.get('combined_page_on', ''))

    nodes = data.get('nodes')
    if not isinstance(nodes, dict) or not nodes:
        raise ConfigError(f'{where}: the [nodes.NAME] tables are missing (mpc-node-0, mpc-node-1, db-node-0 ...)')
    d['nodes'] = {}
    for node, spec in nodes.items():
        if node not in MPC_NODES and not re.fullmatch(r'db-node-(0|[1-9][0-9]?)', node):
            raise ConfigError(f'{where}: [nodes.{node}] is not a node name (mpc-node-0, mpc-node-1, db-node-0, db-node-1, ...)')
        if not isinstance(spec, dict):
            raise ConfigError(f'{where}: [nodes.{node}] must be a table with operator = "..."')
        _unknown(spec, {'operator'}, f'{where} [nodes.{node}]')
        operator = spec.get('operator')
        if not isinstance(operator, str) or not LABEL.match(operator):
            raise ConfigError(f'{where} [nodes.{node}]: operator must be a short name (letters, digits, "_", "-", "."), got {operator!r}')
        d['nodes'][node] = dict(operator=operator)
    for node in MPC_NODES:
        if node not in d['nodes']:
            raise ConfigError(f'{where}: [nodes.{node}] is missing (there are always exactly two computation nodes)')
    dbs = sorted((db_index(n) for n in d['nodes'] if n.startswith(DB_PREFIX)))
    if dbs != list(range(len(dbs))):
        raise ConfigError(f'{where}: database nodes must be numbered db-node-0, db-node-1, ... without gaps (got {", ".join(f"db-node-{i}" for i in dbs) or "none"})')
    n, t, mm = len(dbs), d['database']['threshold'], d['database']['max_malicious']
    if n < 3:
        raise ConfigError(f'{where}: {n} database nodes is too few; the database needs at least 3 (5 is what has been run)')
    if n > DB_MAX_NODES:
        raise ConfigError(f'{where}: {n} database nodes is too many; the database software supports at most {DB_MAX_NODES}')
    if t > n:
        raise ConfigError(f'{where} [database]: threshold {t} is more than the {n} database nodes')
    if t + mm > n:
        raise ConfigError(f'{where} [database]: threshold + max_malicious = {t + mm} exceeds the {n} database nodes '
                          f'(an epoch needs that many signatures; the database refuses this)')
    d['db_count'] = n
    combined = d['monitoring']['combined_page_on']
    if combined and combined not in d['nodes']:
        raise ConfigError(f'{where} [monitoring]: combined_page_on = "{combined}" is not one of the nodes')

    sw = data.get('software') or {}
    _unknown(sw, {'commit', 'builds', 'node_image', 'dbnode_image', 'manifest_sha256', 'word_dir_sha256'}, f'{where} [software]')
    d['software'] = dict(commit=sw.get('commit', ''), builds=_choice(sw, 'builds', ['one-builder', 'each-operator'], 'one-builder', f'{where} [software]'))
    if d['software']['commit'] and not re.fullmatch(r'[0-9a-f]{40}', d['software']['commit']):
        raise ConfigError(f'{where} [software]: commit must be a full 40-character git commit id (`git rev-parse HEAD`)')
    for key in ('node_image', 'dbnode_image', 'manifest_sha256', 'word_dir_sha256'):
        value = sw.get(key, '')
        if value and not HEX64.match(value):
            raise ConfigError(f'{where} [software]: {key} must be a 64-hex-digit digest (as `deploy.py build` prints), got {value!r:.80}')
        d['software'][key] = value.removeprefix('sha256:')
    return d


def deployment_warnings(d):
    """Trust consequences of who operates what, one sentence each."""
    out = []
    ops = {node: spec['operator'] for node, spec in d['nodes'].items()}
    if ops['mpc-node-0'] == ops['mpc-node-1']:
        out.append(f'operator "{ops["mpc-node-0"]}" runs BOTH computation nodes: they can read every contact\'s data; '
                   'this gives convenience, not the two-party protection')
    t = d['database']['threshold']
    per = {}
    for node, op in ops.items():
        if node.startswith(DB_PREFIX):
            per.setdefault(op, []).append(node)
    for op, held in sorted(per.items()):
        if len(held) >= t:
            out.append(f'operator "{op}" runs {len(held)} database nodes ({", ".join(held)}), at least the threshold {t}: '
                       'they alone can reconstruct every contact\'s key')
    if d['db_count'] != DB_NODES_RUN_SO_FAR:
        out.append(f'{d["db_count"]} database nodes: only 5 have ever been run; the software allows it but it is untested')
    if d['database']['max_malicious'] + t == d['db_count']:
        out.append(f'database: threshold {t} + max_malicious {d["database"]["max_malicious"]} = {d["db_count"]}: '
                   'every database node must be up for the database to advance')
    if d['worker_logic'] == 'lean':
        out.append('worker_logic = "lean": the Lean script path is slower until parity and not yet the tested production path')
    return out


# ---------------------------------------------------------------------------------------------
# operator.toml


OPERATOR_KEYS = {'operator', 'deployment', 'admin_ips', 'monitoring_allow_ips', 'software', 'nodes', 'credentials'}


def load_operator(path):
    data = _load(path, 'the operator file')
    return validate_operator(data, str(path), base=Path(path).resolve().parent)


def _path(value, base):
    p = Path(os.path.expanduser(value))
    return p if p.is_absolute() else (base / p)


def validate_operator(data, where='operator.toml', base=Path('.')):
    _unknown(data, OPERATOR_KEYS, where)
    o = {}
    op = data.get('operator')
    if not isinstance(op, str) or not LABEL.match(op):
        raise ConfigError(f'{where}: operator must be your short name as it appears in deployment.toml, got {op!r}')
    o['operator'] = op
    o['deployment'] = _path(data.get('deployment', 'deployment.toml'), base)
    admin = data.get('admin_ips', ['auto'])
    if not isinstance(admin, list) or not admin:
        raise ConfigError(f'{where}: admin_ips must be a list such as ["auto"] or ["198.51.100.7/32"]')
    for value in admin:
        if value != 'auto':
            try:
                ipaddress.ip_network(value, strict=False)
            except ValueError:
                raise ConfigError(f'{where}: admin_ips entry {value!r} is not an address or network (or "auto")') from None
    o['admin_ips'] = admin
    allow = data.get('monitoring_allow_ips', [])
    for value in allow:
        try:
            ipaddress.ip_network(value, strict=False)
        except ValueError:
            raise ConfigError(f'{where}: monitoring_allow_ips entry {value!r} is not an address or network') from None
    o['monitoring_allow_ips'] = allow
    sw = data.get('software') or {}
    _unknown(sw, {'images', 'images_dir', 'circuits_dir', 'word_dir', 'platform'}, f'{where} [software]')
    o['software'] = dict(images=_choice(sw, 'images', ['prebuilt', 'build-here'], 'prebuilt', f'{where} [software]'),
                         images_dir=_path(sw['images_dir'], base) if sw.get('images_dir') else None,
                         circuits_dir=_path(sw['circuits_dir'], base) if sw.get('circuits_dir') else None,
                         word_dir=_path(sw['word_dir'], base) if sw.get('word_dir') else None,
                         platform=sw.get('platform', ''))
    nodes = data.get('nodes')
    if not isinstance(nodes, dict) or not nodes:
        raise ConfigError(f'{where}: no [nodes.NAME] table: list the node(s) you operate (deployment.toml says which)')
    o['nodes'] = {}
    for node, spec in nodes.items():
        if not isinstance(spec, dict):
            raise ConfigError(f'{where}: [nodes.{node}] must be a table')
        provider = spec.get('provider')
        if provider not in P.PROVIDERS:
            raise ConfigError(f'{where} [nodes.{node}]: provider must be one of {", ".join(sorted(P.PROVIDERS))}, not {provider!r}')
        o['nodes'][node] = P.PROVIDERS[provider].validate(node, role(node), spec, f'{where} [nodes.{node}]', base)
    creds = data.get('credentials') or {}
    o['credentials'] = {}
    o['inline_secrets'] = []
    used = {spec['provider'] for spec in o['nodes'].values()}
    for provider in sorted(used):
        need = P.PROVIDERS[provider].credentials
        if not need:
            continue
        table = creds.get(provider)
        if not isinstance(table, dict):
            raise ConfigError(f'{where}: [credentials.{provider}] is missing; it needs {", ".join(need)} '
                              '(each as "env:VARIABLE" or "file:/path"; see operator.example.toml)')
        _unknown(table, set(need), f'{where} [credentials.{provider}]')
        o['credentials'][provider] = {}
        for key in need:
            value = table.get(key)
            if not isinstance(value, str) or not value:
                raise ConfigError(f'{where} [credentials.{provider}]: {key} is missing (write "env:VARIABLE" or "file:/path")')
            if not (value.startswith('env:') or value.startswith('file:')):
                o['inline_secrets'].append(f'[credentials.{provider}] {key}')
            o['credentials'][provider][key] = value
    return o


def resolve_secret(value, base=Path('.')):
    """The value of a credential reference: env:NAME, file:PATH, or (warned) the inline value."""
    if value.startswith('env:'):
        name = value[4:]
        if name not in os.environ:
            raise ConfigError(f'the environment variable {name} is not set (it holds a cloud credential; export it first)')
        return os.environ[name]
    if value.startswith('file:'):
        path = _path(value[5:], base)
        if not path.is_file():
            raise ConfigError(f'credential file {path} does not exist')
        return path.read_text().strip()
    return value


def check_pair(d, o):
    """The operator file against the deployment file."""
    mine = sorted(n for n, spec in d['nodes'].items() if spec['operator'] == o['operator'])
    if not mine:
        raise ConfigError(f'deployment.toml names no node for operator "{o["operator"]}" (the operator names there: '
                          f'{", ".join(sorted({s["operator"] for s in d["nodes"].values()}))})')
    for node in o['nodes']:
        if node not in d['nodes']:
            raise ConfigError(f'operator.toml lists [nodes.{node}], which deployment.toml does not have')
        if d['nodes'][node]['operator'] != o['operator']:
            raise ConfigError(f'operator.toml lists [nodes.{node}], but deployment.toml says "{d["nodes"][node]["operator"]}" operates it')
    missing = [n for n in mine if n not in o['nodes']]
    if missing:
        raise ConfigError(f'deployment.toml says you ("{o["operator"]}") operate {", ".join(missing)}: add [nodes.{missing[0]}] to operator.toml')
    providers = {spec['provider'] for spec in o['nodes'].values()}
    if d['signal']['endpoint'] == 'local-test' and providers - {'local'}:
        raise ConfigError('[signal] endpoint = "local-test" uses the test Signal server on this computer, which machines elsewhere cannot reach: '
                          'use provider = "local" to rehearse here, or set endpoint = "none" (deploy without any Signal connection) '
                          'or "production" (the real service, needs --i-have-the-go-ahead)')
    if 'local' in providers and providers != {'local'}:
        raise ConfigError('provider "local" cannot be mixed with real machines in one operator file (local machines are containers on this computer)')
    if any(o['nodes'][n]['provider'] == 'local' for n in o['nodes']) and d['signal']['endpoint'] == 'production':
        raise ConfigError('provider "local" is for tests: it cannot use endpoint = "production"')
    me = [n for n in MPC_NODES if n in o['nodes']]
    if len(me) == 2 and o['nodes']['mpc-node-0']['provider'] == o['nodes']['mpc-node-1']['provider'] \
            and o['nodes']['mpc-node-0']['provider'] != 'local' and not d['allow_same_provider']:
        raise ConfigError(f'both computation nodes are on provider "{o["nodes"]["mpc-node-0"]["provider"]}": that provider could read both; '
                          'put them on different providers, or set allow_same_provider = true in deployment.toml to accept it')
    if me and not o['software']['circuits_dir']:
        raise ConfigError('you operate a computation node: set [software] circuits_dir (the circuit set whose manifest digest deployment.toml lists)')
    if me and not o['software']['word_dir']:
        raise ConfigError('you operate a computation node: set [software] word_dir (the word circuits and field programs)')
    return mine


def operator_warnings(d, o):
    out = []
    for item in o['inline_secrets']:
        out.append(f'operator.toml holds a secret inline ({item}); prefer "env:VARIABLE" or "file:/path" so the file can be shown safely')
    for node, spec in o['nodes'].items():
        out.extend(f'{node}: {w}' for w in spec.get('warnings', []))
    return out
