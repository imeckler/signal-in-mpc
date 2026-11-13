"""Public bundles, their checks, and the deployment fingerprint.

A bundle (`<node>.bundle.json`) is everything the other operators need to know about one node,
and nothing secret: its WireGuard public key and endpoint, its other public keys and
certificates, and the digests of the software it actually runs. `collect` checks a set of
bundles against deployment.toml and derives ONE fingerprint from deployment.toml and every bundle;
the operators compare that fingerprint by voice or in person. That comparison is the only thing
that authenticates the keys: whoever relays the files could otherwise swap one.

What the fingerprint does NOT authenticate: that the software is honest. It only shows that
everyone runs the SAME digests (and which); what those digests contain is decided by who built
them (DEPLOYMENT.md, "Who builds the software").
"""
import hashlib
import json
import re
from pathlib import Path

from . import config as C

FORMAT = 'tls-mpc-node-bundle-v1'
SECRET_LOOKING = re.compile(r'PRIVATE KEY|secret_seed|"password"|pg-password|PrivateKey', re.I)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)


def deployment_digest(d):
    return hashlib.sha256(canonical(d).encode()).hexdigest()


def bundle_digest(bundle):
    return hashlib.sha256(canonical(bundle).encode()).hexdigest()


def assert_public(bundle):
    """Refuse to write anything that looks secret into a bundle."""
    text = canonical(bundle)
    m = SECRET_LOOKING.search(text)
    if m:
        raise ValueError(f'refusing to write a bundle that contains "{m.group(0)}" (bundles must hold public data only)')


def write_bundle(bundle, directory):
    assert_public(bundle)
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f'{bundle["node"]}.bundle.json'
    path.write_text(json.dumps(bundle, indent=1, sort_keys=True) + '\n')
    return path


def read_bundles(directories):
    """Every *.bundle.json in the directories (later directories win for the same file content)."""
    out, problems = {}, []
    for directory in directories:
        for path in sorted(Path(directory).glob('*.bundle.json')):
            try:
                bundle = json.loads(path.read_text())
            except (OSError, ValueError) as e:
                problems.append(f'{path.name}: not readable JSON ({e})')
                continue
            node = bundle.get('node')
            if bundle.get('format') != FORMAT:
                problems.append(f'{path.name}: not a {FORMAT} bundle')
                continue
            if node in out and bundle_digest(out[node]) != bundle_digest(bundle):
                problems.append(f'two different bundles for {node} ({path}); keep only the newest from its operator')
                continue
            out[node] = bundle
    return out, problems


def fingerprint(d, bundles):
    """Six groups of five digits (about 100 bits) from deployment.toml and every bundle."""
    material = 'tls-mpc deployment fingerprint v1\n' + canonical(d) + '\n' + canonical([bundles[n] for n in sorted(bundles)])
    number = int.from_bytes(hashlib.sha256(material.encode()).digest(), 'big') % (10 ** 30)
    digits = f'{number:030d}'
    return '-'.join(digits[i:i + 5] for i in range(0, 30, 5))


def normalize_fingerprint(text):
    return re.sub(r'[^0-9]', '', text or '')


def check(d, bundles):
    """(errors, warnings, table) for a complete set of bundles."""
    errors, warnings = [], []
    want = sorted(d['nodes'])
    for node in want:
        if node not in bundles:
            errors.append(f'missing: {node} (operator "{d["nodes"][node]["operator"]}" sends {node}.bundle.json after `deploy.py join`)')
    for node in sorted(bundles):
        if node not in d['nodes'] and node != C.APP:
            errors.append(f'{node}.bundle.json is not a node of this deployment')
    ddig = deployment_digest(d)
    seen_keys = {}
    for node, b in sorted(bundles.items()):
        if node == C.APP:
            continue
        if node not in d['nodes']:
            continue
        if b.get('deployment') != d['name']:
            errors.append(f'{node}: made for deployment "{b.get("deployment")}", not "{d["name"]}"')
        if b.get('deployment_sha256') != ddig:
            errors.append(f'{node}: made with a different deployment.toml; its operator must run `deploy.py join` again with the current file')
        if b.get('operator') != d['nodes'][node]['operator']:
            errors.append(f'{node}: made by "{b.get("operator")}", but deployment.toml says "{d["nodes"][node]["operator"]}" operates it')
        key = (b.get('wireguard') or {}).get('public_key', '')
        if not C.B64KEY.match(key or ''):
            errors.append(f'{node}: no valid WireGuard public key')
        elif key in seen_keys:
            errors.append(f'{node} and {seen_keys[key]} have the same WireGuard public key')
        else:
            seen_keys[key] = node
        if (b.get('wireguard') or {}).get('address') != C.wg_address(node):
            errors.append(f'{node}: tunnel address {b.get("wireguard", {}).get("address")} is not {C.wg_address(node)}')
        try:
            assert_public(b)
        except ValueError as e:
            errors.append(f'{node}: {e}')
    # Software: what every node actually runs.
    sw_d = d['software']
    mpc = [bundles[n] for n in C.MPC_NODES if n in bundles]
    dbs = [bundles[n] for n in sorted(bundles) if n.startswith(C.DB_PREFIX)]
    rows = []
    for node in sorted(bundles):
        s = bundles[node].get('software') or {}
        rows.append((node, bundles[node].get('operator', ''), s.get('tool_digest', '')[:12] + ('*' if s.get('tool_dirty') else ''),
                     (s.get('image_id') or '')[:12], s.get('images', ''), (s.get('manifest_sha256') or '')[:12],
                     (s.get('word_dir_sha256') or '')[:12], ((s.get('settings') or {}).get('serve') or '')[:12]))

    def same(values, what, nodes):
        values = [v for v in values]
        if len(set(values)) > 1:
            return f'{what} differs between {", ".join(nodes)}: ' + ', '.join(f'{n}={str(v)[:16]}' for n, v in zip(nodes, values))
        return None

    tools = {n: (bundles[n].get('software') or {}).get('tool_digest', '') for n in bundles if n in d['nodes']}
    problem = same(list(tools.values()), 'the deploy tool itself (digest of deploy/)', list(tools))
    if problem:
        errors.append(problem + ' (every operator must run the tool from the agreed commit, unmodified)')
    commits = {n: (bundles[n].get('software') or {}).get('tool_commit', '') for n in bundles if n in d['nodes']}
    problem = same(list(commits.values()), 'the repository commit the tool ran from', list(commits))
    if problem and not same(list(tools.values()), '', list(tools)):
        warnings.append(problem + ' (the tool\'s files are identical, so this does not matter for the deployment)')
    if sw_d['commit'] and any(c != sw_d['commit'] for c in commits.values()):
        warnings.append(f'a node ran the deploy tool from a commit other than deployment.toml\'s {sw_d["commit"][:12]} '
                        '(the tool digests above are what must agree)')
    dirty = [n for n in bundles if (bundles[n].get('software') or {}).get('tool_dirty')]
    if dirty:
        warnings.append(f'{", ".join(dirty)}: the deploy tool ran from a checkout with uncommitted changes')
    if len(mpc) == 2:
        names = C.MPC_NODES
        s0, s1 = mpc[0]['software'], mpc[1]['software']
        for key, what in (('manifest_sha256', 'circuit manifest'), ('word_dir_sha256', 'word circuits / field programs'),
                          ('pins_sha256', 'field-program pins'), ('mode', 'security mode'), ('worker_logic', 'worker logic')):
            problem = same([s0.get(key), s1.get(key)], what, names)
            if problem:
                errors.append(problem)
        for kind in ('serve', 'receive', 'notify', 'worker_session'):
            problem = same([(s0.get('settings') or {}).get(kind), (s1.get('settings') or {}).get(kind)], f'agreed settings ({kind})', names)
            if problem:
                errors.append(problem)
        for s, n in ((s0, names[0]), (s1, names[1])):
            if s.get('mode') != d['security']:
                errors.append(f'{n} runs the {s.get("mode")} image, but deployment.toml says security = "{d["security"]}"')
            if sw_d['manifest_sha256'] and s.get('manifest_sha256') != sw_d['manifest_sha256']:
                errors.append(f'{n}: circuit manifest {str(s.get("manifest_sha256"))[:16]} is not deployment.toml\'s {sw_d["manifest_sha256"][:16]}')
            if sw_d['word_dir_sha256'] and s.get('word_dir_sha256') != sw_d['word_dir_sha256']:
                errors.append(f'{n}: word dir {str(s.get("word_dir_sha256"))[:16]} is not deployment.toml\'s {sw_d["word_dir_sha256"][:16]}')
        ids = [s0.get('image_id'), s1.get('image_id')]
        if ids[0] != ids[1]:
            if sw_d['builds'] == 'each-operator' and s0.get('images') == s1.get('images') == 'build-here':
                warnings.append('the two computation nodes run images built independently (different image digests, as expected '
                                'until builds are reproducible): only the commit, circuits, pins and settings above could be compared')
                bins = same([s0.get('binaries_sha256'), s1.get('binaries_sha256')], 'binaries', names)
                if bins:
                    warnings.append(bins)
            else:
                errors.append(same(ids, 'the computation image', names))
        if sw_d['builds'] == 'one-builder' and sw_d['node_image'] and any(i != sw_d['node_image'] for i in ids):
            errors.append(f'a computation node does not run deployment.toml\'s image {sw_d["node_image"][:16]}')
        if (mpc[0].get('provider') == mpc[1].get('provider') and mpc[0].get('provider') not in ('local', 'existing')
                and not d['allow_same_provider']):
            errors.append(f'both computation nodes are on provider "{mpc[0].get("provider")}" (set allow_same_provider = true to accept that this provider could read both)')
    if dbs:
        ids = {b['node']: (b.get('software') or {}).get('image_id') for b in dbs}
        if len(set(ids.values())) > 1 and sw_d['builds'] == 'one-builder':
            errors.append(same(list(ids.values()), 'the database image', list(ids)))
        if sw_d['builds'] == 'one-builder' and sw_d['dbnode_image'] and any(i != sw_d['dbnode_image'] for i in ids.values()):
            errors.append(f'a database node does not run deployment.toml\'s image {sw_d["dbnode_image"][:16]}')
    return [e for e in errors if e], warnings, rows


def network_config(d, bundles):
    """secret-shared-db's network-config.json, assembled from the public parts of the bundles (what
    `pki` writes, without anyone having seen another node's secret)."""
    n = d['db_count']
    dbs = [bundles[f'{C.DB_PREFIX}{i}']['db'] for i in range(n)]
    addr = [C.wg_address(f'{C.DB_PREFIX}{i}') for i in range(n)]
    ports = DB_PORTS
    return {
        'threshold': d['database']['threshold'],
        'max_malicious_parties': d['database']['max_malicious'],
        'public_keys': [x['public_key'] for x in dbs],
        'signing_public_keys': [x['signing_public_key'] for x in dbs],
        'database_url': 'postgresql://not-used-see-each-node-config',
        'peer_addresses': [f'{a}:{ports["peer"]}' for a in addr],
        'tarpc_addresses': [f'{a}:{ports["sync"]}' for a in addr],
        'relay_addresses': [f'{a}:{ports["relay"]}' for a in addr],
        'relay_node_address': f'10.77.0.9:{ports["relay"]}',
        'monitor_public_key': dbs[0]['monitor_public_key'],
        'signup_public_key': d['app']['signup_public_key'],
        'compute_addresses': [f'{a}:{ports["compute"]}' for a in addr],
        'compute_public_keys': [bundles[m]['mpc']['db_client_public_key'] for m in C.MPC_NODES],
        'notify_public_key': d['app']['notify_public_key'],
        'epoch_duration_secs': d['database']['epoch_seconds'],
    }


DB_PORTS = {'peer': 8000, 'sync': 10001, 'relay': 9001, 'compute': 11001}
