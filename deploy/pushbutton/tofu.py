"""OpenTofu for the cloud providers: two stacks per operator under the state directory.

  disks/     one data disk per node (kept by `destroy`; removed only with --delete-data)
  machines/  machines, firewalls, ssh keys, disk attachments

The stacks are rendered as JSON (main.tf.json) from the provider table; every module comes from
deploy/providers/NAME/{disk,machine}. tofu state can contain secrets (provider tokens are not
stored, but resource attributes may be): the directories are mode 700 and the state files 600.
"""
import json
import os
from pathlib import Path

from . import config as C
from . import providers as P
from .tools import ToolError, tofu


def _required(used):
    return {name: {'source': P.PROVIDERS[name].tofu['source'], 'version': P.PROVIDERS[name].tofu['version']} for name in sorted(used)}


def _provider_blocks(used):
    blocks = {}
    if 'hetzner' in used:
        blocks['hcloud'] = {}
    if 'upcloud' in used:
        blocks['upcloud'] = {}
    if 'ovh' in used:
        blocks['openstack'] = {'user_domain_name': 'Default', 'project_domain_name': 'Default'}
    return blocks


def _module_provider_name(provider):
    return {'hetzner': 'hcloud', 'upcloud': 'upcloud', 'ovh': 'openstack'}[provider]


def render(state, d, o, nodes, ssh_public_key, admin_cidrs, monitoring_cidrs, disk_outputs=None):
    cloud = {n: o['nodes'][n] for n in nodes if o['nodes'][n]['provider'] in P.CLOUD}
    if not cloud:
        return None
    used = {s['provider'] for s in cloud.values()}
    required = {_module_provider_name(p): {'source': P.PROVIDERS[p].tofu['source'], 'version': P.PROVIDERS[p].tofu['version']} for p in used}
    out = {}
    for stack in ('disks', 'machines'):
        doc = {'terraform': {'required_providers': required}, 'provider': _provider_blocks(used), 'module': {}, 'output': {}}
        for node, spec in sorted(cloud.items()):
            prefix = f'tls-mpc-{d["name"]}-{node}'
            source = f'/deploy/providers/{spec["provider"]}/{"disk" if stack == "disks" else "machine"}'
            if stack == 'disks':
                doc['module'][node] = {'source': source, 'name': f'{prefix}-data', 'region': spec['region'], 'size_gb': spec['data_disk_gb']}
            else:
                disk = (disk_outputs or {}).get(node) or {'disk_id': 'PENDING', 'device': ''}
                doc['module'][node] = {'source': source, 'name': prefix, 'region': spec['region'], 'size': spec['size'],
                                       'ssh_public_key': ssh_public_key, 'admin_cidrs': admin_cidrs,
                                       'monitoring_cidrs': monitoring_cidrs, 'disk_id': disk['disk_id'], 'device': disk.get('device', '')}
            doc['output'][node] = {'value': f'${{module.{node}}}'}
        directory = state / 'tofu' / stack
        directory.mkdir(parents=True, exist_ok=True)
        os.chmod(directory, 0o700)
        (directory / 'main.tf.json').write_text(json.dumps(doc, indent=1, sort_keys=True) + '\n')
        out[stack] = directory
    return out


def env_names(o, nodes):
    names = []
    for provider in sorted({o['nodes'][n]['provider'] for n in nodes} & set(P.CLOUD)):
        for key, value in o['credentials'].get(provider, {}).items():
            name = P.PROVIDERS[provider].env[key]
            os.environ[name] = C.resolve_secret(value)
            names.append(name)
    return names


def _protect(directory):
    for f in Path(directory).glob('*.tfstate*'):
        os.chmod(f, 0o600)


def init(directory, log, names):
    code, text = tofu(directory, ['init', '-input=false', '-no-color'], log, names, timeout=900)
    if code:
        raise ToolError(f'tofu init failed in {directory} (log {log}): ' + text.strip().splitlines()[-1][:300] if text.strip() else '')


def apply(directory, log, names):
    init(directory, log, names)
    code, text = tofu(directory, ['apply', '-auto-approve', '-input=false', '-no-color'], log, names, timeout=3600)
    _protect(directory)
    if code:
        raise ToolError(f'tofu apply failed in {directory}; see {log}: ' + ' | '.join(l for l in text.splitlines() if 'Error' in l)[:400])
    code, text = tofu(directory, ['output', '-json', '-no-color'], log, names, timeout=300)
    if code:
        raise ToolError(f'tofu output failed in {directory}; see {log}')
    return {k: v['value'] for k, v in json.loads(text[text.index('{'):]).items()}


def plan(directory, log, names):
    init(directory, log, names)
    return tofu(directory, ['plan', '-input=false', '-no-color'], log, names, timeout=900)


def destroy(directory, log, names):
    if not (directory / 'main.tf.json').exists():
        return
    init(directory, log, names)
    code, text = tofu(directory, ['destroy', '-auto-approve', '-input=false', '-no-color'], log, names, timeout=3600)
    _protect(directory)
    if code:
        raise ToolError(f'tofu destroy failed in {directory}; see {log}')
