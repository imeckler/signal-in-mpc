"""The `local` provider: containers on this computer standing in for ssh-reachable machines.

Each machine is a privileged container running systemd and sshd (deploy/providers/local/
machine.Dockerfile) on a private Docker network that plays the internet. From then on it is
treated exactly like a machine of the `existing` provider: Ansible reaches it over ssh and
installs Docker, WireGuard, the firewall and the services itself. Its "provider disk" is a Docker
volume mounted at /srv/data, kept by `destroy` unless --delete-data. TEST ONLY.
"""
import ipaddress
import json

from . import config as C
from .providers import LOCAL_SUBNET
from .tools import DEPLOY, MACHINE_IMAGE, ToolError, docker, ensure_image, run

NET = ipaddress.ip_network(LOCAL_SUBNET)


def network_name(name):
    return f'pb-{name}'


def container(name, node):
    return f'pb-{name}-{node}'


def ip(node):
    base = int(NET.network_address)
    if node in C.MPC_NODES:
        offset = 10 + C.MPC_NODES.index(node)
    elif node == C.APP:
        offset = 30
    else:
        offset = 20 + C.db_index(node)
    return str(ipaddress.ip_address(base + offset))


def ensure_network(name, log):
    net = network_name(name)
    code, text = run([docker(), 'network', 'inspect', net, '--format', '{{json .IPAM.Config}}'], log, 30)
    if code == 0:
        return net
    code, text = run([docker(), 'network', 'create', '--driver', 'bridge', '--subnet', LOCAL_SUBNET,
                      '--ip-range', str(list(NET.subnets(new_prefix=25))[1]), net], log, 60)
    if code:
        raise ToolError(f'could not create the local network {net} ({LOCAL_SUBNET}): {text.strip()[-200:]}')
    return net


def volumes(name, node):
    base = container(name, node)
    return {'data': f'{base}-data', 'docker': f'{base}-docker', 'containerd': f'{base}-containerd'}


def up(name, node, spec, ssh_pub, log):
    """Create (or start) the machine; return its connection details."""
    ensure_image(MACHINE_IMAGE, DEPLOY / 'providers/local/machine.Dockerfile', log)
    net = ensure_network(name, log)
    box = container(name, node)
    code, text = run([docker(), 'inspect', box, '--format', '{{.State.Running}}'], log, 30)
    if code == 0 and text.strip().endswith('false'):
        run([docker(), 'start', box], log, 60)
    elif code != 0:
        v = volumes(name, node)
        argv = [docker(), 'run', '-d', '--name', box, '--hostname', node, '--privileged', '--cgroupns=private',
                '--tmpfs', '/run', '--tmpfs', '/run/lock', '--network', net, '--ip', ip(node),
                '--memory', f'{spec.get("memory_gb", 4) + 2}g',
                '-v', f'{v["data"]}:/srv/data', '-v', f'{v["docker"]}:/var/lib/docker', '-v', f'{v["containerd"]}:/var/lib/containerd',
                '-v', f'{ssh_pub}:/etc/pb-authorized_key:ro', '-p', '127.0.0.1::22',
                '--label', 'tls-mpc-deploy=local-machine', MACHINE_IMAGE]
        code, text = run(argv, log, 120)
        if code:
            raise ToolError(f'could not start the local machine {box}: {text.strip()[-300:]}')
    code, text = run([docker(), 'port', box, '22/tcp'], log, 30)
    tunnel_port = int(text.strip().splitlines()[0].rsplit(':', 1)[1]) if code == 0 and text.strip() else None
    return dict(provider='local', ssh_host=ip(node), ssh_port=22, ssh_user='root', ssh_key=None, endpoint=ip(node),
                data_device='', data_path='/srv/data', requirements='relaxed', tunnel_host='127.0.0.1', tunnel_port=tunnel_port,
                container=box)


def down(name, node, delete_data, log):
    box = container(name, node)
    run([docker(), 'rm', '-f', box], log, 120)
    v = volumes(name, node)
    gone = [v['docker'], v['containerd']] + ([v['data']] if delete_data else [])
    run([docker(), 'volume', 'rm', '-f', *gone], log, 120)
    return gone


def remove_network_if_unused(name, log):
    code, text = run([docker(), 'network', 'inspect', network_name(name), '--format', '{{json .Containers}}'], log, 30)
    if code == 0 and text.strip() in ('{}', 'null'):
        run([docker(), 'network', 'rm', network_name(name)], log, 60)


def host_gateway_address(name, log):
    """The address the machines (and the containers inside them) reach this computer by:
    where the local test Signal server listens."""
    code, text = run([docker(), 'run', '--rm', '--network', network_name(name), '--entrypoint', 'getent', MACHINE_IMAGE,
                      'hosts', 'host.docker.internal'], log, 60)
    if code or not text.split():
        raise ToolError('cannot resolve host.docker.internal from the local machines (Docker Desktop and OrbStack provide it)')
    return text.split()[0]


def exists(name, node, log):
    code, _ = run([docker(), 'inspect', container(name, node), '--format', '{{.Id}}'], log, 30)
    return code == 0


def describe(name, log):
    code, text = run([docker(), 'ps', '-a', '--filter', f'name=pb-{name}-', '--format', '{{json .}}'], log, 30)
    return [json.loads(line) for line in text.splitlines() if line.startswith('{')] if code == 0 else []
