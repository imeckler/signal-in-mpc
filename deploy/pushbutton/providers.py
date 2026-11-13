"""The provider table. Adding a provider = one directory deploy/providers/NAME/ (an OpenTofu module
pair `disk/` and `machine/` with the interface below) + one entry in PROVIDERS.

OpenTofu module interface (every cloud provider):
  disk/     inputs  name, region, size_gb
            outputs disk_id, device            (the disk survives `destroy` unless --delete-data)
  machine/  inputs  name, region, size, ssh_public_key, admin_cidrs, monitoring_cidrs, disk_id, device
            outputs public_ip, device, ssh_user

Two providers are not OpenTofu modules:
  existing  a machine you created by any means, reachable over ssh: the BASELINE path; every other
            provider ends by handing the same thing (an ssh address and a data disk) to it.
  local     containers on this computer that stand in for ssh-reachable machines (tests only).

Prices are monthly, in euros without VAT, from deployment/PROVIDERS_CHEAP.md (fetched
2026-11-11); None = not known (check the provider's page).
"""
import re
from pathlib import Path

LOCAL_SUBNET = '172.30.77.0/24'


class Provider:
    name = ''
    credentials = []          # keys of [credentials.NAME] in operator.toml
    tofu = None               # {'source': ..., 'version': ...} of the OpenTofu provider plugin
    env = {}                  # credentials key -> environment variable the plugin reads
    sizes = {}                # role -> default size
    regions = []
    prices = {}               # size -> EUR/month
    disk_price_per_gb = None
    default_disk_gb = {'mpc': 200, 'db': 40, 'app': 20}
    keys = {'provider', 'region', 'size', 'data_disk_gb'}

    def validate(self, node, role, spec, where, base):
        for key in spec:
            if key not in self.keys:
                raise _err(f'{where}: unknown setting "{key}" for provider {self.name} (allowed: {", ".join(sorted(self.keys))})')
        region = spec.get('region', self.regions[0] if self.regions else '')
        if self.regions and region not in self.regions:
            raise _err(f'{where}: region {region!r} is not one this tool knows for {self.name} ({", ".join(self.regions)}); '
                       'add it to deploy/pushbutton/providers.py if the provider has it')
        size = spec.get('size', self.sizes.get(role, ''))
        if not isinstance(size, str) or not size:
            raise _err(f'{where}: size is missing (the provider\'s machine type, e.g. {self.sizes.get(role)})')
        disk = spec.get('data_disk_gb', self.default_disk_gb[role])
        if not isinstance(disk, int) or not 10 <= disk <= 10000:
            raise _err(f'{where}: data_disk_gb must be a whole number of GB from 10 to 10000')
        warnings = []
        if role == 'mpc' and disk < 60:
            warnings.append(f'data_disk_gb {disk} is small for a computation node (the production circuit set alone is 31 GB)')
        return dict(provider=self.name, region=region, size=size, data_disk_gb=disk, warnings=warnings)

    def monthly(self, spec):
        machine = self.prices.get(spec['size'])
        disk = None if self.disk_price_per_gb is None else self.disk_price_per_gb * spec['data_disk_gb']
        return machine, disk


def _err(text):
    from .config import ConfigError
    return ConfigError(text)


class Hetzner(Provider):
    name = 'hetzner'
    credentials = ['token']
    env = {'token': 'HCLOUD_TOKEN'}
    tofu = {'source': 'hetznercloud/hcloud', 'version': '1.70.2'}
    # Cloud servers only. A dedicated server (e.g. the AX102 the research recommends) is ordered in
    # Hetzner's Robot and then deployed with provider = "existing".
    sizes = {'mpc': 'ccx43', 'db': 'cx43', 'app': 'cx22'}
    regions = ['hel1', 'fsn1', 'nbg1', 'ash', 'hil', 'sin']
    prices = {'cx43': 16.49, 'cpx42': 59.49}
    disk_price_per_gb = None


class UpCloud(Provider):
    name = 'upcloud'
    credentials = ['username', 'password']
    env = {'username': 'UPCLOUD_USERNAME', 'password': 'UPCLOUD_PASSWORD'}
    tofu = {'source': 'UpCloudLtd/upcloud', 'version': '5.49.1'}
    sizes = {'mpc': '16xCPU-64GB', 'db': '4xCPU-8GB', 'app': '1xCPU-2GB'}
    regions = ['fi-hel1', 'fi-hel2', 'de-fra1', 'nl-ams1', 'se-sto1', 'dk-cph1', 'pl-waw1', 'es-mad1', 'uk-lon1']


class OVH(Provider):
    """OVHcloud Public Cloud through its OpenStack API (the openrc file of a Public Cloud project:
    OS_AUTH_URL, OS_USERNAME, OS_PASSWORD, OS_PROJECT_ID / tenant, region). OVH VPS and dedicated
    servers (VPS-6, Advance-3 in the research) are ordered in OVH's control panel and deployed with
    provider = "existing"."""
    name = 'ovh'
    credentials = ['auth_url', 'username', 'password', 'project_id']
    env = {'auth_url': 'OS_AUTH_URL', 'username': 'OS_USERNAME', 'password': 'OS_PASSWORD', 'project_id': 'OS_PROJECT_ID'}
    tofu = {'source': 'terraform-provider-openstack/openstack', 'version': '3.4.0'}
    sizes = {'mpc': 'b3-64', 'db': 'b3-16', 'app': 'd2-4'}
    regions = ['SBG5', 'GRA11', 'GRA9', 'DE1', 'UK1', 'WAW1', 'BHS5']


class Existing(Provider):
    """A machine you already have. The baseline path: every other provider hands over the same thing."""
    name = 'existing'
    keys = {'provider', 'ssh', 'ssh_port', 'ssh_key', 'data_device', 'data_path', 'endpoint'}

    def validate(self, node, role, spec, where, base):
        from .config import _path
        for key in spec:
            if key not in self.keys:
                raise _err(f'{where}: unknown setting "{key}" for provider existing (allowed: {", ".join(sorted(self.keys))})')
        ssh = spec.get('ssh', '')
        m = re.fullmatch(r'([a-z_][a-z0-9_-]{0,31})@([A-Za-z0-9.:-]+)', ssh or '')
        if not m:
            raise _err(f'{where}: ssh must be "user@address" of the machine (for example "root@203.0.113.10"), got {ssh!r}')
        port = spec.get('ssh_port', 22)
        if not isinstance(port, int) or not 1 <= port <= 65535:
            raise _err(f'{where}: ssh_port must be a port number')
        key = spec.get('ssh_key')
        key = _path(key, base) if key else None
        device, path = spec.get('data_device', ''), spec.get('data_path', '')
        if bool(device) == bool(path):
            raise _err(f'{where}: give exactly one of data_device (a whole disk for the data, e.g. "/dev/sdb": formatted if blank, never if not) '
                       'or data_path (a directory on an existing file system, e.g. "/srv/data")')
        if device and not re.fullmatch(r'/dev/[A-Za-z0-9/_.:-]+', device):
            raise _err(f'{where}: data_device must be a /dev/... path')
        if path and not path.startswith('/'):
            raise _err(f'{where}: data_path must be an absolute path')
        warnings = []
        if path:
            warnings.append('data_path: the data lives wherever that directory is; if it is on the boot disk, replacing the machine loses it')
        return dict(provider='existing', user=m.group(1), host=m.group(2), port=port, ssh_key=key, data_device=device,
                    data_path=path or '/srv/data', endpoint=spec.get('endpoint', m.group(2)), warnings=warnings,
                    size='(yours)', region='(yours)', data_disk_gb=0)


class Local(Provider):
    """Containers on this computer standing in for ssh-reachable machines. TEST ONLY."""
    name = 'local'
    keys = {'provider', 'memory_gb'}

    def validate(self, node, role, spec, where, base):
        for key in spec:
            if key not in self.keys:
                raise _err(f'{where}: unknown setting "{key}" for provider local (allowed: {", ".join(sorted(self.keys))})')
        return dict(provider='local', memory_gb=int(spec.get('memory_gb', 12 if role == 'mpc' else 2)), size='container',
                    region='this computer', data_disk_gb=0, warnings=[])


PROVIDERS = {p.name: p for p in (Hetzner(), UpCloud(), OVH(), Existing(), Local())}
CLOUD = [name for name, p in PROVIDERS.items() if p.tofu]
MODULES = Path(__file__).resolve().parents[1] / 'providers'
