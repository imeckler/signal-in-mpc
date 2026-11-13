"""Running Docker, OpenTofu and Ansible: always with a timeout, output to a log file, a short
summary on the terminal. OpenTofu and Ansible run from pinned container images, so the only
prerequisites are Docker, Python 3.11+ and ssh."""
import json
import os
import shutil
import subprocess
import time
from pathlib import Path

DEPLOY = Path(__file__).resolve().parents[1]
ROOT = DEPLOY.parent
TOFU_IMAGE = 'ghcr.io/opentofu/opentofu:1.10.6'
ANSIBLE_IMAGE = 'tls-mpc-deploy-ansible:1'          # built from deploy/tools/ansible.Dockerfile (pinned versions)
MACHINE_IMAGE = 'tls-mpc-deploy-machine:1'          # the local provider's stand-in machine


class ToolError(Exception):
    pass


def docker():
    path = shutil.which('docker')
    if not path:
        raise ToolError('Docker is not installed (it is the one prerequisite besides Python 3 and ssh)')
    return path


def run(argv, log, timeout, env=None, input_text=None, quiet=False):
    """Run argv; append everything to `log`; return (returncode, output). A timeout returns 124
    and leaves whatever was started alone (never restarts Docker)."""
    log = Path(log)
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.time()
    with log.open('a') as out:
        out.write(f'\n===== {time.strftime("%Y-%m-%d %H:%M:%S")} {" ".join(map(str, argv))[:2000]}\n')
        out.flush()
        try:
            r = subprocess.run([str(a) for a in argv], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                               timeout=timeout, env=env, input=input_text)
            code, text = r.returncode, r.stdout
        except subprocess.TimeoutExpired as e:
            code = 124
            text = (e.stdout.decode(errors='replace') if isinstance(e.stdout, bytes) else (e.stdout or '')) + \
                f'\n(timed out after {timeout} s; nothing was killed or restarted beyond this command)'
        out.write(text)
        out.write(f'\n===== exit {code} after {time.time() - started:.0f} s\n')
    return code, text


def docker_ok(log):
    code, text = run([docker(), 'version', '--format', '{{.Server.Version}}'], log, 30)
    if code:
        raise ToolError('Docker is not answering (start Docker Desktop / OrbStack; this tool never restarts it): ' + text.strip()[-200:])


def image_exists(name, log):
    code, _ = run([docker(), 'image', 'inspect', name, '--format', '{{.Id}}'], log, 30)
    return code == 0


def ensure_image(name, dockerfile, log, timeout=1800):
    if image_exists(name, log):
        return
    print(f'  building the tool image {name} (once) ...', flush=True)
    code, text = run([docker(), 'build', '-f', dockerfile, '-t', name, Path(dockerfile).parent], log, timeout)
    if code:
        raise ToolError(f'building {name} failed; see {log}')


def ansible(state, playbook, inventory, extra_vars, log, timeout=7200, network=None, mounts=(), limit=None, check=False, tags=None):
    """ansible-playbook PLAYBOOK from the tool image. `state` is mounted at /state, deploy/ at
    /deploy (read-only); `mounts` adds (host_path, container_path) read-only."""
    ensure_image(ANSIBLE_IMAGE, DEPLOY / 'tools/ansible.Dockerfile', log)
    (state / 'vars').mkdir(exist_ok=True)
    vars_file = state / 'vars' / f'{Path(playbook).stem}.json'
    vars_file.write_text(json.dumps(extra_vars, indent=1, sort_keys=True))
    os.chmod(vars_file, 0o600)
    argv = [docker(), 'run', '--rm', '-v', f'{DEPLOY}:/deploy:ro', '-v', f'{state}:/state',
            '-v', f'{ROOT / "deployment/vm_pair_test/bench_certs.sh"}:/extra/bench_certs.sh:ro']
    for host, inside in mounts:
        argv += ['-v', f'{host}:{inside}:ro']
    if network:
        argv += ['--network', network]
    argv += ['-e', 'ANSIBLE_CONFIG=/deploy/ansible/ansible.cfg', ANSIBLE_IMAGE, 'ansible-playbook', '-i', f'/state/{inventory}',
             f'/deploy/ansible/{playbook}', '-e', f'@/state/vars/{vars_file.name}']
    if limit:
        argv += ['--limit', limit]
    if tags:
        argv += ['--tags', tags]
    if check:
        argv += ['--syntax-check']
    code, text = run(argv, log, timeout)
    return code, summarize_ansible(text)


def summarize_ansible(text):
    """The failed tasks' messages and the recap, not the whole output."""
    lines = text.splitlines()
    keep = []
    for i, line in enumerate(lines):
        if line.startswith(('fatal:', 'failed:')) or 'FAILED!' in line or line.startswith('ERROR!'):
            task = next((lines[j] for j in range(i, -1, -1) if lines[j].startswith('TASK [')), '')
            keep.append(task.strip('* '))
            keep.append('  ' + _short_failure(line))
    recap = False
    for line in lines:
        if line.startswith('PLAY RECAP'):
            recap = True
        if recap and line.strip():
            keep.append(line)
    if not keep:
        keep = lines[-15:]
    return keep


def _short_failure(line):
    for marker in ('"msg": "', "'msg': '"):
        if marker in line:
            return line.split(marker, 1)[1][:400]
    return line[:400]


def tofu(stack, args, log, env_names=(), timeout=3600, deploy_mount=True):
    """tofu ARGS in the stack directory, from the pinned OpenTofu image. Credentials pass as
    environment variable NAMES (docker run -e NAME), never on the command line."""
    cache = stack.parent / 'plugin-cache'
    cache.mkdir(parents=True, exist_ok=True)
    argv = [docker(), 'run', '--rm', '-v', f'{stack}:/stack', '-v', f'{cache}:/plugin-cache', '-w', '/stack',
            '-e', 'TF_PLUGIN_CACHE_DIR=/plugin-cache', '-e', 'TF_IN_AUTOMATION=1']
    if deploy_mount:
        argv += ['-v', f'{DEPLOY}:/deploy:ro']
    for name in env_names:
        argv += ['-e', name]
    argv += [TOFU_IMAGE, *args]
    return run(argv, log, timeout)
