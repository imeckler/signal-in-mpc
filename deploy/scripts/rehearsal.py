#!/usr/bin/env python3
"""Local two-node rehearsal: both computation nodes in containers (deploy/compose/rehearsal.yml),
the LOCAL Signal-Server and five LOCAL database nodes on this machine. One signup, one send.

    rehearsal.py [--mode malicious|semi-honest] [--image TAG] [--work DIR] [--circuits DIR]
                 [--word-dir DIR] [--keep] --yes

Run it alone, under the heavy-job lock (it shares local_signal_server/'s ports and state with
harness runs):

    python3 scripts/guarded.py --heavy 24 2400 python3 deploy/scripts/rehearsal.py --yes

Steps (each reuses local_signal_server/check_signal_service_local.py's own pieces):
  1. the local server (scripts/start_server.sh), provisioning, the export (TEST accounts, fictional numbers);
  2. five REAL database nodes (scripts/start_db_nodes.py via the harness's Cluster) and the
     application's keys; signup tokens for the export's contacts and the account's row;
  3. TEST fixture, as the harness's --app stage: the account's row on the database nodes, by one
     two-party session run natively on this machine from the export's credentials in two shares;
  4. per-node directories under WORK: configuration (container paths), the shared peer key, each
     node's database client key, each worker's own certificate made by bench_certs.sh (only
     certificates cross), the export/tokens/network/CA (scaffolding) in WORK/shared;
  5. `docker compose up -d`; both daemons answer `status`;
  6. signup: the application's token for a new id, a new local user sends it, both daemons report the id;
  7. send: notify([new id], a 200-byte text); both daemons agree "delivered"; the new user
     decrypts it from an envelope without source fields;
  8. `docker compose down`, database nodes and server stopped (unless --keep). WORK/report.json.

Nothing here talks to a Signal host: every address is 127.0.0.1 or the containers' private
network. Without --yes it prints the plan.
"""
import argparse
import json
import os
import secrets
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import deploylib as dl  # noqa: E402

ROOT = dl.ROOT
HARNESS_DIR = ROOT / 'local_signal_server'
COMPOSE = ROOT / 'deploy/compose/rehearsal.yml'
BENCH_CERTS = ROOT / 'deployment/vm_pair_test/bench_certs.sh'
NODE_IP = ['172.29.0.10', '172.29.0.11']
APP = ['127.0.0.1:19700', '127.0.0.1:19701']
TEXT = ('Deployment rehearsal: one message to a contact who signed up a moment ago. ' + 'x' * 200)[:200]


def plan(a):
    print(__doc__)
    print(f'mode {a.mode}, image {a.image}, work {a.work}, circuits {a.circuits}, word dir {a.word_dir}')
    print('(plan only: add --yes)')
    return 0


def node_config(party, cluster_dir, mode_env):
    other = 1 - party
    return dict(
        party=party, listen=f'{NODE_IP[party]}:{19700 + party}', peer_listen=f'{NODE_IP[party]}:19710', peer=f'{NODE_IP[other]}:19710',
        peer_key_file='/srv/tls-mpc/secrets/peer.key', state_directory='/srv/tls-mpc/state/daemon',
        controller='/opt/tls-mpc/bin/public_service_controller',
        worker=dict(binary='/opt/tls-mpc/bin/node-worker', send_directory='/srv/tls-mpc/state/worker-send',
                    receive_directory='/srv/tls-mpc/state/worker-receive', hosts=NODE_IP, port_base=23000),
        circuits=dict(tool='/opt/tls-mpc/share/circuit_cache.py', manifest='/srv/tls-mpc/circuits/manifest.txt'),
        signal=dict(endpoint='127.0.0.1', port=18443, hostname='server.example', trust_root='/srv/tls-mpc/shared/ca.pem',
                    certificate_checker='/opt/tls-mpc/bin/public_auth'),
        database=dict(client='/opt/tls-mpc/bin/handoff_client', network='/srv/tls-mpc/shared/network.json',
                      key='/srv/tls-mpc/secrets/db-key.json'),
        test=dict(export='/srv/tls-mpc/shared/mpc-export.json', tokens='/srv/tls-mpc/shared/tokens', kem_tool='/opt/tls-mpc/bin/lss-provision'),
        environment=dict(TLS_WORKER_FIELD_BATCH='3000', TLS_WORKER_PEER=NODE_IP[other], **({'TLS_WORKER_LISTEN': NODE_IP[0]} if party == 0 else {}),
                         **mode_env),
        timeouts=dict(send_seconds=360, send_seconds_per_id=30))


def certificates(work, log):
    """Each party's key made in its own directory; only the .pem crosses (bench_certs.sh)."""
    for party, node in ((0, 'node-a'), (1, 'node-b')):
        base = work / node / 'state' / 'worker-send'
        status, tail = dl.run_logged(['sh', BENCH_CERTS, 'init', str(party), base], log, 60)
        if status:
            raise RuntimeError('bench_certs init failed: ' + ' | '.join(tail[-3:]))
    for party, node in ((0, 'node-a'), (1, 'node-b')):
        other = work / ('node-b' if party == 0 else 'node-a') / 'state' / 'worker-send' / 'Player-Data' / f'P{1 - party}.pem'
        status, tail = dl.run_logged(['sh', BENCH_CERTS, 'trust', other, work / node / 'state' / 'worker-send'], log, 60)
        if status:
            raise RuntimeError('bench_certs trust failed: ' + ' | '.join(tail[-3:]))
        shutil.copytree(work / node / 'state' / 'worker-send', work / node / 'state' / 'worker-receive', symlinks=True)


def wait_status(seconds=300):
    deadline = time.time() + seconds
    replies = [None, None]
    while time.time() < deadline:
        for i, address in enumerate(APP):
            try:
                replies[i] = dl.daemon_call(address, {'op': 'status'}, timeout=5)
            except OSError:
                replies[i] = None
        if all(r and r.get('ok') for r in replies):
            return replies
        time.sleep(3)
    raise RuntimeError(f'the daemons did not answer status within {seconds} s: {replies}')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--mode', default='malicious', choices=['malicious', 'semi-honest'])
    p.add_argument('--image', help='default tls-mpc-node:MODE')
    p.add_argument('--work', default=str(ROOT / '.deps/deploy-rehearsal'))
    p.add_argument('--circuits', default=str(HARNESS_DIR / 'state/circuits'), help='a strict circuit set (manifest.txt) for the local deployment')
    p.add_argument('--word-dir', default=str(ROOT / '.deps/emp-hybrid-word-v1'))
    p.add_argument('--keep', action='store_true', help='leave containers, database nodes and server running')
    p.add_argument('--yes', action='store_true')
    a = p.parse_args()
    a.image = a.image or f'tls-mpc-node:{a.mode}'
    if not a.yes:
        return plan(a)
    work = Path(a.work).resolve()
    if work.exists():
        shutil.rmtree(work)
    for node in ('node-a', 'node-b'):
        for sub in ('config', 'secrets', 'state'):
            (work / node / sub).mkdir(parents=True)
        os.chmod(work / node / 'secrets', 0o700)
        os.chmod(work / node / 'state', 0o700)
    (work / 'shared').mkdir()
    log = work / 'rehearsal.log'
    report = dict(started=time.time(), mode=a.mode, image=a.image, passed=False, steps={})
    docker = dl.docker_binary()
    sys.path.insert(0, str(HARNESS_DIR))
    import check_signal_service_local as harness
    manifest = Path(a.circuits) / 'manifest.txt'
    os.environ['CIRCUIT_MANIFEST'] = str(manifest)            # the fixture session runs strict too
    os.environ.setdefault('SIGNAL_WORKER', 'node')
    harness.Cluster.REAL = True
    cluster, compose_up = None, False
    compose = [docker, 'compose', '-f', str(COMPOSE), '--env-file', str(work / 'rehearsal.env')]

    def step(name, **detail):
        report['steps'][name] = dict(at=round(time.time() - report['started'], 1), **detail)
        print(f'[{report["steps"][name]["at"]:7.1f} s] {name} ' + json.dumps(detail)[:300], flush=True)

    try:
        if not manifest.exists():
            raise RuntimeError(f'{manifest} missing: produce the local strict set first (check_signal_service_local.py --strict)')
        digest, rows = dl.read_manifest(manifest)
        problems, words = dl.word_dir_summary(a.word_dir)
        if problems:
            raise RuntimeError('word dir: ' + '; '.join(problems[:4]))
        probe = subprocess.run([docker, 'image', 'inspect', a.image, '--format', '{{.Id}}'], capture_output=True, text=True, timeout=30)
        if probe.returncode:
            raise RuntimeError(f'image {a.image} not built (build_artifacts.py image)')
        step('inputs', manifest=digest, kernels=len(rows), word_dir=words['word_dir_sha256'], image=probe.stdout.strip())
        # 1. Server, accounts, export.
        if not (HARNESS_DIR / 'state/classpath.txt').exists():
            harness.run(['bash', HARNESS_DIR / 'scripts/build_server.sh'])
        harness.run(['bash', HARNESS_DIR / 'scripts/start_server.sh'])
        harness.lss('provision')
        harness.lss('export-mpc')
        export = json.loads(harness.EXPORT.read_text())
        step('local server and export')
        # 2. Database nodes, tokens.
        cluster = harness.Cluster()
        ids = [int(c['contact_id_u128_hex'], 16) for c in export['contacts']]
        for contact in ids + [harness.ACCOUNT]:
            cluster.token(contact)
        step('database nodes', network=str(cluster.network))
        # 3. TEST fixture: the account's row (as AppNodes does).
        credentials = bytes.fromhex(export['sender']['upgrade_credentials_hex'])
        share = secrets.token_bytes(len(credentials))
        shares = [share.hex(), bytes(x ^ y for x, y in zip(credentials, share)).hex()]
        tool = HARNESS_DIR / 'provision/target/debug/lss-provision'
        fixture = harness.run_mpc(export, a.mode, {}, party_env=lambda party: dict(
            cluster.env(party), SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT='0', SIGNAL_LOCAL_KEM=str(tool)))
        cluster.refresh()
        step('account row (native fixture session)', seconds=round(fixture['elapsed_seconds'], 1))
        # 4. Node directories.
        shutil.copy2(harness.EXPORT, work / 'shared/mpc-export.json')
        shutil.copytree(cluster.dir / 'tokens', work / 'shared/tokens')
        shutil.copy2(cluster.network, work / 'shared/network.json')
        shutil.copy2(harness.STATE / 'tls/ca.pem', work / 'shared/ca.pem')
        key = secrets.token_hex(32)
        mode_env = {'SIGNAL_WORKER': 'node'}
        for party, node in ((0, 'node-a'), (1, 'node-b')):
            (work / node / 'secrets/peer.key').write_text(key + '\n')
            shutil.copy2(cluster.config / f'compute-nodes/{party}/key.json', work / node / 'secrets/db-key.json')
            for f in ('peer.key', 'db-key.json'):
                os.chmod(work / node / 'secrets' / f, 0o600)
            (work / node / 'config/node.json').write_text(json.dumps(node_config(party, cluster.dir, mode_env), indent=1) + '\n')
            (work / node / 'state/daemon').mkdir()
        certificates(work, log)
        (work / 'rehearsal.env').write_text(
            f'IMAGE={a.image}\nREHEARSAL_DIR={work}\nCIRCUITS_DIR={Path(a.circuits).resolve()}\nWORD_DIR={Path(a.word_dir).resolve()}\n'
            f'EXPECTED_MANIFEST_SHA256={digest}\nEXPECTED_WORD_DIR_SHA256={words["word_dir_sha256"]}\n')
        step('node directories', work=str(work))
        # 5. Containers.
        status, tail = dl.run_logged(compose + ['up', '-d'], log, 180)
        compose_up = True
        if status:
            raise RuntimeError('docker compose up failed: ' + ' | '.join(tail[-4:]))
        replies = wait_status()
        step('daemons up', status=replies)
        # 6. Signup.
        app_cmd = lambda command, *args: [str(ROOT / 'node_daemon/target/debug/notify-app'), command, *map(str, args), '--daemons', ','.join(APP),
                                          '--db-client', str(cluster.BIN / 'handoff_client'), '--work', str(work / 'application'),
                                          '--key', str(cluster.config / 'app-server/notify-key.json'),
                                          '--app-config', str(cluster.config / 'app-server/config.json'), '--network', str(cluster.network)]

        def app(command, *args, timeout=900):
            r = subprocess.run(app_cmd(command, *args), capture_output=True, text=True, timeout=timeout)
            lines = r.stdout.strip().splitlines()
            return r.returncode == 0, (json.loads(lines[-1]) if lines else {})

        new = secrets.randbits(100)
        good, issued = app('token', '--id', new)
        if not good:
            raise RuntimeError('notify-app token failed')
        harness.lss('signup', 'newuser', '+12025550104', 'sender', issued.get('token', ''))
        good, events = app('events', '--wait', 300, '--until-id', new)
        signed_up = good and events.get('signups') == [str(new)] and bool(events.get('agreed'))
        step('signup', passed=signed_up)
        if not signed_up:
            raise RuntimeError(f'signup not reported by both daemons: {events}')
        cluster.refresh()
        # 7. Send.
        (work / 'message.txt').write_text(TEXT)
        good, result = app('notify', '--ids', new, '--message-file', work / 'message.txt', '--timeout', 420)
        rows = (result.get('result') or {}).get('results') or []
        seen = harness.receive('newuser', 6)
        attributed = [g for g in seen if g['envelope'].get('source_service_id') or g['envelope'].get('source_device')]
        delivered = good and bool(result.get('agreed')) and [r.get('result') for r in rows] == ['delivered']
        decrypted = TEXT in [g['text'] for g in seen] and not attributed
        step('send', delivered=delivered, decrypted_sealed=decrypted)
        report['passed'] = bool(signed_up and delivered and decrypted)
    except Exception as e:  # noqa: BLE001
        report['error'] = f'{type(e).__name__}: {e}'
        print('error:', report['error'], flush=True)
    finally:
        if compose_up and docker:
            dl.run_logged(compose + ['logs', '--no-color'], work / 'compose-logs.txt', 120)
            if not a.keep:
                dl.run_logged(compose + ['down'], log, 180)
        if cluster and not a.keep:
            cluster.stop()
        if not a.keep:
            subprocess.run(['bash', str(HARNESS_DIR / 'scripts/stop_server.sh')], capture_output=True)
        report['seconds'] = round(time.time() - report['started'], 1)
        (work / 'report.json').write_text(json.dumps(report, indent=1, default=str) + '\n')
        print(f'rehearsal {"PASSED" if report["passed"] else "FAILED"}; {work / "report.json"}', flush=True)
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    sys.exit(main())
