#!/usr/bin/env python3
"""The first test against a Signal server, recorded in full (real_signal/REAL_TEST_PLAN.md).

    run_real_test.py local      --export DIR --local-account NAME   the same flow against the LOCAL server
    run_real_test.py production --export DIR --i-have-the-go-ahead  Signal's service (chat.signal.org)
    run_real_test.py production --export DIR --dry-run              everything but the connections
    run_real_test.py TARGET --export DIR --resume RUN_DIR [...]      only step 3, for the contact RUN_DIR stored

DIR is what `lss-provision export-account ACCOUNT_JSON DIR production|local` wrote.

The database nodes (`--db real`, the default since 2026-11-12) are secret-shared-db's REAL node
binary with a private Postgres instance under RUN/db/real (local_signal_server/scripts/
start_db_nodes.py): they are stopped at the end and their data stays, so a send that failed can be
tried again for the contact the run stored, without a new signup: `--resume RUN` starts that
run's nodes again (same ports, same keys), waits one epoch, and runs only the send session, recorded
in a new run directory. `--db memory` uses the harness's in-memory test nodes, as the first real run
did (2026-11-12): their state ends with the process and cannot be resumed. `--stop-after receive`
ends after step 2 (for testing --resume). Steps:

  1. the database nodes start; the application's signup token for a new id is issued and shown
     (production: the owner's phone sends it to the account as a text message);
  2. a RECEIVE session (authenticated socket, each party holding one XOR share of the account's
     credentials): the account's row is created on the database nodes, then the session waits
     for one delivered message: the signup. It is opened in the engines, the contact is created
     under the token's id and stored, and only then acknowledged;
  3. a SEND session (unauthenticated socket, sealed sender): one text to that id, the contact read
     back from the database nodes; resent on an ambiguous outcome (the recovery path);
  4. local only: the new user's client must decrypt it.

Recorded under real_signal/state/runs/STAMP-TARGET/ (git-ignored): plan.json (configuration and
binary hashes, no secrets), timeline.jsonl (this launcher's steps), record-receive-party-N.jsonl
and record-send-party-N.jsonl (SIGNAL_RECORD: every exchange with the server), the parties'
logs and final reports, the kernels asked for and refused, report.json.

Nothing here sends a read or delivery receipt, or any request but those of the two sessions.
"""
import argparse, hashlib, json, os, secrets, shutil, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / 'local_signal_server'))
import check_signal_service_local as harness   # noqa: E402  (Cluster, the in-memory database nodes)

LSS = ROOT / 'local_signal_server/provision/target/debug/lss-provision'
CONTROLLER = ROOT / '.lake/build/bin/public_service_controller'
BASE = ROOT / '.deps/two-party-comparison'
MP = BASE / 'data61-MP-SPDZ-113c4e4'
CACHE = ROOT / 'handshake_backend/EmpHybridWork/circuit_cache.py'
DEFAULT_TEXT = 'Thanks for signing up. This is the first message from the two-party test client; there is nothing to reply.'
# The receive kernels accept a first message that is the sender's number 0..RECEIVE_JUMP of its
# unanswered session (service_kernels.h; the deployments' `signup_jump`): a phone whose earlier
# signup was never answered sends its next one as number 1.
RECEIVE_JUMP = '3'


class Run:
    def __init__(self, target, mode, suffix=''):
        stamp = time.strftime('%Y%m%d-%H%M%S', time.gmtime())
        self.dir = HERE / 'state' / 'runs' / f'{stamp}-{target}{suffix}'
        self.dir.mkdir(parents=True)
        os.chmod(self.dir, 0o700)
        self.target, self.mode = target, mode

    def log(self, step, **detail):
        line = dict(time_ms=int(time.time() * 1000), step=step, **detail)
        with open(self.dir / 'timeline.jsonl', 'a') as f:
            f.write(json.dumps(line) + '\n')
        print(json.dumps(line), flush=True)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest() if Path(path).exists() else None


def git(*args):
    return subprocess.run(['git', '-C', str(ROOT), *args], capture_output=True, text=True).stdout.strip()


def prepare_workers(run):
    """What every session needs locally: the certificate checker and the workers' TLS material."""
    sys.path.insert(0, str(ROOT / 'scripts'))
    from check_full_handshake import OPENSSL
    auth = run.dir / 'public_auth'
    subprocess.run(['c++', '-std=c++20', '-O2', '-I' + str(OPENSSL / 'include'), str(ROOT / 'handshake_backend/public_auth.cpp'),
                    '-L' + str(OPENSSL / 'lib'), '-lssl', '-lcrypto', '-o', str(auth)], check=True)
    work = run.dir / 'work'
    work.mkdir()
    with open(run.dir / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(MP / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    hosts = run.dir / 'hosts'
    hosts.write_text('127.0.0.1\n' * 2)
    return auth, work, hosts


def reopen_cluster(db):
    """The REAL database nodes of an earlier run (RUN/db), started again with their data."""
    cluster = harness.Cluster.__new__(harness.Cluster)
    script = cluster._nodes_script()
    cluster.BIN = script.DEFAULT_BIN
    cluster.dir, cluster.real, cluster.config, cluster.nodes = db, db / 'real', db / 'real/config', []
    started = time.time()
    state = script.restart(cluster.real)
    cluster.network = Path(state['network'])
    cluster.waits = dict(start=round(time.time() - started, 1), epochs=[])
    return cluster


def stored_contact(previous):
    """The contact id an earlier run issued its signup token for, and whether it was stored."""
    steps = [json.loads(line) for line in (previous / 'timeline.jsonl').read_text().splitlines() if line.strip()]
    contact = next((s['id'] for s in steps if s['step'] == 'signup-token'), None)
    ends = [s for s in steps if s['step'] == 'receive-end']
    stored = bool(ends) and all(r and r[0][0] == contact for r in ends[-1].get('received') or [None])
    return contact, stored


def stop(p):
    """End a controller and its worker: the worker is the controller's child and outlives it,
    holding the link ports the next session needs."""
    children = subprocess.run(['pgrep', '-P', str(p.pid)], capture_output=True, text=True).stdout.split()
    p.terminate()
    for pid in children:
        try:
            os.kill(int(pid), 15)
        except OSError:
            pass


def session(run, label, server, export_dir, auth, work, hosts, party_env, common, timeout, during=None):
    """One two-party session; both controllers' outputs kept under the run directory."""
    sh = run.mode == 'semi-honest'
    worker = BASE / ('tls-worker-sh-fixture-v3' if sh else 'tls-worker-fixture-v3')
    port = 22700 if sh else 22600
    session_id = secrets.token_hex(32)
    processes, logs = [], []
    run.log(f'{label}-start', endpoint=server['endpoint'], port=server['port'], hostname=server['hostname'])
    started = time.monotonic()
    try:
        for party in range(2):
            logs.append(open(run.dir / f'{label}-party-{party}.log', 'w'))
            env = dict(os.environ, **common, SIGNAL_RECORD=str(run.dir / f'record-{label}-party-{party}.jsonl'), **party_env(party))
            command = [str(CONTROLLER), str(worker), str(work), str(party), str(hosts), str(port), str(CACHE), session_id,
                       server['endpoint'], str(server['port']), server['hostname'], str(auth), server['tls_trust_root_pem'], '0']
            processes.append(subprocess.Popen(command, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=logs[-1], text=True))
        if during:
            during(processes)
        outputs = []
        for party, p in enumerate(processes):
            try:
                stdout, _ = p.communicate(timeout=max(1, timeout - (time.monotonic() - started)))
            except subprocess.TimeoutExpired:
                run.log(f'{label}-timeout', party=party, seconds=timeout)
                stop(p)
                stdout, _ = p.communicate()
            (run.dir / f'{label}-party-{party}.json').write_text(stdout)
            lines = [line for line in stdout.splitlines() if line.startswith('{') and '"passed":' in line]
            outputs.append(json.loads(lines[-1]) if lines else dict(passed=False, error='no report', stdout_tail=stdout[-500:]))
    finally:
        for p in processes:
            if p.poll() is None:
                stop(p)
        for p in processes:
            p.wait()
        for log in logs:
            log.close()
    result = dict(seconds=round(time.monotonic() - started, 1), exit_codes=[p.returncode for p in processes], controllers=outputs)
    run.log(f'{label}-end', seconds=result['seconds'], exit_codes=result['exit_codes'],
            passed=[c.get('passed') for c in outputs], errors=[c.get('error') for c in outputs],
            received=[c.get('received') for c in outputs], refused=[c.get('refused') for c in outputs],
            results=[c.get('results') for c in outputs])
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('target', choices=['local', 'production'])
    p.add_argument('--export', required=True, help='directory written by lss-provision export-account')
    p.add_argument('--mode', default='malicious', choices=['malicious', 'semi-honest'])
    p.add_argument('--text', default=DEFAULT_TEXT, help='the one text sent back (at most 256 bytes)')
    p.add_argument('--manifest', help='strict mode: CIRCUIT_MANIFEST (manifest.txt of scripts/produce_circuits.py); nothing is produced while connected')
    p.add_argument('--ack-refused', action='store_true', help='acknowledge refused messages (default: leave them on the server, SIGNAL_ACK_REFUSED=0)')
    p.add_argument('--wait-minutes', type=float, default=30, help='how long the receive session waits for the signup')
    p.add_argument('--local-account', help='local target: the lss-provision account name the export was made from')
    p.add_argument('--i-have-the-go-ahead', action='store_true', help='production: the owner said to go ahead')
    p.add_argument('--dry-run', action='store_true', help='check and record the plan; no connection')
    p.add_argument('--db', default='real', choices=['real', 'memory'],
                   help='real: secret-shared-db nodes with Postgres under RUN/db/real, kept after the run (resumable); memory: in-memory test nodes')
    p.add_argument('--resume', metavar='RUN_DIR', help='only the send, to the contact RUN_DIR stored (its database nodes are started again)')
    p.add_argument('--stop-after', choices=['receive'], help='end after the receive session (to test --resume)')
    a = p.parse_args()
    export_dir = Path(a.export).resolve()
    export = json.loads((export_dir / 'mpc-export.json').read_text())
    hints = json.loads((export_dir / 'deployment-hints.json').read_text())
    if export.get('target') != a.target:
        sys.exit(f'the export was made for {export.get("target")}, not {a.target}')
    if a.target == 'local' and not a.local_account:
        sys.exit('local: --local-account NAME (the lss-provision account the export was made from)')
    if len(a.text.encode()) > 256:
        sys.exit('the text is longer than 256 bytes')
    server = export['server']
    if a.target == 'local' and server.get('plain_port'):
        # The local server instance the export names (the compact one listens on 19080/19443).
        os.environ['LSS_SERVER'] = f'127.0.0.1:{server["plain_port"]}'
    hours_left =(export['sender']['certificate_expires_ms'] - time.time() * 1000) / 3.6e6
    problems = []
    if hours_left < 2:
        problems.append(f'the sender certificate expires in {hours_left:.1f} hours: refresh it first')
    for path in (CONTROLLER, LSS, BASE / 'tls-worker-fixture-v3', Path(server['tls_trust_root_pem'])):
        if not Path(path).exists():
            problems.append(f'missing {path}')
    if a.manifest and not Path(a.manifest).exists():
        problems.append(f'missing manifest {a.manifest}')
    previous, contact = None, None
    if a.resume:
        previous = Path(a.resume).resolve()
        contact, stored = stored_contact(previous) if (previous / 'timeline.jsonl').exists() else (None, False)
        if not (previous / 'db/real/nodes.json').exists():
            problems.append(f'{previous} kept no database (its nodes were the in-memory test nodes, --db memory, or it ended before '
                            'they started): the contact it stored is gone; a new signup is needed')
        if not stored:
            problems.append(f'{previous} did not store a contact (no receive session stored the signup)')
        if previous.exists() and json.loads((previous / 'plan.json').read_text()).get('target') != a.target:
            problems.append(f'{previous} was a run against another target')
    run = Run(a.target, a.mode, '-resume' if a.resume else '')
    common = dict(DYLD_LIBRARY_PATH=str(MP), TLS_WORKER_FIELD_BATCH='3000', SIGNAL_CLIENT_PROFILE='libsignal',
                  SIGNAL_LOCAL_EXPORT=str(export_dir / 'mpc-export.json'), SIGNAL_LOCAL_KEM=str(LSS),
                  CIRCUIT_CACHE_LOG=str(run.dir / 'kernels-requested.txt'), SIGNAL_ACK_REFUSED='1' if a.ack_refused else '0',
                  SIGNAL_RECEIVE_JUMP=RECEIVE_JUMP)
    if a.manifest:
        common.update(CIRCUIT_MANIFEST=str(Path(a.manifest).resolve()), CIRCUIT_REFUSED_LOG=str(run.dir / 'kernels-refused.txt'))
    plan = dict(target=a.target, mode=a.mode, server=server, profile='libsignal', ack_refused=a.ack_refused,
                db=a.db, resume_from=str(previous) if previous else None, contact=contact, stop_after=a.stop_after,
                text_bytes=len(a.text.encode()), manifest=a.manifest, manifest_sha256=sha256(a.manifest) if a.manifest else None,
                deployment_hints=hints, certificate_hours_left=round(hours_left, 1), sealed_sender_server_key_id=export['sealed_sender_server']['key_id'],
                environment={k: v for k, v in common.items()}, git_head=git('rev-parse', 'HEAD'),
                git_dirty_files=git('status', '--porcelain').count('\n') + 1, git_diff_sha256=hashlib.sha256(git('diff').encode()).hexdigest(),
                binaries={str(path): sha256(path) for path in (CONTROLLER, LSS, BASE / 'tls-worker-fixture-v3', BASE / 'tls-worker-sh-fixture-v3')},
                problems=problems, wait_minutes=a.wait_minutes)
    (run.dir / 'plan.json').write_text(json.dumps(plan, indent=1) + '\n')
    run.log('plan', directory=str(run.dir), problems=problems, certificate_hours_left=round(hours_left, 1))
    if problems:
        sys.exit('not starting: ' + '; '.join(problems))
    if a.dry_run:
        run.log('dry-run-done')
        return
    if a.target == 'production':
        if not a.i_have_the_go_ahead:
            sys.exit('production contacts Signal\'s service: only with the owner\'s explicit go-ahead (--i-have-the-go-ahead)')
        if input(f'This connects to {server["endpoint"]}:{server["port"]} as the real account. Type YES: ').strip() != 'YES':
            run.log('cancelled-before-any-connection')
            return

    harness.STATE = run.dir    # the database nodes' files go under the run directory
    harness.Cluster.REAL = a.db == 'real'
    report = dict(directory=str(run.dir), target=a.target, passed=False, db=a.db, resumed_from=str(previous) if previous else None)
    cluster = None
    try:
        auth, work, hosts = prepare_workers(run)
        if previous:
            # Only the send: the earlier run's nodes, with the contact it stored, started again.
            cluster = reopen_cluster(previous / 'db')
            run.log('database-restarted', directory=str(previous / 'db/real'), seconds=cluster.waits['start'])
            contact = int(contact)
            cluster.refresh()    # one epoch: everything written before the earlier run stopped is applied
            run.log('database-epoch', seconds=cluster.waits['epochs'][-1])
        else:
            cluster = harness.Cluster()
            cluster.token(harness.ACCOUNT)
            contact = secrets.randbits(100)
            token = cluster.token(contact).read_text().strip()
            (run.dir / 'token.txt').write_text(token + '\n')
            run.log('signup-token', id=str(contact), characters=len(token), file=str(run.dir / 'token.txt'))
        shares = [(export_dir / f'credentials-party-{party}.hex').read_text().strip() for party in range(2)]

        # 2. Receive the signup.
        if not previous:
            if a.target == 'local':
                out = subprocess.run([str(LSS), 'signup', 'realtest-user', '+12025550199', a.local_account, token], capture_output=True, text=True)
                run.log('local-signup-sent', exit_code=out.returncode, error=out.stderr[-300:])
            else:
                print(f'\nSend this text from the phone to the account (one message, nothing else):\n\n{token}\n', flush=True)
            receive = session(run, 'receive', server, export_dir, auth, work, hosts,
                              lambda party: dict(cluster.env(party), SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT='1'),
                              common, a.wait_minutes * 60 + 300)
            report['receive'] = receive
            signed_up = all(c.get('received') == [[str(contact), token]] for c in receive['controllers'])
            report['signed_up'] = signed_up
            if not signed_up:
                raise RuntimeError('the signup was not received and stored (see the receive records)')
            if a.stop_after == 'receive':
                report['passed'] = True
                run.log('stopped-after-receive', resume=f'--resume {run.dir}')
                return
            cluster.refresh()

        # 3. Send one text back.
        request = cluster.request([contact], a.text)
        send = session(run, 'send', server, export_dir, auth, work, hosts,
                       lambda party: dict(cluster.env(party, request), SIGNAL_NOTIFY_MESSAGE_FILE=str(cluster.dir / 'message.txt')),
                       common, 900)
        report['send'] = send
        results = [c.get('results') for c in send['controllers']]
        report['delivered'] = all(r and r[0].get('result', '').startswith('delivered') for r in results)

        # 4. Local only: the new user decrypts it.
        if a.target == 'local':
            seen = harness.receive('realtest-user', 6)
            report['new_user_received'] = [g['text'] for g in seen]
            report['sealed'] = all(not g['envelope'].get('source_service_id') for g in seen)
            report['passed'] = report['delivered'] and a.text in report['new_user_received'] and report['sealed']
        else:
            report['passed'] = report['delivered']
            print('\nDone. Check on the phone that the text arrived, then note it in the run directory.', flush=True)
    except Exception as e:
        report['error'] = f'{type(e).__name__}: {e}'
        run.log('error', error=report['error'])
    finally:
        if cluster:
            cluster.stop()
        (run.dir / 'report.json').write_text(json.dumps(report, indent=1) + '\n')
        run.log('end', passed=report['passed'], error=report.get('error'))
    sys.exit(0 if report['passed'] else 1)


if __name__ == '__main__':
    main()
