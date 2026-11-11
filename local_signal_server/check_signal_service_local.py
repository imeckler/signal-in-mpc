#!/usr/bin/env python3
"""Signal service path of the MPC client against the LOCAL Signal-Server (not Signal's service).

Counterpart of handshake_backend/EmpHybridWork/check_signal_service_v3.py, which runs the client
against an in-process fake. Stages:
  1. build (once) and start the local server + TLS terminator      scripts/build_server.sh, start_server.sh
  2. provision sender + two recipients with established sessions   lss-provision provision
  3. export what the MPC client needs                              lss-provision export-mpc -> state/mpc-export.json
  4. optional --self-check: conventional reference sender using ONLY the export, one send per contact
     on an unauthenticated socket                                  lss-provision ref-send
  5. the MPC run, twice: the first admits the contacts from the export and stores each contact's
     advanced state (sealed) with this party's key share in state/store/party-N; the second loads
     the contacts from that store only, so it passes only if the stored state is complete
  6. verification: each recipient decrypts the expected texts, and every envelope has NO source
     fields (a sealed-sender message the server could not attribute)  lss-provision receive
  7. stop everything (unless --keep-server)

Talks only to 127.0.0.1. Never point this at Signal's service.

Circuits are produced before the server is contacted (the server drops a socket after 90 s
without traffic, and producing a large circuit for the first time takes longer): kernels.txt
lists what a run asks for and is rewritten after a passing run.

Usage: check_signal_service_local.py [malicious|semi-honest] [--self-check] [--keep-server] [--skip-build] [--runs N]
"""
import argparse, json, os, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent            # local_signal_server/
ROOT = HERE.parent                                # tls-mpc/
SCRIPTS = HERE / 'scripts'
STATE = HERE / 'state'
EXPORT = STATE / 'mpc-export.json'
CONTACTS = ['recipient', 'recipient2']
KERNELS = HERE / 'kernels.txt'
KERNEL_LOG = STATE / 'kernels-requested.txt'
STORE = STATE / 'store'
CACHE = ROOT / 'handshake_backend/EmpHybridWork/circuit_cache.py'


def run(args, **kw):
    print('+', ' '.join(str(a) for a in args), flush=True)
    return subprocess.run([str(a) for a in args], check=True, text=True, **kw)


def lss(*args, capture=False):
    """lss-provision via scripts/provision.sh (builds offline first)."""
    r = run(['bash', SCRIPTS / 'provision.sh', *args], stdout=subprocess.PIPE if capture else None)
    return r.stdout if capture else None


def receive(name, seconds=15):
    out = lss('receive', name, str(seconds), capture=True)
    return [json.loads(line) for line in out.splitlines() if line.startswith('{')]


def kernel_lines(path):
    return sorted(set(line.strip() for line in path.read_text().splitlines() if line.strip())) if path.exists() else []


def warm():
    """Produce every circuit a run is known to ask for before any connection.
    A name the emitter no longer knows is skipped: the run asks for what it needs anyway."""
    run(['lake', 'build', 'flat_kernel_emitter'], cwd=ROOT, capture_output=True)
    names = sorted(set(kernel_lines(KERNELS) + kernel_lines(KERNEL_LOG)))
    started = time.monotonic()
    def one(name):
        return subprocess.run([sys.executable, str(CACHE), *name.split()], cwd=ROOT, capture_output=True).returncode == 0
    # ONE AT A TIME: lowering a large kernel takes many gigabytes; several at once exhausted the
    # machine's memory (twice). Do not parallelize this.
    ok = [one(name) for name in names]
    return dict(kernels=len(names), skipped=[n for n, good in zip(names, ok) if not good], seconds=time.monotonic() - started)


def run_mpc(export, mode, texts, party_env=None, during=None):
    """One two-party client session against 127.0.0.1:18443: handshake, unauthenticated chat
    socket, two broadcasts to every contact, contact state written back to the store.
    Controller argv: WORKER DIRECTORY PARTY HOSTS PORT MANIFEST SESSION ENDPOINT PORT HOSTNAME AUTH TRUST UNUSED.
    Not exercised here: the authenticated socket (credentials, server requests, keepalive)."""
    import hashlib, re, secrets
    base = ROOT / '.deps/two-party-comparison'
    here = ROOT / 'handshake_backend/EmpHybridWork'
    sys.path.insert(0, str(ROOT / 'scripts'))
    from check_full_handshake import OPENSSL
    sh = mode == 'semi-honest'
    output = base / 'signal-service-local-run' / secrets.token_hex(8)
    output.mkdir(parents=True)
    run(['lake', 'build', 'public_service_controller', 'flat_kernel_emitter'], cwd=ROOT, capture_output=True)
    run(['c++', '-std=c++20', '-O2', '-I' + str(OPENSSL / 'include'), ROOT / 'handshake_backend/public_auth.cpp',
         '-L' + str(OPENSSL / 'lib'), '-lssl', '-lcrypto', '-o', output / 'public_auth'])
    mp = base / 'data61-MP-SPDZ-113c4e4'
    work = output / 'work'
    work.mkdir()
    with open(output / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(mp / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    stamp = int(time.time() * 1000)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(mp), TLS_WORKER_FIELD_BATCH='3000', CIRCUIT_CACHE_LOG=str(KERNEL_LOG),
               SIGNAL_LOCAL_EXPORT=str(EXPORT))
    stored_before = sorted(p.name for p in (STORE / 'party-0').glob('*')) if (STORE / 'party-0').exists() else []
    hosts = output / 'hosts'
    hosts.write_text('127.0.0.1\n' * 2)
    session = secrets.token_hex(32)
    worker = base / ('tls-worker-sh-fixture-v3' if sh else 'tls-worker-fixture-v3')
    controller = ROOT / '.lake/build/bin/public_service_controller'
    trust = STATE / 'tls' / 'ca.pem'
    port = 22300 if sh else 22200
    processes, logs, cases = [], [], []
    started = time.monotonic()
    try:
        for party in range(2):
            log = open(output / f'party-{party}.log', 'w')
            logs.append(log)
            command = [str(controller), str(worker), str(work), str(party), str(hosts), str(port), str(here / 'circuit_cache.py'),
                       session, '127.0.0.1', '18443', 'server.example', str(output / 'public_auth'), str(trust), '0']
            (STORE / f'party-{party}').mkdir(parents=True, exist_ok=True)
            processes.append(subprocess.Popen(command, cwd=ROOT, env=dict(env, SIGNAL_LOCAL_STORE=str(STORE / f'party-{party}'),
                                                                        **(party_env(party) if party_env else {})),
                                              stdout=subprocess.PIPE, stderr=log, text=True))
        if during:
            during(processes)
        for party, p in enumerate(processes):
            stdout, _ = p.communicate(timeout=7200)
            (output / f'party-{party}.json').write_text(stdout)
            if stdout.strip():
                cases.append(json.loads(stdout.strip().splitlines()[0]))
    finally:
        for p in processes:
            if p.poll() is None:
                p.terminate()
        for p in processes:
            p.wait()
        for log in logs:
            log.close()
    totals, rejections = [], []
    for party in range(2):
        text = (output / f'party-{party}.log').read_text()
        rows = re.findall(r'operation (\d+) ok seconds=([\d.e+-]+) and_gates=(\d+) emp_sent_bytes=(\d+) field_sent_bytes=(\d+) field_products=(\d+)', text)
        if rows:
            last = rows[-1]
            totals.append(dict(operation=int(last[0]), seconds=float(last[1]), and_gates=int(last[2]), emp_sent_bytes=int(last[3]),
                               field_sent_bytes=int(last[4]), field_products=int(last[5])))
        rejections += re.findall(r'operation \d+ rejected[^\n]*', text) + re.findall(r'tls-worker-v3 aborted[^\n]*', text)
    result = dict(logs=str(output), timestamp=stamp, contacts_loaded_from_store=stored_before, controllers=cases, worker_totals=totals, rejections=rejections,
                  elapsed_seconds=time.monotonic() - started, exit_codes=[p.returncode for p in processes])
    if any(p.returncode for p in processes) or len(cases) != 2 or not all(c['passed'] for c in cases):
        raise RuntimeError('MPC controllers failed: ' + json.dumps(result))
    return result


def run_receive(export, mode, delay):
    """The authenticated socket in a two-party session. Each controller gets one XOR share of the
    account's socket credentials, so neither could open the socket alone. The controllers answer
    the server's requests and send keepalives; after `delay` seconds (past the server's 90 s idle
    limit by default) a contact sends the account a message, which must be delivered to the
    session. Its body is not opened or acknowledged here."""
    import secrets
    credentials = bytes.fromhex(export['sender']['upgrade_credentials_hex'])
    share = secrets.token_bytes(len(credentials))
    shares = [share.hex(), bytes(a ^ b for a, b in zip(credentials, share)).hex()]
    def during(processes):
        deadline = time.monotonic() + delay
        while time.monotonic() < deadline and all(p.poll() is None for p in processes):
            time.sleep(1)
        if all(p.poll() is None for p in processes):
            lss('send', CONTACTS[0], 'sender', 'to the MPC client')
    result = run_mpc(export, mode, {}, party_env=lambda party: dict(SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT='1'),
                     during=during)
    result['delay_seconds'] = delay
    result['passed'] = all(c.get('messages_delivered') == 1 for c in result['controllers']) and (
        delay < 30 or all(c.get('keepalives', 0) >= delay // 30 for c in result['controllers']))
    return result


def run_signup(export, mode, texts):
    """A NEW user signs up: a fresh libsignal client registers, fetches the account's prekey
    bundle and sends one sealed-sender first message (with its profile key). The two-party
    session on the authenticated socket must open it, report its text, store the new contact
    under a new id and acknowledge the message. A second session then loads that contact from
    the store alone and broadcasts to it; the new user must decrypt the broadcasts."""
    import secrets
    name, token, contact = 'newuser', 'signup token ' + secrets.token_hex(4), 1000
    lss('signup', name, '+12025550104', 'sender', token)   # queued by the server until the session connects
    credentials = bytes.fromhex(export['sender']['upgrade_credentials_hex'])
    share = secrets.token_bytes(len(credentials))
    shares = [share.hex(), bytes(a ^ b for a, b in zip(credentials, share)).hex()]
    tool = HERE / 'provision/target/debug/lss-provision'
    first = run_mpc(export, mode, {}, party_env=lambda party: dict(
        SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT='1', SIGNAL_LOCAL_KEM=str(tool), SIGNAL_LOCAL_NEW_CONTACT=str(contact)))
    result = dict(receive=first, token=token)
    result['received'] = all(c.get('received') == [[str(contact), token]] for c in first['controllers'])
    if result['received']:
        result['send'] = run_mpc(export, mode, texts, party_env=lambda party: dict(SIGNAL_LOCAL_EXTRA_CONTACTS=str(contact)))
        good, recipients = verify({name: texts[CONTACTS[0]]})
        result['new_user'] = recipients
        # Nothing may be left in the account's queue: the first message was acknowledged.
        result['passed'] = good
    else:
        result['passed'] = False
    return result


class Cluster:
    """Five database nodes of secret-shared-db (its in-memory test node: no Postgres, no epochs;
    `refresh` stands for an epoch passing), plus the application server's keys. The binaries are
    built from the `two-party-handoff` branch checked out at .deps/secret-shared-db-handoff."""
    BIN = ROOT / '.deps/secret-shared-db-handoff/target/debug'

    def __init__(self):
        import shutil, socket
        self.dir = STATE / 'db'
        shutil.rmtree(self.dir, ignore_errors=True)
        subprocess.run([str(self.BIN / 'pki'), '-n', '5', '-o', str(self.dir), '-d', 'postgresql://unused', '-t', '3', '-l'],
                       check=True, capture_output=True)
        network = json.loads((self.dir / 'relay/network-config.json').read_text())
        sockets = [socket.socket() for _ in range(5)]
        for s in sockets:
            s.bind(('127.0.0.1', 0))
        network['compute_addresses'] = ['127.0.0.1:%d' % s.getsockname()[1] for s in sockets]
        for s in sockets:
            s.close()
        # A session outlasts the default 120 s for which a signed request is accepted.
        network['notify_max_age_secs'] = 7200
        self.network = self.dir / 'network.json'
        self.network.write_text(json.dumps(network))
        (self.dir / 'tokens').mkdir()
        self.nodes = []
        for j in range(5):
            node = subprocess.Popen([str(self.BIN / 'handoff_test_node'), '--network', str(self.network), '--key',
                                     str(self.dir / f'share-dbs/{j}/config.json'), '--node', str(j), '--refresh-seed', 'local test',
                                     '--exit-on-eof'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
            self.nodes.append(node)
            if not node.stdout.readline().startswith('listening'):
                raise RuntimeError('database node did not start')

    def refresh(self):
        for node in self.nodes:
            node.stdin.write('refresh\n')
            node.stdin.flush()
            if not node.stdout.readline().startswith('refreshed'):
                raise RuntimeError('database node did not refresh')

    def client(self, *args):
        subprocess.run([str(self.BIN / 'handoff_client'), *map(str, args)], check=True, capture_output=True, text=True)

    def token(self, contact):
        """The application server's signup token for an id."""
        path = self.dir / 'tokens' / f'{contact}.json'
        self.client('sign-signup', '--app-config', self.dir / 'app-server/config.json', '--id', contact, '--out', path)
        return path

    def request(self, contacts, message):
        """The application server's signed notify request for these ids."""
        path = self.dir / 'request.json'
        (self.dir / 'message.txt').write_text(message)
        self.client('sign-request', '--key', self.dir / 'app-server/notify-key.json', '--ids', ','.join(str(c) for c in sorted(contacts)),
                    '--message-file', self.dir / 'message.txt', '--out', path)
        return path

    def env(self, party, request=None):
        work = self.dir / f'work-{party}'
        work.mkdir(exist_ok=True)
        values = dict(SIGNAL_DB_CLIENT=str(self.BIN / 'handoff_client'), SIGNAL_DB_NETWORK=str(self.network),
                      SIGNAL_DB_KEY=str(self.dir / f'compute-nodes/{party}/key.json'), SIGNAL_DB_WORK=str(work),
                      SIGNAL_DB_TOKENS=str(self.dir / 'tokens'))
        if request:
            values['SIGNAL_DB_REQUEST'] = str(request)
        return values

    def stop(self):
        for node in self.nodes:
            node.kill()
            node.wait()


def run_db(export, mode, texts):
    """The whole flow with contact keys and state held by the database nodes:
      A. broadcast; the export's two contacts are created in the database (key dealt by both
         parties, state written as blob version 1);
      B. broadcast again with both contacts read back from the nodes (shares combined after the
         parity check between the parties; state written as version 2);
      C. a new user signs up by sending the application's signup token: the session receives it,
         creates the contact under the id the token names, and acknowledges;
      D. broadcast to all three, the new contact read from the nodes like the others."""
    import secrets
    cluster = Cluster()
    result = {}
    try:
        ids = [int(c['contact_id_u128_hex'], 16) for c in export['contacts']]
        for contact in ids:
            cluster.token(contact)
        steps = [('created', ids, {}), ('reloaded', ids, {})]
        ok = True
        for label, contacts, extra in steps:
            request = cluster.request(contacts, 'broadcast')
            run = run_mpc(export, mode, texts, party_env=lambda party: dict(cluster.env(party, request), **extra))
            good, recipients = verify(texts)
            result[label] = dict(run=run, recipients=recipients, passed=good)
            cluster.refresh()
            ok = ok and good
        new = secrets.randbits(100)
        token = cluster.token(new).read_text()
        lss('signup', 'newuser', '+12025550104', 'sender', token)
        credentials = bytes.fromhex(export['sender']['upgrade_credentials_hex'])
        share = secrets.token_bytes(len(credentials))
        shares = [share.hex(), bytes(a ^ b for a, b in zip(credentials, share)).hex()]
        tool = HERE / 'provision/target/debug/lss-provision'
        receive = run_mpc(export, mode, {}, party_env=lambda party: dict(
            cluster.env(party), SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT='1', SIGNAL_LOCAL_KEM=str(tool)))
        signed_up = all(c.get('received') == [[str(new), token]] for c in receive['controllers'])
        result['signup'] = dict(run=receive, contact=str(new), passed=signed_up)
        ok = ok and signed_up
        if signed_up:
            cluster.refresh()
            request = cluster.request(ids + [new], 'broadcast')
            run = run_mpc(export, mode, texts, party_env=lambda party: dict(cluster.env(party, request), SIGNAL_LOCAL_EXTRA_CONTACTS=str(new)))
            good, recipients = verify(dict(texts, newuser=texts[CONTACTS[0]]))
            result['all'] = dict(run=run, recipients=recipients, passed=good)
            ok = ok and good
        result['passed'] = ok
    finally:
        cluster.stop()
    return result


def verify(expected):
    """expected: {recipient name: [texts]}. Every delivered envelope must be sealed (no source fields)."""
    result = {}
    ok = True
    for name, texts in expected.items():
        got = receive(name)
        attributed = [g for g in got if g['envelope'].get('source_service_id') or g['envelope'].get('source_device')]
        missing = [t for t in texts if t not in [g['text'] for g in got]]
        result[name] = dict(received=[g['text'] for g in got], missing=missing,
                            envelopes_with_source_fields=len(attributed))
        ok = ok and not missing and not attributed
    return ok, result


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('mode', nargs='?', default='malicious', choices=['malicious', 'semi-honest'])
    p.add_argument('--self-check', action='store_true', help='reference sender from the export (no MPC)')
    p.add_argument('--keep-server', action='store_true')
    p.add_argument('--skip-build', action='store_true')
    p.add_argument('--runs', type=int, default=2, help='MPC sessions; each after the first loads contacts from the store')
    p.add_argument('--receive', action='store_true', help='also run the authenticated-socket session')
    p.add_argument('--receive-delay', type=int, default=100, help='seconds of silence before the incoming message')
    p.add_argument('--signup', action='store_true', help="also receive a new user's first message, then broadcast to them")
    p.add_argument('--db', action='store_true', help='also run the flow against five database nodes (secret-shared-db)')
    p.add_argument('--broadcasts', type=int, default=2, help='broadcasts per send session (more than 2: to measure the cost per message)')
    a = p.parse_args()
    os.environ['SIGNAL_LOCAL_BROADCASTS'] = str(max(2, a.broadcasts))
    report = dict(passed=False, mode=a.mode, started=time.time())
    try:
        if not a.skip_build and not (STATE / 'classpath.txt').exists():
            run(['bash', SCRIPTS / 'build_server.sh'])
        report['circuits'] = warm()
        import shutil
        shutil.rmtree(STORE, ignore_errors=True)   # the accounts below are new: no stored state applies
        run(['bash', SCRIPTS / 'start_server.sh'])
        lss('provision')
        lss('export-mpc')
        export = json.loads(EXPORT.read_text())
        report['export'] = dict(path=str(EXPORT), contacts=[c['recipient_aci'] for c in export['contacts']],
                                projection=[c['projection'] for c in export['contacts']])
        if a.self_check:
            text = 'lss self-check from export'
            lss('ref-send', text)
            ok, result = verify({name: [text] for name in CONTACTS})
            report['self_check'] = dict(passed=ok, recipients=result)
            if not ok:
                raise RuntimeError('reference sender from the export was not received intact')
        # The texts PublicServiceController.lean broadcasts in its local-server mode.
        texts = {CONTACTS[0]: ['MPC broadcast one', 'MPC broadcast two ☕'],
                 CONTACTS[1]: ['MPC broadcast one', 'MPC broadcast two ☕']}
        report['mpc_runs'], report['mpc'] = [], []
        ok = True
        for index in range(a.runs):
            report['mpc_runs'].append(run_mpc(export, a.mode, texts))
            good, result = verify(texts)
            report['mpc'].append(dict(passed=good, recipients=result))
            ok = ok and good
            if not good:
                break
        if ok and a.receive:
            report['receive'] = run_receive(export, a.mode, a.receive_delay)
            ok = report['receive']['passed']
        if ok and a.signup:
            report['signup'] = run_signup(export, a.mode, texts)
            ok = report['signup']['passed']
        if ok and a.db:
            if a.runs or a.signup:
                # The sessions above advanced the contacts' state past the export, and the database
                # flow starts from an export: new accounts and a new export for it.
                lss('provision')
                lss('export-mpc')
                export = json.loads(EXPORT.read_text())
            report['db'] = run_db(export, a.mode, texts)
            ok = report['db']['passed']
        report['passed'] = ok
        if ok:
            KERNELS.write_text(''.join(line + '\n' for line in kernel_lines(KERNEL_LOG)))
    except Exception as e:
        report['error'] = f'{type(e).__name__}: {e}'
    finally:
        if not a.keep_server:
            subprocess.run(['bash', str(SCRIPTS / 'stop_server.sh')])
        report['elapsed_seconds'] = time.time() - report.pop('started')
        (STATE / 'check-report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=2))
    sys.exit(0 if report['passed'] else 1)


if __name__ == '__main__':
    main()
