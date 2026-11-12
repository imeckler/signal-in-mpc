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

--circuits 1,3: broadcasts through scripts/socks5_test_proxy.py (a stand-in for a local Tor client)
with N Tor circuits each, checked from the proxy's log (run_circuits). Never uses Tor.
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


DEPLOYMENT = HERE / 'deployment.json'
CIRCUITS = STATE / 'circuits'
REFUSED = STATE / 'kernels-refused.txt'


def strict_manifest(produce=True):
    """--strict: every circuit the test deployment can need, produced one at a time before the
    server is contacted, and pinned. The sessions' workers then take CIRCUIT_MANIFEST from the
    environment: they use nothing else and never produce a circuit.
    --strict-produced: the same with the manifest already in state/circuits (produced earlier, as
    a deployment does; a manifest stays usable after the Lean emitter is rebuilt)."""
    started = time.monotonic()
    if produce:
        r = subprocess.run([sys.executable, str(ROOT / 'scripts/produce_circuits.py'), str(DEPLOYMENT), str(CIRCUITS)], cwd=ROOT,
                           capture_output=True, text=True)
        if r.returncode:
            raise RuntimeError('circuit production failed: ' + (r.stdout + r.stderr)[-600:])
    REFUSED.write_text('')
    os.environ['CIRCUIT_MANIFEST'] = str(CIRCUITS / 'manifest.txt')
    os.environ['CIRCUIT_REFUSED_LOG'] = str(REFUSED)
    manifest = json.loads((CIRCUITS / 'manifest.json').read_text())
    return dict(manifest=os.environ['CIRCUIT_MANIFEST'], manifest_sha256=manifest['manifest_sha256'], summary=manifest['summary'],
                seconds=time.monotonic() - started)


def run_mpc(export, mode, texts, party_env=None, during=None, endpoint='127.0.0.1', server_port=18443, during_logs=None):
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
    # TEST (--link-delay-ms): every link between the two workers through the delay relay. The
    # connecting worker dials PORT + shift (TLS_WORKER_TEST_LINK_SHIFT), where the relay listens.
    relay, link_delay = None, float(os.environ.get('SIGNAL_LINK_DELAY_MS', '0'))
    if link_delay > 0:
        shift = 40
        relay = subprocess.Popen([str(base / 'delay-relay'), str(link_delay), f'{port + shift}:{port}', f'{port + 10 + shift}:{port + 10}'],
                                 stderr=open(output / 'delay-relay.log', 'w'))
        env['TLS_WORKER_TEST_LINK_SHIFT'] = str(shift)
    started = time.monotonic()
    try:
        for party in range(2):
            log = open(output / f'party-{party}.log', 'w')
            logs.append(log)
            command = [str(controller), str(worker), str(work), str(party), str(hosts), str(port), str(here / 'circuit_cache.py'),
                       session, endpoint, str(server_port), 'server.example', str(output / 'public_auth'), str(trust), '0']
            (STORE / f'party-{party}').mkdir(parents=True, exist_ok=True)
            processes.append(subprocess.Popen(command, cwd=ROOT, env=dict(env, SIGNAL_LOCAL_STORE=str(STORE / f'party-{party}'),
                                                                        **(party_env(party) if party_env else {})),
                                              stdout=subprocess.PIPE, stderr=log, text=True))
        if during:
            during(processes)
        if during_logs:
            during_logs(processes, output)   # as `during`, with the directory of the parties' logs
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
        if relay:
            relay.terminate()   # it writes its connection and byte counts to delay-relay.log
            relay.wait()
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


def run_receive(export, mode, delay, server_port=18443):
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
                     during=during, server_port=server_port)
    result['delay_seconds'] = delay
    result['passed'] = all(c.get('messages_delivered') == 1 for c in result['controllers']) and (
        delay < 30 or all(c.get('keepalives', 0) >= delay // 30 for c in result['controllers']))
    return result


def run_fingerprint(export, mode, texts):
    """--fingerprint: one send session and one receive session (40 s idle: one keepalive) through
    scripts/fingerprint_terminator.py on port 18445, which records the raw ClientHello and records
    and the decrypted upgrade requests and frames; then fingerprint/check_fingerprint.py compares
    them with the official client's reference (fingerprint/reference/reference.json) and fails on
    any difference it does not list with a reason (handshake_backend/EmpHybridWork/CLIENT_FINGERPRINT.md).
    The transcripts (state/fingerprint/..., local test-account credentials) stay out of the
    repository; the report holds only redacted shapes."""
    out = STATE / 'fingerprint' / time.strftime('%Y%m%d-%H%M%S')
    out.mkdir(parents=True)
    log = open(out / 'terminator.log', 'w')
    terminator = subprocess.Popen([sys.executable, '-I', str(SCRIPTS / 'fingerprint_terminator.py'), '--cert', str(STATE / 'tls/server.pem'),
                                   '--key', str(STATE / 'tls/server.key'), '--listen', '18445', '--out', str(out / 'transcripts')],
                                  stdout=log, stderr=subprocess.STDOUT)
    time.sleep(1)
    try:
        send = run_mpc(export, mode, texts, server_port=18445)
        good, recipients = verify(texts)
        receive = run_receive(export, mode, 40, server_port=18445)
    finally:
        terminator.terminate()
        terminator.wait()
        log.close()
    check = subprocess.run([sys.executable, '-I', str(HERE / 'fingerprint/check_fingerprint.py'), str(out / 'transcripts'),
                            '--out', str(out / 'report.json')], capture_output=True, text=True)
    fingerprint = json.loads((out / 'report.json').read_text()) if (out / 'report.json').exists() else dict(passed=False, error=check.stderr[-2000:])
    return dict(capture=str(out), send=send, send_received=dict(passed=good, recipients=recipients), receive=receive,
                fingerprint=fingerprint, passed=good and receive['passed'] and fingerprint.get('passed', False))


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


ACCOUNT = 2 ** 128 - 2   # the reserved id of the account's own row on the database nodes


class Cluster:
    """Five database nodes of secret-shared-db (its in-memory test node: no Postgres, no epochs;
    `refresh` stands for an epoch passing), plus the application server's keys. The binaries are
    built from the `two-party-handoff` branch checked out at .deps/secret-shared-db-handoff."""
    BIN = ROOT / '.deps/secret-shared-db-handoff/target/debug'
    # --real-db: the REAL node binary instead (Postgres, peers, consensus, epochs), started by
    # scripts/start_db_nodes.py; `refresh` then waits for the epoch that makes dealt rows readable.
    REAL = False
    REAL_EPOCH_SECS = 20

    def __init__(self):
        import shutil, socket
        self.dir = STATE / 'db'
        self.real = None
        if (self.dir / 'real').exists():
            self._nodes_script().stop(self.dir / 'real')   # left over from a run that was killed
        shutil.rmtree(self.dir, ignore_errors=True)
        self.config = self.dir
        if self.REAL:
            script = self._nodes_script()
            self.BIN = script.DEFAULT_BIN   # pki, server and handoff_client of one revision
            self.dir.mkdir(parents=True)
            self.config = self.dir / 'real/config'
            self.nodes = []
            started = time.time()
            state = script.start(self.dir / 'real', self.BIN, 25400, self.REAL_EPOCH_SECS, 1, True, None)
            self.real = self.dir / 'real'
            self.network = Path(state['network'])
            self.waits = dict(start=round(time.time() - started, 1), epochs=[])
            (self.dir / 'tokens').mkdir()
            return
        subprocess.run([str(self.BIN / 'pki'), '-n', '5', '-o', str(self.dir), '-d', 'postgresql://unused', '-t', '3', '-l'],
                       check=True, capture_output=True)
        network = json.loads((self.dir / 'relay/network-config.json').read_text())
        sockets = [socket.socket() for _ in range(5)]
        for s in sockets:
            s.bind(('127.0.0.1', 0))
        network['compute_addresses'] = ['127.0.0.1:%d' % s.getsockname()[1] for s in sockets]
        for s in sockets:
            s.close()
        # A signed request is accepted for 120 s; a session that read under it while it was fresh
        # may still write its contacts' state back later (the nodes remember the read).
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

    @staticmethod
    def _nodes_script():
        if str(SCRIPTS) not in sys.path:
            sys.path.insert(0, str(SCRIPTS))
        import start_db_nodes
        return start_db_nodes

    def refresh(self):
        if self.real:
            # Rows dealt so far become readable 1.5 to 2.5 epochs after they were dealt.
            self.waits['epochs'].append(round(self._nodes_script().wait_epoch(self.real), 1))
            return
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
        self.client('sign-signup', '--app-config', self.config / 'app-server/config.json', '--id', contact, '--out', path)
        return path

    def request(self, contacts, message):
        """The application server's signed notify request for these ids."""
        path = self.dir / 'request.json'
        (self.dir / 'message.txt').write_text(message)
        self.client('sign-request', '--key', self.config / 'app-server/notify-key.json', '--ids', ','.join(str(c) for c in sorted(contacts)),
                    '--message-file', self.dir / 'message.txt', '--out', path)
        return path

    def env(self, party, request=None):
        work = self.dir / f'work-{party}'
        work.mkdir(exist_ok=True)
        values = dict(SIGNAL_DB_CLIENT=str(self.BIN / 'handoff_client'), SIGNAL_DB_NETWORK=str(self.network),
                      SIGNAL_DB_KEY=str(self.config / f'compute-nodes/{party}/key.json'), SIGNAL_DB_WORK=str(work),
                      SIGNAL_DB_TOKENS=str(self.dir / 'tokens'))
        if request:
            values['SIGNAL_DB_REQUEST'] = str(request)
        return values

    def stop(self):
        if self.real:
            self._nodes_script().stop(self.real)
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
        for contact in ids + [ACCOUNT]:
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
        token = cluster.token(new).read_text().strip()   # fixed width: 108 characters of base64
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
            cluster.refresh()
            # E. A second new user, received by a session that has NO credentials of its own:
            # the account (identity key, password) comes from the database nodes.
            second = secrets.randbits(100)
            token = cluster.token(second).read_text().strip()
            lss('signup', 'newuser2', '+12025550105', 'sender', token)
            receive = run_mpc(export, mode, {}, party_env=lambda party: dict(
                cluster.env(party), SIGNAL_LOCAL_RECEIVE='1', SIGNAL_LOCAL_EXPECT='1', SIGNAL_LOCAL_KEM=str(tool)))
            stored_account = all(c.get('received') == [[str(second), token]] for c in receive['controllers'])
            result['account_from_database'] = dict(run=receive, contact=str(second), passed=stored_account)
            ok = ok and stored_account
            # F. The application deletes a contact: both parties submit its signed request.
            request = cluster.dir / 'delete.json'
            cluster.client('sign-delete', '--key', cluster.config / 'app-server/notify-key.json', '--ids', new, '--out', request)
            controller = ROOT / '.lake/build/bin/public_service_controller'
            parties = [subprocess.Popen([str(controller), 'db-delete', str(party), str(request)], env=dict(os.environ, **cluster.env(party)),
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) for party in range(2)]
            outputs = [p.communicate(timeout=120) for p in parties]
            check = cluster.request([new], 'after delete')
            cluster.client('read', '--network', cluster.network, '--key', cluster.config / 'compute-nodes/0/key.json', '--party', 0,
                           '--request', check, '--out', cluster.dir / 'read-after-delete.json')
            after = json.loads((cluster.dir / 'read-after-delete.json').read_text())
            deleted = all(p.returncode == 0 for p in parties) and str(new) in after.get('missing', []) and not after.get('ids')
            result['delete'] = dict(passed=deleted, errors=[e[-300:] for _, e in outputs if e], missing=after.get('missing'))
            ok = ok and deleted
        result['passed'] = ok
    finally:
        if cluster.real:
            result['real_nodes'] = cluster.waits   # seconds: start-up, and each wait for an epoch
        cluster.stop()
    return result


def run_ceremony(mode, texts):
    """--ceremony: the account is REGISTERED by the two nodes (CEREMONY.md), then used.
      A. keys for a new account, generated in the clear by the key tool (no network);
      B. `public_service_controller ceremony NODE_CONFIG NAME register` on both nodes: verification
         session, captcha and code (the local server's stubs), the password and recovery password
         made in the engines, `POST /v1/registration` with them inserted there. The number, the
         captcha and the keys are given to node 0 only, the code to node 1 only;
      C. `... certificate`: the authenticated socket opened with the two nodes' shares (so the
         server accepted the shared password), the sender certificate, the one-time prekeys;
      D. `... store`: the account's row on the database nodes;
      E. a new user signs up to the account: a receive session that has only the database row;
      F. a send session broadcasts to that user, who must decrypt.
    Checked besides: both nodes end with the same public account; the password (recombined HERE
    from the two share files, which no node can do) is 22 base64 characters and appears in no
    record or log of either node, in text, hex or inside the Basic credential."""
    import base64, re, secrets, shutil
    name, number = 'ceremony', '+120255501%02d' % (20 + secrets.randbelow(70))
    base = ROOT / '.deps/two-party-comparison'
    directory = STATE / 'ceremony'
    tool = HERE / 'provision/target/debug/lss-provision'
    controller = ROOT / '.lake/build/bin/public_service_controller'
    cluster = Cluster()
    result = dict(number=number)
    try:
        shutil.rmtree(directory, ignore_errors=True)
        directory.mkdir(parents=True)
        cluster.token(ACCOUNT)
        run(['lake', 'build', 'public_service_controller', 'ceremony_kernel_emitter'], cwd=ROOT, capture_output=True)
        sys.path.insert(0, str(ROOT / 'scripts'))
        from check_full_handshake import OPENSSL
        run(['c++', '-std=c++20', '-O2', '-I' + str(OPENSSL / 'include'), ROOT / 'handshake_backend/public_auth.cpp',
             '-L' + str(OPENSSL / 'lib'), '-lssl', '-lcrypto', '-o', directory / 'public_auth'])
        mp = base / 'data61-MP-SPDZ-113c4e4'
        for kind in ('send', 'receive'):
            (directory / f'worker-{kind}').mkdir()
            subprocess.run(['bash', str(mp / 'Scripts/setup-ssl.sh'), '2'], cwd=directory / f'worker-{kind}', stdout=subprocess.DEVNULL,
                           stderr=subprocess.STDOUT, check=True)
        nodes = [directory / f'node-{party}' / 'ceremony' for party in range(2)]
        for party in range(2):
            nodes[party].mkdir(parents=True)
            config = dict(
                party=party, state_directory=str(directory / f'node-{party}'), controller=str(controller),
                worker=dict(binary=str(base / ('tls-worker-sh-fixture-v3' if mode == 'semi-honest' else 'tls-worker-fixture-v3')),
                            send_directory=str(directory / 'worker-send'), receive_directory=str(directory / 'worker-receive'),
                            hosts=['127.0.0.1', '127.0.0.1'], port_base=23400),
                circuits=dict(tool=str(CACHE), manifest=None),
                signal=dict(endpoint='127.0.0.1', port=18443, hostname='server.example', trust_root=str(STATE / 'tls' / 'ca.pem'),
                            certificate_checker=str(directory / 'public_auth')),
                database=dict(client=str(cluster.BIN / 'handoff_client'), network=str(cluster.network),
                              key=str(cluster.config / f'compute-nodes/{party}/key.json')),
                test=dict(export=str(EXPORT), tokens=str(cluster.dir / 'tokens'), kem_tool=str(tool)),
                environment=dict(DYLD_LIBRARY_PATH=str(mp), TLS_WORKER_FIELD_BATCH='3000'))
            (directory / f'node-{party}.json').write_text(json.dumps(config, indent=1))
        # A. The operator's inputs: number, captcha and keys on node 0; the code on node 1.
        lss('ceremony-keys', name, nodes[0] / 'keys.json')
        (nodes[0] / 'number.txt').write_text(number + '\n')
        (nodes[0] / 'captcha.txt').write_text('signalcaptcha://noop.noop.registration.noop\n')
        (nodes[1] / 'code.txt').write_text('123456\n')

        def stage(label):
            started = time.monotonic()
            parties = [subprocess.Popen([str(controller), 'ceremony', str(directory / f'node-{party}.json'), name, label], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) for party in range(2)]
            outputs = [p.communicate(timeout=900) for p in parties]
            reports = [json.loads(out.strip().splitlines()[-1]) if out.strip() else {} for out, _ in outputs]
            good = all(p.returncode == 0 for p in parties) and all(r.get('passed') for r in reports)
            result[label] = dict(passed=good, seconds=round(time.monotonic() - started, 1), errors=[r.get('error') for r in reports if r.get('error')],
                                 stderr=[e[-300:] for _, e in outputs if e and not good])
            return good

        ok = stage('register') and stage('certificate')
        if ok:
            # Test-only check of what no node can do: recombine the password from both shares.
            shares = [bytes.fromhex((node / 'credentials.share').read_text().strip()) for node in nodes]
            recovery = [(node / 'recovery.share').read_text().strip() for node in nodes]
            password = bytes(a ^ b for a, b in zip(*shares))[16:].decode('latin-1')
            needles = [password, password.encode().hex(), base64.b64encode((number + ':' + password).encode()).decode()]
            leaked = [str(path) for path in directory.rglob('*') if path.is_file() and not path.name.endswith('.share')
                      and path.stat().st_size < 64 * 2 ** 20 and any(n.encode() in path.read_bytes() for n in needles)]
            accounts = [json.loads((node / 'account.json').read_text()) for node in nodes]
            checks = dict(
                password_is_22_base64_characters=bool(re.fullmatch(r'[A-Za-z0-9+/]{22}', password)),
                shares_differ=shares[0][16:] != shares[1][16:] and recovery[0] != recovery[1] and len(recovery[0]) == 64,
                same_public_account=accounts[0] == accounts[1] and accounts[0].get('number') == number and len(accounts[0].get('aci', '')) == 36,
                same_certificate=(nodes[0] / 'certificate.b64').read_text() == (nodes[1] / 'certificate.b64').read_text(),
                password_in_no_record_or_log=not leaked)
            result['checks'] = dict(checks, leaked=leaked)
            ok = all(checks.values())
        if ok:
            # The sessions' export (scaffolding): keys and public account, no password.
            lss('ceremony-finish', name, nodes[0])
            lss('export-mpc', name)
            export = json.loads(EXPORT.read_text())
            ok = stage('store')
        if ok:
            cluster.refresh()
            # E. A new user signs up; the receive session has only the database row.
            new = secrets.randbits(100)
            token = cluster.token(new).read_text().strip()
            lss('signup', 'newuser', '+12025550104', name, token)
            receive = run_mpc(export, mode, {}, party_env=lambda party: dict(
                cluster.env(party), SIGNAL_LOCAL_RECEIVE='1', SIGNAL_LOCAL_EXPECT='1', SIGNAL_LOCAL_KEM=str(tool)))
            signed_up = all(c.get('received') == [[str(new), token]] for c in receive['controllers'])
            result['receive'] = dict(passed=signed_up, contact=str(new), seconds=round(receive['elapsed_seconds'], 1), run=receive)
            ok = signed_up
        if ok:
            cluster.refresh()
            # F. An ordinary send session to that contact.
            request = cluster.request([new], 'broadcast')
            send = run_mpc(export, mode, texts, party_env=lambda party: dict(cluster.env(party, request), SIGNAL_LOCAL_EXTRA_CONTACTS=str(new)))
            good, recipients = verify({'newuser': texts[CONTACTS[0]]})
            result['send'] = dict(passed=good, recipients=recipients, seconds=round(send['elapsed_seconds'], 1), run=send)
            ok = good
        result['passed'] = bool(ok)
    finally:
        cluster.stop()
    return result


def run_app(export, mode):
    """--app: the application end to end, through the two node daemons and the application
    stand-in only (node_daemon/README.md). After the fixtures below, nothing here starts a
    controller or signs anything: `notify-app` does what an application server would.
      A. both daemons start; they keep a receive session running;
      B. the application issues a signup token for a new id; a new libsignal user sends it to the
         account; the application learns the id from both daemons;
      C. notify([the new id, two pre-provisioned contacts], a 200-byte text): all three decrypt
         it and both daemons report them delivered;
      D. the same again, every contact's state reloaded from the database nodes;
      E. delete([the new id]), with the database nodes' signatures checked by the application;
      F. notify to all three ids: the deleted one is reported unknown, the others are delivered.
    TEST fixtures (not the daemons' work): the account's row on the database nodes is created by
    a harness-run session from the export's credentials; the two pre-provisioned contacts are
    created on the database nodes from the export by the first notify, under tokens issued
    here; `refresh` stands for a database epoch passing."""
    import secrets, shutil, signal
    cluster = Cluster()
    result, daemons, logs = {}, [], []
    binaries = ROOT / 'node_daemon/target/debug'
    directory = STATE / 'app'
    tool = HERE / 'provision/target/debug/lss-provision'
    addresses = ['127.0.0.1:19700', '127.0.0.1:19701']

    def app(command, *args):
        started = time.monotonic()
        r = subprocess.run([str(binaries / 'notify-app'), command, *map(str, args), '--daemons', ','.join(addresses), '--db-client', cluster.BIN / 'handoff_client',
                            '--work', directory / 'application', '--key', cluster.config / 'app-server/notify-key.json',
                            '--app-config', cluster.config / 'app-server/config.json', '--network', cluster.network], capture_output=True, text=True)
        lines = r.stdout.strip().splitlines()
        return r.returncode == 0, json.loads(lines[-1]) if lines else {}, round(time.monotonic() - started, 1)

    def notify(label, contacts, text, expected, readers, absent=()):
        """One notify; `expected`: {id: result}; `readers` must decrypt the text, `absent` must not get it."""
        (directory / 'message.txt').write_text(text)
        good, report, seconds = app('notify', '--ids', ','.join(str(c) for c in contacts), '--message-file', directory / 'message.txt', '--timeout', 420)
        got = {r['id']: r['result'] for r in ((report.get('result') or {}).get('results') or [])}
        recipients = {}
        for name in list(readers) + list(absent):
            seen = receive(name, 4)
            attributed = [g for g in seen if g['envelope'].get('source_service_id') or g['envelope'].get('source_device')]
            has = text in [g['text'] for g in seen]
            recipients[name] = dict(received=len(seen), has_text=has, envelopes_with_source_fields=len(attributed),
                                    passed=(has == (name in readers)) and not attributed)
        passed = good and report.get('agreed') and got == {str(c): r for c, r in expected.items()} and all(r['passed'] for r in recipients.values())
        result[label] = dict(passed=bool(passed), seconds=seconds, results=got, expected={str(c): r for c, r in expected.items()},
                             agreed=report.get('agreed'), recipients=recipients, application=report)
        cluster.refresh()
        return bool(passed)

    try:
        ids = [int(c['contact_id_u128_hex'], 16) for c in export['contacts']]
        for contact in ids + [ACCOUNT]:
            cluster.token(contact)
        # TEST fixture: the account's row. A receive session with the export's credentials, split
        # between the parties, stores it and ends at once (it expects no message).
        credentials = bytes.fromhex(export['sender']['upgrade_credentials_hex'])
        share = secrets.token_bytes(len(credentials))
        shares = [share.hex(), bytes(a ^ b for a, b in zip(credentials, share)).hex()]
        fixture = run_mpc(export, mode, {}, party_env=lambda party: dict(
            cluster.env(party), SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT='0', SIGNAL_LOCAL_KEM=str(tool)))
        result['account_fixture'] = dict(seconds=round(fixture['elapsed_seconds'], 1), passed=True)
        cluster.refresh()
        # A. The daemons. What run_mpc prepared for its session is reused: the certificate checker
        # and the workers' key material (one directory per kind of session).
        run(['bash', ROOT / 'node_daemon/build.sh'])
        shutil.rmtree(directory, ignore_errors=True)
        directory.mkdir(parents=True)
        (directory / 'peer.key').write_text(secrets.token_hex(32))
        prepared = Path(fixture['logs'])
        for kind in ('send', 'receive'):
            shutil.copytree(prepared / 'work', directory / f'worker-{kind}')
        base = ROOT / '.deps/two-party-comparison'
        for party in range(2):
            config = dict(
                party=party, listen=addresses[party], peer=addresses[1 - party], peer_key_file=str(directory / 'peer.key'),
                state_directory=str(directory / f'node-{party}'), controller=str(ROOT / '.lake/build/bin/public_service_controller'),
                worker=dict(binary=str(base / ('tls-worker-sh-fixture-v3' if mode == 'semi-honest' else 'tls-worker-fixture-v3')),
                            send_directory=str(directory / 'worker-send'), receive_directory=str(directory / 'worker-receive'),
                            hosts=['127.0.0.1', '127.0.0.1'], port_base=23000),
                circuits=dict(tool=str(CACHE), manifest=os.environ.get('CIRCUIT_MANIFEST')),
                signal=dict(endpoint='127.0.0.1', port=18443, hostname='server.example', trust_root=str(STATE / 'tls' / 'ca.pem'),
                            certificate_checker=str(prepared / 'public_auth')),
                database=dict(client=str(cluster.BIN / 'handoff_client'), network=str(cluster.network),
                              key=str(cluster.config / f'compute-nodes/{party}/key.json')),
                test=dict(export=str(EXPORT), tokens=str(cluster.dir / 'tokens'), kem_tool=str(tool)),
                environment=dict(DYLD_LIBRARY_PATH=str(base / 'data61-MP-SPDZ-113c4e4'), TLS_WORKER_FIELD_BATCH='3000', CIRCUIT_CACHE_LOG=str(KERNEL_LOG)),
                timeouts=dict(send_seconds=360, send_seconds_per_id=30))
            (directory / f'node-{party}.json').write_text(json.dumps(config, indent=1))
            logs.append(open(directory / f'daemon-{party}.log', 'w'))
            daemons.append(subprocess.Popen([str(binaries / 'node-daemon'), str(directory / f'node-{party}.json')], cwd=ROOT,
                                            stdout=subprocess.PIPE, stderr=logs[-1], text=True))
        if not all(d.stdout.readline().startswith('listening') for d in daemons):
            raise RuntimeError('a node daemon did not start')
        # B. Signup.
        new = secrets.randbits(100)
        good, issued, _ = app('token', '--id', new)
        lss('signup', 'newuser', '+12025550104', 'sender', issued.get('token', ''))
        good, events, seconds = app('events', '--wait', 300, '--until-id', new)
        result['signup'] = dict(passed=good and events.get('signups') == [str(new)] and bool(events.get('agreed')), seconds=seconds, id=str(new),
                                signups=events.get('signups'))
        cluster.refresh()
        ok = result['signup']['passed']
        everyone, delivered = ids + [new], 'delivered'
        text = lambda label: (f'Application notify {label}: ' + 'x' * 200)[:200]
        # C, D.
        ok = ok and notify('notify', everyone, text('one'), {c: delivered for c in everyone}, CONTACTS + ['newuser'])
        ok = ok and notify('notify_reloaded', everyone, text('two'), {c: delivered for c in everyone}, CONTACTS + ['newuser'])
        if ok:
            # E.
            good, report, seconds = app('delete', '--ids', new, '--timeout', 120)
            result['delete'] = dict(passed=good and bool(report.get('agreed')) and report.get('evidence_verified') == [True, True], seconds=seconds,
                                    application=report)
            ok = result['delete']['passed']
        # F.
        ok = ok and notify('notify_after_delete', everyone, text('three'), {c: 'unknown contact' if c == new else delivered for c in everyone},
                           CONTACTS, absent=['newuser'])
        good, status, _ = app('status')
        result['daemons'] = status
        result['passed'] = bool(ok)
    finally:
        for d in daemons:
            d.send_signal(signal.SIGTERM)
        for d in daemons:
            try:
                d.wait(timeout=15)
            except subprocess.TimeoutExpired:
                d.kill()
        for log in logs:
            log.close()
        cluster.stop()
    return result


def run_multi_device(export, mode, texts):
    """A contact gets a second device after its state exists (contact keys and state on the
    database nodes, as in run_db):
      A. broadcast; the export's two contacts are created in the database, one device each;
      B. the first recipient links a second device (`lss-provision link`). Broadcast: the server
         answers the send to that contact 409. The session fetches the contact's prekey bundles
         (the response body is never revealed), establishes a session per device in the engines,
         stores the device list, and sends again with one message per device. BOTH devices must
         decrypt both broadcasts (the second one goes to the two devices directly);
      C. broadcast again in a new session, the device list read back from the database nodes.
         Both devices must decrypt again."""
    cluster = Cluster()
    result = {}
    try:
        ids = [int(c['contact_id_u128_hex'], 16) for c in export['contacts']]
        for contact in ids + [ACCOUNT]:
            cluster.token(contact)

        def step(label, expected):
            request = cluster.request(ids, 'broadcast')
            run = run_mpc(export, mode, texts, party_env=lambda party: cluster.env(party, request))
            good, recipients = verify(expected)
            result[label] = dict(run=run, recipients=recipients, passed=good)
            cluster.refresh()
            return good

        ok = step('created', texts)
        if ok:
            linked = json.loads(lss('link', CONTACTS[0], capture=True).strip().splitlines()[-1])
            result['linked'] = linked
            both = dict(texts, **{linked['linked']: texts[CONTACTS[0]]})
            ok = step('refreshed', both) and step('reloaded', both)
        result['passed'] = ok
    finally:
        cluster.stop()
    return result


# ---- Tor circuits (--circuits): the leader connects through a SOCKS5 proxy, one TLS connection
# per circuit. The proxy is scripts/socks5_test_proxy.py, never Tor. The controllers are given the
# server as SIGNAL_HOST, a reserved name (RFC 2606) that resolves nowhere: only the proxy can
# reach the server by it, so a session that passes made no direct connection and no lookup.
CIRCUIT_CONTACTS = ['recipient', 'recipient2', 'recipient3', 'recipient4']
SOCKS_PORT = 19050
SIGNAL_HOST = 'server.example'


class SocksProxy:
    def __init__(self):
        self.log = STATE / 'socks-proxy.jsonl'
        self.log.write_text('')
        self.process = subprocess.Popen([sys.executable, str(SCRIPTS / 'socks5_test_proxy.py'), str(SOCKS_PORT), str(self.log),
                                         f'{SIGNAL_HOST}:18443=127.0.0.1:18443'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        if not self.process.stdout.readline().startswith('listening'):
            raise RuntimeError('SOCKS test proxy did not start')

    @staticmethod
    def env(circuits):
        return dict(SIGNAL_TOR_SOCKS=f'127.0.0.1:{SOCKS_PORT}', SIGNAL_TOR_CIRCUITS=str(circuits))

    def command(self, line):
        self.process.stdin.write(line + '\n')
        self.process.stdin.flush()
        self.process.stdout.readline()

    def rows(self):
        return [json.loads(line) for line in self.log.read_text().splitlines() if line.strip()]

    def session(self, username):
        """This session's opened connections, each with its close record (waits for them)."""
        for _ in range(40):
            rows = [r for r in self.rows() if r.get('username') == username]
            opened = [r for r in rows if r['event'] == 'open']
            closed = {r['id']: r for r in rows if r['event'] == 'close'}
            if all(r['id'] in closed for r in opened):
                break
            time.sleep(0.5)
        return [dict(r, close=closed.get(r['id'], {})) for r in opened]

    def stop(self):
        self.process.kill()
        self.process.wait()


def check_circuits(proxy, run, circuits, contacts):
    """What the proxy saw of one send session, against the controllers' public report."""
    import collections
    cases = run['controllers']
    labels = cases[0].get('circuit_labels') or [[None, None]]
    connections = proxy.session(labels[0][0])
    sends = [(contact, int(index)) for contact, index in cases[0].get('circuit_sends', [])]
    by_contact = collections.defaultdict(set)
    for contact, index in sends:
        by_contact[contact].add(index)
    expected = [password for _, password in labels]
    per_circuit = collections.Counter(index for _, index in sends)
    records = {c['password']: c['close'].get('up_records', {}).get('23', 0) for c in connections}
    checks = dict(
        both_controllers_agree=all(c.get('circuit_sends') == cases[0].get('circuit_sends') and c.get('circuit_labels') == labels for c in cases),
        every_connection_through_the_proxy_by_hostname=len(connections) == circuits and all(
            c['atyp'] == 3 and c['host'] == SIGNAL_HOST and c['port'] == 18443 for c in connections),
        nothing_refused=not [r for r in proxy.rows() if r['event'] == 'refused'],
        distinct_credentials=len(set(expected)) == circuits and sorted(c['password'] for c in connections) == sorted(expected),
        each_contact_on_one_circuit=len(by_contact) == contacts and all(len(v) == 1 for v in by_contact.values()),
        circuits_carrying_sends=len(per_circuit) == min(circuits, contacts),
        # Each send is one client record; besides them each connection carries its Finished and upgrade request.
        records_cover_sends=all(records.get(expected[index], 0) >= 2 + count for index, count in per_circuit.items()),
    )
    return dict(passed=all(checks.values()), checks=checks, sends_per_circuit=dict(per_circuit),
                connections=[dict(password=c['password'], application_records=records.get(c['password']), up_bytes=c['close'].get('up_bytes'),
                                  down_bytes=c['close'].get('down_bytes')) for c in connections])


def circuit_export():
    """New accounts and four contacts, so that three circuits each carry a contact and one carries two."""
    lss('provision')
    for name, number in [('recipient3', '+12025550106'), ('recipient4', '+12025550107')]:
        lss('register', name, number)
        lss('establish', 'sender', name)
    lss('export-mpc', 'sender', *CIRCUIT_CONTACTS)
    return json.loads(EXPORT.read_text())


def run_circuits(mode, texts, counts, db):
    """Broadcast sessions through the SOCKS test proxy with N circuits for each N in `counts`,
    contact state in the store (or on the database nodes with `db`). Each must pass
    `check_circuits`, and every recipient must decrypt everything. Without `db` also a receive
    session through the proxy (its own single circuit). With `db` also a dropped circuit: the
    proxy closes a send connection mid-broadcast; the session must fail cleanly in both parties,
    and a new session must then deliver everything (each contact's state was stored before its
    message left, so nothing is sent twice under the same key)."""
    import shutil, secrets
    export = circuit_export()
    texts = {name: texts[CONTACTS[0]] for name in CIRCUIT_CONTACTS}
    shutil.rmtree(STORE, ignore_errors=True)
    proxy = SocksProxy()
    cluster = Cluster() if db else None
    result, ok = dict(database=db), True
    try:
        ids = [int(c['contact_id_u128_hex'], 16) for c in export['contacts']]
        if cluster:
            for contact in ids + [ACCOUNT]:
                cluster.token(contact)

        def session(circuits, during=None, extra=None):
            request = cluster.request(ids, 'broadcast') if cluster else None
            return run_mpc(export, mode, texts, during=during, endpoint=SIGNAL_HOST, party_env=lambda party: dict(
                cluster.env(party, request) if cluster else {}, **SocksProxy.env(circuits), **(extra or {})))

        for circuits in counts:
            run = session(circuits)
            good, recipients = verify(texts)
            seen = check_circuits(proxy, run, circuits, len(ids))
            result[f'circuits_{circuits}'] = dict(run=run, recipients=recipients, proxy=seen, passed=good and seen['passed'])
            ok = ok and good and seen['passed']
            if cluster:
                cluster.refresh()
        if ok and not db:
            # The authenticated socket: one connection, on a circuit of its own.
            credentials = bytes.fromhex(export['sender']['upgrade_credentials_hex'])
            share = secrets.token_bytes(len(credentials))
            shares = [share.hex(), bytes(a ^ b for a, b in zip(credentials, share)).hex()]

            def during(processes):
                deadline = time.monotonic() + 8
                while time.monotonic() < deadline and all(p.poll() is None for p in processes):
                    time.sleep(1)
                if all(p.poll() is None for p in processes):
                    lss('send', CONTACTS[0], 'sender', 'to the MPC client through the proxy')
            circuits = max(counts)
            run = run_mpc(export, mode, {}, during=during, endpoint=SIGNAL_HOST, party_env=lambda party: dict(
                SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT='1', **SocksProxy.env(circuits)))
            username = (run['controllers'][0].get('circuit_labels') or [[None]])[0][0]
            connections = proxy.session(username)
            good = all(c.get('messages_delivered') == 1 for c in run['controllers']) and len(connections) == 1 and \
                connections[0]['password'] == 'receive' and connections[0]['host'] == SIGNAL_HOST and connections[0]['atyp'] == 3
            result['receive'] = dict(run=run, connections=[dict(password=c['password'], host=c['host']) for c in connections], passed=good)
            ok = ok and good
        if ok and db:
            circuits = max(counts)
            dropped = f'send-{min(1, circuits - 1)}-of-{circuits}'
            # Its Finished, its upgrade request, then the first send on it: dropped right after that.
            proxy.command(f'drop-after {dropped} 3')
            started = time.monotonic()
            try:
                # Without recovery (SIGNAL_RECOVERY=0): the session must end cleanly in both parties.
                # With it the connection is replaced and the session passes: `--recovery drop`.
                failed = session(circuits, extra=dict(SIGNAL_RECOVERY='0'))
                failed_cleanly = False   # it should not have passed
            except RuntimeError as e:
                failed = json.loads(str(e).split(': ', 1)[1])
                failed_cleanly = all(code != 0 for code in failed['exit_codes']) and len(failed['controllers']) == 2 and \
                    all(not c['passed'] and c['error'] for c in failed['controllers'])
            elapsed = time.monotonic() - started
            username = ((failed.get('controllers') or [{}])[0].get('circuit_labels') or [[None]])[0][0]
            was_dropped = any(c['close'].get('dropped') for c in proxy.session(username))
            cluster.refresh()
            run = session(circuits)
            good, recipients = verify(texts)
            seen = check_circuits(proxy, run, circuits, len(ids))
            result['dropped_circuit'] = dict(failed_run=failed, failed_cleanly=failed_cleanly, dropped=was_dropped, failure_seconds=elapsed,
                                             errors=[c.get('error') for c in failed.get('controllers', [])], rerun=run, recipients=recipients,
                                             proxy=seen, passed=failed_cleanly and was_dropped and good and seen['passed'])
            ok = ok and result['dropped_circuit']['passed']
        result['passed'] = ok
    finally:
        proxy.stop()
        if cluster:
            cluster.stop()
    return result


# ---- Recovery (--recovery STAGE,...): failures as per-contact results (PRODUCT_TODO.md sections 3
# and 4; handshake_backend/EmpHybridWork/PublicServiceController.lean, `Recovery` and `deliver`).
# Every stage has its own accounts and database nodes and runs these sessions, each of two
# broadcasts to every contact:
#   created   the contacts are created on the database nodes;
#   fault     something goes wrong for some contacts (below), usually between the two broadcasts:
#             the controllers pause there on request (SIGNAL_LOCAL_PAUSE_AFTER, a test hook);
#   after     a plain session. It shows the state left on the database nodes is consistent.
# Required of every session: both controllers end normally with the same per-id results, those
# results are the expected ones, and each recipient decrypts what was reported delivered.
D, RF, IC = 'delivered', 'delivered after device refresh', 'delivered after identity change'
RL, NS, FAULT = 'retry later', 'needs re-signup', 'fault'
TEXTS = ['MPC broadcast one', 'MPC broadcast two ☕']
FAULT_PLAIN, FAULT_TLS = 18090, 18444
RECOVERY_STAGES = ['classify', 'devices', 'refresh-retry', 'identity', 'unauthorized', 'drop', 'throttle', 'bundle-fault', 'resume']


def wait_for(path, text, processes, seconds=400):
    """Wait until `text` is in the file (a party's log); False if a party exits first."""
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        if path.exists() and text in path.read_text(errors='replace'):
            return True
        if any(p.poll() is not None for p in processes):
            return False
        time.sleep(0.2)
    return False


def mid(inject, marker='recovery: TEST pause'):
    """A `during_logs` callback: run `inject` once the controllers reach `marker`."""
    def during(processes, output):
        if wait_for(output / 'party-0.log', marker, processes):
            inject(processes, output)
    return during


class FaultProxy:
    """scripts/fault_proxy.py behind a second TLS terminator (port FAULT_TLS): a session pointed
    there has chosen requests answered by the proxy instead of the server."""
    def __init__(self):
        import socket
        self.log = STATE / 'fault-proxy.jsonl'
        self.log.write_text('')
        self.process = subprocess.Popen([sys.executable, str(SCRIPTS / 'fault_proxy.py'), str(FAULT_PLAIN), str(self.log)],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        if not self.process.stdout.readline().startswith('listening'):
            raise RuntimeError('fault proxy did not start')
        self.terminator = subprocess.Popen([sys.executable, '-I', str(SCRIPTS / 'tls_terminator.py'), '--cert', str(STATE / 'tls/server.pem'),
                                            '--key', str(STATE / 'tls/server.key'), '--listen', str(FAULT_TLS), '--backend',
                                            f'127.0.0.1:{FAULT_PLAIN}', '--require-aes128'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(100):
            try:
                socket.create_connection(('127.0.0.1', FAULT_TLS), timeout=1).close()
                return
            except OSError:
                time.sleep(0.1)
        raise RuntimeError('second TLS terminator did not start')

    def command(self, line):
        self.process.stdin.write(line + '\n')
        self.process.stdin.flush()
        self.process.stdout.readline()

    def rows(self):
        return [json.loads(line) for line in self.log.read_text().splitlines() if line.strip()]

    def stop(self):
        for p in (self.process, self.terminator):
            p.kill()
            p.wait()


class Recovery:
    def __init__(self, mode, names=('recipient', 'recipient2')):
        self.mode, self.names = mode, list(names)
        lss('provision')
        if 'recipient3' in self.names:
            lss('register', 'recipient3', '+12025550106')
            lss('establish', 'sender', 'recipient3')
        lss('export-mpc', 'sender', *self.names)
        self.export = json.loads(EXPORT.read_text())
        self.aci = {name: json.loads((STATE / 'accounts' / f'{name}.json').read_text())['aci'] for name in self.names}
        by_aci = {c['recipient_aci']: int(c['contact_id_u128_hex'], 16) for c in self.export['contacts']}
        self.id_of = {name: by_aci[self.aci[name]] for name in self.names}
        self.ids = list(self.id_of.values())
        self.cluster = Cluster()
        for contact in self.ids + [ACCOUNT]:
            self.cluster.token(contact)
        self.pause = dict(SIGNAL_LOCAL_PAUSE_AFTER=f'{len(self.ids)}:16000')   # after the first broadcast
        self.early = {}

    def drain(self, *names):
        """Receive what is queued for these accounts now (it counts towards the next `check`). To be
        done before a test step that opens an account's own socket: the provisioning tool's
        other commands acknowledge and discard what the server delivers to them."""
        for name in names:
            self.early.setdefault(name, []).extend(g['text'] for g in receive(name, 2))

    def session(self, env=None, during=None, endpoint='127.0.0.1', port=18443):
        request = self.cluster.request(self.ids, 'broadcast')
        try:
            return run_mpc(self.export, self.mode, {}, during_logs=during, endpoint=endpoint, server_port=port,
                           party_env=lambda party: dict(self.cluster.env(party, request), **(env(party) if callable(env) else (env or {}))))
        finally:
            self.cluster.refresh()

    def check(self, run, expected, received, events=(), exactly=False):
        """expected: {name: [result of message 0, of message 1]}; received: {account: [texts]} that
        must have been decrypted (`exactly`: and nothing else); events: texts the controllers'
        public recovery log must contain."""
        cases = run['controllers']
        rows = cases[0].get('results', [])
        got = {name: [r['result'] for r in sorted(rows, key=lambda r: r['message']) if r['id'] == str(self.id_of[name])] for name in self.names}
        log = cases[0].get('recovery', [])
        recipients, delivered = {}, True
        for name, texts in received.items():
            try:
                seen = receive(name, 4)
            except subprocess.CalledProcessError:
                seen = []   # the device no longer exists (unlinked): what it received earlier counts
            attributed = [g for g in seen if g['envelope'].get('source_service_id') or g['envelope'].get('source_device')]
            found = self.early.pop(name, []) + [g['text'] for g in seen]
            good = all(t in found for t in texts) and not attributed and (not exactly or sorted(found) == sorted(texts))
            recipients[name] = dict(received=found, expected=texts, duplicates=len(found) - len(set(found)), passed=good)
            delivered = delivered and good
        checks = dict(results_as_expected=got == expected,
                      both_controllers_agree=all(c.get('results') == rows and c.get('recovery_used') for c in cases),
                      no_session_abort=all(c.get('passed') and not c.get('error') for c in cases) and not run['rejections'],
                      recipients_decrypted=delivered,
                      events_seen=all(any(e in line for line in log) for e in events))
        return dict(passed=all(checks.values()), checks=checks, results=got, expected=expected, reasons=[r['reason'] for r in rows if r['reason']],
                    recovery=log, recipients=recipients, seconds=round(run['elapsed_seconds'], 1))

    def stop(self):
        self.cluster.stop()


def finish(out):
    out['passed'] = all(v.get('passed') for v in out.values() if isinstance(v, dict) and 'passed' in v)
    return out


def stage_classify(mode):
    """The controller's own unit check: the classification table, back-off, and the response
    parser on 429 (with Retry-After), 503 and 409 responses."""
    r = subprocess.run([str(ROOT / '.lake/build/bin/public_service_controller'), 'recovery-check'], capture_output=True, text=True)
    return dict(json.loads(r.stdout.strip().splitlines()[0]) if r.stdout.strip() else {}, exit_code=r.returncode,
                passed=r.returncode == 0)


def stage_devices(mode):
    """A device is linked, then removed, each in the middle of a session: 409, refresh, resend."""
    r, out = Recovery(mode), {}
    both = {'recipient': [D, D], 'recipient2': [D, D]}
    try:
        out['created'] = r.check(r.session(), both, {'recipient': TEXTS, 'recipient2': TEXTS})
        run = r.session(env=r.pause, during=mid(lambda *_: (r.drain('recipient'), lss('link', 'recipient'))))
        out['linked'] = r.check(run, {'recipient': [D, RF], 'recipient2': [D, D]},
                                {'recipient': TEXTS, 'recipient.2': TEXTS[1:], 'recipient2': TEXTS}, events=['answered 409'])
        run = r.session(env=r.pause, during=mid(lambda *_: (r.drain('recipient', 'recipient.2'), lss('unlink', 'recipient', '2'))))
        out['unlinked'] = r.check(run, {'recipient': [D, RF], 'recipient2': [D, D]},
                                  {'recipient': TEXTS, 'recipient.2': TEXTS[:1], 'recipient2': TEXTS},
                                  events=['1 sessions established'])
        out['after'] = r.check(r.session(), both, {'recipient': TEXTS, 'recipient2': TEXTS})
    finally:
        r.stop()
    return finish(out)


def stage_refresh_retry(mode):
    """The device list changes again between the refresh and the resend (a second 409): the
    refresh is repeated. The controllers pause after storing the first refresh (test hook)."""
    r, out = Recovery(mode), {}
    both = {'recipient': [D, D], 'recipient2': [D, D]}

    def inject(processes, output):
        r.drain('recipient')
        lss('link', 'recipient')                                           # device 2: the next send gets 409
        if wait_for(output / 'party-0.log', '2 sessions established', processes):
            lss('link', 'recipient')                                       # device 3, before the resend: 409 again
    try:
        out['created'] = r.check(r.session(), both, {'recipient': TEXTS, 'recipient2': TEXTS})
        run = r.session(env=dict(r.pause, SIGNAL_LOCAL_PAUSE_REFRESH='9000'), during=mid(inject))
        out['second_mismatch'] = r.check(run, {'recipient': [D, RF], 'recipient2': [D, D]},
                                         {'recipient': TEXTS, 'recipient.2': TEXTS[1:], 'recipient.3': TEXTS[1:], 'recipient2': TEXTS},
                                         events=['refresh 2', '3 sessions established'])
        out['after'] = r.check(r.session(), both, {'recipient': TEXTS, 'recipient.2': TEXTS, 'recipient.3': TEXTS, 'recipient2': TEXTS})
    finally:
        r.stop()
    return finish(out)


def stage_identity(mode):
    """A contact registers again (new identity key, same account id and access key): accepted,
    sessions replaced, reported. The message sent before it went to the old installation."""
    r, out = Recovery(mode), {}
    both = {'recipient': [D, D], 'recipient2': [D, D]}
    try:
        out['created'] = r.check(r.session(), both, {'recipient': TEXTS, 'recipient2': TEXTS})
        run = r.session(env=r.pause, during=mid(lambda *_: (r.drain('recipient'), lss('reregister', 'recipient'))))
        out['reregistered'] = r.check(run, {'recipient': [D, IC], 'recipient2': [D, D]}, {'recipient': TEXTS, 'recipient2': TEXTS},
                                      events=['under a new identity key'])
        out['after'] = r.check(r.session(), both, {'recipient': TEXTS, 'recipient2': TEXTS})
    finally:
        r.stop()
    return finish(out)


def stage_unauthorized(mode):
    """A contact's profile key changes, and its access key with it: sealed sends get 401 and the
    contact is reported as needing to sign up again, in that session and in the next.
    (A deleted account cannot be run here: the local server answers 500 to DELETE /v1/accounts/me,
    its configuration has no address for a service that deletion calls. By the server's source a
    sealed send to an account that no longer exists is answered 401 as well, not 404:
    OptionalAccess.verify. An injected 404 is in the `throttle` stage.)"""
    r, out = Recovery(mode), {}

    def inject(*_):
        r.drain('recipient')
        lss('rotate-access', 'recipient')
    try:
        every = {name: [D, D] for name in r.names}
        out['created'] = r.check(r.session(), every, {name: TEXTS for name in r.names})
        run = r.session(env=r.pause, during=mid(inject))
        out['rotated'] = r.check(run, {'recipient': [D, NS], 'recipient2': [D, D]}, {'recipient': TEXTS[:1], 'recipient2': TEXTS}, exactly=True)
        out['after'] = r.check(r.session(), {'recipient': [NS, NS], 'recipient2': [D, D]}, {'recipient': [], 'recipient2': TEXTS}, exactly=True)
    finally:
        r.stop()
    return finish(out)


def stage_drop(mode):
    """A circuit is dropped right after a send left on it (through the SOCKS test proxy, two
    circuits): that connection is replaced and the send repeated; the other connection is kept.
    The recipient may get that text twice (the server had received the first copy)."""
    r, out = Recovery(mode), {}
    proxy = SocksProxy()
    both = {'recipient': [D, D], 'recipient2': [D, D]}
    via = dict(endpoint=SIGNAL_HOST, env=SocksProxy.env(2))
    try:
        out['created'] = r.check(r.session(**via), both, {'recipient': TEXTS, 'recipient2': TEXTS})
        proxy.command('drop-after send-1-of-2 3')   # its Finished, its upgrade request, its first send
        run = r.session(**via)
        username = (run['controllers'][0].get('circuit_labels') or [[None]])[0][0]
        connections = proxy.session(username)
        out['dropped'] = r.check(run, both, {'recipient': TEXTS, 'recipient2': TEXTS}, events=['connection 1 was closed and replaced'])
        out['dropped']['proxy'] = dict(connections=[c['password'] for c in connections], dropped=[c['password'] for c in connections if c['close'].get('dropped')])
        out['dropped']['passed'] = out['dropped']['passed'] and out['dropped']['proxy']['dropped'] == ['send-1-of-2'] and len(connections) == 3
        out['after'] = r.check(r.session(**via), both, {'recipient': TEXTS, 'recipient2': TEXTS}, exactly=True)
    finally:
        proxy.stop()
        r.stop()
    return finish(out)


def stage_throttle(mode):
    """429, 503 and 404, injected by scripts/fault_proxy.py (the local server has no switch for
    them): one contact's first send is answered 429 with Retry-After and is delivered on the
    retry; another's sends are all answered 503 and end as "retry later" after the bounded
    retries; a third's are answered 404 and it is reported "gone". Then, directly: everyone is
    delivered (the state stored for the sends that never arrived is consistent)."""
    r, out = Recovery(mode, ('recipient', 'recipient2', 'recipient3')), {}
    proxy = FaultProxy()
    every = {name: [D, D] for name in r.names}
    try:
        out['created'] = r.check(r.session(), every, {name: TEXTS for name in r.names})
        proxy.command(f'answer 429 1 0 /v1/messages/{r.aci["recipient"]} 2')
        proxy.command(f'answer 503 99 0 /v1/messages/{r.aci["recipient2"]}')
        proxy.command(f'answer 404 99 0 /v1/messages/{r.aci["recipient3"]}')
        run = r.session(port=FAULT_TLS)
        out['throttled'] = r.check(run, {'recipient': [D, D], 'recipient2': [RL, RL], 'recipient3': ['gone', 'gone']},
                                   {'recipient': TEXTS, 'recipient2': [], 'recipient3': []}, exactly=True,
                                   events=['answered 429, retry 1 in 2000 ms', 'answered 503, retry 3 in 9000 ms', 'after 3 retries', 'answered 404'])
        out['throttled']['injected'] = [row['status'] for row in proxy.rows() if row['action'] == 'answer']
        out['after'] = r.check(r.session(), every, {name: TEXTS for name in r.names}, exactly=True)
    finally:
        proxy.stop()
        r.stop()
    return finish(out)


def stage_bundle_fault(mode):
    """A prekey response that is not a bundle, and one that is well formed but does not verify
    (both from scripts/fault_proxy.py): fault, nothing stored. Then, directly: the same contacts
    are refreshed from the real bundles and delivered, so their state was left as it was."""
    r, out = Recovery(mode, ('recipient', 'recipient2', 'recipient3')), {}
    proxy = FaultProxy()
    every = {name: [D, D] for name in r.names}

    def inject(*_):
        r.drain('recipient', 'recipient3')
        lss('link', 'recipient')
        lss('link', 'recipient3')
    try:
        out['created'] = r.check(r.session(), every, {name: TEXTS for name in r.names})
        proxy.command(f'garbage 1 0 /v2/keys/{r.aci["recipient"]} 2600')
        proxy.command(f'forged 1 0 /v2/keys/{r.aci["recipient3"]}')
        run = r.session(env=r.pause, during=mid(inject), port=FAULT_TLS)
        out['bad_bundles'] = r.check(run, {'recipient': [D, FAULT], 'recipient2': [D, D], 'recipient3': [D, FAULT]},
                                     {'recipient': TEXTS[:1], 'recipient2': TEXTS, 'recipient3': TEXTS[:1], 'recipient.2': [], 'recipient3.2': []},
                                     exactly=True, events=['is not a bundle', 'did not verify'])
        out['bad_bundles']['injected'] = [row['action'] for row in proxy.rows() if row['action'] != 'forwarded']
        out['after'] = r.check(r.session(), {'recipient': [RF, D], 'recipient2': [D, D], 'recipient3': [RF, D]},
                               {'recipient': TEXTS, 'recipient.2': TEXTS, 'recipient2': TEXTS, 'recipient3': TEXTS, 'recipient3.2': TEXTS})
    finally:
        proxy.stop()
        r.stop()
    return finish(out)


def stage_resume(mode):
    """A session dies in the middle of a notify (one party's controller is killed after the first
    broadcast). A new session for the same notify (SIGNAL_NOTIFY_ID, each party's journal) reloads
    the contacts from the database nodes, does not resend what both journals show as settled, and
    sends the rest."""
    import secrets
    r, out = Recovery(mode), {}
    both = {'recipient': [D, D], 'recipient2': [D, D]}
    notify = 'notify-' + secrets.token_hex(4)
    journals = [STATE / f'notify-journal-{party}.jsonl' for party in range(2)]
    for path in journals:
        path.write_text('')
    env = lambda party: dict(r.pause, SIGNAL_NOTIFY_ID=notify, SIGNAL_NOTIFY_JOURNAL=str(journals[party]))

    def lose_party(processes, output):
        # The whole node goes: its worker, then its controller. (Killing the controller alone
        # leaves its worker alive and the other party waiting on it: the link between the workers
        # has no timeout, PRODUCT_TODO.md section 4.)
        children = subprocess.run(['pgrep', '-P', str(processes[1].pid)], capture_output=True, text=True).stdout.split()
        for pid in children:
            os.kill(int(pid), 9)
        processes[1].kill()
    try:
        out['created'] = r.check(r.session(), both, {'recipient': TEXTS, 'recipient2': TEXTS})
        try:
            r.session(env=env, during=mid(lose_party))
            died = dict(passed=False, error='the session should have failed')
        except RuntimeError as e:
            failed = json.loads(str(e).split(': ', 1)[1])
            lines = [len(path.read_text().splitlines()) for path in journals]
            died = dict(passed=lines == [2, 2] and any(code != 0 for code in failed['exit_codes']), journal_lines=lines,
                        exit_codes=failed['exit_codes'], errors=[c.get('error') for c in failed.get('controllers', [])])
        out['session_killed'] = died
        run = r.session(env=lambda party: dict(SIGNAL_NOTIFY_ID=notify, SIGNAL_NOTIFY_JOURNAL=str(journals[party])))
        # Across the killed session and this one: every text exactly once.
        out['resumed'] = r.check(run, both, {'recipient': TEXTS, 'recipient2': TEXTS}, exactly=True,
                                 events=['2 results settled by an earlier session'])
        out['resumed']['passed'] = out['resumed']['passed'] and out['resumed']['reasons'].count('settled by an earlier session of this notify') == 2
        out['after'] = r.check(r.session(), both, {'recipient': TEXTS, 'recipient2': TEXTS}, exactly=True)
    finally:
        r.stop()
    return finish(out)


STAGES = {'classify': stage_classify, 'devices': stage_devices, 'refresh-retry': stage_refresh_retry, 'identity': stage_identity,
          'unauthorized': stage_unauthorized, 'drop': stage_drop, 'throttle': stage_throttle, 'bundle-fault': stage_bundle_fault,
          'resume': stage_resume}


def run_recovery(mode, stages):
    result = {}
    for stage in stages:
        try:
            result[stage] = STAGES[stage](mode)
        except Exception as e:
            result[stage] = dict(passed=False, error=f'{type(e).__name__}: {e}'[:2000])
    result['passed'] = all(result[stage].get('passed') for stage in stages)
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
    p.add_argument('--real-db', action='store_true', help='the database nodes are the REAL node binary (five `server` processes on a private '
                   'Postgres instance, with consensus and epochs; scripts/start_db_nodes.py) instead of the in-memory test node')
    p.add_argument('--multi-device', action='store_true', help='also link a second device to a contact and require both devices to decrypt (database nodes)')
    p.add_argument('--app', action='store_true', help='also the application end to end through the node daemons and the application stand-in '
                   '(node_daemon/; --runs 0 --app runs only this): signup, notify, notify again, delete, notify')
    p.add_argument('--ceremony', action='store_true', help='also REGISTER a new account in two-party sessions (CEREMONY.md: the password is '
                   'made and used only inside the engines), store it on the database nodes, then receive a signup and send with it '
                   '(--runs 0 --ceremony runs only this)')
    p.add_argument('--recovery', default='', help='fault-injection stages, comma separated, each with its own accounts and database nodes '
                   '(--runs 0 --recovery devices runs only that one): ' + ', '.join(RECOVERY_STAGES))
    p.add_argument('--broadcasts', type=int, default=2, help='broadcasts per send session (more than 2: to measure the cost per message)')
    p.add_argument('--trace', action='store_true', help='controllers log the server bytes they reveal (public) to their logs')
    p.add_argument('--circuits', default='', help='also broadcast through the SOCKS test proxy with N Tor circuits, for each N of a '
                   'comma-separated list (e.g. 1,3); with --db the contacts are on the database nodes and a dropped circuit is tested')
    p.add_argument('--circuits-db', action='store_true', help='the --circuits stage on the database nodes without the rest of --db '
                   '(e.g. --runs 0 --circuits 3 --circuits-db runs only that stage)')
    p.add_argument('--strict', action='store_true', help='produce the circuit manifest of deployment.json first (scripts/produce_circuits.py), '
                   'then run every session in strict mode: only circuits of the manifest, none produced while connected; a refused '
                   'name fails the run (it is a gap in the inventory, CIRCUIT_SHAPES.md)')
    p.add_argument('--strict-produced', action='store_true', help='--strict with the manifest already in state/circuits: nothing is produced')
    p.add_argument('--profile', choices=['legacy', 'libsignal'], help='SIGNAL_CLIENT_PROFILE for every session (what the server sees; '
                   'handshake_backend/EmpHybridWork/CLIENT_FINGERPRINT.md)')
    p.add_argument('--fingerprint', action='store_true', help='also a send and a receive session through the capturing terminator '
                   '(scripts/fingerprint_terminator.py, port 18445), checked against the official client\'s reference '
                   '(fingerprint/check_fingerprint.py); implies --profile libsignal unless --profile is given')
    p.add_argument('--link-delay-ms', type=float, default=0.0, help='TEST: every link between the two workers goes through '
                   'scripts/delay_relay.cpp, which delays each direction by this much (round trip = twice this); 1 for a 2 ms round trip')
    p.add_argument('--hinted', action='store_true', help='TLS_WORKER_HINTED=1 for every session: the constant-depth curve programs, '
                   'and contacts prepared in batches (PERFORMANCE.md, "Rounds")')
    p.add_argument('--field-direct', action='store_true', help='TLS_WORKER_FIELD_DIRECT=1 for every session: the field engine\'s '
                   'openings sent by both workers at once (one message delay per round instead of two)')
    a = p.parse_args()
    if a.link_delay_ms > 0:
        run(['c++', '-std=c++17', '-O2', '-pthread', ROOT / 'scripts/delay_relay.cpp', '-o', ROOT / '.deps/two-party-comparison/delay-relay'])
        os.environ['SIGNAL_LINK_DELAY_MS'] = str(a.link_delay_ms)
    if a.hinted:
        os.environ['TLS_WORKER_HINTED'] = '1'
    if a.field_direct:
        os.environ['TLS_WORKER_FIELD_DIRECT'] = '1'
    if a.fingerprint and not a.profile:
        a.profile = 'libsignal'
    if a.profile:
        os.environ['SIGNAL_CLIENT_PROFILE'] = a.profile
    a.strict = a.strict or a.strict_produced
    Cluster.REAL = a.real_db
    if a.trace:
        os.environ['SIGNAL_LOCAL_TRACE'] = '1'
    os.environ['SIGNAL_LOCAL_BROADCASTS'] = str(max(2, a.broadcasts))
    report = dict(passed=False, mode=a.mode, started=time.time())
    try:
        if not a.skip_build and not (STATE / 'classpath.txt').exists():
            run(['bash', SCRIPTS / 'build_server.sh'])
        if a.strict:
            report['strict'] = strict_manifest(not a.strict_produced)
        else:
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
        if a.broadcasts >= 3:
            for name in CONTACTS:
                texts[name] = texts[name] + ['MPC broadcast 3 ' + 'x' * 184]   # 200 bytes: a larger size class
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
        if ok and a.fingerprint:
            report['fingerprint'] = run_fingerprint(export, a.mode, texts)
            ok = report['fingerprint']['passed']
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
        if ok and a.multi_device:
            if a.runs or a.signup or a.db:
                # As for --db: this flow starts from an export, with one device per contact.
                lss('provision')
                lss('export-mpc')
                export = json.loads(EXPORT.read_text())
            report['multi_device'] = run_multi_device(export, a.mode, texts)
            ok = report['multi_device']['passed']
        if ok and a.app:
            if a.runs or a.signup or a.db or a.multi_device:
                # As for --db: this flow starts from an export.
                lss('provision')
                lss('export-mpc')
                export = json.loads(EXPORT.read_text())
            report['app'] = run_app(export, a.mode)
            ok = report['app']['passed']
        if ok and a.ceremony:
            # Its own account, registered by the two nodes; it replaces the export.
            report['ceremony'] = run_ceremony(a.mode, texts)
            ok = report['ceremony']['passed']
        if ok and a.circuits:
            # Its own accounts and export (four contacts); runs last.
            report['tor_circuits'] = run_circuits(a.mode, texts, [int(n) for n in a.circuits.split(',')], a.db or a.circuits_db)
            ok = report['tor_circuits']['passed']
        if ok and a.recovery:
            # Each stage provisions its own accounts.
            report['recovery'] = run_recovery(a.mode, a.recovery.split(','))
            ok = report['recovery']['passed']
        if a.strict:
            # A name a session asked for outside the manifest (the session went on without it or failed).
            report['strict']['refused'] = kernel_lines(REFUSED)
            ok = ok and not report['strict']['refused']
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
