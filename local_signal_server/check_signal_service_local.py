#!/usr/bin/env python3
"""Signal service path of the MPC client against the LOCAL Signal-Server (not Signal's service).

Counterpart of handshake_backend/EmpHybridWork/check_signal_service_v3.py, which runs the client
against an in-process fake. Stages:
  1. build (once) and start the local server + TLS terminator      scripts/build_server.sh, start_server.sh
  2. provision sender + two recipients with established sessions   lss-provision provision
  3. export what the MPC client needs                              lss-provision export-mpc -> state/mpc-export.json
  4. optional --self-check: conventional reference sender using ONLY the export, one send per contact
     on an unauthenticated socket                                  lss-provision ref-send
  5. the MPC run                                                   run_mpc(): NOT IMPLEMENTED (needs client changes)
  6. verification: each recipient decrypts the expected texts, and every envelope has NO source
     fields (a sealed-sender message the server could not attribute)  lss-provision receive
  7. stop everything (unless --keep-server)

Talks only to 127.0.0.1. Never point this at Signal's service.

Usage: check_signal_service_local.py [malicious|semi-honest] [--self-check] [--keep-server] [--skip-build]
"""
import argparse, json, os, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent            # local_signal_server/
ROOT = HERE.parent                                # tls-mpc/
SCRIPTS = HERE / 'scripts'
STATE = HERE / 'state'
EXPORT = STATE / 'mpc-export.json'
CONTACTS = ['recipient', 'recipient2']


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


def run_mpc(export, mode, texts):
    """The two-party MPC client run against 127.0.0.1:18443. NOT IMPLEMENTED: it depends on client
    changes listed below; nothing here invents an interface the client does not have.

    What exists today (handshake_backend/EmpHybridWork/check_signal_service_v3.py, read-only):
      controller argv  WORKER DIRECTORY PARTY HOSTS PORT MANIFEST SESSION ENDPOINT PORT HOSTNAME AUTH TRUST UNUSED
                       (PublicServiceController.lean `main`), launched once per party (0, 1)
      worker           .deps/two-party-comparison/tls-worker-fixture-v3 (malicious) or
                       tls-worker-sh-fixture-v3 (semi-honest), env TLS_WORKER_SERVICE_FIXTURE=text,
                       DYLD_LIBRARY_PATH=<MP-SPDZ dir>
      AUTH             public_auth built from handshake_backend/public_auth.cpp
    For the local server the network arguments become (no bridge, no fixture server):
      ENDPOINT=127.0.0.1  PORT=18443  HOSTNAME=server.example
      TRUST=export['server']['tls_trust_root_pem']   (local_signal_server/state/tls/ca.pem)

    Client changes this depends on (none exist yet):
      1. Credentials: service_kernels.h `upgrade()` hardcodes UUID 00112233-... and 'x'*22; it must take
         export['sender']['upgrade_credentials_hex'] (16-byte ACI || 22-byte password).
      2. Conversation admission: `admit_fixture()` reads PublicTextFixture::initial(slot); it must read
         export['contacts'][slot]['initial_hex'] (identity secret[32] || record[579]) for contact ids
         export['contacts'][slot]['contact_id_u128_hex'] (00..01, 00..02, as fixture_id() today).
         CERT stays 260: the export pads the 244-byte local certificate to the slot (unknown protobuf
         field 15), which a libsignal recipient accepts (verified by ref-send).
      3. Sealed-sender sends on a SECOND, UNAUTHENTICATED WebSocket (upgrade without Authorization).
         On the authenticated socket the server attributes the message to the sender (source fields
         set, delivery receipts to the sender); step 6 below fails such a run on purpose.
      4. Server requests on the authenticated socket: `PUT /api/v1/queue/empty` arrives right after the
         upgrade; committed PublicReceive rejects it, the working-tree version replies (replayed in
         local_signal_server/replay; the reply bytes were accepted by the server).
      5. Keepalive: the server closes any socket after 90 s without I/O; MPC operations between
         requests must keep each socket alive (client ping frames or GET /v1/keepalive both work).
      6. Text inputs: notify(ids, message) as today; `texts` below lists what step 6 expects.
      7. State write-back: after each send the new conversation record must replace the exported one
         (the reference sender writes it back into the export; the MPC client would reseal it).
    """
    # The client now has what the list above asks for, for the send path: contacts are admitted from
    # the export at the certificate's exact length (SIGNAL_LOCAL_EXPORT), sends go on the
    # unauthenticated socket (so items 1 and 4 do not apply to this run), and the controller issues
    # two broadcasts to every contact. Not done: keepalive (5) and state write-back (7).
    import hashlib, re, secrets
    base = ROOT / '.deps/two-party-comparison'
    here = ROOT / 'handshake_backend/EmpHybridWork'
    sys.path.insert(0, str(ROOT / 'scripts'))
    from check_full_handshake import OPENSSL
    sh = mode == 'semi-honest'
    output = base / 'signal-service-local-run' / secrets.token_hex(8)
    output.mkdir(parents=True)
    run(['lake', 'build', 'public_service_controller', 'hybrid_kdf_emitter'], cwd=ROOT, capture_output=True)
    run(['c++', '-std=c++20', '-O2', '-I' + str(OPENSSL / 'include'), ROOT / 'handshake_backend/public_auth.cpp',
         '-L' + str(OPENSSL / 'lib'), '-lssl', '-lcrypto', '-o', output / 'public_auth'])
    mp = base / 'data61-MP-SPDZ-113c4e4'
    work = output / 'work'
    work.mkdir()
    with open(output / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(mp / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    stamp = int(time.time() * 1000)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(mp), TLS_WORKER_FIELD_BATCH='3000',
               SIGNAL_LOCAL_EXPORT=str(EXPORT), SIGNAL_LOCAL_TIMESTAMP=str(stamp))
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
            processes.append(subprocess.Popen(command, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=log, text=True))
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
    result = dict(logs=str(output), timestamp=stamp, controllers=cases, worker_totals=totals, rejections=rejections,
                  elapsed_seconds=time.monotonic() - started, exit_codes=[p.returncode for p in processes])
    if any(p.returncode for p in processes) or len(cases) != 2 or not all(c['passed'] for c in cases):
        raise RuntimeError('MPC controllers failed: ' + json.dumps(result))
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
    a = p.parse_args()
    report = dict(passed=False, mode=a.mode, started=time.time())
    try:
        if not a.skip_build and not (STATE / 'classpath.txt').exists():
            run(['bash', SCRIPTS / 'build_server.sh'])
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
        report['mpc_run'] = run_mpc(export, a.mode, texts)
        ok, result = verify(texts)
        report['mpc'] = dict(passed=ok, recipients=result)
        report['passed'] = ok
    except NotImplementedError as e:
        # The pipeline up to the MPC run worked; the run itself is not possible yet, so not passed.
        report['mpc'] = dict(skipped=str(e))
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
