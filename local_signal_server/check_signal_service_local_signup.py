#!/usr/bin/env python3
"""LOCAL server only: the first real test's flow (real_signal/REAL_TEST_PLAN.md) with signups in the
layouts official clients send, a refused signup before good ones, and optionally production's
compact sender certificates and strict circuits. Uses real_signal/run_real_test.py's pieces, as the
real run does (libsignal profile, in-memory database nodes).

  setup: a fresh local account in the registration tool's format (`register NAME NUMBER
         unrestricted`, scripts/make_fake_account.py), exported with
         `lss-provision export-account … local`
  queue: one signup per LAYOUT (lss-provision's LSS_DATA_LAYOUT: legacy, android, android-tag,
         android-timer); `bad:LAYOUT` sends a text that is not a token, so the message opens and is
         refused at the token step (REAL_TEST_PLAN.md B6b). Default:
         bad:android legacy android android-tag android-timer
  receive session (SIGNAL_ACK_REFUSED=1): every good signup stored under its token's id, every
         bad one refused, and the session must not end early
  send session: one text to the contact of the first good non-legacy signup; its user's client
         must decrypt it (the server checks the access key the engines derived from that layout's
         profile key: these test senders are not unrestricted). Reported: how old the message's
         timestamp was when the server received it.

  --compact     against a SECOND server instance issuing compact sender certificates
                (scripts/start_compact_server.sh: embedSigner false, ports 19080/19443); started
                if needed, the default instance is not touched
  --manifest M  strict mode: CIRCUIT_MANIFEST=M; a kernel not in it is refused (kernels-refused.txt)
  --devices N   the reply's recipient has N devices (default 1), as the first real run's contact
                had three: after the receive session N − 1 devices are linked to the user who signed
                up (`lss-provision link USER K`: its own registration id, signed prekey and Kyber
                last-resort key, K one-time EC prekeys; K from --one-time, default 5, 0, 5, ...).
                The reply is then answered 409, the client refreshes the contact's devices
                (`GET /v2/keys/{uuid}/*`, one establishment per device) and sends again; required:
                "delivered after device refresh" and the text decrypted by EVERY device
  --one-time K,K,..  one-time EC prekeys of each linked device (0: its bundle has "preKey":null)

check_signal_service_local_signup.py [semi-honest|malicious] [--compact] [--manifest M] [--devices N] [LAYOUT ...]
Recorded under real_signal/state/runs/STAMP-local-signup/ (report.json)."""
import argparse, json, os, secrets, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'real_signal'))
import run_real_test as r  # noqa: E402

p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
p.add_argument('mode', nargs='?', default='semi-honest', choices=['semi-honest', 'malicious'])
p.add_argument('--compact', action='store_true')
p.add_argument('--manifest')
p.add_argument('--devices', type=int, default=1)
p.add_argument('--one-time', default='')
p.add_argument('queue', nargs='*')
a = p.parse_args()
queue = a.queue or (['android'] if a.devices > 1 else ['bad:android', 'legacy', 'android', 'android-tag', 'android-timer'])
one_time = [int(k) for k in a.one_time.split(',') if k] or [5 if i % 2 == 0 else 0 for i in range(a.devices - 1)]
if len(one_time) != a.devices - 1:
    sys.exit('--one-time: one count per linked device')
HERE = ROOT / 'local_signal_server'

if a.compact:
    os.environ['LSS_SERVER'] = '127.0.0.1:19080'   # every lss-provision call below, harness.receive included
    subprocess.run(['bash', str(HERE / 'scripts/start_compact_server.sh')], check=True, capture_output=True)
else:
    subprocess.run(['bash', str(HERE / 'scripts/start_server.sh')], check=True, capture_output=True)
run = r.Run('local-signup' + ('-compact' if a.compact else ''), a.mode)
stamp = str(int(time.time()))[-6:]
account = f'signup-{stamp}'
out = subprocess.run([str(r.LSS), 'register', account, f'+1202555{stamp[-4:]}', 'unrestricted'], capture_output=True, text=True)
run.log('account-registered', exit_code=out.returncode, error=out.stderr[-300:])
fake = run.dir / 'account.json'
subprocess.run([sys.executable, str(HERE / 'scripts/make_fake_account.py'), str(HERE / f'state/accounts/{account}.json'), str(fake)],
               check=True, capture_output=True)
export_dir = run.dir / 'export'
out = subprocess.run([str(r.LSS), 'export-account', str(fake), str(export_dir), 'local'], capture_output=True, text=True)
run.log('exported', exit_code=out.returncode, output=out.stdout[-600:], error=out.stderr[-300:])
export_path = export_dir / 'mpc-export.json'
export = json.loads(export_path.read_text())
if a.compact:
    export['server']['port'] = 19443
    export['server']['plain_port'] = 19080
    export_path.write_text(json.dumps(export, indent=1))
server = export['server']
hints = json.loads((export_dir / 'deployment-hints.json').read_text())
r.harness.STATE = run.dir
common = dict(DYLD_LIBRARY_PATH=str(r.MP), TLS_WORKER_FIELD_BATCH='3000', SIGNAL_CLIENT_PROFILE='libsignal',
              SIGNAL_LOCAL_EXPORT=str(export_path), SIGNAL_LOCAL_KEM=str(r.LSS),
              CIRCUIT_CACHE_LOG=str(run.dir / 'kernels-requested.txt'), SIGNAL_ACK_REFUSED='1', SIGNAL_RECEIVE_JUMP=r.RECEIVE_JUMP)
if a.manifest:
    common.update(CIRCUIT_MANIFEST=str(Path(a.manifest).resolve()), CIRCUIT_REFUSED_LOG=str(run.dir / 'kernels-refused.txt'))
shares = [(export_dir / f'credentials-party-{party}.hex').read_text().strip() for party in range(2)]
auth, work, hosts = r.prepare_workers(run)
cluster = r.harness.Cluster()
result = dict(queue=queue, compact=a.compact, manifest=a.manifest, deployment_hints=hints, devices=a.devices, one_time=one_time)


def events(label):
    rows = [json.loads(line) for line in (run.dir / f'record-{label}-party-0.jsonl').read_text().splitlines()]
    return [[e['event'], e.get('reason') or e.get('outcome') or e.get('size')] for e in rows if e['event'] in ('envelope', 'envelope-refused')]


try:
    cluster.token(r.harness.ACCOUNT)
    expected, users, last = [], {}, None
    for index, entry in enumerate(queue):
        # `again:LAYOUT`: the previous good signup's token once more (as a redelivered signup or a
        # phone sending its token twice): it must be refused at the token step, no second contact.
        bad, again = entry.startswith('bad:'), entry.startswith('again:')
        layout = entry.split(':', 1)[1] if bad or again else entry
        contact = secrets.randbits(100)
        token = last if again else cluster.token(contact).read_text().strip()
        name = f'{account}-u{index}'
        out = subprocess.run([str(r.LSS), 'signup', name, f'+1202556{stamp[-3:]}{index}', account, 'x' * len(token) if bad else token],
                             capture_output=True, text=True, env=dict(os.environ, LSS_DATA_LAYOUT=layout))
        run.log('signup-sent', layout=layout, bad=bad, again=again, exit_code=out.returncode,
                detail=[line for line in out.stderr.splitlines() if 'layout' in line or 'rror' in line][-3:])
        if not bad and not again:
            expected.append([str(contact), token])
            users.setdefault(layout, (name, contact))
            last = token
    env = lambda party: dict(cluster.env(party), SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT=str(len(queue)))
    receive = r.session(run, 'receive', server, export_dir, auth, work, hosts, env, common, 420)
    received = [c.get('received') for c in receive['controllers']]
    result['receive'] = dict(events=events('receive'), received=received, errors=[c.get('error') for c in receive['controllers']],
                             exit_codes=receive['exit_codes'], seconds=receive['seconds'])
    stored = all(sorted(x or []) == sorted(expected) for x in received)
    refused = sum(e[0] == 'envelope-refused' for e in result['receive']['events'])
    result['receive_passed'] = stored and refused == sum(q.startswith(('bad:', 'again:')) for q in queue)
    target = next((users[q] for q in queue if q in users and q != 'legacy'), None) or next(iter(users.values()), None)
    if result['receive_passed'] and target:
        cluster.refresh()
        # The user's other devices (linked after the signup: `signup` registers the user afresh).
        names = [target[0]]
        for k in one_time:
            out = subprocess.run([str(r.LSS), 'link', target[0], str(k)], capture_output=True, text=True)
            linked = json.loads(out.stdout.strip().splitlines()[-1]) if out.returncode == 0 else {}
            run.log('device-linked', exit_code=out.returncode, device=linked.get('device_id'), registration_id=linked.get('registration_id'),
                    signed_prekey_id=linked.get('signed_prekey_id'), one_time_prekeys=k, error=out.stderr[-300:])
            if out.returncode:
                raise RuntimeError('lss-provision link failed: ' + out.stderr[-300:])
            names.append(linked['linked'])
        # 110 bytes, as real_signal/run_real_test.py's default text (message class 2).
        text = ('Thanks for signing up. A reply from the local two-party test of the signup layouts.' if a.devices == 1 else
                'Thanks for signing up. This is a reply to every device of a user with %d devices; nothing to answer.' % a.devices)
        request = cluster.request([target[1]], text)
        send = r.session(run, 'send', server, export_dir, auth, work, hosts,
                         lambda party: dict(cluster.env(party, request), SIGNAL_NOTIFY_MESSAGE_FILE=str(cluster.dir / 'message.txt')), common, 420)
        results = [c.get('results') for c in send['controllers']]
        seen = {name: r.harness.receive(name, 6) for name in names}
        lags = [g['envelope'].get('server_timestamp', 0) - g['timestamp'] for g in seen[names[0]] if g['text'] == text]
        rows = [json.loads(line) for line in (run.dir / 'record-send-party-0.jsonl').read_text().splitlines()]
        result['send'] = dict(results=results, seconds=send['seconds'], received={name: [g['text'] for g in got] for name, got in seen.items()},
                              timestamp_age_ms_at_server=lags, sealed=all(not g['envelope'].get('source_service_id') for got in seen.values() for g in got),
                              recovery=[c.get('recovery') for c in send['controllers']], errors=[c.get('error') for c in send['controllers']],
                              statuses=[e['status'] for e in rows if e['event'] == 'response'],
                              prekey_response_bytes=[e['bytes'] for e in rows if e['event'] == 'passed-over' and 'prekey' in e.get('to', '')],
                              records=[e['content_bytes'] for e in rows if e['event'] == 'record'])
        good = (lambda r: r == 'delivered after device refresh') if a.devices > 1 else (lambda r: r.startswith('delivered'))
        result['send_passed'] = all(x and good(x[0].get('result', '')) for x in results) \
            and all(text in got for got in result['send']['received'].values()) and result['send']['sealed']
    if a.manifest:
        refused_path = run.dir / 'kernels-refused.txt'
        result['kernels_refused'] = refused_path.read_text().split('\n') if refused_path.exists() and refused_path.read_text().strip() else []
    result['passed'] = bool(result.get('receive_passed') and result.get('send_passed') and not result.get('kernels_refused'))
finally:
    cluster.stop()
    (run.dir / 'report.json').write_text(json.dumps(result, indent=1) + '\n')
print(json.dumps(result, indent=1)[:5000])
print('directory', run.dir)
sys.exit(0 if result.get('passed') else 1)
