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

check_signal_service_local_signup.py [semi-honest|malicious] [--compact] [--manifest M] [LAYOUT ...]
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
p.add_argument('queue', nargs='*')
a = p.parse_args()
queue = a.queue or ['bad:android', 'legacy', 'android', 'android-tag', 'android-timer']
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
              CIRCUIT_CACHE_LOG=str(run.dir / 'kernels-requested.txt'), SIGNAL_ACK_REFUSED='1')
if a.manifest:
    common.update(CIRCUIT_MANIFEST=str(Path(a.manifest).resolve()), CIRCUIT_REFUSED_LOG=str(run.dir / 'kernels-refused.txt'))
shares = [(export_dir / f'credentials-party-{party}.hex').read_text().strip() for party in range(2)]
auth, work, hosts = r.prepare_workers(run)
cluster = r.harness.Cluster()
result = dict(queue=queue, compact=a.compact, manifest=a.manifest, deployment_hints=hints)


def events(label):
    rows = [json.loads(line) for line in (run.dir / f'record-{label}-party-0.jsonl').read_text().splitlines()]
    return [[e['event'], e.get('reason') or e.get('outcome') or e.get('size')] for e in rows if e['event'] in ('envelope', 'envelope-refused')]


try:
    cluster.token(r.harness.ACCOUNT)
    expected, users = [], {}
    for index, entry in enumerate(queue):
        bad = entry.startswith('bad:')
        layout = entry[4:] if bad else entry
        contact = secrets.randbits(100)
        token = cluster.token(contact).read_text().strip()
        name = f'{account}-u{index}'
        out = subprocess.run([str(r.LSS), 'signup', name, f'+1202556{stamp[-3:]}{index}', account, 'x' * len(token) if bad else token],
                             capture_output=True, text=True, env=dict(os.environ, LSS_DATA_LAYOUT=layout))
        run.log('signup-sent', layout=layout, bad=bad, exit_code=out.returncode,
                detail=[line for line in out.stderr.splitlines() if 'layout' in line or 'rror' in line][-3:])
        if not bad:
            expected.append([str(contact), token])
            users.setdefault(layout, (name, contact))
    env = lambda party: dict(cluster.env(party), SIGNAL_LOCAL_CREDENTIALS=shares[party], SIGNAL_LOCAL_EXPECT=str(len(queue)))
    receive = r.session(run, 'receive', server, export_dir, auth, work, hosts, env, common, 420)
    received = [c.get('received') for c in receive['controllers']]
    result['receive'] = dict(events=events('receive'), received=received, errors=[c.get('error') for c in receive['controllers']],
                             exit_codes=receive['exit_codes'], seconds=receive['seconds'])
    stored = all(sorted(x or []) == sorted(expected) for x in received)
    refused = sum(e[0] == 'envelope-refused' for e in result['receive']['events'])
    result['receive_passed'] = stored and refused == sum(q.startswith('bad:') for q in queue)
    target = next((users[q] for q in queue if not q.startswith('bad:') and q != 'legacy'), None) or next(iter(users.values()), None)
    if result['receive_passed'] and target:
        cluster.refresh()
        text = 'Thanks for signing up. A reply from the local two-party test of the signup layouts.'
        request = cluster.request([target[1]], text)
        send = r.session(run, 'send', server, export_dir, auth, work, hosts,
                         lambda party: dict(cluster.env(party, request), SIGNAL_NOTIFY_MESSAGE_FILE=str(cluster.dir / 'message.txt')), common, 420)
        results = [c.get('results') for c in send['controllers']]
        seen = r.harness.receive(target[0], 6)
        lags = [g['envelope'].get('server_timestamp', 0) - g['timestamp'] for g in seen if g['text'] == text]
        result['send'] = dict(results=results, seconds=send['seconds'], received=[g['text'] for g in seen],
                              timestamp_age_ms_at_server=lags, sealed=all(not g['envelope'].get('source_service_id') for g in seen))
        result['send_passed'] = all(x and x[0].get('result', '').startswith('delivered') for x in results) and text in result['send']['received'] \
            and result['send']['sealed']
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
