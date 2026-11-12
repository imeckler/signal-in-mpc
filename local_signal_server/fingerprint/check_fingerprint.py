#!/usr/bin/env python3
"""Compare this client's captured fingerprint with the stored reference (an official client).

    check_fingerprint.py CAPTURE_DIR [--reference reference/reference.json] [--out report.json]

CAPTURE_DIR holds fingerprint_terminator.py transcripts of one local run of this client
(check_signal_service_local.py --fingerprint makes them). They are normalized with analyze.py
(secrets and identities become shapes) and compared item by item with the reference's HTTP/1.1
profile (reference connections 1 and 2; make_reference.py says where every value comes from).

Every difference fails the check unless ALLOWED names it, with the reason it is accepted for
now. Exit status 0 only when there is no other difference. The report lists everything,
allowed or not, so it doubles as the current state of CLIENT_FINGERPRINT.md's table.
"""
import argparse, json, re, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Differences accepted for now, each with its reason (CLIENT_FINGERPRINT.md has the costs).
ALLOWED = {
    'tls.cipher_suites': 'cannot honour: offering TLS_AES_256_GCM_SHA384 and TLS_CHACHA20_POLY1305_SHA256 needs '
                         'those ciphers in the engines (new capability; the server could select them)',
    'tls.extension_detail.supported_groups': 'cannot honour: offering P-256 and P-384 needs ECDH on those curves in the '
                                             'engines (the server could ask for them by HelloRetryRequest)',
    'tls.extension_detail.server_name': 'the local test hostname (server.example) instead of the real one',
    'tls.record_length': 'follows from the cipher suites, groups and hostname above',
    'tls.handshake_length': 'follows from the cipher suites, groups and hostname above',
    'tls.ja3': 'follows from the cipher suites and groups above',
    'tls.ja3_md5': 'follows from the cipher suites and groups above',
    'tls.ja4': 'follows from the cipher suites (count and hash) and groups above',
    'request.id': 'request ids still count from 2^63 (libsignal: from 0 per connection); fixed-width ids keep '
                  'the request kernels to one shape per size (size-class owner, CLIENT_FINGERPRINT.md (d))',
    'request.body.canonical': 'the device and registration ids are space-padded slots the engines fill '
                              '(replacement specified in CLIENT_FINGERPRINT.md (d), not built)',
    'request.body.space_padded_numbers': 'as request.body.canonical',
    'request.extra./v1/keepalive': 'one keepalive request before leaving a receive session: its response '
                                   'proves the server read our acknowledgements (libsignal sends the same '
                                   'request on a network change)',
    'upgrade.password_length': 'the LOCAL test account\'s password (lss-provision) is 22 characters; Signal-Android has '
                               'generated 24 (base64 of 18 random bytes, Util.getSecret(18)): the product\'s account '
                               'password must be generated that way (PRODUCT_TODO section 2)',
    'close.websocket':'sessions end without a WebSocket Close frame (libsignal sends Close 1000 on disconnect)',
}


def analyze(directory):
    out = subprocess.run([sys.executable, '-I', str(HERE / 'analyze.py'), str(directory)], check=True,
                         capture_output=True, text=True).stdout
    return json.loads(out)['connections']


def is_auth(conn):
    return any(h[0].lower() == 'authorization' for h in conn.get('upgrade', {}).get('headers', []))


class Report:
    def __init__(self):
        self.items = []

    def compare(self, key, ours, reference, where):
        same = ours == reference
        self.items.append(dict(key=key, where=where, same=same, ours=ours, reference=reference,
                               allowed=None if same else ALLOWED.get(key)))

    def note(self, key, where, ours, reference):
        self.items.append(dict(key=key, where=where, same=False, ours=ours, reference=reference, allowed=ALLOWED.get(key)))


def compare_tls(r, ours, ref, where):
    a, b = ours['client_hello'], ref['client_hello']
    for key in ('record_version', 'legacy_version', 'session_id_length', 'cipher_suites', 'compression', 'extensions',
                'record_length', 'handshake_length', 'ja3', 'ja3_md5', 'ja4'):
        r.compare('tls.' + key, a.get(key), b.get(key), where)
    for key in sorted(set(a['extension_detail']) | set(b['extension_detail'])):
        r.compare('tls.extension_detail.' + key, a['extension_detail'].get(key), b['extension_detail'].get(key), where)
    flags = lambda pattern: dict(change_cipher_spec='change_cipher_spec' in pattern,
                                 key_update=any(p.startswith('key_update') for p in pattern))
    r.compare('tls.client_records', flags(ours['client_records']), flags(ref['client_records']), where)


def requests_of(conn):
    return [f['chat'] for f in conn.get('frames', []) if isinstance(f.get('chat'), dict)]


def compare_chat(r, ours, ref, where):
    r.compare('upgrade.request_line', ours['upgrade']['request_line'], ref['upgrade']['request_line'], where)
    # The password's length is the account's, compared on its own.
    lengths = lambda headers: [m.group(1) for h in headers for m in [re.search(r'<password:(\d+)>', h[1])] if m]
    strip = lambda headers: [[h[0], re.sub(r'<password:\d+>', '<password>', h[1])] for h in headers]
    r.compare('upgrade.headers', strip(ours['upgrade']['headers']), strip(ref['upgrade']['headers']), where)
    r.compare('upgrade.password_length', lengths(ours['upgrade']['headers']), lengths(ref['upgrade']['headers']), where)
    reference_requests = {(c['request']['verb'], c['request']['path']): c for c in requests_of(ref) if 'request' in c}
    reference_response = next((c for c in requests_of(ref) if 'response' in c), None)
    for i, chat in enumerate(requests_of(ours)):
        w = f'{where}, message {i}'
        if 'response' in chat:
            if reference_response:
                r.compare('response.field_order', chat['field_order'], reference_response['field_order'], w)
                for key in ('field_order', 'status', 'message'):
                    r.compare('response.' + key, chat['response'].get(key), reference_response['response'].get(key), w)
            continue
        req = chat['request']
        match = reference_requests.get((req['verb'], req['path']))
        if match is None:
            r.note('request.extra.' + req['path'], w, req['verb'] + ' ' + req['path'], None)
            continue
        refreq = match['request']
        r.compare('request.message_field_order', chat['field_order'], match['field_order'], w)
        r.compare('request.field_order', req['field_order'], refreq['field_order'], w)
        r.compare('request.headers', req.get('headers'), refreq.get('headers'), w)
        if isinstance(req.get('body'), dict):
            for key in ('keys_in_order', 'canonical', 'space_padded_numbers'):
                r.compare('request.body.' + key, req['body'][key], refreq['body'][key], w)
            shape = dict(req['body']['shape'])
            refshape = dict(refreq['body']['shape'])
            for s in (shape, refshape):     # the envelope size is the message's, not a property of the client
                for m in s.get('messages', []):
                    m['content'] = '<base64>'
            r.compare('request.body.shape', shape, refshape, w)
    ids = [int(x) for x in ours.get('request_ids', [])]
    if ids:
        r.compare('request.id', dict(first=ids[0], step=sorted({b - a for a, b in zip(ids, ids[1:])})),
                  dict(first=0, step=[1] if len(ids) > 1 else []), where)
    pings = [f for f in ours.get('frames', []) if f['opcode'] == 9]
    r.compare('keepalive.ping_payloads', [p['payload_hex'] for p in pings], [f'{i + 1:02x}' for i in range(len(pings))], where)
    # A ping follows 31 s without anything sent (libsignal); allow a few seconds of scheduling.
    frames = ours.get('frames', [])
    gaps = [round(f['at'] - frames[i - 1]['at'], 1) for i, f in enumerate(frames) if f['opcode'] == 9 and i > 0]
    r.compare('keepalive.idle_seconds', all(29 <= g <= 35 for g in gaps), True, where)
    closes = [f for f in ours.get('frames', []) if f['opcode'] == 8]
    if not closes:
        r.note('close.websocket', where, None, 'Close 1000')
    else:
        r.compare('close.websocket', closes[-1].get('payload_hex'), '03e8', where)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('capture')
    p.add_argument('--reference', default=str(HERE / 'reference' / 'reference.json'))
    p.add_argument('--out')
    a = p.parse_args()
    ref = {c['connection']: c for c in json.loads(Path(a.reference).read_text())['connections']}
    ours = analyze(a.capture)
    r = Report()
    for conn in ours:
        where = f'connection {conn["connection"]}' + (' (authenticated)' if is_auth(conn) else '')
        model = ref[2] if is_auth(conn) else ref[1]
        compare_tls(r, conn, model, where)
        if 'upgrade' in conn:
            compare_chat(r, conn, model, where)
        r.note('tls.alpn_of_current_libsignal', where, conn['client_hello']['extension_detail'].get('alpn'),
               ref[3]['client_hello']['extension_detail'].get('alpn'))
    ALLOWED.setdefault('tls.alpn_of_current_libsignal',
                       'libsignal >= 0.97.1 connects to grpc.chat.signal.org with ALPN h2 and runs the WebSocket over '
                       'HTTP/2 extended CONNECT: needs an HTTP/2 framing layer (new capability, CLIENT_FINGERPRINT.md (c))')
    for item in r.items:
        if not item['same'] and item['allowed'] is None:
            item['allowed'] = ALLOWED.get(item['key'])
    failures = [i for i in r.items if not i['same'] and not i['allowed']]
    allowed = [i for i in r.items if not i['same'] and i['allowed']]
    report = dict(passed=not failures and bool(ours), connections=len(ours), compared=len(r.items),
                  failures=failures, allowed_differences=sorted({(i['key'], i['allowed']) for i in allowed}))
    text = json.dumps(report, indent=1, default=str)
    if a.out:
        Path(a.out).write_text(text + '\n')
    print(text)
    sys.exit(0 if report['passed'] else 1)


if __name__ == '__main__':
    main()
