#!/usr/bin/env python3
"""Measure a TLS server's encrypted handshake records with a CONVENTIONAL client (OpenSSL), with
the parameters the two-party client offers (TLS 1.3, TLS_AES_128_GCM_SHA256, X25519, ALPN
http/1.1, SNI), and nothing after the handshake (no HTTP request; the connection is closed).

    measure_handshake.py local OUT.json
    measure_handshake.py local-compact OUT.json      (the second local instance, production's shape)
    measure_handshake.py production OUT.json --i-have-the-go-ahead     (contacts chat.signal.org)

Why: `tls-open-handshake N` is one circuit per encrypted server handshake record size N (the
record with its 5-byte header), a deployment setting (`handshake` in the deployment description,
CIRCUIT_SHAPES.md). Locally the sizes are 43, 58, 94, 922; production's are unknown until a
connection. This also records the certificate chain the server sends and whether it verifies
against the pinned root (real_signal/signal-root-ca.pem), and what ALPN and group it picks.

Records: OUT.json (parsed) and OUT.json.raw.txt (OpenSSL's full -msg output: every record header
and every decrypted handshake message, in order). Nothing secret: the client's keys are
OpenSSL's own, thrown away.

What the server sees: one TLS 1.3 handshake from an OpenSSL client (its ClientHello is not
libsignal's), then close_notify. No Signal request, no account.
"""
import json, re, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OPENSSL = '/opt/homebrew/opt/openssl@3/bin/openssl'
TARGETS = {
    'local': dict(host='127.0.0.1', port=18443, name='server.example', ca=ROOT / 'local_signal_server/state/tls/ca.pem'),
    # The second local instance (local_signal_server/scripts/start_compact_server.sh): production's
    # handshake shape from scripts/coalesced_terminator.py.
    'local-compact': dict(host='127.0.0.1', port=19443, name='server.example', ca=ROOT / 'local_signal_server/state/tls/ca.pem'),
    'production': dict(host='chat.signal.org', port=443, name='chat.signal.org', ca=HERE / 'signal-root-ca.pem'),
}


def parse(text):
    """Every record header OpenSSL printed, in order, with the decrypted messages that follow it."""
    records, current = [], None
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = re.match(r'(<<<|>>>) (\S+ \S+), RecordHeader \[length 0005\]', line)
        if m:
            octets = lines[i + 1].split() if i + 1 < len(lines) else []
            if len(octets) == 5:
                kind, length = int(octets[0], 16), int(octets[3] + octets[4], 16)
                current = dict(direction='server' if m.group(1) == '<<<' else 'client', type=kind, length=length,
                               record_bytes=5 + length, messages=[])
                records.append(current)
            continue
        m = re.match(r'(<<<|>>>) (\S+ \S+), (Handshake|Alert|InnerContent|ChangeCipherSpec)( \[length ([0-9a-f]+)\])?(, (.+))?', line)
        if m and current is not None and m.group(3) != 'InnerContent':
            current['messages'].append(dict(kind=m.group(3), length=int(m.group(5), 16) if m.group(5) else None, name=m.group(7)))
    return records


def main():
    if len(sys.argv) < 3 or sys.argv[1] not in TARGETS:
        sys.exit(__doc__)
    target, out = sys.argv[1], Path(sys.argv[2])
    if target == 'production' and '--i-have-the-go-ahead' not in sys.argv:
        sys.exit('production contacts chat.signal.org: only with the owner\'s explicit go-ahead (--i-have-the-go-ahead)')
    t = TARGETS[target]
    command = [OPENSSL, 's_client', '-connect', f"{t['host']}:{t['port']}", '-servername', t['name'], '-tls1_3',
               '-ciphersuites', 'TLS_AES_128_GCM_SHA256', '-groups', 'X25519', '-alpn', 'http/1.1', '-CAfile', str(t['ca']),
               '-verify_return_error', '-verify_hostname', t['name'], '-msg', '-showcerts']
    started = time.time()
    r = subprocess.run(command, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=60)
    raw = r.stdout + '\n--- stderr ---\n' + r.stderr
    Path(str(out) + '.raw.txt').write_text(raw)
    records = parse(r.stdout)
    # The server's encrypted handshake flight: its application-data-typed records before the
    # client's first one (the client's Finished).
    first_client = next((i for i, rec in enumerate(records) if rec['direction'] == 'client' and rec['type'] == 23), len(records))
    flight = [rec for rec in records[:first_client] if rec['direction'] == 'server' and rec['type'] == 23]
    after = [rec for rec in records[first_client:] if rec['direction'] == 'server']
    certs = re.findall(r'-----BEGIN CERTIFICATE-----.*?-----END CERTIFICATE-----', r.stdout, re.S)
    grab = lambda pattern: (re.search(pattern, r.stdout + r.stderr) or [None, None])[1]
    report = dict(target=target, command=command, started=started, exit_code=r.returncode,
                  handshake_record_sizes=[rec['record_bytes'] for rec in flight],
                  deployment_setting='"handshake": [' + ', '.join(str(rec['record_bytes']) for rec in flight) + ']',
                  flight=flight, server_records_after_client_finished=after,
                  verify=grab(r'Verify return code: ([^\n]+)'), alpn=grab(r'ALPN protocol: ([^\n]+)'),
                  cipher=grab(r'Ciphersuite: ([^\n]+)') or grab(r'Cipher is ([^\n]+)'), group=grab(r'Negotiated TLS1.3 group: ([^\n]+)') or grab(r'(?:Peer|Server) Temp Key: ([^\n]+)'),
                  protocol=grab(r'Protocol\s*: ([^\n]+)'),
                  peer_signature=grab(r'Peer signature type: ([^\n]+)'), certificate_chain_pem=certs,
                  certificate_chain_lengths=len(certs), raw=str(out) + '.raw.txt')
    out.write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps({k: report[k] for k in ('exit_code', 'handshake_record_sizes', 'verify', 'alpn', 'cipher', 'group', 'peer_signature',
                                             'certificate_chain_lengths')}))


if __name__ == '__main__':
    main()
