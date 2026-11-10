#!/usr/bin/env python3
"""Send the MPC client's exact WebSocket upgrade request (TlsMpc/Signal/RelayUpgrade.lean)
through the local TLS terminator and print the server's HTTP response head.

Byte-for-byte the same as the client: path `/v1/websocket/`, `Host: chat.signal.org`
(hardcoded in the client; harmless locally), Basic credentials `<aci>:<password>`
without a device suffix, `X-Signal-Receive-Stories: false`, `Accept-Language: en`,
`User-Agent: tls-mpc`. TLS profile: 1.3, X25519, ALPN http/1.1, chain verified
against state/tls/ca.pem for `server.example`.

Only connects to 127.0.0.1.

Usage: probe_upgrade.py [--account state/accounts/sender.json] [--user UUID --password PW] [--port 18443]
                        [--listen SECONDS]   (decode server-initiated frames after the 101)
Exit 0 iff the server answered 101.
"""
import argparse, base64, json, os, socket, ssl, sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]


def upgrade_request(user, password, nonce):
    return (b'GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n'
            b'Sec-WebSocket-Key: ' + base64.b64encode(nonce) +
            b'\r\nSec-WebSocket-Version: 13\r\nAuthorization: Basic ' +
            base64.b64encode(user.encode() + b':' + password.encode()) +
            b'\r\nX-Signal-Receive-Stories: false\r\nAccept-Language: en\r\nUser-Agent: tls-mpc\r\n\r\n')


def varint(b, i):
    n = s = 0
    while True:
        x = b[i]; i += 1; n |= (x & 127) << s; s += 7
        if x < 128:
            return n, i


def fields(b):
    """Minimal protobuf walk: {field: [values]} (varint ints, length-delimited bytes)."""
    out, i = {}, 0
    while i < len(b):
        key, i = varint(b, i)
        f, t = key >> 3, key & 7
        if t == 0:
            v, i = varint(b, i)
        elif t == 2:
            n, i = varint(b, i); v = b[i:i + n]; i += n
        else:
            raise ValueError('wire type')
        out.setdefault(f, []).append(v)
    return out


def describe(payload):
    m = fields(payload)
    kind = m.get(1, [0])[0]
    if kind == 1:
        q = fields(m[2][0])
        return f'server REQUEST verb={q.get(1,[b""])[0].decode()} path={q.get(2,[b""])[0].decode()} id={q.get(4,[None])[0]} headers={[h.decode() for h in q.get(5, [])]}'
    if kind == 2:
        r = fields(m[3][0])
        return f'server RESPONSE id={r.get(1,[None])[0]} status={r.get(2,[None])[0]}'
    return f'unknown message type {kind}'


def read_frames(s, buf, seconds):
    """Print every WebSocket frame the server sends within `seconds` (server frames are unmasked)."""
    s.settimeout(seconds)
    try:
        while True:
            while len(buf) >= 2:
                op, n, off = buf[0] & 15, buf[1] & 127, 2
                if n == 126:
                    if len(buf) < 4: break
                    n, off = int.from_bytes(buf[2:4], 'big'), 4
                elif n == 127:
                    if len(buf) < 10: break
                    n, off = int.from_bytes(buf[2:10], 'big'), 10
                if len(buf) < off + n: break
                payload, buf = buf[off:off + n], buf[off + n:]
                print(f'frame opcode={op} len={n}: ' + (describe(payload) if op == 2 else payload.hex()))
            chunk = s.recv(65536)
            if not chunk:
                print('connection closed by server'); return
            buf += chunk
    except socket.timeout:
        return


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--listen', type=float, default=0, help='after a 101, print server frames for this many seconds')
    p.add_argument('--account'); p.add_argument('--user'); p.add_argument('--password')
    p.add_argument('--port', type=int, default=18443)
    p.add_argument('--ca', default=str(HERE / 'state/tls/ca.pem'))
    a = p.parse_args()
    if a.account:
        acct = json.loads(Path(a.account).read_text())
        user, password = acct['aci'], acct['password']
    else:
        user = a.user or '00000000-0000-4000-8000-000000000000'
        password = a.password or 'x' * 22
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    ctx.minimum_version = ctx.maximum_version = ssl.TLSVersion.TLSv1_3
    ctx.load_verify_locations(a.ca)
    ctx.set_alpn_protocols(['http/1.1'])
    if hasattr(ctx, 'set_ciphersuites'):
        ctx.set_ciphersuites('TLS_AES_128_GCM_SHA256')   # the MPC client's only suite
    with socket.create_connection(('127.0.0.1', a.port), timeout=10) as raw:
        with ctx.wrap_socket(raw, server_hostname='server.example') as s:
            print(f'tls {s.version()} {s.cipher()[0]} alpn={s.selected_alpn_protocol()}')
            s.sendall(upgrade_request(user, password, os.urandom(16)))
            head = b''
            while b'\r\n\r\n' not in head:
                chunk = s.recv(4096)
                if not chunk:
                    break
                head += chunk
            text = head.split(b'\r\n\r\n')[0].decode(errors='replace')
            print(text)
            if a.listen and text.startswith('HTTP/1.1 101'):
                read_frames(s, head.split(b'\r\n\r\n', 1)[1], a.listen)
    sys.exit(0 if text.startswith('HTTP/1.1 101') else 1)


if __name__ == '__main__':
    main()
