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
    """RelayUpgrade.request; with user=None the same request without the Authorization line
    (a proposed unauthenticated send socket)."""
    auth = (b'\r\nAuthorization: Basic ' + base64.b64encode(user.encode() + b':' + password.encode())) if user else b''
    return (b'GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n'
            b'Sec-WebSocket-Key: ' + base64.b64encode(nonce) +
            b'\r\nSec-WebSocket-Version: 13' + auth +
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


def pb_varint(n):
    out = bytearray()
    while True:
        b = n & 127; n >>= 7
        if n: out.append(b | 128)
        else: out.append(b); return bytes(out)


def client_frame(payload, opcode=2):
    """Masked client frame (payload < 126 bytes), as PublicReceive.clientFrame builds it."""
    mask = os.urandom(4)
    assert len(payload) < 126
    return bytes([0x80 | opcode, 0x80 | len(payload)]) + mask + bytes(b ^ mask[i % 4] for i, b in enumerate(payload))


def queue_empty_reply(request_id):
    """Byte-identical to PublicReceive.reply (working tree) for /api/v1/queue/empty."""
    response = b'\x08' + pb_varint(request_id) + b'\x10\xc8\x01\x1a\x02OK'
    return client_frame(b'\x08\x02\x1a' + pb_varint(len(response)) + response)


def keepalive_request(request_id):
    request = b'\x0a\x03GET' + b'\x12\x0d/v1/keepalive' + b'\x20' + pb_varint(request_id)
    return client_frame(b'\x08\x01\x12' + pb_varint(len(request)) + request)


def session(s, buf, seconds, every, action, reply_queue_empty):
    """Keep the socket for `seconds`; every `every` seconds send `action` ('ping'|'keepalive'|'none').
    Answer queue/empty with the MPC client's reply if asked. Prints every server frame; reports close."""
    import time
    start = last = time.monotonic(); next_id = 2**63 + 100
    s.settimeout(0.5)
    while time.monotonic() - start < seconds:
        if every and action != 'none' and time.monotonic() - last >= every:
            last = time.monotonic()
            if action == 'ping':
                s.sendall(client_frame(b'lss', opcode=9)); print(f'{last - start:6.1f}s sent ping')
            else:
                s.sendall(keepalive_request(next_id)); print(f'{last - start:6.1f}s sent GET /v1/keepalive id={next_id}'); next_id += 1
        try:
            chunk = s.recv(65536)
            if not chunk:
                print(f'{time.monotonic() - start:6.1f}s connection closed by server'); return
            buf += chunk
        except socket.timeout:
            pass
        while len(buf) >= 2:
            op, n, off = buf[0] & 15, buf[1] & 127, 2
            if n == 126:
                if len(buf) < 4: break
                n, off = int.from_bytes(buf[2:4], 'big'), 4
            if len(buf) < off + n: break
            payload, buf = buf[off:off + n], buf[off + n:]
            t = time.monotonic() - start
            if op == 8:
                code = int.from_bytes(payload[:2], 'big') if len(payload) >= 2 else None
                print(f'{t:6.1f}s server CLOSE code={code} reason={payload[2:].decode(errors="replace")}'); return
            if op == 10:
                print(f'{t:6.1f}s server pong'); continue
            print(f'{t:6.1f}s ' + describe(payload))
            m = fields(payload)
            if reply_queue_empty and m.get(1, [0])[0] == 1:
                q = fields(m[2][0])
                if q.get(2, [b''])[0] == b'/api/v1/queue/empty':
                    s.sendall(queue_empty_reply(q[4][0])); print(f'{t:6.1f}s sent queue/empty reply (PublicReceive.reply bytes)')
    print(f'{seconds:.0f}s elapsed, connection still open')


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
    p.add_argument('--session', type=float, default=0, help='after a 101, keep the socket this many seconds (see --action)')
    p.add_argument('--action', choices=['none', 'ping', 'keepalive'], default='none')
    p.add_argument('--every', type=float, default=30)
    p.add_argument('--reply-queue-empty', action='store_true', help="answer queue/empty with the MPC client's reply bytes")
    p.add_argument('--unauthenticated', action='store_true', help='no Authorization header')
    p.add_argument('--save', help='with --unauthenticated only: save the exact upgrade request and the 101 head to DIR')
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
            if a.save and not a.unauthenticated:
                raise SystemExit('--save is only allowed with --unauthenticated (an authenticated request carries the password)')
            request = upgrade_request(None if a.unauthenticated else user, password, os.urandom(16))
            s.sendall(request)
            head = b''
            while b'\r\n\r\n' not in head:
                chunk = s.recv(4096)
                if not chunk:
                    break
                head += chunk
            text = head.split(b'\r\n\r\n')[0].decode(errors='replace')
            print(text)
            if a.save:
                Path(a.save).mkdir(parents=True, exist_ok=True)
                (Path(a.save) / 'mpc-unauthenticated-upgrade-request.bin').write_bytes(request)
                (Path(a.save) / 'mpc-unauthenticated-upgrade-response-head.bin').write_bytes(head.split(b'\r\n\r\n')[0] + b'\r\n\r\n')
            rest = head.split(b'\r\n\r\n', 1)[1]
            if a.session and text.startswith('HTTP/1.1 101'):
                session(s, rest, a.session, a.every, a.action, a.reply_queue_empty)
            elif a.listen and text.startswith('HTTP/1.1 101'):
                read_frames(s, rest, a.listen)
    sys.exit(0 if text.startswith('HTTP/1.1 101') else 1)


if __name__ == '__main__':
    main()
