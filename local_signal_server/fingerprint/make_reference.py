#!/usr/bin/env python3
"""Build the REFERENCE fingerprint of an official Signal client from source, as a synthetic
transcript in fingerprint_terminator.py's format, and normalize it with analyze.py:

    make_reference.py OUT_DIR      -> OUT_DIR/transcript/*.json and OUT_DIR/reference.json

Why synthetic: libsignal-net cannot be built here (boring-sys needs the BoringSSL sources, which
are not vendored: .deps/libsignal-vendor/boring-sys/deps/boringssl is empty), so nothing could run
libsignal's connection code against the local server. Every byte below is derived from source,
cited inline (CLIENT_FINGERPRINT.md has the full table):
  libsignal v0.106.1 on disk (.deps/libsignal-v0.106.1), the model client's transport;
  BoringSSL 427ec40 (the submodule of signalapp/boring at signal-v5.3.0, which libsignal pins);
  Signal-Android b8544a8 (the model client: libsignal 0.107.0, same transport code).
Values that would be account data are dummies (zero UUID, zero keys), and randoms are fixed, so
the output is deterministic and contains nothing from any account.

Two profiles of the same client:
  connection 1, 2  "http1":  libsignal's own HTTP/1.1 path (what libsignal < 0.97.1 used for
                   the direct route, and what libsignal still uses through proxies/fronting).
                   This is the layout this client implements: the regression check compares
                   against it.
  connection 3     "h2":     libsignal >= 0.97.1's direct route (grpc.chat.signal.org, ALPN h2,
                   WebSocket over HTTP/2 extended CONNECT). Only the ClientHello is modelled;
                   the HTTP/2 framing is described in CLIENT_FINGERPRINT.md.
"""
import base64, json, struct, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def u16(n): return struct.pack('>H', n)
def vec(n, b): return len(b).to_bytes(n, 'big') + b
def ext(kind, body): return u16(kind) + vec(2, body)


def client_hello(host, alpn):
    """BoringSSL ClientHello for libsignal-net (rust/net/infra/src/tcp_ssl.rs `ssl_config`):
    min version TLS 1.3, ALPN per route, verify prefs set, curves "X25519:P-256:P-384",
    no GREASE / OCSP / SCT / tickets / extension permutation."""
    random, session_id, share = bytes(range(32)), bytes(range(32, 64)), bytes(32)
    # ssl/ssl_cipher.cc kCiphersAESHardware: AES-128-GCM, AES-256-GCM, ChaCha20 (with AES hardware;
    # without it ChaCha20 comes first). No TLS 1.2 suites when min_version >= TLS 1.3.
    suites = u16(0x1301) + u16(0x1302) + u16(0x1303)
    sigalgs = b''.join(u16(x) for x in [0x0807, 0x0403, 0x0804, 0x0401, 0x0503, 0x0805, 0x0501, 0x0806, 0x0601])
    exts = (ext(0, vec(2, b'\x00' + vec(2, host.encode())))                       # server_name
            + ext(10, vec(2, u16(29) + u16(23) + u16(24)))                       # supported_groups
            + ext(16, vec(2, b''.join(vec(1, p.encode()) for p in alpn)))       # ALPN
            + ext(13, vec(2, sigalgs))                                           # signature_algorithms
            + ext(51, vec(2, u16(29) + vec(2, share)))                           # key_share: first group only
            + ext(45, vec(1, b'\x01'))                                           # psk_key_exchange_modes: psk_dhe_ke
            + ext(43, vec(1, u16(0x0304))))                                      # supported_versions
    body = u16(0x0303) + random + vec(1, session_id) + vec(2, suites) + vec(1, b'\x00') + vec(2, exts)
    hs = b'\x01' + vec(3, body)
    return b'\x16' + u16(0x0301) + vec(2, hs)     # ssl/tls_record.cc: TLS 1.0 before the version is known


def finished_record():
    # Client Finished under AES-128-GCM: 4 + 32 + 1 (type) + 16 (tag). No ChangeCipherSpec:
    # BoringSSL's client sends one only after a HelloRetryRequest or with early data.
    return b'\x17\x03\x03' + vec(2, bytes(53))


def varint(n):
    out = b''
    while True:
        b, n = n & 0x7f, n >> 7
        out += bytes([b | (0x80 if n else 0)])
        if not n:
            return out


def field(tag, wire, value):
    key = varint(tag << 3 | wire)
    return key + (varint(value) if wire == 0 else varint(len(value)) + value)


def request(verb, path, body, rid, headers):
    """prost encodes WebSocketRequestMessage fields in tag order: verb 1, path 2, body 3, id 4,
    headers 5 (rust/net/src/proto/chat_websocket.proto); libsignal formats headers as
    "{name}: {value}" with lowercase names (rust/net/src/chat/ws.rs)."""
    r = field(1, 2, verb.encode()) + field(2, 2, path.encode())
    if body is not None:
        r += field(3, 2, body)
    r += field(4, 0, rid)
    for h in headers:
        r += field(5, 2, h.encode())
    return field(1, 0, 1) + field(2, 2, r)


def response(rid, status, message):
    return field(1, 0, 2) + field(3, 2, field(1, 0, rid) + field(2, 0, status) + field(3, 2, message.encode()))


def ws_frame(opcode, payload, mask=b'\x11\x22\x33\x44'):
    n = len(payload)
    head = bytes([0x80 | opcode]) + (bytes([0x80 | n]) if n < 126 else bytes([0x80 | 126]) + u16(n))
    return head + mask + bytes(b ^ mask[i % 4] for i, b in enumerate(payload))


UUID = '00000000-0000-4000-8000-000000000000'
UA = 'Signal-Android/8.36.0 Android/35 libsignal/0.107.0'   # Signal-Android StandardUserAgentInterceptor + libsignal UserAgent
KEY = base64.b64encode(bytes(16)).decode()


def upgrade(authenticated):
    """tungstenite 0.29 generate_request: Host, Connection, Upgrade, Sec-WebSocket-Version,
    Sec-WebSocket-Key, then the remaining HeaderMap entries in order (lowercase names):
    libsignal's ChatHeaders (authorization, x-signal-receive-stories, accept-language if any
    languages — Signal-Android passes none) and user-agent (rust/net/src/chat.rs)."""
    lines = ['GET /v1/websocket/ HTTP/1.1', 'Host: chat.signal.org', 'Connection: Upgrade', 'Upgrade: websocket',
             'Sec-WebSocket-Version: 13', 'Sec-WebSocket-Key: ' + KEY]
    if authenticated:
        password = 'x' * 24
        lines += ['authorization: Basic ' + base64.b64encode(f'{UUID}.1:{password}'.encode()).decode(),
                  'x-signal-receive-stories: false']
    lines += ['user-agent: ' + UA]
    return ('\r\n'.join(lines) + '\r\n\r\n').encode()


def send_body(envelope_len, registration=12345):
    """serde_json of SendMessageRequest (rust/net/chat/src/ws/messages.rs): messages[type,
    destinationDeviceId, destinationRegistrationId, content], online, urgent, timestamp."""
    content = base64.b64encode(bytes(envelope_len)).decode()
    return json.dumps({'messages': [{'type': 6, 'destinationDeviceId': 1, 'destinationRegistrationId': registration,
                                     'content': content}], 'online': False, 'urgent': True,
                       'timestamp': 1762800000000}, separators=(',', ':')).encode()


def transcript(n, events):
    return dict(connection=n, started=0, tls=None, events=[[t, d, k, b.hex()] for t, d, k, b in events])


def main():
    out = Path(sys.argv[1])
    tdir = out / 'transcript'
    tdir.mkdir(parents=True, exist_ok=True)
    access = 'unidentified-access-key: ' + base64.b64encode(bytes(16)).decode()
    # Connection 1: unauthenticated socket of a send. libsignal request ids count from 0 per
    # connection (RECOMMENDED_CHAT_WS_CONFIG.initial_request_id = 0, +1 per request).
    send = request('PUT', f'/v1/messages/{UUID}', send_body(1000), 0, ['content-type: application/json', access])
    fetch = request('GET', f'/v2/keys/{UUID}/*', None, 1, [access])   # rust/net/chat/src/ws/keys.rs
    conn1 = [(0.0, 'c2s', 'raw', client_hello('chat.signal.org', ['http/1.1'])),
             (0.05, 'c2s', 'raw', finished_record()),
             (0.05, 'c2s', 'plain', upgrade(False)),
             (0.2, 'c2s', 'plain', ws_frame(2, send)),
             (0.4, 'c2s', 'plain', ws_frame(2, fetch)),
             # After 31 s without sending: a ping whose payload is the ping counter (from 1)
             # (rust/net/infra/src/ws/connection.rs, WS_KEEP_ALIVE_INTERVAL = 31 s).
             (31.4, 'c2s', 'plain', ws_frame(9, b'\x01')),
             (62.4, 'c2s', 'plain', ws_frame(9, b'\x02')),
             # Disconnect: Close 1000 with an empty reason (rust/net/infra/src/ws/connection.rs
             # lines 328-346, Event::ClientDisconnect), then the stream is dropped: no
             # close_notify, no wait for the server's Close.
             (63.0, 'c2s', 'plain', ws_frame(8, u16(1000)))]
    # Connection 2: authenticated socket: answers the server's requests with 200 "OK"
    # (`response_for_status`: status canonical reason), pings when idle.
    conn2 = [(0.0, 'c2s', 'raw', client_hello('chat.signal.org', ['http/1.1'])),
             (0.05, 'c2s', 'raw', finished_record()),
             (0.05, 'c2s', 'plain', upgrade(True)),
             (0.3, 'c2s', 'plain', ws_frame(2, response(7, 200, 'OK'))),
             (31.3, 'c2s', 'plain', ws_frame(9, b'\x01')),
             # Disconnect, as on connection 1: Close 1000, empty reason (rust/net/infra/src/ws/
             # connection.rs, Event::ClientDisconnect); no close_notify after it (the stream is
             # dropped without SSL_shutdown) and no wait for the server's Close.
             (32.0, 'c2s', 'plain', ws_frame(8, u16(1000)))]
    # Connection 3: libsignal >= 0.97.1 direct route: grpc.chat.signal.org, ALPN h2.
    conn3 = [(0.0, 'c2s', 'raw', client_hello('grpc.chat.signal.org', ['h2'])),
             (0.05, 'c2s', 'raw', finished_record())]
    for n, events in ((1, conn1), (2, conn2), (3, conn3)):
        (tdir / f'{n}.json').write_text(json.dumps(transcript(n, events)) + '\n')
    subprocess.run([sys.executable, '-I', str(HERE / 'analyze.py'), str(tdir), str(out / 'reference.json')], check=True)
    print(out / 'reference.json')


if __name__ == '__main__':
    main()
