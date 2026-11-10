#!/usr/bin/env python3
"""LOCAL TLS 1.3 terminator in front of the local Signal-Server's plain h2c/HTTP-1.1 port.

The local Signal-Server (test configuration) listens without TLS. The MPC client
requires TLS 1.3 and validates the server chain against a configured trust root
(state/tls/ca.pem). This terminator uses the same TLS profile as the existing
fixture server (signal_backend/VariableServiceWork/fixture_server.py): TLS 1.3
only, X25519, ALPN http/1.1, no session tickets. It forwards plaintext bytes
unchanged in both directions, so the real server sees exactly the client's HTTP
upgrade request and WebSocket frames.

Optionally (--transcripts DIR) it writes per-connection plaintext transcripts:
  <n>.c2s.bin / <n>.s2c.bin   raw bytes; <n>.json  summary (TLS version, cipher, ALPN, sizes)
Transcripts contain credentials (Authorization header) of LOCAL test accounts only.

Only binds to 127.0.0.1. Never point --backend at anything but the local server.

Usage: tls_terminator.py --cert state/tls/server.pem --key state/tls/server.key \
          [--listen 18443] [--backend 127.0.0.1:18080] [--require-aes128] [--transcripts logs/transcripts]
"""
import argparse, asyncio, json, ssl, sys, time
from pathlib import Path

LOCAL_BACKENDS = ('127.0.0.1', 'localhost', '::1')


def make_context(cert, key, aes128_only):
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.minimum_version = ctx.maximum_version = ssl.TLSVersion.TLSv1_3
    ctx.load_cert_chain(cert, key)
    ctx.set_alpn_protocols(['http/1.1'])
    ctx.set_ecdh_curve('X25519')
    ctx.num_tickets = 0
    if aes128_only and hasattr(ctx, 'set_ciphersuites'):
        # Newer Pythons can restrict TLS 1.3 suites; otherwise the post-handshake check rejects.
        ctx.set_ciphersuites('TLS_AES_128_GCM_SHA256')
    return ctx


async def pump(reader, writer, sink, counter, key):
    try:
        while True:
            data = await reader.read(65536)
            if not data:
                break
            counter[key] += len(data)
            if sink:
                sink.write(data); sink.flush()
            writer.write(data)
            await writer.drain()
    except (ConnectionError, ssl.SSLError):
        pass
    finally:
        try:
            writer.close()
        except Exception:
            pass


class Terminator:
    def __init__(self, args):
        self.args = args
        self.count = 0
        host, _, port = args.backend.rpartition(':')
        if host not in LOCAL_BACKENDS:
            raise SystemExit('backend must be local')
        self.backend = (host, int(port))
        self.dir = Path(args.transcripts) if args.transcripts else None
        if self.dir:
            self.dir.mkdir(parents=True, exist_ok=True)

    async def handle(self, client_reader, client_writer):
        self.count += 1
        n = self.count
        tls = client_writer.get_extra_info('ssl_object')
        info = dict(connection=n, started=time.time(), version=tls.version(), cipher=tls.cipher()[0],
                    alpn=tls.selected_alpn_protocol())
        print(f'conn {n}: {info["version"]} {info["cipher"]} alpn={info["alpn"]}', flush=True)
        if self.args.require_aes128 and info['cipher'] != 'TLS_AES_128_GCM_SHA256':
            print(f'conn {n}: rejected (cipher)', flush=True)
            client_writer.close(); return
        try:
            backend_reader, backend_writer = await asyncio.open_connection(*self.backend)
        except OSError as e:
            print(f'conn {n}: backend unavailable: {e}', flush=True)
            client_writer.close(); return
        c2s = open(self.dir / f'{n}.c2s.bin', 'wb') if self.dir else None
        s2c = open(self.dir / f'{n}.s2c.bin', 'wb') if self.dir else None
        counter = {'c2s': 0, 's2c': 0}
        try:
            await asyncio.gather(pump(client_reader, backend_writer, c2s, counter, 'c2s'),
                                 pump(backend_reader, client_writer, s2c, counter, 's2c'))
        finally:
            for f in (c2s, s2c):
                if f: f.close()
            info.update(counter, ended=time.time())
            if self.dir:
                (self.dir / f'{n}.json').write_text(json.dumps(info, indent=2) + '\n')
            print(f'conn {n}: closed c2s={counter["c2s"]} s2c={counter["s2c"]}', flush=True)


async def main():
    p = argparse.ArgumentParser()
    p.add_argument('--cert', required=True); p.add_argument('--key', required=True)
    p.add_argument('--listen', type=int, default=18443)
    p.add_argument('--backend', default='127.0.0.1:18080')
    p.add_argument('--require-aes128', action='store_true')
    p.add_argument('--transcripts')
    args = p.parse_args()
    t = Terminator(args)
    server = await asyncio.start_server(t.handle, '127.0.0.1', args.listen, ssl=make_context(args.cert, args.key, args.require_aes128))
    print(f'tls terminator listening on 127.0.0.1:{args.listen} -> {args.backend}', flush=True)
    async with server:
        await server.serve_forever()


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        sys.exit(0)
