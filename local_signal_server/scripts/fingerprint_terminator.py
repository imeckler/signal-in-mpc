#!/usr/bin/env python3
"""LOCAL capturing TLS 1.3 terminator for the client-fingerprint check (CLIENT_FINGERPRINT.md).

Like tls_terminator.py (same TLS profile, same backend), but it runs TLS itself on memory BIOs,
so it sees and records every byte the client puts on the wire: the raw ClientHello and the
encrypted records (sizes, timing), and after decryption the HTTP upgrade request and every
WebSocket frame. One JSON file per connection in --out:

  {"connection": n, "started": t0, "tls": {...}, "events": [[seconds, "c2s"|"s2c", "raw"|"plain", hex], ...]}

"raw" events are the bytes exactly as they crossed the TCP socket; "plain" events are the
decrypted application bytes. Transcripts hold LOCAL test-account credentials only; the
analyzer (fingerprint/analyze.py) redacts them before anything is stored in the repository.

Only binds to 127.0.0.1 and only forwards to a local backend. Its own port (default 18445), so it
never disturbs the shared terminator on 18443.

Usage: fingerprint_terminator.py --cert state/tls/server.pem --key state/tls/server.key --out DIR
         [--listen 18445] [--backend 127.0.0.1:18080] [--alpn http/1.1]
"""
import argparse, json, selectors, socket, ssl, sys, threading, time
from pathlib import Path

LOCAL_BACKENDS = ('127.0.0.1', 'localhost', '::1')


def context(cert, key, alpn):
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.minimum_version = ctx.maximum_version = ssl.TLSVersion.TLSv1_3
    ctx.load_cert_chain(cert, key)
    ctx.set_alpn_protocols(alpn)
    ctx.set_ecdh_curve('X25519')
    ctx.num_tickets = 0
    return ctx


class Connection:
    def __init__(self, n, client, ctx, backend, out):
        self.n, self.client, self.backend_address, self.out = n, client, backend, out
        self.incoming, self.outgoing = ssl.MemoryBIO(), ssl.MemoryBIO()
        self.tls = ctx.wrap_bio(self.incoming, self.outgoing, server_side=True)
        self.t0 = time.time()
        self.events = []
        self.backend = None

    def log(self, direction, kind, data):
        if data:
            self.events.append([round(time.time() - self.t0, 6), direction, kind, data.hex()])

    def flush(self):
        data = self.outgoing.read()
        if data:
            self.log('s2c', 'raw', data)
            self.client.sendall(data)

    def pump_tls(self):
        """Read decrypted application bytes; forward them to the backend."""
        while True:
            try:
                data = self.tls.read(65536)
            except ssl.SSLWantReadError:
                return True
            except (ssl.SSLZeroReturnError, ssl.SSLEOFError):
                return False
            if not data:
                return False
            self.log('c2s', 'plain', data)
            self.backend.sendall(data)

    def run(self):
        info = dict(connection=self.n, started=self.t0)
        try:
            sel = selectors.DefaultSelector()
            sel.register(self.client, selectors.EVENT_READ, 'client')
            handshaken = False
            while True:
                ready = sel.select(timeout=600)
                if not ready:
                    break
                done = False
                for key, _ in ready:
                    if key.data == 'client':
                        data = self.client.recv(65536)
                        if not data:
                            done = True
                            break
                        self.log('c2s', 'raw', data)
                        self.incoming.write(data)
                        if not handshaken:
                            try:
                                self.tls.do_handshake()
                                handshaken = True
                                info['tls'] = dict(version=self.tls.version(), cipher=self.tls.cipher()[0],
                                                   alpn=self.tls.selected_alpn_protocol())
                                self.backend = socket.create_connection(self.backend_address)
                                sel.register(self.backend, selectors.EVENT_READ, 'backend')
                            except ssl.SSLWantReadError:
                                pass
                            self.flush()
                        if handshaken and not self.pump_tls():
                            self.flush()
                            done = True
                            break
                        self.flush()
                    else:
                        data = self.backend.recv(65536)
                        if not data:
                            done = True
                            break
                        self.log('s2c', 'plain', data)
                        self.tls.write(data)
                        self.flush()
                if done:
                    break
        except (OSError, ssl.SSLError) as e:
            info['error'] = f'{type(e).__name__}: {e}'
        finally:
            for s in (self.client, self.backend):
                if s is not None:
                    try:
                        s.close()
                    except OSError:
                        pass
            info['ended'] = time.time()
            info['events'] = self.events
            (self.out / f'{self.n}.json').write_text(json.dumps(info) + '\n')
            print(f'conn {self.n}: closed, {len(self.events)} events', flush=True)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--cert', required=True)
    p.add_argument('--key', required=True)
    p.add_argument('--out', required=True)
    p.add_argument('--listen', type=int, default=18445)
    p.add_argument('--backend', default='127.0.0.1:18080')
    p.add_argument('--alpn', default='http/1.1')
    a = p.parse_args()
    host, _, port = a.backend.rpartition(':')
    if host not in LOCAL_BACKENDS:
        raise SystemExit('backend must be local')
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    ctx = context(a.cert, a.key, a.alpn.split(','))
    server = socket.socket()
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind(('127.0.0.1', a.listen))
    server.listen(16)
    print(f'fingerprint terminator listening on 127.0.0.1:{a.listen} -> {a.backend}, transcripts in {out}', flush=True)
    n = 0
    while True:
        client, _ = server.accept()
        n += 1
        threading.Thread(target=Connection(n, client, ctx, (host, int(port)), out).run, daemon=True).start()


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(0)
