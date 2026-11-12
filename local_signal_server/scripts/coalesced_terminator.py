#!/usr/bin/env python3
"""LOCAL TLS 1.3 terminator whose handshake has PRODUCTION's shape (real_signal/state/
handshake-production.json, measured 2026-11-12 at chat.signal.org):

  * the whole encrypted server flight (EncryptedExtensions, Certificate, CertificateVerify,
    Finished) in ONE record, with `--pad` bytes of TLSInnerPlaintext zero padding (production: 16);
  * ONE certificate in the chain (`--leaf-only`: only the first certificate of --cert is sent; the
    client must build the path to its trust root itself), an Ed25519 key, CertificateVerify 0x0807;
  * a ChangeCipherSpec after the ServerHello when the client sent a legacy session id
    (middlebox compatibility, as BoringSSL does).

tls_terminator.py (Python's ssl, OpenSSL) cannot do the first: OpenSSL writes each handshake
message in its own record (the local server's 43, 922, 94, 58). This one implements the server
side of TLS 1.3 itself, for exactly one profile: TLS_AES_128_GCM_SHA256, X25519, an Ed25519
certificate, ALPN http/1.1, no tickets, no client certificates, no HelloRetryRequest. Then it
forwards plaintext both ways, as tls_terminator.py does (KeyUpdate from the client is followed).

Only binds to 127.0.0.1; the backend must be local. TEST KEYS ONLY (state/tls).

Usage: coalesced_terminator.py --cert state/tls/server.pem --key state/tls/server.key
          [--listen 19443] [--backend 127.0.0.1:19080] [--pad 16] [--leaf-only]
"""
import argparse, asyncio, hashlib, hmac, os, struct, sys
from cryptography import x509
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

LOCAL_BACKENDS = ('127.0.0.1', 'localhost', '::1')


def hkdf_extract(salt, ikm):
    return hmac.new(salt, ikm, hashlib.sha256).digest()


def hkdf_expand_label(secret, label, context, length):
    info = struct.pack('>H', length) + bytes([len(b'tls13 ' + label)]) + b'tls13 ' + label + bytes([len(context)]) + context
    out, block, i = b'', b'', 1
    while len(out) < length:
        block = hmac.new(secret, block + info + bytes([i]), hashlib.sha256).digest()
        out += block
        i += 1
    return out[:length]


def derive_secret(secret, label, transcript):
    return hkdf_expand_label(secret, label, hashlib.sha256(transcript).digest(), 32)


def handshake(kind, body):
    return bytes([kind]) + len(body).to_bytes(3, 'big') + body


def vector(size, body):
    return len(body).to_bytes(size, 'big') + body


class Keys:
    """One direction's traffic keys and sequence number."""

    def __init__(self, secret):
        self.secret = secret
        self.aead = AESGCM(hkdf_expand_label(secret, b'key', b'', 16))
        self.iv = hkdf_expand_label(secret, b'iv', b'', 12)
        self.seq = 0

    def nonce(self):
        n = bytes(a ^ b for a, b in zip(self.iv, self.seq.to_bytes(12, 'big')))
        self.seq += 1
        return n

    def seal(self, kind, content, pad=0):
        inner = content + bytes([kind]) + bytes(pad)
        header = bytes([23, 3, 3]) + (len(inner) + 16).to_bytes(2, 'big')
        return header + self.aead.encrypt(self.nonce(), inner, header)

    def open(self, header, body):
        inner = self.aead.decrypt(self.nonce(), body, header).rstrip(b'\x00')
        if not inner:
            raise ValueError('empty inner plaintext')
        return inner[-1], inner[:-1]

    def updated(self):
        return Keys(hkdf_expand_label(self.secret, b'traffic upd', b'', 32))


async def read_record(reader):
    header = await reader.readexactly(5)
    body = await reader.readexactly(int.from_bytes(header[3:5], 'big'))
    if len(body) > 16640:
        raise ValueError('record too long')
    return header, body


def parse_client_hello(body):
    at = 2 + 32
    session = body[at + 1:at + 1 + body[at]]
    at += 1 + body[at]
    suites = body[at + 2:at + 2 + int.from_bytes(body[at:at + 2], 'big')]
    at += 2 + len(suites)
    at += 1 + body[at]
    end = at + 2 + int.from_bytes(body[at:at + 2], 'big')
    at += 2
    extensions = {}
    while at < end:
        kind, size = int.from_bytes(body[at:at + 2], 'big'), int.from_bytes(body[at + 2:at + 4], 'big')
        extensions[kind] = body[at + 4:at + 4 + size]
        at += 4 + size
    if b'\x13\x01' not in [suites[i:i + 2] for i in range(0, len(suites), 2)]:
        raise ValueError('TLS_AES_128_GCM_SHA256 not offered')
    versions = extensions.get(0x2b, b'')
    if b'\x03\x04' not in [versions[i:i + 2] for i in range(1, len(versions), 2)]:
        raise ValueError('TLS 1.3 not offered')
    shares, key = extensions.get(0x33, b''), None
    at = 2
    while at < len(shares):
        group, size = int.from_bytes(shares[at:at + 2], 'big'), int.from_bytes(shares[at + 2:at + 4], 'big')
        if group == 0x1d and size == 32:
            key = shares[at + 4:at + 36]
        at += 4 + size
    if key is None:
        raise ValueError('no X25519 key share (a HelloRetryRequest is not implemented)')
    alpn = extensions.get(0x10)
    offered = []
    if alpn:
        at = 2
        while at < len(alpn):
            offered.append(alpn[at + 1:at + 1 + alpn[at]])
            at += 1 + alpn[at]
    schemes = extensions.get(0x0d, b'')
    if b'\x08\x07' not in [schemes[i:i + 2] for i in range(2, len(schemes), 2)]:
        raise ValueError('Ed25519 signatures not offered')
    return session, key, offered


class Terminator:
    def __init__(self, args):
        self.args = args
        host, _, port = args.backend.rpartition(':')
        if host not in LOCAL_BACKENDS:
            raise SystemExit('backend must be local')
        self.backend = (host, int(port))
        pem = open(args.cert, 'rb').read()
        self.chain = [c.public_bytes(serialization.Encoding.DER) for c in x509.load_pem_x509_certificates(pem)]
        if args.leaf_only:
            self.chain = self.chain[:1]
        self.key = serialization.load_pem_private_key(open(args.key, 'rb').read(), None)
        if not isinstance(self.key, Ed25519PrivateKey):
            raise SystemExit('the certificate key must be Ed25519')
        self.count = 0

    async def handle(self, reader, writer):
        self.count += 1
        n = self.count
        try:
            client, server = await self.handshake(reader, writer, n)
        except (ValueError, KeyError, IndexError, asyncio.IncompleteReadError, ConnectionError) as e:
            print(f'conn {n}: handshake failed: {type(e).__name__}: {e}', flush=True)
            writer.close()
            return
        try:
            backend_reader, backend_writer = await asyncio.open_connection(*self.backend)
        except OSError as e:
            print(f'conn {n}: backend unavailable: {e}', flush=True)
            writer.close()
            return
        counter = {'c2s': 0, 's2c': 0}

        async def up():
            nonlocal client
            try:
                while True:
                    header, body = await read_record(reader)
                    if header[0] == 20:
                        continue
                    kind, content = client.open(header, body)
                    if kind == 23:
                        counter['c2s'] += len(content)
                        backend_writer.write(content)
                        await backend_writer.drain()
                    elif kind == 22 and content[:1] == b'\x18':
                        # KeyUpdate: follow it; if the client asks, update ours too and say so.
                        client = client.updated()
                        if content[4:5] == b'\x01':
                            writer.write(state['server'].seal(22, handshake(24, b'\x00')))
                            state['server'] = state['server'].updated()
                            await writer.drain()
                    else:
                        break
            except (asyncio.IncompleteReadError, ConnectionError, ValueError):
                pass
            finally:
                backend_writer.close()

        async def down():
            try:
                while True:
                    data = await backend_reader.read(16384)
                    if not data:
                        break
                    counter['s2c'] += len(data)
                    writer.write(state['server'].seal(23, data))
                    await writer.drain()
            except ConnectionError:
                pass
            finally:
                writer.close()

        state = {'server': server}
        await asyncio.gather(up(), down())
        print(f'conn {n}: closed c2s={counter["c2s"]} s2c={counter["s2c"]}', flush=True)

    async def handshake(self, reader, writer, n):
        buffered = b''
        while len(buffered) < 4 or len(buffered) < 4 + int.from_bytes(buffered[1:4], 'big'):
            header, body = await read_record(reader)
            if header[0] != 22:
                raise ValueError('expected a plaintext ClientHello')
            buffered += body
        if buffered[0] != 1:
            raise ValueError('expected ClientHello')
        hello = buffered[:4 + int.from_bytes(buffered[1:4], 'big')]
        session, their_share, offered = parse_client_hello(hello[4:])
        ours = X25519PrivateKey.generate()
        share = ours.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
        shared = ours.exchange(X25519PublicKey.from_public_bytes(their_share))
        extensions = struct.pack('>HHH', 0x2b, 2, 0x0304) + struct.pack('>HHHH', 0x33, 36, 0x1d, 32) + share
        server_hello = handshake(2, b'\x03\x03' + os.urandom(32) + vector(1, session) + b'\x13\x01\x00' + vector(2, extensions))
        transcript = hello + server_hello
        early = hkdf_extract(bytes(32), bytes(32))
        secret = hkdf_extract(derive_secret(early, b'derived', b''), shared)
        client_hs, server_hs = derive_secret(secret, b'c hs traffic', transcript), derive_secret(secret, b's hs traffic', transcript)
        out = bytes([22, 3, 3]) + vector(2, server_hello)
        if session:
            out += bytes([20, 3, 3, 0, 1, 1])
        alpn = b'http/1.1' if b'http/1.1' in offered else None
        ee = handshake(8, vector(2, struct.pack('>HH', 0x10, len(alpn) + 3) + vector(2, vector(1, alpn)) if alpn else b''))
        certificate = handshake(11, b'\x00' + vector(3, b''.join(vector(3, der) + b'\x00\x00' for der in self.chain)))
        transcript += ee + certificate
        signed = b' ' * 64 + b'TLS 1.3, server CertificateVerify\x00' + hashlib.sha256(transcript).digest()
        verify = handshake(15, b'\x08\x07' + vector(2, self.key.sign(signed)))
        transcript += verify
        finished_key = hkdf_expand_label(server_hs, b'finished', b'', 32)
        finished = handshake(20, hmac.new(finished_key, hashlib.sha256(transcript).digest(), hashlib.sha256).digest())
        transcript += finished
        flight = ee + certificate + verify + finished
        server_keys = Keys(server_hs)
        record = server_keys.seal(22, flight, self.args.pad)
        writer.write(out + record)
        await writer.drain()
        master = hkdf_extract(derive_secret(secret, b'derived', b''), bytes(32))
        client_ap, server_ap = derive_secret(master, b'c ap traffic', transcript), derive_secret(master, b's ap traffic', transcript)
        client_keys = Keys(client_hs)
        while True:
            header, body = await read_record(reader)
            if header[0] == 20:
                continue
            kind, content = client_keys.open(header, body)
            if kind != 22 or content[:1] != b'\x14':
                raise ValueError('expected the client Finished')
            expected = hmac.new(hkdf_expand_label(client_hs, b'finished', b'', 32), hashlib.sha256(transcript).digest(), hashlib.sha256).digest()
            if not hmac.compare_digest(content[4:], expected):
                raise ValueError('client Finished does not verify')
            break
        print(f'conn {n}: TLS 1.3 handshake done: flight in one record of {len(record)} bytes ({len(self.chain)} certificate(s), pad {self.args.pad}), '
              f'alpn {alpn}', flush=True)
        return Keys(client_ap), Keys(server_ap)


async def main():
    p = argparse.ArgumentParser()
    p.add_argument('--cert', required=True)
    p.add_argument('--key', required=True)
    p.add_argument('--listen', type=int, default=19443)
    p.add_argument('--backend', default='127.0.0.1:19080')
    p.add_argument('--pad', type=int, default=16)
    p.add_argument('--leaf-only', action='store_true')
    args = p.parse_args()
    t = Terminator(args)
    server = await asyncio.start_server(t.handle, '127.0.0.1', args.listen)
    print(f'coalesced terminator listening on 127.0.0.1:{args.listen} -> {args.backend}', flush=True)
    async with server:
        await server.serve_forever()


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        sys.exit(0)
