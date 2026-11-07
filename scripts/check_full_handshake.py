#!/usr/bin/env python3
"""Run the Lean TLS client against real OpenSSL memory-BIO servers.

PUBLIC FIXTURES ONLY: the client uses a documented fixed test scalar. This
checks protocol integration and authentication failures, not MPC execution.
"""
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from cryptography import x509
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, ed25519, ed448, rsa
from cryptography.x509.oid import ExtendedKeyUsageOID, NameOID

ROOT = Path(__file__).resolve().parents[1]
OPENSSL = Path('/opt/homebrew/opt/openssl@3')


def certificates(directory):
    now = datetime.now(timezone.utc)
    ca_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, 'PUBLIC TLS MPC fixture CA')])
    ca = (x509.CertificateBuilder().subject_name(name).issuer_name(name)
          .public_key(ca_key.public_key()).serial_number(x509.random_serial_number())
          .not_valid_before(now - timedelta(days=2)).not_valid_after(now + timedelta(days=30))
          .add_extension(x509.BasicConstraints(ca=True, path_length=1), critical=True)
          .add_extension(x509.KeyUsage(False, False, False, False, False, True, True, False, False), critical=True)
          .sign(ca_key, hashes.SHA256()))
    ca_pem = ca.public_bytes(serialization.Encoding.PEM)
    (directory / 'ca.pem').write_bytes(ca_pem)
    profiles = {}
    for kind in ('rsa', 'p256', 'p384', 'p521', 'ed25519', 'ed448', 'expired', 'future', 'client-usage', 'cn-only'):
        if kind.startswith('p') and kind[1:].isdigit():
            key = ec.generate_private_key({'p256': ec.SECP256R1, 'p384': ec.SECP384R1, 'p521': ec.SECP521R1}[kind]())
        elif kind == 'ed25519':
            key = ed25519.Ed25519PrivateKey.generate()
        elif kind == 'ed448':
            key = ed448.Ed448PrivateKey.generate()
        else:
            key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        before = now + timedelta(days=1) if kind == 'future' else now - timedelta(days=1)
        after = now - timedelta(hours=1) if kind == 'expired' else now + timedelta(days=7)
        leaf = (x509.CertificateBuilder().subject_name(x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, 'server.example')]))
                .issuer_name(name).public_key(key.public_key()).serial_number(x509.random_serial_number())
                .not_valid_before(before).not_valid_after(after)
                .add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
                .add_extension(x509.ExtendedKeyUsage([ExtendedKeyUsageOID.CLIENT_AUTH if kind == 'client-usage'
                                                    else ExtendedKeyUsageOID.SERVER_AUTH]), critical=False))
        if kind != 'cn-only':
            leaf = leaf.add_extension(x509.SubjectAlternativeName([x509.DNSName('server.example')]), critical=False)
        leaf = leaf.sign(ca_key, hashes.SHA256())
        cert_path, key_path = directory / f'{kind}.pem', directory / f'{kind}.key'
        cert_path.write_bytes(leaf.public_bytes(serialization.Encoding.PEM) + ca_pem)
        key_path.write_bytes(key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                              serialization.NoEncryption()))
        profiles[kind] = (cert_path, key_path)
    return profiles, directory / 'ca.pem'


def main():
    subprocess.run(['lake', 'build', 'handshake_fixture'], cwd=ROOT, check=True)
    result = []
    with tempfile.TemporaryDirectory(prefix='tls-mpc-full-handshake-') as tmp:
        directory = Path(tmp)
        for name in ('public_auth', 'fixture_server'):
            subprocess.run(['c++', '-std=c++20', '-O2', '-I' + str(OPENSSL / 'include'),
                            str(ROOT / f'handshake_backend/{name}.cpp'), '-L' + str(OPENSSL / 'lib'),
                            '-lssl', '-lcrypto', '-o', str(directory / name)], check=True)
        profiles, trust = certificates(directory)
        tests = [(kind, 0, 'no', 'no', 'valid', True) for kind in ('rsa', 'p256', 'p384', 'p521', 'ed25519', 'ed448')]
        tests += [('rsa', 512, 'no', 'no', 'valid', True), ('rsa', 0, 'no', 'yes', 'valid', True),
                  ('rsa', 0, 'yes', 'no', 'valid', True), ('rsa', 512, 'yes', 'yes', 'valid', True)]
        tests += [('rsa', 0, 'no', 'no', mode, False) for mode in ('bad-host', 'bad-signature', 'bad-finished', 'bad-tag', 'fail-client-finished')]
        tests += [(kind, 0, 'no', 'no', 'valid', False) for kind in ('expired', 'future', 'client-usage', 'cn-only')]
        tests += [('rsa', 512, 'no', 'no', mode, True) for mode in
                  ('post-server-close', 'post-client-close', 'post-corrupt', 'post-replay', 'post-h2')]
        tests += [('ed25519', 512, 'yes', 'yes', 'post-h2', True)]
        for kind, fragment, request, retry, mode, accepted in tests:
            cert, key = profiles[kind]
            command = [str(ROOT / '.lake/build/bin/handshake_fixture'), str(directory / 'fixture_server'),
                       str(directory / 'public_auth'), str(cert), str(key), str(trust),
                       str(fragment), request, retry, mode]
            run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=180)
            if run.returncode:
                raise RuntimeError(f'fixture crashed ({kind}, {mode}): {run.stdout}\n{run.stderr}')
            observed = json.loads(run.stdout)
            if observed['accepted'] != accepted:
                raise AssertionError((kind, fragment, request, retry, mode, observed, run.stderr))
            if mode.startswith('post-'):
                post = observed['post_handshake']
                assert post['send_key_rotations'] == post['receive_key_rotations'] == 4
                assert post['cleanup_count'] == 1
                assert post['events'].count(3) == 4
                assert post['events'].count(1) == 6  # The 1205-byte echo spans three records.
                assert post['tampered_or_replayed_record_rejected'] == (mode in ('post-corrupt', 'post-replay'))
                assert observed['alpn'] == ('h2' if mode == 'post-h2' else 'http/1.1')
            case = {'certificate': kind, 'fragment_limit': fragment, 'certificate_request': request == 'yes',
                    'hello_retry': retry == 'yes', 'mode': mode, 'expected_accept': accepted, **observed}
            print(json.dumps(case), flush=True)
            result.append(case)
    names = ('TlsMpc/TlsWorker.lean', 'TlsMpc/TlsClient.lean', 'TlsMpc/TlsWire.lean', 'TlsMpc/TlsPublicHandshake.lean',
             'TlsMpc/TlsReceive.lean', 'TlsMpc/TlsInner.lean', 'TlsMpc/TlsHandshake.lean',
             'TlsMpc/FieldDag.lean', 'TlsMpc/X25519.lean', 'TlsMpc/TlsKdf.lean', 'TlsMpc/TlsKdfPrepared.lean',
             'TlsMpc/HmacPrepared.lean', 'TlsMpc/Sha256.lean', 'TlsMpc/TlsRecord.lean', 'TlsMpc/GcmOpen.lean',
             'TlsMpc/Gcm.lean', 'TlsMpc/Ghash.lean', 'TlsMpc/Aes.lean', 'TlsMpc/AesSbox.lean',
             'TlsMpc/ByteAuth.lean', 'TlsMpc/TlsApplication.lean', 'TlsMpc/TlsApplicationPolicy.lean',
             'TlsMpc/TlsApplicationRoute.lean', 'TlsMpc/TlsPostHandshake.lean',
             'HandshakeFixture.lean', 'handshake_backend/public_auth.cpp',
             'handshake_backend/fixture_server.cpp', 'scripts/check_full_handshake.py')
    report = {'kind': 'lean_full_tls_handshake_and_application_fixture_checks',
              'checked_utc': datetime.now(timezone.utc).isoformat(), 'cases': result,
              'openssl_version': subprocess.check_output([str(OPENSSL/'bin/openssl'), 'version', '-a'], text=True),
              'profile': 'TLS1.3, X25519, AES128-GCM, SHA256, certificate authentication; no PSK/0RTT/client credential',
              'public_server_auth_metadata_authorized': True,
              'native_mpc_executed': False, 'localhost_sockets_used': False, 'throughput_measured': False,
              'source_sha256': {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in names},
              'limitations': ['Client backend executes clear Lean specifications on public fixture inputs.',
                             'This report does not establish mixed MPC execution or operational erasure.',
                             'OpenSSL certificate/signature validation is an explicitly unverified public boundary.',
                             'No session tickets, resumption or client credentials are tested.',
                             'h2 tests check TLS ALPN and protected opaque bytes, not an HTTP/2 implementation.']}
    (ROOT / 'benchmarks/results/lean-full-handshake-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
