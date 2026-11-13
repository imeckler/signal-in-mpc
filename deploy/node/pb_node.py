#!/usr/bin/env python3
"""Runs ON a deployed machine (copied to /opt/pb by Ansible; Python 3 standard library only).

    pb_node.py keys ROLE DATA [--party N] [--image IMAGE] [--dbimage IMAGE]
        Make this machine's private keys if they do not exist yet (they never leave the machine)
        and print the PUBLIC parts as JSON. Idempotent: existing keys are kept, so re-running
        `join` gives the same public keys (and the same fingerprint).
          every node   WireGuard key            DATA/pb/keys/wg.key
          mpc          daemon-link key (X25519)  DATA/pb/keys/link.key   (the shared daemon-link key is
                                                 derived from it and the other node's public key at start)
                       database client key       DATA/tls-mpc/secrets/db-key.json   (handoff_client gen-key)
                       field-engine certificate  DATA/tls-mpc/state/worker-send/Player-Data/PN.key (bench_certs.sh)
          db           node secret seed          DATA/ssdb/keys/seed.json  (from a throwaway `pki` run on
                                                 this machine: only this node's seed is kept)
                       Postgres password         DATA/ssdb/keys/pg-password
          app (test)   notify and signup keys    DATA/app/keys/{notify-key,signup-key}.json
    pb_node.py digests CIRCUITS WORD PINS.json   manifest and word-dir digests, every file checked
    pb_node.py peer-key DATA PEER_LINK.pem NAME  derive DATA/tls-mpc/secrets/peer.key (both nodes get the same)
    pb_node.py trust DATA PEER_CERT.pem          install the other party's field-engine certificate (send and receive dirs)
    pb_node.py sender-cert EXPORT.json           the Signal sender certificate's expiry (JSON)
"""
import base64
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
UID = 10001          # the computation image's user
DB_UID = 10002       # the database image's user


def run(argv, **kw):
    r = subprocess.run(argv, capture_output=True, text=True, **kw)
    if r.returncode:
        raise SystemExit(f'{argv[0]} failed: {(r.stderr or r.stdout).strip()[-400:]}')
    return r.stdout


def private_dir(path, owner=0):
    path.mkdir(parents=True, exist_ok=True)
    os.chmod(path, 0o700)
    os.chown(path, owner, owner)
    return path


def write_private(path, text, owner=0):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, 'w') as f:
        f.write(text)
    os.chown(path, owner, owner)


def wireguard(data):
    keys = private_dir(data / 'pb/keys')
    key = keys / 'wg.key'
    if not key.exists():
        write_private(key, run(['wg', 'genkey']))
    return run(['wg', 'pubkey'], input=key.read_text()).strip()


def cert_info(pem):
    end = run(['openssl', 'x509', '-in', str(pem), '-noout', '-enddate']).strip().split('=', 1)[1]
    fp =run(['openssl', 'x509', '-in', str(pem), '-noout', '-fingerprint', '-sha256']).strip().split('=', 1)[1]
    return dict(not_after=end, sha256=fp.replace(':', '').lower())


def keys_mpc(data, party, image):
    out = {}
    keys = data / 'pb/keys'
    link = keys / 'link.key'
    if not link.exists():
        run(['openssl', 'genpkey', '-algorithm', 'X25519', '-out', str(link)])
        os.chmod(link, 0o600)
    out['link_public_key'] = run(['openssl', 'pkey', '-in', str(link), '-pubout'])
    base = data / 'tls-mpc'
    secrets = private_dir(base / 'secrets', UID)
    state = private_dir(base / 'state', UID)
    db_key = secrets / 'db-key.json'
    if not db_key.exists():
        run(['docker', 'run', '--rm', '--network', 'none', '--user', f'{UID}:{UID}', '-v', f'{secrets}:/k',
             '--entrypoint', '/opt/tls-mpc/bin/handoff_client', image, 'gen-key', '--out', '/k/db-key.json'])
        os.chmod(db_key, 0o600)
    out['db_client_public_key'] = run(['docker', 'run', '--rm', '--network', 'none', '--user', f'{UID}:{UID}', '-v', f'{secrets}:/k:ro',
                                       '--entrypoint', '/opt/tls-mpc/bin/handoff_client', image, 'public-key', '--key', '/k/db-key.json']).strip()
    send = state / 'worker-send'
    own = send / 'Player-Data' / f'P{party}.key'
    if not own.exists():
        send.mkdir(exist_ok=True)
        os.chown(send, UID, UID)
        run(['sh', str(HERE / 'bench_certs.sh'), 'init', str(party), str(send)])
    for p in [send, *send.rglob('*')]:
        os.chown(p, UID, UID)
    pem = send / 'Player-Data' / f'P{party}.pem'
    out['field_certificate'] = pem.read_text()
    out['field_certificate_info'] = cert_info(pem)
    return out


def keys_db(data, dbimage):
    keys = private_dir(data / 'ssdb/keys')
    seed = keys / 'seed.json'
    public = keys / 'public.json'
    if not seed.exists() or not public.exists():
        # A throwaway `pki` run on THIS machine: every seed it makes is random and independent
        # (pki/src/config.rs); keep slot 0's seed and its public keys, discard the rest.
        with tempfile.TemporaryDirectory(dir=keys) as tmp:
            os.chown(tmp, DB_UID, DB_UID)
            run(['docker', 'run', '--rm', '--network', 'none', '--user', f'{DB_UID}:{DB_UID}', '-v', f'{tmp}:/out',
                 '--entrypoint', '/opt/ssdb/bin/pki', dbimage, '-n', '3', '-t', '2', '-l', '--max-malicious', '1',
                 '-o', '/out/pki', '-d', 'postgresql://unused'])
            net = json.loads((Path(tmp) / 'pki/relay/network-config.json').read_text())
            own = json.loads((Path(tmp) / 'pki/share-dbs/0/config.json').read_text())
            write_private(seed, json.dumps({'secret_seed': own['secret_seed']}))
            write_private(public, json.dumps({'public_key': net['public_keys'][0], 'signing_public_key': net['signing_public_keys'][0],
                                              'monitor_public_key': net['monitor_public_key']}))
    pw = keys / 'pg-password'
    if not pw.exists():
        write_private(pw, base64.b32encode(os.urandom(20)).decode().lower().rstrip('='))
    return json.loads(public.read_text())


def keys_app(data, image):
    keys = private_dir(data / 'app/keys', UID)
    out = {}
    for name in ('notify-key', 'signup-key'):
        path = keys / f'{name}.json'
        if not path.exists():
            run(['docker', 'run', '--rm', '--network', 'none', '--user', f'{UID}:{UID}', '-v', f'{keys}:/k',
                 '--entrypoint', '/opt/tls-mpc/bin/handoff_client', image, 'gen-key', '--out', f'/k/{name}.json'])
        out[name.replace('-key', '_public_key')] = run(['docker', 'run', '--rm', '--network', 'none', '--user', f'{UID}:{UID}', '-v', f'{keys}:/k:ro',
                                                        '--entrypoint', '/opt/tls-mpc/bin/handoff_client', image, 'public-key', '--key', f'/k/{name}.json']).strip()
    return {'notify_public_key': out['notify_public_key'], 'signup_public_key': out['signup_public_key']}


def cmd_keys(args):
    role, data = args[0], Path(args[1])
    opts = dict(zip(args[2::2], args[3::2]))
    out = dict(wireguard_public_key=wireguard(data))
    if role == 'mpc':
        out['mpc'] = keys_mpc(data, int(opts['--party']), opts['--image'])
    elif role == 'db':
        out['db'] = keys_db(data, opts['--dbimage'])
    elif role == 'app':
        out['app'] = keys_app(data, opts['--image'])
    print(json.dumps(out))


def cmd_digests(args):
    sys.path.insert(0, str(HERE))
    import deploylib as dl
    circuits, word, pins = Path(args[0]), Path(args[1]), json.loads(Path(args[2]).read_text())
    problems, stats = dl.check_manifest_files(circuits / 'manifest.txt')
    wproblems, wstats = dl.word_dir_summary(word, pins)
    print(json.dumps(dict(manifest_sha256=stats['manifest_sha256'], kernels=stats['kernels'], gate_list_bytes=stats['gate_list_bytes'],
                          circuit_problems=problems, word_dir_sha256=wstats.get('word_dir_sha256'), word_problems=wproblems,
                          v3_programs=wstats.get('v3_programs'), pins_sha256=hashlib.sha256(json.dumps(pins, sort_keys=True).encode()).hexdigest())))


def cmd_peer_key(args):
    data, peer_pem, name = Path(args[0]), Path(args[1]), args[2]
    secret = subprocess.run(['openssl', 'pkeyutl', '-derive', '-inkey', str(data / 'pb/keys/link.key'), '-peerkey', str(peer_pem)],
                            capture_output=True, check=True).stdout
    if len(secret) != 32:
        raise SystemExit('X25519 derivation did not give 32 bytes')
    key = hashlib.sha256(b'tls-mpc daemon-link key v1\0' + name.encode() + b'\0' + secret).hexdigest()
    target = data / 'tls-mpc/secrets/peer.key'
    old = target.read_text().strip() if target.exists() else None
    write_private(target, key + '\n', UID)
    print(json.dumps(dict(changed=old != key, fingerprint=hashlib.sha256(b'peer-key-fingerprint\0' + key.encode()).hexdigest()[:16])))


def cmd_trust(args):
    data, pem = Path(args[0]), Path(args[1])
    state = data / 'tls-mpc/state'
    send, receive = state / 'worker-send', state / 'worker-receive'
    run(['sh', str(HERE / 'bench_certs.sh'), 'trust', str(pem), str(send)])
    if receive.exists():
        shutil.rmtree(receive)
    shutil.copytree(send, receive, symlinks=True)
    for p in [send, receive, *send.rglob('*'), *receive.rglob('*')]:
        os.chown(p, UID, UID, follow_symlinks=False)
    print(json.dumps(dict(trusted=cert_info(pem))))


def protobuf_fields(data):
    """Top-level fields of a protobuf message: {number: [value, ...]} (varint, fixed64, bytes, fixed32)."""
    fields, i = {}, 0
    while i < len(data):
        key, shift = 0, 0
        while True:
            b = data[i]; i += 1
            key |= (b & 0x7f) << shift; shift += 7
            if b < 0x80:
                break
        number, wire = key >> 3, key & 7
        if wire == 0:
            value, shift = 0, 0
            while True:
                b = data[i]; i += 1
                value |= (b & 0x7f) << shift; shift += 7
                if b < 0x80:
                    break
        elif wire == 1:
            value = data[i:i + 8]; i += 8
        elif wire == 2:
            length, shift = 0, 0
            while True:
                b = data[i]; i += 1
                length |= (b & 0x7f) << shift; shift += 7
                if b < 0x80:
                    break
            value = data[i:i + length]; i += length
        elif wire == 5:
            value = data[i:i + 4]; i += 4
        else:
            raise ValueError(f'unsupported wire type {wire}')
        fields.setdefault(number, []).append(value)
    return fields


def sender_certificate_expiry(export_path):
    """SenderCertificate (Signal-Server TextSecure.proto): field 1 = Certificate bytes; inside it,
    field 3 `expires` is a fixed64 in milliseconds. Reads only `sender.certificate_hex` of the export
    (the certificate is public: the server hands it to every recipient)."""
    sender = json.loads(Path(export_path).read_text()).get('sender') or {}
    if sender.get('certificate_expires_ms'):
        return int(sender['certificate_expires_ms'])
    outer = protobuf_fields(bytes.fromhex(sender['certificate_hex']))
    inner = protobuf_fields(outer[1][0])
    return int.from_bytes(inner[3][0], 'little')


def cmd_sender_cert(args):
    print(json.dumps(dict(expires_ms=sender_certificate_expiry(args[0]))))


def cmd_image_facts(args):
    """IMAGE [node|dbnode]: its id, architecture, and (computation image) mode and binaries' digest."""
    image, kind = args[0], args[1]
    ident, arch = run(['docker', 'image', 'inspect', image, '--format', '{{.Id}} {{.Architecture}}']).split()
    out = dict(image_id=ident.removeprefix('sha256:'), image_arch=arch)
    if kind == 'node':
        info = json.loads(run(['docker', 'run', '--rm', '--network', 'none', image, 'version']))
        out.update(mode=info.get('mode'), build_commit=(info.get('context') or {}).get('commit'),
                   binaries_sha256=hashlib.sha256(json.dumps(info.get('binaries') or {}, sort_keys=True).encode()).hexdigest())
    print(json.dumps(out))


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    command, args = sys.argv[1], sys.argv[2:]
    {'keys': cmd_keys, 'digests': cmd_digests, 'peer-key': cmd_peer_key, 'trust': cmd_trust,
     'sender-cert': cmd_sender_cert, 'image-facts': cmd_image_facts}[command](args)
    return 0


if __name__ == '__main__':
    sys.exit(main())
