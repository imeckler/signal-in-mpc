#!/usr/bin/env python3
"""S12 end-to-end check (test set E/K) with the REAL engines. NOT RUN in stage S12 (it needs the
heavy-job lock). Two parts:

1. `vectors` (default): two node-worker processes run the Lean-generated S12 flows
   (tests/s12_vectors.txt: GHASH key-power shares, a seal of "ping", an open of "hello!", a forged
   open) while this script plays the controller's side of both pipes and compares every reply with
   the reply the Lean model computes, as tests/e2e_s10.py does. The vectors' circuits are the
   kernels' specifications; the real workers run the pinned kernels, which compute the same
   functions (gcmKeyShare_spec, gcmMultiply_spec, gcmTag_spec, gcmCheck_spec, tlsSealCtr_spec,
   openParsed_refines, direct_refines), so the replies must be equal byte for byte.

       python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s12.py NODE_WORKER

   Prerequisites: the kernel cache (.deps/emp-hybrid-word-v1/cache) holds the lowered kernels
   gcm-key-share, gcm-multiply, gcm-tag, gcm-check, tls-parser-initial, tls-seal-ctr 23 4 0,
   tls-open-typed 32 (produce_circuits.py with these names, heavy, alone); the word circuit
   xor-bit.flat exists. A one-session manifest of exactly these kernels is written here.

2. `handshake`: the handshake fixture of handshake_backend/EmpHybridWork/check_tls_worker_v3.py
   moved to the new backend. It needs what this branch does not have: the controller-side script
   runner (`TlsBackend.Runner`, sending op 93 batches from Lean) and S11's `KeyAgreement`
   (`Curve.split` / `Curve.agree`). Once both exist: build `session_handshake_fixture` with
   `Flow.Tls.handshake` replaced by `TlsClient.run (TlsBackend.scriptBackend runner agreement check
   refs) transport config` (and `TlsApplication.make (TlsBackend.scriptApplicationBackend …)` for the
   records), then run check_tls_worker_v3.py's server and controller exactly as today:

       python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s12.py NODE_WORKER handshake

   This script refuses that mode until `TLS_SCRIPT_BACKEND_FIXTURE` names the built fixture.

Writes only under .deps/lowering-scratch/s12-e2e/. Ports 24040-24060."""
import hashlib, os, pathlib, queue, secrets, struct, subprocess, sys, threading, time, json
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / '.deps/lowering-scratch/s12-e2e' / secrets.token_hex(6)
MP = ROOT / '.deps/two-party-comparison/data61-MP-SPDZ-113c4e4'
WORDS = ROOT / '.deps/emp-hybrid-word-v1'
VECTORS = ROOT / 'node_worker/tests/s12_vectors.txt'
PORT = 24040
BATCH = 93
KERNELS = ['gcm-key-share', 'gcm-multiply', 'gcm-tag', 'gcm-check', 'tls-parser-initial', 'tls-seal-ctr 23 4 0',
           'tls-open-typed 32']
worker = pathlib.Path(sys.argv[1])
mode = sys.argv[2] if len(sys.argv) > 2 else 'vectors'
report = {'out': str(OUT), 'worker': str(worker), 'mode': mode, 'passed': False}


def rounds(text):
    out, party, end = [], 0, ''
    for line in text.splitlines():
        key, _, rest = line.partition(' ')
        if key == 'round':
            out.append({'batch': [None, None], 'reply': [None, None]})
        elif key == 'party':
            party = 0 if rest == 'a' else 1
        elif key in ('batch', 'reply') and out:
            out[-1][key][party] = bytes.fromhex(rest)
        elif key in ('finished', 'abort', 'error'):
            end = line
    return out, end


def request(code, seq, payload):
    return bytes([code]) + struct.pack('>Q', seq) + struct.pack('>I', len(payload)) + payload


class Worker:
    def __init__(self, party, env, work, session, port):
        self.log = open(OUT / f'worker-{party}-{port}.log', 'w')
        self.p = subprocess.Popen([str(worker), str(party), str(OUT / 'hosts'), str(port),
                                   str(ROOT / 'handshake_backend/EmpHybridWork/circuit_cache.py'), session],
                                  cwd=str(work), env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.log)
        self.replies = queue.Queue()
        threading.Thread(target=self.reader, daemon=True).start()

    def reader(self):
        try:
            while True:
                head = self.p.stdout.read(5)
                if len(head) < 5:
                    self.replies.put(None)
                    return
                size = struct.unpack('>I', head[1:5])[0]
                self.replies.put((head[0], self.p.stdout.read(size)))
        except Exception as e:
            self.replies.put(('error', str(e)))

    def send(self, data):
        self.p.stdin.write(data)
        self.p.stdin.flush()

    def reply(self, wait=900):
        return self.replies.get(timeout=wait)

    def close(self):
        try:
            self.p.stdin.close()
        except Exception:
            pass
        try:
            self.p.wait(timeout=60)
        except Exception:
            self.p.kill()
            self.p.wait()
        self.log.close()


def stem(name):
    return 'kernel-' + name.replace(' ', '-')


def manifest():
    """A manifest of the S12 kernels, each from the kernel cache with its pins checked."""
    cache = WORDS / 'cache'
    d = OUT / 'circuits'
    d.mkdir()
    rows = []
    for name in KERNELS:
        for record in sorted(cache.glob(f'*/{stem(name)}.json'), key=lambda p: p.stat().st_mtime, reverse=True):
            meta = json.loads(record.read_text())
            flat, layout = record.with_suffix('.flat'), record.with_suffix('.layout')
            if not (flat.is_file() and layout.is_file()):
                continue
            if hashlib.sha256(flat.read_bytes()).hexdigest() != meta['sha256'] or \
                    hashlib.sha256(layout.read_bytes()).hexdigest() != meta['layout_sha256']:
                continue
            (d / f'{stem(name)}.flat').write_bytes(flat.read_bytes())
            (d / f'{stem(name)}.layout').write_bytes(layout.read_bytes())
            rows.append(f"{meta['sha256']} {meta['layout_sha256']} {name}")
            break
        else:
            raise SystemExit(f'no usable {name} kernel in the cache (see the prerequisites)')
    (d / 'manifest.txt').write_text('EMP_HYBRID_CIRCUIT_MANIFEST_V1\n' + '\n'.join(rows) + '\n')
    return d / 'manifest.txt'


def vectors():
    if not (WORDS / 'xor-bit.flat').is_file():
        raise SystemExit(f'missing {WORDS / "xor-bit.flat"}')
    work = OUT / 'work'
    work.mkdir()
    with open(OUT / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(MP / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    (OUT / 'hosts').write_text('127.0.0.1\n' * 2)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(MP), CIRCUIT_MANIFEST=str(manifest()), TLS_WORKER_PEER_WAIT='120',
               TLS_WORKER_TRIPLE_STOCK='0')
    rs, end = rounds(VECTORS.read_text())
    if end != 'finished':
        raise SystemExit('the vectors do not finish')
    session = secrets.token_hex(32)
    ws = [Worker(0, env, work, session, PORT), Worker(1, env, work, session, PORT)]
    try:
        for seq, r in enumerate(rs):
            for party in (0, 1):
                ws[party].send(request(BATCH, seq, r['batch'][party]))
            got = [ws[0].reply(), ws[1].reply()]
            for party in (0, 1):
                g = got[party]
                if not g or g[0] != 0 or g[1] != r['reply'][party]:
                    report['first_difference'] = {'round': seq, 'party': party,
                                                  'got': (g[1].hex()[:160] if g and isinstance(g[1], bytes) else str(g))}
                    raise RuntimeError(f'round {seq}: reply differs from Lean\'s')
        report['rounds'] = len(rs)
        report['passed'] = True
    finally:
        for w in ws:
            w.close()


def handshake():
    fixture = os.environ.get('TLS_SCRIPT_BACKEND_FIXTURE')
    if not fixture:
        raise SystemExit('handshake mode: needs the script runner (op 93 from Lean) and S11\'s KeyAgreement; '
                         'see this file\'s docstring, then set TLS_SCRIPT_BACKEND_FIXTURE')
    subprocess.run([sys.executable, str(ROOT / 'handshake_backend/EmpHybridWork/check_tls_worker_v3.py')],
                   env=dict(os.environ, TLS_CONTROLLER_FIXTURE=fixture), check=True)
    report['passed'] = True


def main():
    OUT.mkdir(parents=True)
    started = time.monotonic()
    try:
        vectors() if mode == 'vectors' else handshake()
    except Exception as e:
        report['error'] = str(e)
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 2)
        (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=1))
    if not report['passed']:
        raise SystemExit(1)


main()
