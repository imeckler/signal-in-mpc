#!/usr/bin/env python3
"""S15 end-to-end check (test sets E/K) with the REAL engines. NOT RUN in stage S15 (it needs the
heavy-job lock, and its second mode needs S11 and the script runner). Two modes:

1. `shape` (default): two node-worker processes run the rounds of tests/s15_vectors.txt up to the
   `stage establish` line (the prekey fetch's seal, first phase, with `bundle-fetch-ctr 126 6 26 102`, the
   real fetch's shape: the emitter refuses the earlier `40 6 10 50`, whose slots overran the frame;
   two takes; the shape with `bundle-shape CAP`) while this script plays the controller's side of
   both pipes. The vectors' circuits are labelled stand-ins EXCEPT the shape's, which computes the
   kernel's meaning (one flag per body byte, 255 for JSON punctuation): every batch must be accepted
   by both workers, every reply must have Lean's length, and the shape's opened flags must equal
   Lean's byte for byte. (The fetch's opened record differs: the real kernel encrypts.)

       python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s15.py NODE_WORKER

   Prerequisites: the kernel cache (.deps/emp-hybrid-word-v1/cache) holds `bundle-fetch-ctr 126 6 26 102`
   and `bundle-shape CAP` (CAP from the vectors' `sig` lines; produce_circuits.py with these names,
   heavy, alone). A one-session manifest of exactly these kernels is written here.

2. `refresh`: the whole two-device refresh on the real kernels (`bundle-slot`, `establish-*`,
   `bundle-rebind`, the twelve `kem-*` runs, `establish-session`, `contact-seal`). It needs what
   this branch does not have: S11's curve operations (`Refresh.CurveOps`: `lift`, `check`,
   `agree`, S15_NOTES.md), the controller-side script runner (op 93 from Lean) and a real prekey
   response (the local Signal server's `GET /v2/keys/{uuid}/*` for a two-device account; never the
   real service). Once they exist: regenerate the vectors with the S11 operations in place of the
   stand-ins and a captured response body, then run

       python3 scripts/guarded.py --heavy 16 3600 python3 node_worker/tests/e2e_s15.py NODE_WORKER refresh

   This script refuses that mode until `S15_REFRESH_VECTORS` names such vectors.

Writes only under .deps/lowering-scratch/s15-e2e/. Ports 24070-24090."""
import hashlib, os, pathlib, queue, secrets, struct, subprocess, sys, threading, time, json
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / '.deps/lowering-scratch/s15-e2e' / secrets.token_hex(6)
MP = ROOT / '.deps/two-party-comparison/data61-MP-SPDZ-113c4e4'
WORDS = ROOT / '.deps/emp-hybrid-word-v1'
VECTORS = ROOT / 'node_worker/tests/s15_vectors.txt'
PORT = 24070
BATCH = 93
worker = pathlib.Path(sys.argv[1])
mode = sys.argv[2] if len(sys.argv) > 2 else 'shape'
report = {'out': str(OUT), 'worker': str(worker), 'mode': mode, 'passed': False}


def rounds(text, stop=None):
    out, party, end = [], 0, ''
    for line in text.splitlines():
        key, _, rest = line.partition(' ')
        if key == 'stage' and stop and rest == stop:
            break
        if key == 'round':
            out.append({'batch': [None, None], 'reply': [None, None]})
        elif key == 'party':
            party = 0 if rest == 'a' else 1
        elif key in ('batch', 'reply') and out:
            out[-1][key][party] = bytes.fromhex(rest)
        elif key in ('finished', 'abort', 'error'):
            end = line
    return out, end


def kernel_names(text):
    names = []
    for line in text.splitlines():
        if line.startswith('sig '):
            names.append(bytes.fromhex(line.split(' ')[1]).decode())
    return names


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


def manifest(names):
    cache = WORDS / 'cache'
    d = OUT / 'circuits'
    d.mkdir()
    rows = []
    for name in names:
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


def shape():
    text = VECTORS.read_text()
    names = [n for n in kernel_names(text) if n.startswith(('bundle-fetch-ctr', 'bundle-shape'))]
    work = OUT / 'work'
    work.mkdir()
    with open(OUT / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(MP / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    (OUT / 'hosts').write_text('127.0.0.1\n' * 2)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(MP), CIRCUIT_MANIFEST=str(manifest(names)), TLS_WORKER_PEER_WAIT='120',
               TLS_WORKER_TRIPLE_STOCK='0')
    rs, _ = rounds(text, stop='establish')
    # the shape's opening is the longest reply of these rounds (one byte per flag bit)
    shape_round = max(range(len(rs)), key=lambda i: len(rs[i]['reply'][0]))
    session = secrets.token_hex(32)
    ws = [Worker(0, env, work, session, PORT), Worker(1, env, work, session, PORT)]
    try:
        for seq, r in enumerate(rs):
            for party in (0, 1):
                ws[party].send(request(BATCH, seq, r['batch'][party]))
            got = [ws[0].reply(), ws[1].reply()]
            for party in (0, 1):
                g = got[party]
                if not g or g[0] != 0 or len(g[1]) != len(r['reply'][party]):
                    report['first_difference'] = {'round': seq, 'party': party,
                                                  'got': (g[1].hex()[:160] if g and isinstance(g[1], bytes) else str(g))}
                    raise RuntimeError(f'round {seq}: refused, or a reply of another length than Lean\'s')
            # the shape's opening: the real kernel's flags are Lean's
            if seq == shape_round and (got[0][1] != r['reply'][0] or got[1][1] != r['reply'][1]):
                raise RuntimeError('the opened shape differs from Lean\'s')
        report['rounds'] = len(rs)
        report['passed'] = True
    finally:
        for w in ws:
            w.close()


def refresh():
    vectors = os.environ.get('S15_REFRESH_VECTORS')
    if not vectors:
        raise SystemExit('refresh mode: needs S11\'s curve operations, the op-93 runner and a captured two-device '
                         'prekey response; see this file\'s docstring, then set S15_REFRESH_VECTORS')
    raise SystemExit('refresh mode: not automated in S15 (run the `shape` loop over the whole file, '
                     'comparing every reply byte for byte)')


def main():
    OUT.mkdir(parents=True)
    started = time.monotonic()
    try:
        shape() if mode == 'shape' else refresh()
    except Exception as e:
        report['error'] = str(e)
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 2)
        (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=1))
    if not report['passed']:
        raise SystemExit(1)


main()
