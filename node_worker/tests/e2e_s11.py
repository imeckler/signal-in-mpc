#!/usr/bin/env python3
"""S11 end-to-end check (test set E) with the REAL engines: two node-worker processes run the
Lean-generated curve flows (tests/s11_vectors.txt: s11-split, s11-agree, s11-offset, s11-hinted,
s11-prepare and the four cheating cases) while this script plays the controller's side of both
pipes and compares every reply with the reply the Lean model computes. NOT RUN in stage S11 (it
needs the heavy-job lock and the files the V3 re-export produces). Mirrors tests/e2e_s10.py.

    python3 scripts/guarded.py --heavy 16 3600 python3 node_worker/tests/e2e_s11.py NODE_WORKER

Prerequisites (in .deps/emp-hybrid-word-v1, the worker's word-circuit directory):
  * the V3 programs of the re-export (FIELD_PROGRAMS_V3.md) for every name of the vectors' `pin`
    lines (17: field-quotient, field-bit-check, field-bit-xor and the 14 curve programs), each
    with the SHA-256 the vectors give (Lean's render of the exported declaration; this script
    refuses a different file), and those pins pasted into loader.rs FIELD_PROGRAMS (the S10/S11
    entries are placeholders that fail closed until then).
A staged flow's local step (`local a`/`local b`) is the controller's own work between two
scripts: nothing is sent, the session continues. The cheating cases: the replies up to Lean's
abort must match. Writes only under .deps/lowering-scratch/s11-e2e/. Ports 24040-24100."""
import hashlib, json, os, pathlib, queue, secrets, struct, subprocess, sys, threading, time
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / '.deps/lowering-scratch/s11-e2e' / secrets.token_hex(6)
MP = ROOT / '.deps/two-party-comparison/data61-MP-SPDZ-113c4e4'
WORDS = ROOT / '.deps/emp-hybrid-word-v1'
VECTORS = ROOT / 'node_worker/tests/s11_vectors.txt'
PORT = 24040
BATCH = 93
worker = pathlib.Path(sys.argv[1])
report = {'out': str(OUT), 'worker': str(worker), 'passed': False, 'flows': []}


def flows(text):
    out, party = [], 0
    for line in text.splitlines():
        key, _, rest = line.partition(' ')
        if key == 'flow':
            out.append({'name': rest, 'rounds': [], 'end': ''})
        elif key == 'round':
            out[-1]['rounds'].append({'batch': [None, None], 'reply': [None, None]})
        elif key == 'party':
            party = 0 if rest == 'a' else 1
        elif key in ('batch', 'reply') and out and out[-1]['rounds']:
            out[-1]['rounds'][-1][key][party] = bytes.fromhex(rest)
        elif key in ('finished', 'abort', 'error') and out:
            out[-1]['end'] = line
    return out


def pins(text):
    return {l.split(' ')[1]: l.split(' ')[2] for l in text.splitlines() if l.startswith('pin ')}


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

    def reply(self, wait=1800):
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


def manifest():
    """A one-kernel manifest (tls-reveal 7) from the kernel cache, as tests/e2e_s10.py: the workers
    run in strict circuit mode; the S11 flows use only V3 field programs."""
    cache = ROOT / '.deps/emp-hybrid-word-v1/cache'
    d = OUT / 'circuits'
    d.mkdir()
    for record in sorted(cache.glob('*/kernel-tls-reveal-7.json'), key=lambda p: p.stat().st_mtime, reverse=True):
        meta = json.loads(record.read_text())
        flat, layout = record.with_suffix('.flat'), record.with_suffix('.layout')
        if not (flat.is_file() and layout.is_file()):
            continue
        if hashlib.sha256(flat.read_bytes()).hexdigest() != meta['sha256'] or hashlib.sha256(layout.read_bytes()).hexdigest() != meta['layout_sha256']:
            continue
        (d / 'kernel-tls-reveal-7.flat').write_bytes(flat.read_bytes())
        (d / 'kernel-tls-reveal-7.layout').write_bytes(layout.read_bytes())
        (d / 'manifest.txt').write_text(f"EMP_HYBRID_CIRCUIT_MANIFEST_V1\n{meta['sha256']} {meta['layout_sha256']} tls-reveal 7\n")
        return d / 'manifest.txt'
    raise SystemExit('no usable tls-reveal 7 kernel in the cache')


def main():
    OUT.mkdir(parents=True)
    text = VECTORS.read_text()
    for name, pin in pins(text).items():
        f = WORDS / f'{name}.v3'
        if not f.is_file():
            raise SystemExit(f'missing {f} (see the prerequisites)')
        if hashlib.sha256(f.read_bytes()).hexdigest() != pin:
            raise SystemExit(f'{f}: not the text Lean renders (pin {pin})')
    work = OUT / 'work'
    work.mkdir()
    with open(OUT / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(MP / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    (OUT / 'hosts').write_text('127.0.0.1\n' * 2)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(MP), CIRCUIT_MANIFEST=str(manifest()), TLS_WORKER_PEER_WAIT='300',
               TLS_WORKER_TRIPLE_STOCK='0')
    started = time.monotonic()
    try:
        for i, f in enumerate(flows(text)):
            port = PORT + 5 * i
            session = secrets.token_hex(32)
            ws = [Worker(0, env, work, session, port), Worker(1, env, work, session, port)]
            entry = {'flow': f['name'], 'end': f['end'], 'rounds': len(f['rounds']), 'ok': True}
            t0 = time.monotonic()
            try:
                for seq, r in enumerate(f['rounds']):
                    for party in (0, 1):
                        ws[party].send(request(BATCH, seq, r['batch'][party]))
                    got = [ws[0].reply(), ws[1].reply()]
                    for party in (0, 1):
                        g = got[party]
                        if not g or g[0] != 0 or g[1] != r['reply'][party]:
                            entry['ok'] = False
                            entry['first_difference'] = {'round': seq, 'party': party,
                                                         'got': (g[1].hex()[:160] if g and isinstance(g[1], bytes) else str(g))}
                            raise RuntimeError(f"{f['name']} round {seq}: reply differs from Lean's")
            finally:
                entry['seconds'] = round(time.monotonic() - t0, 2)
                for w in ws:
                    w.close()
                report['flows'].append(entry)
        report['passed'] = all(e['ok'] for e in report['flows'])
    except Exception as e:
        report['error'] = str(e)
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 2)
        (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=1))
    if not report['passed']:
        raise SystemExit(1)


main()
