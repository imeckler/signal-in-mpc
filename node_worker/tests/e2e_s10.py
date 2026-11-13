#!/usr/bin/env python3
"""S10 end-to-end check (test set E) with the REAL engines: two node-worker processes run the
Lean-generated S10 flows (tests/s10_vectors.txt: s10-generate, s10-demo and the five cheating
cases) while this script plays the controller's side of both pipes and compares every reply with
the reply the Lean model computes. NOT RUN in stage S10 (it needs the heavy-job lock and files the
re-export produces). Mirrors tests/e2e_batches.py.

    python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s10.py NODE_WORKER

Prerequisites (all in .deps/emp-hybrid-word-v1, the worker's word-circuit directory):
  * the pinned word circuits of lower_word_circuits.py: modadd.flat, finalize-mask.flat,
    finalize-bits.flat, into-field.flat, xor-bit.flat, swap-bits.flat (they exist today);
  * the V3 programs of the re-export (FIELD_PROGRAMS_V3.md): field-bit-check.v3, field-bit-xor.v3,
    field-recompose.v3, field-quotient.v3, with their pins pasted into loader.rs FIELD_PROGRAMS
    (the S10 entries are placeholders that fail closed until then);
  * field-mask-sub.v3: this script writes it from the vectors' `native` line when absent (its pin is
    loader.rs FIELD_MASK_SUB_SHA256, checked here).
The vectors' STAND-IN texts of field-bit-check / -xor / -recompose differ from the exported ones
row for row but compute the same values (ConvertBase.lean `ProgsLoaded`); a batch names programs,
not texts, and their openings are empty, so the replies are the same.

The cheating cases: the replies up to Lean's abort must match; Lean's honest party then stops (the
vectors' `abort` line); the workers are closed. The TEST parameters (Masks.testParams 3 1) are a
Config.test deviation. Writes only under .deps/lowering-scratch/s10-e2e/. Ports 23940-23970."""
import hashlib, os, pathlib, queue, secrets, struct, subprocess, sys, threading, time, json
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / '.deps/lowering-scratch/s10-e2e' / secrets.token_hex(6)
MP = ROOT / '.deps/two-party-comparison/data61-MP-SPDZ-113c4e4'
WORDS = ROOT / '.deps/emp-hybrid-word-v1'
VECTORS = ROOT / 'node_worker/tests/s10_vectors.txt'
MASK_SUB_SHA256 = '1dd3b23751bf286d034dad86bf90bd9ab46ec0e35adb90eb3da57b4b6c6ff4bf'
PORT = 23940
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


def native_program():
    text = VECTORS.read_text()
    line = next(l for l in text.splitlines() if l.startswith('native field-mask-sub '))
    _, _, text_hex, pin = line.split(' ')
    body = bytes.fromhex(text_hex)
    if hashlib.sha256(body).hexdigest() != pin or pin != MASK_SUB_SHA256:
        raise SystemExit('field-mask-sub: the vectors do not carry the pinned text')
    target = WORDS / 'field-mask-sub.v3'
    if not target.exists():
        target.write_bytes(body)
    elif hashlib.sha256(target.read_bytes()).hexdigest() != pin:
        raise SystemExit(f'{target}: another text than the pinned one')


def main():
    OUT.mkdir(parents=True)
    native_program()
    for name in ['modadd.flat', 'finalize-mask.flat', 'finalize-bits.flat', 'into-field.flat', 'xor-bit.flat',
                 'swap-bits.flat', 'field-bit-check.v3', 'field-bit-xor.v3', 'field-recompose.v3', 'field-quotient.v3']:
        if not (WORDS / name).is_file():
            raise SystemExit(f'missing {WORDS / name} (see the prerequisites)')
    work = OUT / 'work'
    work.mkdir()
    with open(OUT / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(MP / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    (OUT / 'hosts').write_text('127.0.0.1\n' * 2)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(MP), TLS_WORKER_PEER_WAIT='120', TLS_WORKER_TRIPLE_STOCK='0',
               SIGNAL_TEST='1')
    started = time.monotonic()
    try:
        for i, f in enumerate(flows(VECTORS.read_text())):
            # One fresh session per flow (the vectors start each flow from the empty context).
            port = PORT + 5 * i
            session = secrets.token_hex(32)
            ws = [Worker(0, env, work, session, port), Worker(1, env, work, session, port)]
            entry = {'flow': f['name'], 'end': f['end'], 'rounds': len(f['rounds']), 'ok': True}
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
