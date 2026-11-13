#!/usr/bin/env python3
"""S16 end-to-end check (test set E/F) with the REAL engines.

Two node-worker processes run the Lean-generated S16 ceremony flow (tests/s16_vectors.txt:
`s16-ceremony`: party A's traffic block, op 80 `Ceremony.secretsScript` with `ceremony-secrets`, op
81's engine part `Ceremony.registerScript`, the registration request's record phase
`Send.requestCtrScript` with `ceremony-register-ctr 5584 8 5552 1 365`) while this script plays the
controller's side of both pipes and compares every reply with the reply the Lean model computes, as
tests/e2e_s13.py does. The vectors' circuits are the kernels' references (`Ceremony.secrets`, the
right-hand side of `Ceremony.ceremonyRegisterCtr_spec`); the real workers run the pinned kernels,
which compute the same functions (`ceremonySecrets_spec`, `ceremonyRegisterCtr_spec`), so the replies
must be equal byte for byte (the opened masked password; the opened accepted ‖ header ‖ ciphertext of
the registration record).

    python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s16.py NODE_WORKER

Prerequisites: the kernel cache (.deps/emp-hybrid-word-v1/cache) holds `ceremony-secrets` and
`ceremony-register-ctr 5584 8 5552 1 365` (lowered for the C++ ceremony; the vectors use that shape
so nothing is lowered for this fixture). A one-session manifest of exactly these two kernels is
written here; each kernel's flat file and layout are checked against its cache record's pins.

Writes only under .deps/lowering-scratch/s16-e2e/ (of the checkout that holds .deps). Ports
24160-24170."""
import hashlib, os, pathlib, queue, secrets, struct, subprocess, sys, threading, time, json
ROOT = pathlib.Path(__file__).resolve().parents[2]
# The untracked data (.deps: engines, kernel cache): this checkout's, or, in a git worktree under
# .claude/worktrees/, the main checkout's.
DATA = next((p for p in [ROOT, *ROOT.parents] if (p / '.deps/emp-hybrid-word-v1').is_dir()), ROOT)
OUT = DATA / '.deps/lowering-scratch/s16-e2e' / secrets.token_hex(6)
MP = DATA / '.deps/two-party-comparison/data61-MP-SPDZ-113c4e4'
WORDS = DATA / '.deps/emp-hybrid-word-v1'
VECTORS = ROOT / 'node_worker/tests/s16_vectors.txt'
PORT = 24160
BATCH = 93
worker = pathlib.Path(sys.argv[1])
report = {'out': str(OUT), 'worker': str(worker), 'passed': False, 'flows': {}}


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


def kernel_names(text):
    return [bytes.fromhex(l.split(' ')[1]).decode() for l in text.splitlines() if l.startswith('sig ')]


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

    def reply(self, wait=1500):
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
    """A manifest of the vectors' kernels, each from the kernel cache with its pins checked."""
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
            report.setdefault('kernels', {})[name] = str(record.parent.name)
            break
        else:
            raise SystemExit(f'no usable {name} kernel in the cache (see the prerequisites)')
    (d / 'manifest.txt').write_text('EMP_HYBRID_CIRCUIT_MANIFEST_V1\n' + '\n'.join(rows) + '\n')
    return d / 'manifest.txt'


def run():
    text = VECTORS.read_text()
    work = OUT / 'work'
    work.mkdir()
    with open(OUT / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(MP / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    (OUT / 'hosts').write_text('127.0.0.1\n' * 2)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(MP), CIRCUIT_MANIFEST=str(manifest(kernel_names(text))),
               TLS_WORKER_PEER_WAIT='120', TLS_WORKER_TRIPLE_STOCK='0')
    for i, flow in enumerate(flows(text)):
        if flow['end'] != 'finished':
            raise SystemExit(f"flow {flow['name']} does not finish")
        session = secrets.token_hex(32)
        port = PORT + 4 * i
        ws = [Worker(0, env, work, session, port), Worker(1, env, work, session, port)]
        times = []
        try:
            for seq, r in enumerate(flow['rounds']):
                t0 = time.monotonic()
                for party in (0, 1):
                    ws[party].send(request(BATCH, seq, r['batch'][party]))
                got = [ws[0].reply(), ws[1].reply()]
                times.append(round(time.monotonic() - t0, 2))
                for party in (0, 1):
                    g = got[party]
                    if not g or g[0] != 0 or g[1] != r['reply'][party]:
                        report['first_difference'] = {'flow': flow['name'], 'round': seq, 'party': party,
                                                      'got': (g[1].hex()[:160] if g and isinstance(g[1], bytes) else str(g))}
                        raise RuntimeError(f"{flow['name']} round {seq}: reply differs from Lean's")
            report['flows'][flow['name']] = {'rounds': len(flow['rounds']), 'round_seconds': times}
        finally:
            for w in ws:
                w.close()
    report['passed'] = True


def main():
    OUT.mkdir(parents=True)
    started = time.monotonic()
    try:
        run()
    except Exception as e:
        report['error'] = str(e)
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 2)
        (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=1))
    if not report['passed']:
        raise SystemExit(1)


main()
