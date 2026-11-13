#!/usr/bin/env python3
"""S9 end-to-end check of pipe operation 93 with the REAL engines: two node-worker processes run
Lean-generated batches (tests/engine_vectors.txt: the flows random-joint, upgrade-public, bool,
field and xor) while this script plays the controller's side of both pipes and compares every
reply with the reply the Lean model computes for honest parties. Then one batch that `check`
refuses (an exchange with label 0): both workers must reject it and stay terminal. The same
check as a cargo test: tests/e2e_engines.rs (feature `e2e`).

    python3 node_worker/tests/e2e_batches.py NODE_WORKER

Run it under scripts/guarded.py --heavy (it starts the two-party engines); the wrapper
.deps/lowering-scratch/s9r_run_e2e.py does. The `run` kernel is `tls-reveal 7`, taken from the
local kernel cache (.deps/emp-hybrid-word-v1/cache) into a one-kernel manifest (pins checked), so
the workers run in strict circuit mode. Writes only under .deps/lowering-scratch/s9r-e2e/.
Ports 23900-23930."""
import hashlib, json, os, pathlib, queue, secrets, shutil, struct, subprocess, sys, threading, time
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / '.deps/lowering-scratch/s9r-e2e' / secrets.token_hex(6)
MP = ROOT / '.deps/two-party-comparison/data61-MP-SPDZ-113c4e4'
CACHE = ROOT / '.deps/emp-hybrid-word-v1/cache'
VECTORS = ROOT / 'node_worker/tests/engine_vectors.txt'
PORT = 23900
BATCH = 93
worker = pathlib.Path(sys.argv[1])
OUT.mkdir(parents=True)
report = {'out': str(OUT), 'worker': str(worker), 'passed': False, 'steps': []}


def flows(text):
    out, party = [], 0
    for line in text.splitlines():
        key, _, rest = line.partition(' ')
        if key == 'flow':
            out.append({'name': rest, 'rounds': []})
        elif key == 'round':
            out[-1]['rounds'].append({'batch': [None, None], 'reply': [None, None]})
        elif key == 'party':
            party = 0 if rest == 'a' else 1
        elif key in ('batch', 'reply') and out and out[-1]['rounds']:
            out[-1]['rounds'][-1][key][party] = bytes.fromhex(rest)
    return out


def manifest():
    """A one-kernel manifest (tls-reveal 7) from the kernel cache, pins checked here too."""
    d = OUT / 'circuits'
    d.mkdir()
    for record in sorted(CACHE.glob('*/kernel-tls-reveal-7.json'), key=lambda p: p.stat().st_mtime, reverse=True):
        meta = json.loads(record.read_text())
        flat, layout = record.with_suffix('.flat'), record.with_suffix('.layout')
        if not (flat.is_file() and layout.is_file()):
            continue
        if hashlib.sha256(flat.read_bytes()).hexdigest() != meta['sha256'] or hashlib.sha256(layout.read_bytes()).hexdigest() != meta['layout_sha256']:
            continue
        shutil.copy(flat, d / 'kernel-tls-reveal-7.flat')
        shutil.copy(layout, d / 'kernel-tls-reveal-7.layout')
        (d / 'manifest.txt').write_text(f"EMP_HYBRID_CIRCUIT_MANIFEST_V1\n{meta['sha256']} {meta['layout_sha256']} tls-reveal 7\n")
        report['kernel'] = str(record)
        return d / 'manifest.txt'
    raise SystemExit('no usable tls-reveal 7 kernel in the cache')


def request(code, seq, payload):
    return bytes([code]) + struct.pack('>Q', seq) + struct.pack('>I', len(payload)) + payload


class Worker:
    def __init__(self, party, env, work, session, tag=''):
        self.log = open(OUT / f'worker-{party}{tag}.log', 'w')
        self.p = subprocess.Popen([str(worker), str(party), str(OUT / 'hosts'), str(PORT),
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

    def reply(self, wait=600):
        return self.replies.get(timeout=wait)


def refused(payload_byte):
    """[boolPublic 40 [1], exchange len 1 label 0 [payload_byte]]: `check` refuses instruction 1."""
    return (struct.pack('<Q', 2) + bytes([3]) + struct.pack('<Q', 40) + struct.pack('<Q', 1) + b'\x01'
            + bytes([21]) + struct.pack('<Q', 1) + struct.pack('<Q', 0) + struct.pack('<Q', 1) + bytes([payload_byte]))


def main():
    # The `program` flow needs V3 programs loaded from pinned files (loader.rs FIELD_PROGRAMS, the
    # V3 re-export's files, FIELD_PROGRAMS_V3.md). Its rounds that name only pinned programs
    # (`field-quotient`) run here; `test-allrows` is a vector-only program (no pin), so the rounds
    # from its first use on run on the stand-in engines only (tests/batch_pair.rs).
    fl = flows(VECTORS.read_text())
    for f in fl:
        if f['name'] == 'program':
            cut = next((i for i, r in enumerate(f['rounds']) if any(b'test-allrows' in b for b in r['batch'])), len(f['rounds']))
            report['program_rounds'] = f'{cut} of {len(f["rounds"])} (the rest name test-allrows, not pinned)'
            f['rounds'] = f['rounds'][:cut]
    if not any(f['name'] == 'program' and f['rounds'] for f in fl):
        raise SystemExit('no program round to run (is field-quotient.v3 exported?)')
    path = manifest()
    work = OUT / 'work'
    work.mkdir()
    with open(OUT / 'ssl-setup.log', 'w') as log:
        subprocess.run(['bash', str(MP / 'Scripts/setup-ssl.sh'), '2'], cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    (OUT / 'hosts').write_text('127.0.0.1\n' * 2)
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(MP), CIRCUIT_MANIFEST=str(path), TLS_WORKER_PEER_WAIT='120',
               TLS_WORKER_TRIPLE_STOCK='0')
    started = time.monotonic()
    # Two sessions, each on a fresh pair of workers: the Lean vectors' `program` flow starts from an
    # empty context (its handles 1… would clash with the earlier flows' live handles in one session).
    ok = session_run([f for f in fl if f['name'] != 'program'], env, work, '', True)
    if ok:
        ok = session_run([f for f in fl if f['name'] == 'program'], env, work, '-program', False)
    report['passed'] = ok
    report['elapsed_seconds'] = round(time.monotonic() - started, 2)
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=1))
    if not report['passed']:
        raise SystemExit(1)


def session_run(fl, env, work, tag, refusal):
    """One worker session running the flows `fl` (then, if `refusal`, the refused batch and the latch).
    Returns whether every reply equals Lean's."""
    session = secrets.token_hex(32)
    ws = [Worker(0, env, work, session, tag), Worker(1, env, work, session, tag)]
    seq = 0
    passed = False
    try:
        for f in fl:
            for i, r in enumerate(f['rounds']):
                t = time.monotonic()
                for party in (0, 1):
                    ws[party].send(request(BATCH, seq, r['batch'][party]))
                got = [ws[0].reply(), ws[1].reply()]
                step = {'flow': f['name'], 'round': i, 'sequence': seq, 'seconds': round(time.monotonic() - t, 3)}
                for party in (0, 1):
                    status, payload = got[party] if got[party] and got[party][0] != 'error' else (None, b'')
                    step[f'party{party}'] = 'ok' if status == 0 and payload == r['reply'][party] else \
                        f'status={status} reply={payload.hex()[:120]} expected={r["reply"][party].hex()[:120]}'
                report['steps'].append(step)
                seq += 1
                if any(step[f'party{p}'] != 'ok' for p in (0, 1)):
                    raise RuntimeError(f"{f['name']} round {i}: reply differs from Lean's")
        if refusal:
            for party in (0, 1):
                ws[party].send(request(BATCH, seq, refused(party + 1)))
            got = [ws[0].reply(), ws[1].reply()]
            report['steps'].append({'refused_batch_status': [g[0] if g else None for g in got]})
            if any(g is None or g[0] != 1 for g in got):
                raise RuntimeError('a batch refused by check was not rejected by both')
            for party in (0, 1):
                ws[party].send(request(BATCH, seq + 1, refused(party + 1)))
            got = [ws[0].reply(), ws[1].reply()]
            report['steps'].append({'after_refusal_status': [g[0] if g else None for g in got]})
            if any(g is None or g[0] != 1 for g in got):
                raise RuntimeError('the latch is not terminal after a rejected batch')
        passed = True
    except Exception as e:
        report['error'] = str(e)
    finally:
        for w in ws:
            try:
                w.p.stdin.close()
            except Exception:
                pass
        for w in ws:
            try:
                w.p.wait(timeout=60)
            except Exception:
                w.p.kill()
                w.p.wait()
            w.log.close()
        report[f'exit_codes{tag}'] = [w.p.returncode for w in ws]
        for party in (0, 1):
            lines = (OUT / f'worker-{party}{tag}.log').read_text(errors='replace').splitlines()
            report[f'worker{party}{tag}_log'] = [l[:300] for l in lines if 'operation' in l or 'aborted' in l or 'rejected' in l or 'security_mode' in l][-14:]
    return passed


main()
