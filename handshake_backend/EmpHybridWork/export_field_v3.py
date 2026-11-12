"""Export the V3 field programs (FIELD_PROGRAMS_V3.md), next to the V2 files, and pin them.

HEAVY (it builds and runs the emitter): run it once, alone, under the heavy-job lock:
    python3 scripts/guarded.py --heavy 16 3600 python3 handshake_backend/EmpHybridWork/export_field_v3.py

Steps:
  1. Snapshot the SHA-256 of every file lower_word_circuits.py writes (the V2 field programs and
     the Boolean word circuits, *.flat, and word_circuit_pins.h) in .deps/emp-hybrid-word-v1.
  2. Run lower_word_circuits.py (it rebuilds word_mask_emitter, whose binary changed because
     EmitWordMask now imports TlsMpc/FieldProgramsV3.lean) and check that every one of those
     files is byte-identical to the snapshot: the V2 printers and their inputs are unchanged, so
     a difference is an error (the script then stops; restore from the snapshot copy it kept).
  3. For every name of `word_mask_emitter v3 list`: print the V3 text (`v3 NAME`), parse it here
     exactly as program.rs does (and re-render it: one text per program), evaluate it on random
     inputs and nonzero masks, and compare the outputs with the V2 file of the same program
     evaluated as field_program.h does (field-quotient: with x/z and the zero flag). Write
     NAME.v3, the pins (field_program_v3_pins.txt: `NAME SHA256`), the Rust table
     (field_program_v3_pins.rs.txt, to paste into node_worker/src/loader.rs FIELD_PROGRAMS) and
     field-programs-v3-report.json next to this script.
Nothing here is trusted: program.rs re-parses every file and checks its pin.
"""
import hashlib
import json
import pathlib
import random
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
HERE = pathlib.Path(__file__).resolve().parent
OUT = ROOT / '.deps/emp-hybrid-word-v1'
P = 2 ** 255 - 19
MAGIC = 'EMP_HYBRID_FIELD_DAG_V3'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def snapshot():
    files = sorted(OUT.glob('*.flat')) + [OUT / 'word_circuit_pins.h']
    return {f.name: sha(f.read_bytes()) for f in files if f.is_file()}


def canon(tok):
    if not tok.isdigit() or (len(tok) > 1 and tok[0] == '0'):
        raise ValueError('number')
    return int(tok)


def parse_v3(text):
    """program.rs `parse` (Lean `parse`): the canonical text of a valid program."""
    if not text.endswith('\n'):
        raise ValueError('final newline')
    lines = text[:-1].split('\n')
    if lines[0] != MAGIC or lines[2] != str(P):
        raise ValueError('header')
    head = lines[1].split(' ')
    inputs, masks, count, outputs = (canon(t) for t in head)
    if len(head) != 4 or len(lines) != 3 + count + outputs:
        raise ValueError('counts')
    rows, uses = [], 0
    for j, line in enumerate(lines[3:3 + count]):
        f = line.split(' ')
        op, args = f[0], [canon(t) for t in f[1:]]
        arity = {'I': 1, 'C': 1, 'A': 2, 'S': 2, 'M': 2, 'D': 3, 'Z': 3, 'F': 1}[op]
        if len(args) != arity:
            raise ValueError('row')
        if op == 'I' and args[0] >= inputs or op == 'C' and args[0] >= P:
            raise ValueError('row')
        if op in 'ASMDZ' and (args[0] >= j or args[1] >= j):
            raise ValueError('row')
        if op in 'DZ':
            if args[2] != uses:
                raise ValueError('mask order')
            uses += 1
        if op == 'F' and (args[0] >= j or rows[args[0]][0] != 'Z'):
            raise ValueError('flag')
        rows.append((op, args))
    if uses != masks:
        raise ValueError('masks')
    outs = []
    for line in lines[3 + count:]:
        f = line.split(' ')
        if len(f) != 3 or f[0] != 'O' or f[2] not in ('0', '1') or canon(f[1]) >= count:
            raise ValueError('output')
        outs.append((int(f[1]), int(f[2])))
    return dict(inputs=inputs, masks=masks, rows=rows, outputs=outs)


def render_v3(p):
    body = [MAGIC, f"{p['inputs']} {p['masks']} {len(p['rows'])} {len(p['outputs'])}", str(P)]
    body += [' '.join([op] + [str(a) for a in args]) for op, args in p['rows']]
    body += [f'O {o} {m}' for o, m in p['outputs']]
    return '\n'.join(body) + '\n'


def eval_v3(p, x, m):
    """FieldDagV3.eval: (outputs, openings) or None (a D row opened 0)."""
    v, opened, zero = [], [], {}
    for j, (op, a) in enumerate(p['rows']):
        if op == 'I':
            v.append(x[a[0]])
        elif op == 'C':
            v.append(a[0])
        elif op == 'A':
            v.append((v[a[0]] + v[a[1]]) % P)
        elif op == 'S':
            v.append((v[a[0]] - v[a[1]]) % P)
        elif op == 'M':
            v.append(v[a[0]] * v[a[1]] % P)
        elif op in 'DZ':
            o = v[a[1]] * m[a[2]] % P
            opened.append(o)
            zero[j] = o == 0
            if o == 0 and op == 'D':
                return None
            v.append(0 if o == 0 else v[a[0]] * m[a[2]] * pow(o, P - 2, P) % P)
        elif op == 'F':
            v.append(1 if zero[a[0]] else 0)
    return [v[o] for o, _ in p['outputs']], opened


def eval_v2(text, x):
    """field_program.h `evaluate_clear` on a V2 (or V1) file; None on a zero denominator."""
    lines = text.split('\n')
    head = lines[1].split()
    count, third = int(head[1]), int(head[2])
    v = []
    for line in lines[3:3 + count]:
        f = line.split()
        op, a = f[0], [int(t) for t in f[1:]]
        if op == 'I':
            v.append(x[a[0]])
        elif op == 'C':
            v.append(a[0])
        elif op == 'A':
            v.append((v[a[0]] + v[a[1]]) % P)
        elif op == 'S':
            v.append((v[a[0]] - v[a[1]]) % P)
        elif op == 'M':
            v.append(v[a[0]] * v[a[1]] % P)
        elif op == 'D':
            if v[a[1]] == 0:
                return None
            v.append(v[a[0]] * pow(v[a[1]], P - 2, P) % P)
    if lines[0] == 'EMP_HYBRID_FIELD_DAG_V1':
        return [v[third]]
    outs = [int(t) for t in lines[3 + count].split()[1:]]
    return [v[o] for o in outs]


def emit(*args):
    return subprocess.run(['lake', 'exe', 'word_mask_emitter', *args], cwd=ROOT, check=True,
                          capture_output=True).stdout.decode()


def main():
    rng = random.Random(20261112)
    before = snapshot()
    keep = OUT.parent / 'emp-hybrid-word-v1-before-v3'
    if keep.exists():
        shutil.rmtree(keep)
    shutil.copytree(OUT, keep, ignore=shutil.ignore_patterns('cache'))
    subprocess.run([sys.executable, str(HERE / 'lower_word_circuits.py')], cwd=ROOT, check=True)
    after = snapshot()
    changed = sorted(k for k in before if before[k] != after.get(k))
    if changed or set(before) != set(after):
        raise SystemExit(f'V2/Boolean outputs changed (restore from {keep}): {changed}')
    names = emit('v3', 'list').split()
    pins, rust, report = [], [], {}
    for name in names:
        text = emit('v3', name)
        p = parse_v3(text)
        if render_v3(p) != text:
            raise SystemExit(f'{name}: not canonical')
        cases = 0
        for _ in range(4 if p['inputs'] > 300 else 12):
            # Any inputs: V3 and V2 compute the same polynomials and quotients.
            x = [rng.randrange(P) for _ in range(p['inputs'])]
            m =[rng.randrange(1, P) for _ in range(p['masks'])]
            got = eval_v3(p, x, m)
            if name == 'field-quotient':
                want = [x[0] * pow(x[1], P - 2, P) % P, 1 if x[1] == 0 else 0]
            else:
                flat = OUT / f'{name}.flat'
                want = eval_v2(flat.read_text(), x)
            if got is None or want is None:
                if (got is None) != (want is None):
                    raise SystemExit(f'{name}: V3 and V2 disagree on aborting')
                continue
            if got[0] != want:
                raise SystemExit(f'{name}: V3 outputs differ from V2')
            if len(got[1]) != p['masks']:
                raise SystemExit(f'{name}: openings')
            cases += 1
        (OUT / f'{name}.v3').write_text(text)
        digest = sha(text.encode())
        pins.append(f'{name} {digest}')
        rust.append(f'    FieldProgramPin {{ name: "{name}", file: "{name}.v3", sha256: "{digest}" }},')
        report[name] = dict(v3_sha256=digest, inputs=p['inputs'], masks=p['masks'], rows=len(p['rows']),
                            outputs=len(p['outputs']), public=[j for j, (_, mk) in enumerate(p['outputs']) if mk],
                            cases_checked=cases)
    (OUT / 'field_program_v3_pins.txt').write_text('\n'.join(pins) + '\n')
    (OUT / 'field_program_v3_pins.rs.txt').write_text('\n'.join(rust) + '\n')
    (HERE / 'field-programs-v3-report.json').write_text(json.dumps(dict(
        passed=True, v2_unchanged=sorted(before), programs=report,
        lean_sources={f: sha((ROOT / f).read_bytes()) for f in (
            'TlsMpc/FieldDagV3.lean', 'TlsMpc/FieldProgramsV3.lean', 'handshake_backend/EmpHybridWork/EmitWordMask.lean')}),
        indent=2) + '\n')
    shutil.rmtree(keep)
    print(json.dumps({k: (v['rows'], v['masks'], v['public'][:4]) for k, v in report.items()}))


if __name__ == '__main__':
    main()
