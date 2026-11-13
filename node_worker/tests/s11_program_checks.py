#!/usr/bin/env python3
"""Checks of the exported V3 curve programs (stage S11), in the manner of
handshake_backend/EmpHybridWork/hinted_program_checks.py, for the V3 format the S11 flows run
through node_worker/src/program.rs. NOT RUN in stage S11 (it needs the files of the V3 re-export).

    python3 node_worker/tests/s11_program_checks.py [WORD_DIR]      # default .deps/emp-hybrid-word-v1
    python3 node_worker/tests/s11_program_checks.py --from-vectors  # Lean's renders in the vectors

For every name of tests/s11_vectors.txt's `pin` lines: the file `NAME.v3` exists, its SHA-256 is
the pin Lean's render gives, and its header (inputs, masks, rows, outputs) parses. Then, on random
inputs and nonzero masks, the V3 semantics (FieldDagV3.eval: `D a b m` opens b·m, aborts on 0,
gives a·m·(b·m)⁻¹; `Z` gives 0 and a flag on 0) evaluated here in Python against INDEPENDENT
arithmetic (textbook affine Edwards addition, a Montgomery ladder):
  * edwards-on-curve: zero on curve points, nonzero off the curve;
  * edwards-add-u: (den + num)/(den − num) is the u of the affine sum;
  * x25519-fast: x/z is the RFC 7748 ladder on the clamped scalar of the swap bits;
  * lift-open + lift-point: with the runtime's public root, valid = [u on the curve], Z = P + M_A + M_B;
  * edwards-torsion-hinted: zero outputs for a prime-order point with honest hints;
  * edwards-offset-sum-fast: (Z + Y)/(Z − Y) is the u of the initial point plus the signed entries.
Light (no engine, no lock). Prints a JSON summary; exit status 1 on any failure."""
import hashlib, json, pathlib, random, sys
ROOT = pathlib.Path(__file__).resolve().parents[2]
WORDS = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / '.deps/emp-hybrid-word-v1'
VECTORS = ROOT / 'node_worker/tests/s11_vectors.txt'
P = 2 ** 255 - 19
D = (-121665 * pow(121666, P - 2, P)) % P
ELL = 2 ** 252 + 27742317777372353535851937790883648493
SQRT_M1 = pow(2, (P - 1) // 4, P)
SA2 = 6853475219497561581579357271197624642482790079785650197046958215289687604742
BASE = (15112221349535400772501151409588531511454012693041857206046113283949847762202,
        46316835694926478169428394003475163141307993866256225615783033603165251855960)


def inv(a): return pow(a, P - 2, P)


def sqrt(a):
    x = pow(a, (P + 3) // 8, P)
    if x * x % P != a % P: x = x * SQRT_M1 % P
    return x if x * x % P == a % P else None


def add(p, q):
    (x1, y1), (x2, y2) = p, q; t = D * x1 * x2 * y1 * y2 % P
    return ((x1 * y2 + y1 * x2) * inv(1 + t) % P, (y1 * y2 + x1 * x2) * inv(1 - t) % P)


def mul(k, p):
    r = (0, 1)
    while k:
        if k & 1: r = add(r, p)
        p = add(p, p); k >>= 1
    return r


def on_curve(p): return (-p[0] * p[0] + p[1] * p[1] - 1 - D * p[0] * p[0] * p[1] * p[1]) % P == 0


def mont_u(p): return (1 + p[1]) * inv(1 - p[1]) % P


def ladder(k, u):
    x2, z2, x3, z3, swap = 1, 0, u, 1, 0
    for t in reversed(range(255)):
        b = (k >> t) & 1; swap ^= b
        if swap: x2, x3, z2, z3 = x3, x2, z3, z2
        swap = b
        a = (x2 + z2) % P; aa = a * a % P; b2 = (x2 - z2) % P; bb = b2 * b2 % P; e = (aa - bb) % P
        c = (x3 + z3) % P; d = (x3 - z3) % P; da = d * a % P; cb = c * b2 % P
        x3 = (da + cb) ** 2 % P; z3 = u * (da - cb) ** 2 % P; x2 = aa * bb % P; z2 = e * (aa + 121665 * e) % P
    if swap: x2, x3, z2, z3 = x3, x2, z3, z2
    return x2 * inv(z2) % P


def parse(text):
    lines = text.split('\n')
    if lines[0] != 'EMP_HYBRID_FIELD_DAG_V3' or int(lines[2]) != P or lines[-1] != '':
        raise ValueError('V3 header')
    n_in, n_mask, n_rows, n_out = map(int, lines[1].split())
    rows = [l.split() for l in lines[3:3 + n_rows]]
    outs = [l.split() for l in lines[3 + n_rows:3 + n_rows + n_out]]
    if len(lines) != 3 + n_rows + n_out + 1 or any(o[0] != 'O' for o in outs):
        raise ValueError('V3 rows/outputs')
    return n_in, n_mask, rows, [(int(o[1]), int(o[2])) for o in outs]


def evaluate(prog, inputs, masks):
    _, _, rows, outs = prog
    vals, opened, flags = [], [], {}
    for k, r in enumerate(rows):
        op = r[0]
        if op == 'I': vals.append(inputs[int(r[1])] % P)
        elif op == 'C': vals.append(int(r[1]) % P)
        elif op in 'ASM':
            a, b = vals[int(r[1])], vals[int(r[2])]
            vals.append((a + b if op == 'A' else a - b if op == 'S' else a * b) % P)
        elif op in 'DZ':
            a, b, m = vals[int(r[1])], vals[int(r[2])], masks[int(r[3])]
            o = b * m % P; opened.append(o)
            if o == 0:
                if op == 'D': raise ZeroDivisionError('D row opened 0')
                vals.append(0); flags[k] = 1
            else:
                vals.append(a * m % P * inv(o) % P); flags[k] = 0
        elif op == 'F': vals.append(flags.get(int(r[1]), 0))
        else: raise ValueError(op)
    return [vals[i] for i, _ in outs], opened


def main():
    rng = random.Random(1155)
    text = VECTORS.read_text()
    pins = {l.split(' ')[1]: l.split(' ')[2] for l in text.splitlines() if l.startswith('pin ')}
    progs, report = {}, {'dir': str(WORDS), 'files': {}, 'checks': {}, 'passed': False}
    texts = {bytes.fromhex(l.split(' ')[1]).decode(): bytes.fromhex(l.split(' ')[2])
             for l in text.splitlines() if l.startswith('prog ')}
    for name, pin in pins.items():
        if str(WORDS) == '--from-vectors':
            # Lean's renders themselves (what the re-export must produce): runs before the export.
            body = texts[name]
        else:
            f = WORDS / f'{name}.v3'
            if not f.is_file():
                report['files'][name] = 'missing'; continue
            body = f.read_bytes()
        ok = hashlib.sha256(body).hexdigest() == pin
        report['files'][name] = 'pinned' if ok else 'PIN MISMATCH'
        progs[name] = parse(body.decode())

    def masks(name): return [rng.randrange(1, P) for _ in range(progs[name][1])]

    def check(name, ok): report['checks'][name] = bool(ok)

    if 'edwards-on-curve' in progs:
        pt = mul(rng.randrange(1, ELL), BASE)
        check('on-curve zero on a point', evaluate(progs['edwards-on-curve'], list(pt), [])[0][0] == 0)
        check('on-curve nonzero off the curve', evaluate(progs['edwards-on-curve'], [3, 4], [])[0][0] != 0)
    if 'edwards-add-u' in progs:
        p, q = mul(rng.randrange(1, ELL), BASE), mul(rng.randrange(1, ELL), BASE)
        (n, d), _ = evaluate(progs['edwards-add-u'], [p[0], p[1], q[0], q[1]], [])
        check('add-u is u(P + Q)', n * inv(d) % P == mont_u(add(p, q)))
    if 'x25519-fast' in progs:
        k = rng.randrange(2 ** 254, 2 ** 255) & ~7
        u = mont_u(mul(rng.randrange(1, ELL), BASE))
        bits = [(k >> i) & 1 for i in range(256)]
        ins = [0] * 257
        for t in range(2, 254):
            prev = bits[t + 1] if t + 1 < 254 else (1 if t + 1 == 254 else 0)
            ins[t] = prev ^ bits[t]
        ins[256] = u
        (x, z), _ = evaluate(progs['x25519-fast'], ins, [])
        check('x25519-fast is the ladder', x * inv(z) % P == ladder(k, u))
    if 'lift-open' in progs and 'lift-point' in progs:
        for valid_u in (True, False):
            u = mont_u(mul(rng.randrange(1, ELL), BASE)) if valid_u else 2
            r = rng.randrange(1, P); bA, bB = rng.randrange(2), rng.randrange(2)
            mA, mB = mul(rng.randrange(1, ELL), BASE), mul(rng.randrange(1, ELL), BASE)
            o, _ = evaluate(progs['lift-open'], [u, r, bA, bB, mA[0], mA[1], mB[0], mB[1]], [])
            w, b = o[0], o[5]
            sel = pow(w, (P - 1) // 2, P) == 1
            s = sqrt(w if sel else w * inv(2) % P)
            cs = SA2 * inv(s) % P
            out, _ = evaluate(progs['lift-point'], [cs, int(sel), u, r, b, mA[0], mA[1], mB[0], mB[1]], masks('lift-point'))
            valid, px, py, zx, zy = out
            ok = valid == int(valid_u) and (not valid_u or (on_curve((px, py)) and mont_u((px, py)) == u))
            ok = ok and add(add(mA, mB), (px, py)) == (zx, zy)
            check(f'lift ({"valid" if valid_u else "twist"} u)', ok)
    if 'edwards-torsion-hinted' in progs:
        pt = mul(rng.randrange(1, ELL), BASE)
        q = mul(pow(8, -1, ELL), pt)
        hb = mul(rng.randrange(1, ELL), BASE); ha = add(q, hb)
        out, _ = evaluate(progs['edwards-torsion-hinted'], [pt[0], pt[1], ha[0], ha[1], hb[0], hb[1], rng.randrange(1, P)],
                          masks('edwards-torsion-hinted'))
        check('torsion zero for a prime-order point', out == [0, 0])
    if 'edwards-offset-sum-fast' in progs:
        R = mul(rng.randrange(1, ELL), BASE); k0 = rng.randrange(2 ** 252); init = mul(k0, R)
        tau = rng.randrange(2 ** 252); ins = [init[0], init[1]]; carry = 0
        for w in range(64):
            digit = ((tau >> (4 * w)) & 15) + carry; carry = int(digit > 8); digit -= 16 * carry
            if digit == 0: ins += [0, 1, 1]
            else:
                e = mul(abs(digit) * 16 ** w, R); ins += [e[0], e[1], 1 if digit > 0 else P - 1]
        (zy_p, zy_m), _ = evaluate(progs['edwards-offset-sum-fast'], ins, [])
        check('offset-sum-fast is u((k0 + tau) R)', zy_p * inv(zy_m) % P == mont_u(mul(k0 + tau, R)))
    report['passed'] = (all(v == 'pinned' for v in report['files'].values()) and len(report['files']) == len(pins)
                        and all(report['checks'].values()) and len(report['checks']) >= 7)
    print(json.dumps(report, indent=1))
    if not report['passed']:
        raise SystemExit(1)


main()
