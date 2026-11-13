#!/usr/bin/env python3
"""S14 end-to-end check (test sets K/E) with the REAL kernels and engines. NOT RUN in stage S14.

The stand-in pair test (tests/s14_pair.rs, vectors from tests/lean/S14Vectors.lean) checks the
shells and the scripts' sequencing with STAND-IN kernel tables: an accepted first message needs a
genuine sealed-sender envelope, PQXDH and an XEdDSA signature, which only a real sender produces
(handshake_backend/EmpHybridWork/check_receive_kernels.py drives a real libsignal sender). Two modes:

1. `layouts` (light once the kernels exist): for every `receive-*` kernel of a produced manifest
   (CIRCUIT_MANIFEST, e.g. the one check_receive_kernels.py's shapes were produced into), read its
   layout file and compare its input width and output marks with the closed forms the S14 scripts
   slice by (`Receive.*Out` in TlsMpc/Node/Flows/Receive.lean, `receive_kernel_expected` in
   node_worker/src/loader.rs, repeated here). A difference means the scripts' slices would cut the
   kernel's outputs at the wrong places: the receive scripts must not be selected.

       python3 node_worker/tests/e2e_s14.py layouts MANIFEST

2. `flow` (heavy): the accepted and refused first messages of check_receive_kernels.py through the
   S14 scripts on two real workers. It needs what this branch does not have: the controller-side
   script runner (op 93 batches from Lean, `ReceiveBackend.Runner`), S11's agreements
   (`Receive.Curve.agree`, S14_NOTES.md), and the V3 re-export of `xeddsa-check`, `xeddsa-recover`,
   `receive-torsion` (their pins pasted into loader.rs FIELD_PROGRAMS). Once all exist: build the
   receive fixture with `Flow.Receive.*` replaced by `ReceiveBackend.scriptApi`, then

       python3 scripts/guarded.py --heavy 16 1800 python3 node_worker/tests/e2e_s14.py flow NODE_WORKER

   This mode refuses to start until RECEIVE_SCRIPT_FIXTURE names the built fixture.

Writes nothing."""
import os, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]


def varint_width(n):
    return 1 if n < 128 else 2 if n < 16384 else 3 if n < 2097152 else 4


def body_of(total):
    sub = lambda a, b: max(a - b, 0)
    if sub(total, 2) < 128:
        return sub(total, 2)
    if sub(total, 3) < 16384:
        return sub(total, 3)
    return sub(total, 4)


def expected(name):
    """(input bits or None, [(bits, mark)]) as loader.rs receive_kernel_expected; marks 0 never, 1 public."""
    stem, *a = name.split(' ')
    a = [int(x) for x in a]
    w = 255
    conv = lambda cert: 8 * (cert + 319)
    if stem == 'receive-envelope-point' and len(a) == 1:
        return 8 * a[0], [(w, 0)]
    if stem == 'receive-unseal-static' and len(a) == 1:
        return 8 * a[0] + 256 + w, [(8, 0), (256, 0), (w, 0), (256, 0)]
    if stem == 'receive-unseal-message' and len(a) == 1:
        s = a[0]
        u = max(max(s - (82 + varint_width(body_of(max(s - 81, 0)))), 0) - 10, 0)
        return 8 * s + 8 + 256 + w, [(8, 0), (8 * u, 0), (16, 1)]
    if stem == 'receive-content-shape' and len(a) == 3:
        return 8 * a[0] + 8, [(32, 1)]
    if stem == 'receive-content' and len(a) == 4:
        u, c0, c1, hint = a
        cert = c0 % 128 + 128 * c1
        msg = body_of(max(max(u - (5 + cert), 0) - (2 if hint == 1 else 0), 0))
        return 8 * u + 8, [(8, 0), (8, 0), (8 * cert, 0), (8 * msg, 0)]
    if stem == 'receive-certificate' and len(a) == 4:
        return None, [(8, 0), (128, 0), (8, 0), (512, 0), (1, 0), (256, 0), (253, 0)]
    if stem == 'receive-certificate-verified' and not a:
        return 8 + 512 + 3 * w, [(8, 0)]
    if stem == 'receive-prekey-shape' and len(a) == 1:
        return 8 * a[0] + 8, [(168, 1)]
    if stem == 'receive-prekey-open' and len(a) == 5:
        return 8 * a[0] + 8 + 8 + 256, [(8, 0), (w, 0), (w, 0), (32, 1), (32, 1), (32, 1), (8 * 1568, 1)]
    if stem == 'receive-signal-shape' and len(a) == 5:
        return 8 * a[0] + 8, [(104, 1)]
    if stem == 'receive-session' and len(a) == 12:
        cert, n, one, _, _, _, _, _, low, high, _, _ = a
        ct = low if high == 0 else low % 128 + 128 * high
        dh4 = w if one > 0 else 0
        inp = 8 * n + 8 + 8 + 256 + 256 + 136 + 128 + 8 + 3 * w + dh4 + 256 + 6 * w + 8 * cert + 128 + 64
        return inp, [(8, 1), (conv(cert), 0), (8 * 236, 0), (8 * (8 + ct), 0)]
    if stem == 'receive-text' and len(a) == 2:
        return 8 * (8 + a[0]), [(8, 1), (16, 1), (8 * a[1], 1), (24, 1)]
    if stem == 'receive-access-key' and len(a) == 3:
        return conv(a[0]) + 8 * (8 + a[1]), [(8, 1), (conv(a[0]), 0)]
    return None


def layout(path):
    rows = path.read_text().splitlines()
    assert rows[0] == 'EMP_HYBRID_KERNEL_LAYOUT_V1', path
    inp, marks = 0, []
    for r in rows[1:]:
        f = r.split()
        if f[0] == 'I':
            inp += int(f[2])
        else:
            marks += [int(f[3])] * int(f[2])
    return inp, marks


def layouts(manifest):
    manifest = pathlib.Path(manifest)
    bad, seen = [], 0
    for row in manifest.read_text().splitlines()[1:]:
        sha, lsha, name = row.split(' ', 2)
        if not name.startswith('receive-'):
            continue
        seen += 1
        exp = expected(name)
        if exp is None:
            bad.append(f'{name}: unknown to the scripts')
            continue
        stem = 'kernel-' + name.replace(' ', '-')
        inp, marks = layout(manifest.parent / f'{stem}.layout')
        want = [m for bits, m in exp[1] for _ in range(bits)]
        if (exp[0] is not None and exp[0] != inp) or marks != want:
            bad.append(f'{name}: layout')
    print(f'{seen} receive kernels checked; {len(bad)} differ')
    for b in bad:
        print('  ' + b)
    return not bad and seen > 0


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else ''
    if mode == 'layouts' and len(sys.argv) > 2:
        sys.exit(0 if layouts(sys.argv[2]) else 1)
    if mode == 'flow':
        if not os.environ.get('RECEIVE_SCRIPT_FIXTURE'):
            sys.exit('e2e_s14 flow: needs the script runner, S11 agreements and the V3 re-export '
                     '(RECEIVE_SCRIPT_FIXTURE unset; see this file\'s header)')
        sys.exit('e2e_s14 flow: run the fixture named by RECEIVE_SCRIPT_FIXTURE as described above')
    sys.exit(__doc__)


main()
