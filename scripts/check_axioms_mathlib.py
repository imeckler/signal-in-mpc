#!/usr/bin/env python3
"""Check the axioms of every theorem in the Mathlib proof package (proofs/); write proofs/SECURITY_MATHLIB_AXIOMS.txt.

    python3 scripts/check_axioms_mathlib.py              # run Lean, check, write the file
    python3 scripts/check_axioms_mathlib.py --from-log F # parse a saved `lake env lean` output instead

The companion of scripts/check_axioms.py for the separate package proofs/ (its own lakefile, with
Mathlib). Requires `lake build` in proofs/ to have been run (see proofs/README.md). Then:
  * scans proofs/TlsMpcProofs/**/*.lean for forbidden constructs (sorry, native_decide, bv_decide,
    axiom declarations, implemented_by, extern, unsafe, opaque) and fails on any;
  * generates proofs/.lake/check_axioms_all.lean, which imports the package and runs
    `#print axioms` on EVERY `theorem` declared in proofs/TlsMpcProofs/ (index entries and helpers);
  * runs it with `lake env lean` through scripts/guarded.py (12 GB cap; a light job: it only reads
    .olean files, about 4 GB, under a minute);
  * fails on any Lean error, on a theorem without exactly one result, and on any axiom other than
    propext, Classical.choice, Quot.sound (so `sorryAx` and `Lean.ofReduceBool` fail);
  * writes proofs/SECURITY_MATHLIB_AXIOMS.txt (checked in), so a change shows up as a diff.
The full Lean output is kept in .deps/check-axioms-mathlib.log (not checked in).
"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROOFS = os.path.join(ROOT, 'proofs')
SOURCES = os.path.join(PROOFS, 'TlsMpcProofs')
GENERATED = os.path.join(PROOFS, '.lake', 'check_axioms_all.lean')
OUTPUT = os.path.join(PROOFS, 'SECURITY_MATHLIB_AXIOMS.txt')
LOG = os.path.join(ROOT, '.deps', 'check-axioms-mathlib.log')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = [r'\bsorry\b', r'\bnative_decide\b', r'\bbv_decide\b', r'^\s*axiom\s', r'implemented_by',
             r'@\[extern', r'\bunsafe\b', r'^\s*opaque\s', r'\badmit\b']


def source_files():
    out = []
    for base, _, names in os.walk(SOURCES):
        for n in sorted(names):
            if n.endswith('.lean'):
                out.append(os.path.join(base, n))
    return sorted(out)


def strip_comments(text):
    text = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)


def scan_forbidden():
    problems = []
    for path in source_files():
        code = strip_comments(open(path, encoding='utf-8').read())
        for i, line in enumerate(code.splitlines(), 1):
            for pat in FORBIDDEN:
                if re.search(pat, line):
                    problems.append(f'{os.path.relpath(path, ROOT)}:{i}: forbidden `{pat}`: {line.strip()}')
    return problems


def theorem_names():
    names = []
    for path in source_files():
        stack = []
        for line in strip_comments(open(path, encoding='utf-8').read()).splitlines():
            m = re.match(r'^namespace\s+(\S+)', line)
            if m:
                stack.append(m.group(1))
                continue
            m = re.match(r'^end\s+(\S+)\s*$', line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
                continue
            m = re.match(r'^(?:private\s+|protected\s+)?theorem\s+(\S+)', line)
            if m:
                names.append('.'.join(stack + [m.group(1)]))
    return names


def run_lean(names):
    os.makedirs(os.path.dirname(GENERATED), exist_ok=True)
    with open(GENERATED, 'w') as f:
        f.write('import TlsMpcProofs\n\n' + ''.join(f'#print axioms {n}\n' for n in names))
    cmd = ['python3', os.path.join(ROOT, 'scripts', 'guarded.py'), '12', '1800',
           'lake', 'env', 'lean', GENERATED]
    r = subprocess.run(cmd, cwd=PROOFS, capture_output=True, text=True)
    os.makedirs(os.path.dirname(LOG), exist_ok=True)
    with open(LOG, 'w') as f:
        f.write(r.stdout + '\n--- stderr ---\n' + r.stderr)
    return r.returncode, r.stdout


def parse(text):
    flat = re.sub(r'\s+', ' ', text)
    axioms = {}
    for m in re.finditer(r"'(\S+?)' depends on axioms: \[([^\]]*)\]", flat):
        axioms.setdefault(m.group(1), []).append(sorted(a.strip() for a in m.group(2).split(',') if a.strip()))
    for m in re.finditer(r"'(\S+?)' does not depend on any axioms", flat):
        axioms.setdefault(m.group(1), []).append([])
    errors = [line for line in text.splitlines() if ': error' in line]
    return axioms, errors


def main():
    names = theorem_names()
    problems = scan_forbidden()
    if len(sys.argv) == 3 and sys.argv[1] == '--from-log':
        code, text = 0, open(sys.argv[2]).read().split('\n--- stderr ---\n')[0]
    else:
        code, text = run_lean(names)
    axioms, errors = parse(text)
    if errors:
        problems += ['Lean error: ' + e for e in errors[:20]]
    elif code != 0:
        problems.append(f'lake env lean exited with {code}')
    lines = ['# Axioms of every theorem in the Mathlib proof package (proofs/TlsMpcProofs/).',
             '# Generated by scripts/check_axioms_mathlib.py; do not edit.',
             '# Allowed: propext, Classical.choice, Quot.sound. No sorry, native_decide, bv_decide, new axioms.',
             '']
    for n in names:
        found = axioms.get(n, [])
        if len(found) != 1:
            problems.append(f'{n}: {len(found)} `#print axioms` results (want 1)')
        for a in (found[0] if found else []):
            if a not in ALLOWED:
                problems.append(f'{n}: axiom {a} not allowed')
        lines.append(f'{n}: [{", ".join(found[0]) if found else "MISSING"}]')
    with open(OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')
    print(f'{len(names)} theorems in proofs/TlsMpcProofs; wrote {os.path.relpath(OUTPUT, ROOT)}')
    if problems:
        print('FAILED:')
        for p in problems:
            print('  ' + p)
        sys.exit(1)
    print('OK: only allowed axioms; no forbidden constructs')


if __name__ == '__main__':
    main()
