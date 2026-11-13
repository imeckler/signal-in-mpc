#!/usr/bin/env python3
"""Compare two circuit manifests (`OUT/manifest.txt` of scripts/produce_circuits.py).

    python3 scripts/compare_manifests.py OLD_MANIFEST NEW_MANIFEST [--changed PREFIX ...]

Each line of a manifest is `SHA256 LAYOUT_SHA256 NAME PARAMETERS`. Kernels are matched by
`NAME PARAMETERS`. Every kernel present in both whose name does not start with one of the
`--changed` prefixes must have the same gate-list and layout hashes (byte-identical files);
kernels with such a prefix are listed with whether they changed. Kernels present in only one
manifest are listed. Exit status 1 if an unchanged-by-design kernel differs, 0 otherwise.
Reads the two files only.

For the emitter batch (EMITTER_BATCH.md): `--changed receive-text bundle-slot`.
"""
import sys


def load(path):
    rows = {}
    for line in open(path):
        parts = line.split()
        if len(parts) < 3 or line.startswith('#'):
            continue
        rows[' '.join(parts[2:])] = (parts[0], parts[1])
    return rows


def main():
    args = sys.argv[1:]
    if len(args) < 2:
        print(__doc__)
        sys.exit(2)
    old, new = load(args[0]), load(args[1])
    changed = args[3:] if len(args) > 2 and args[2] == '--changed' else []
    expected = lambda name: any(name == p or name.startswith(p + ' ') for p in changed)
    same, differ, designed = 0, [], []
    for key in sorted(set(old) & set(new)):
        if expected(key):
            designed.append((key, old[key] != new[key]))
        elif old[key] == new[key]:
            same += 1
        else:
            differ.append((key, 'circuit' if old[key][0] != new[key][0] else 'layout'))
    print(f'{same} kernels byte-identical (gate list and layout)')
    for key, what in differ:
        print(f'DIFFERENT ({what}): {key}')
    for key, did in designed:
        print(f'{"changed" if did else "UNCHANGED (expected a change)"}: {key}')
    for key in sorted(set(old) - set(new)):
        print(f'only in old: {key}')
    for key in sorted(set(new) - set(old)):
        print(f'only in new: {key}')
    sys.exit(1 if differ else 0)


if __name__ == '__main__':
    main()
