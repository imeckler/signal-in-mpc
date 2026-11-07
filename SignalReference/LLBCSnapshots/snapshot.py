#!/usr/bin/env python3
"""Preserve exact extraction inputs independently of cached compiler toolchains.

create captures existing LLBC files, verify checks compressed and original
hashes, restore recreates missing files without overwriting different content.
These snapshots retain rejected experiments too; inclusion is not acceptance.
"""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
SKIP = {'.lake', '.deps', 'Build', 'BridgeBuild', 'RegressionBuild', 'Bin', 'Source', 'target', '.git'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def create():
    entries = []
    for base, dirs, names in os.walk(REFERENCE):
        dirs[:] = sorted(x for x in dirs if x not in SKIP)
        for name in sorted(names):
            if not name.endswith('.llbc'):
                continue
            path = Path(base)/name
            if path.is_symlink():
                raise ValueError('symlink extraction input')
            raw = path.read_bytes()
            digest = sha(raw)
            blob = HERE/(digest+'.llbc.gz')
            if not blob.exists():
                buffer = io.BytesIO()
                with gzip.GzipFile(filename='', mode='wb', fileobj=buffer, mtime=0) as stream:
                    stream.write(raw)
                blob.write_bytes(buffer.getvalue())
            if sha(path.read_bytes()) != digest:
                raise ValueError('extraction input changed during snapshot')
            entries.append({'path': str(path.relative_to(REFERENCE)), 'bytes': len(raw),
                            'sha256': digest, 'blob': blob.name, 'compressed_sha256': sha(blob.read_bytes())})
    (HERE/'manifest.json').write_text(json.dumps({'format': 'llbc-snapshot-v1', 'entries': entries}, indent=2)+'\n')
    return entries


def checked(entry):
    if entry['blob'] != entry['sha256']+'.llbc.gz':
        raise ValueError('invalid snapshot blob name')
    blob = (HERE/entry['blob']).read_bytes()
    if sha(blob) != entry['compressed_sha256']:
        raise ValueError('compressed snapshot hash mismatch')
    with gzip.GzipFile(fileobj=io.BytesIO(blob)) as stream:
        raw = stream.read(entry['bytes']+1)
    if len(raw) != entry['bytes'] or sha(raw) != entry['sha256']:
        raise ValueError('extraction snapshot hash/length mismatch')
    return raw


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['create', 'verify', 'restore'])
    parser.add_argument('--destination', type=Path, default=REFERENCE)
    parser.add_argument('--only', help='one exact path from the manifest')
    args = parser.parse_args()
    if args.action == 'create':
        entries = create()
    else:
        manifest = json.loads((HERE/'manifest.json').read_text())
        if manifest['format'] != 'llbc-snapshot-v1':
            raise ValueError('unsupported snapshot manifest')
        entries = manifest['entries']
    if args.only:
        entries = [e for e in entries if e['path'] == args.only]
        if not entries:
            raise ValueError('snapshot path not found')
    root = args.destination.resolve()
    for entry in entries:
        raw = checked(entry)
        path = root/entry['path']
        path.resolve().relative_to(root)
        if args.action == 'restore':
            if path.exists():
                if path.is_symlink() or path.read_bytes() != raw:
                    raise ValueError('refusing to overwrite different extraction input: '+entry['path'])
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open('xb') as output:
                    output.write(raw)
    print(f'{args.action}: {len(entries)} exact LLBC snapshots checked')


if __name__ == '__main__':
    main()
