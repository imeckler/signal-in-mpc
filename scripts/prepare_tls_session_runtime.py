#!/usr/bin/env python3
"""Build isolated owned-stack and raw-capacity lifetime cleanup layers."""
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / 'handshake_backend/SessionWork'
DEST = ROOT / '.deps/tls-session-runtime/MP-SPDZ'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def apply_edits(replace):
    replace('Processor/Machine.h', '  void retire_worker_epoch();', '  void retire_worker_epoch(bool renew_transport = true);')
    replace('Processor/Machine.hpp', 'void Machine<sint, sgf2n>::retire_worker_epoch()', 'void Machine<sint, sgf2n>::retire_worker_epoch(bool renew_transport)')
    replace('Processor/Machine.hpp', '  // Validate before mutation. In particular, never consume someone else\'s job.\n  if (ThreadQueue::thread_queue or threads.empty() or', '  // Validate before mutation. In particular, never consume someone else\'s job.\n  if (ThreadQueue::thread_queue or (threads.empty() and renew_transport) or')
    replace('Processor/Machine.hpp', '  P = new CryptoPlayer(N, "machineepoch" + to_string(worker_epoch));', '  if (renew_transport)\n    P = new CryptoPlayer(N, "machineepoch" + to_string(worker_epoch));')

def main():
    if DEST.exists():
        raise SystemExit('destination exists; retain evidence and use a fresh tree')
    archive = ROOT / '.deps/mp-spdz-v0.4.4.tar.gz'
    dependency = json.loads((ROOT/'benchmarks/config/dependencies.json').read_text())['mp_spdz']
    assert sha(archive.read_bytes()) == dependency['source_archive_sha256']
    with tarfile.open(archive) as tar:
        prefix = tar.getmembers()[0].name.split('/')[0] + '/'
        for member in tar.getmembers():
            if not member.isfile():
                continue
            name = member.name.removeprefix(prefix)
            path = Path(name)
            assert not path.is_absolute() and '..' not in path.parts
            if path.suffix not in ('.h', '.hpp', '.cpp', '.c', '.S') and name not in ('Makefile', 'CONFIG'):
                continue
            target = DEST / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(tar.extractfile(member).read())
    baseline = ROOT / '.deps/sharing-refresh/MP-SPDZ'
    for folder in ('deps', 'local'):
        target = DEST/folder
        if target.exists():
            shutil.rmtree(target)
        target.symlink_to(baseline/folder, target_is_directory=True)
    shutil.copyfile(baseline/'CONFIG.mine', DEST/'CONFIG.mine')
    layers = [ROOT/'handshake_backend/ScratchWork/vm-scratch.patch',
              ROOT/'handshake_backend/LifetimeWork/fixed-field-lifetime.patch',
              ROOT/'handshake_backend/ByteBufferWork/serialized-buffer.patch',
              ROOT/'handshake_backend/EpochWork/runtime-epoch.patch',
              ROOT/'handshake_backend/LifecycleWork/owned-storage.patch',
              ROOT/'handshake_backend/TransportEpochWork/transport-epoch.patch']
    for patch in layers:
        subprocess.run(['patch', '-p1', '-i', str(patch)], cwd=DEST, check=True)
    changes = {}
    def replace(name, old, new):
        before, after = changes.get(name, ((DEST/name).read_text() if (DEST/name).exists() else '', (DEST/name).read_text() if (DEST/name).exists() else ''))
        assert after.count(old) == 1, (name, old[:60])
        changes[name] = before, after.replace(old, new)
    apply_edits(replace)
    patch = ''
    for name, (before, after) in changes.items():
        (DEST/name).write_text(after)
        patch += ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                            fromfile='a/'+name if before else '/dev/null', tofile='b/'+name))
    (WORK/'session-epoch.patch').write_text(patch)
    report = {'source_archive': dependency, 'layers': {str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in layers},
              'patch_sha256':sha(patch.encode()), 'script_sha256':sha(Path(__file__).read_bytes()),
              'files':{n:{'before':sha(a.encode()), 'after':sha(b.encode())} for n,(a,b) in changes.items()},
              'abi_requires_complete_rebuild':True, 'application_execution_enabled':False,
              'full_vm_erasure_implemented':False}
    (WORK/'patch-provenance.json').write_text(json.dumps(report, indent=2)+'\n')
    print(DEST)

if __name__ == '__main__':
    main()
