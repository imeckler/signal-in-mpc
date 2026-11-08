#!/usr/bin/env python3
"""Build a separate pinned source tree for partial VM scratch cleanup experiments.

Never changes the canonical backend. The additive hooks expose only constructed
secret memory/register objects, including hidden stack frames. They do not
establish allocation-history, preprocessing, PRNG, or operational erasure.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'handshake_backend/ScratchWork'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def edits(sources):
    result = dict(sources)
    def replace(name, old, new):
        assert result[name].count(old) == 1, name
        result[name] = result[name].replace(old, new)
    replace('Tools/CheckVector.h', '    size_t size() const { return finish - start; }', '''    // Caller must own this vector exclusively. Visit constructed backing
    // objects, including hidden frames and values beyond the logical end.
    // This does not reach deallocated storage or old inner allocations.
    template<class Visitor>
    void visit_full_storage(Visitor&& visitor)
    {
        for (auto& value : full)
            visitor(value);
    }

    size_t size() const { return finish - start; }''')
    replace('Processor/Machine.h', '  string memory_filename();', '''  // Exclusive host-owner API, between completed exported function calls.
  // Visitors must not allocate MPC work, reveal values, or call back into us.
  // Partial cleanup only: no preprocessing, PRNG, allocator-history receipt.
  template<class ArithmeticVisitor, class BinaryVisitor>
  void visit_secret_scratch(ArithmeticVisitor&& arithmetic,
      BinaryVisitor&& binary);

  string memory_filename();''')
    replace('Processor/Machine.hpp', 'template<class sint, class sgf2n>\npair<DataPositions, NamedCommStats> Machine<sint, sgf2n>::stop_threads()', '''template<class sint, class sgf2n>
template<class ArithmeticVisitor, class BinaryVisitor>
void Machine<sint, sgf2n>::visit_secret_scratch(ArithmeticVisitor&& arithmetic,
        BinaryVisitor&& binary)
{
  // The embedding application serializes all host calls. Reject worker-thread
  // calls and outstanding jobs before visiting or changing any storage.
  if (ThreadQueue::thread_queue or threads.empty() or
      threads.size() != tinfo.size() or queues.size() != threads.size() or
      not active_threads.empty())
    throw runtime_error("secret scratch requires initialized quiescent host");
  for (size_t i = 0; i < threads.size(); ++i)
    if (not queues[i] or not queues[i]->available() or not tinfo[i].processor)
      throw runtime_error("secret scratch requires joined jobs");

  for (size_t i = 0; i < Mp.MS.size(); ++i)
    arithmetic(Mp.MS[i]);
  for (auto& value : bit_memories.MS)
    binary(value);
  for (auto& info : tinfo)
    {
      auto& proc = *info.processor;
      proc.Procp.get_S().visit_full_storage(arithmetic);
      proc.Procb.S.visit_full_storage(binary);
      arithmetic(proc.temp.Sansp);
    }
}

template<class sint, class sgf2n>
pair<DataPositions, NamedCommStats> Machine<sint, sgf2n>::stop_threads()''')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', type=Path, default=ROOT/'.deps/tls-scratch-runtime/MP-SPDZ')
    args = parser.parse_args()
    destination = args.destination.resolve()
    if destination.exists():
        raise SystemExit('destination already exists; retain evidence and use a fresh destination')
    archive = ROOT/'.deps/mp-spdz-v0.4.4.tar.gz'
    expected = json.loads((ROOT/'benchmarks/config/dependencies.json').read_text())['mp_spdz']
    assert digest(archive.read_bytes()) == expected['source_archive_sha256']
    names = ['Tools/CheckVector.h', 'Processor/Machine.h', 'Processor/Machine.hpp']
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        prefix = members[0].name.split('/')[0]+'/'
        sources = {name: tar.extractfile(prefix+name).read().decode() for name in names}
        changed = edits(sources)
        destination.mkdir(parents=True)
        # Source-only clean tree; no baseline objects, shared library or data.
        for member in members:
            if not member.isfile():
                continue
            name = member.name.removeprefix(prefix)
            path = Path(name)
            if path.is_absolute() or '..' in path.parts:
                raise ValueError('invalid archive path')
            if path.suffix not in ('.h', '.hpp', '.cpp', '.c', '.S') and name not in ('Makefile', 'CONFIG'):
                continue
            target = destination/path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(tar.extractfile(member).read())
    baseline = ROOT/'.deps/sharing-refresh/MP-SPDZ'
    for folder in ('deps', 'local'):
        if (baseline/folder).exists():
            # Headers/libraries only; building libSPDZ does not mutate these.
            target = destination/folder
            if target.exists():shutil.rmtree(target)
            target.symlink_to(baseline/folder, target_is_directory=True)
    shutil.copyfile(baseline/'CONFIG.mine', destination/'CONFIG.mine')
    patch = ''
    for name in names:
        (destination/name).write_text(changed[name])
        patch += ''.join(difflib.unified_diff(sources[name].splitlines(True),
                         changed[name].splitlines(True), fromfile='a/'+name, tofile='b/'+name))
    OUT.mkdir(exist_ok=True)
    (OUT/'vm-scratch.patch').write_text(patch)
    report = {'mp_spdz': expected, 'patch_sha256': digest(patch.encode()),
              'files': {name: {'before': digest(sources[name].encode()),
                               'after': digest(changed[name].encode())} for name in names},
              'configuration_sha256': digest((destination/'CONFIG.mine').read_bytes()),
              'script_sha256': digest(Path(__file__).read_bytes()),
              'full_vm_erasure_implemented': False, 'application_execution_enabled': False}
    (OUT/'patch-provenance.json').write_text(json.dumps(report, indent=2)+'\n')
    print(destination)


if __name__ == '__main__':
    main()
