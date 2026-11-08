#!/usr/bin/env python3
"""Build an isolated quiescent protocol-epoch renewal candidate."""
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / 'handshake_backend/EpochWork'
DEST = ROOT / '.deps/tls-epoch-runtime/MP-SPDZ'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def apply_edits(replace):
    replace('Tools/random.h', '   static const int N_CACHE = 10;', '''   class EraseOnExit
   {
     void* ptr; size_t size;
   public:
     EraseOnExit(void* ptr, size_t size) : ptr(ptr), size(size) {}
     EraseOnExit(const EraseOnExit&) = delete;
     ~EraseOnExit() { sodium_memzero(ptr, size); }
   };
   static const int N_CACHE = 10;''')
    replace('Tools/random.h', '   PRNG();', '''   PRNG();
   PRNG(const PRNG&) = default;
   PRNG& operator=(const PRNG&) = default;
   ~PRNG() { erase_state(); }

   // Invalidation only. Correlated streams must be rebuilt collectively;
   // never erase a live shared stream and then continue using it.
   void erase_state() noexcept
   {
     sodium_memzero(seed, sizeof(seed));
     sodium_memzero(state, sizeof(state));
     sodium_memzero(random, sizeof(random));
#ifdef USE_AES
     sodium_memzero(KeyScheduleC, sizeof(KeyScheduleC));
     sodium_memzero(KeySchedule, sizeof(KeySchedule));
#endif
     cnt = RAND_SIZE;
     n_cached_bits = 0;
     cached_bits = 0;
     initialized = false;
   }''')
    replace('Tools/random.cpp', '  initialized = true;\n  #ifdef USE_AES', '''  // Reseeding must not return cached bits/random bytes from the old epoch.
  sodium_memzero(random, sizeof(random));
  sodium_memzero(state, sizeof(state));
#ifdef USE_AES
  sodium_memzero(KeyScheduleC, sizeof(KeyScheduleC));
  sodium_memzero(KeySchedule, sizeof(KeySchedule));
#endif
  n_cached_bits = 0;
  cached_bits = 0;
  initialized = true;
  #ifdef USE_AES''')
    replace('Tools/random.cpp', '  octet seed[SEED_SIZE];', '  octet seed[SEED_SIZE];\n  EraseOnExit cleanup(seed, sizeof(seed));')
    replace('Tools/random.cpp', '  octet tmp[SEED_SIZE];', '  octet tmp[SEED_SIZE];\n  EraseOnExit cleanup(tmp, sizeof(tmp));')
    replace('Tools/random.cpp', '    unsigned char tmp[RAND_SIZE + SEED_SIZE];', '    unsigned char tmp[RAND_SIZE + SEED_SIZE];\n    EraseOnExit cleanup(tmp, sizeof(tmp));')
    # The allocation remains live until the guard has erased its content.
    replace('Tools/random.cpp', '  delete[] words;', '  sodium_memzero(words, n_words * sizeof(word));\n  delete[] words;')
    replace('Tools/random.cpp', '  assert(initialized);', '  if (not initialized)\n    throw runtime_error("uninitialized PRNG");')
    replace('Tools/Hash.cpp', '    free(state);', '    sodium_memzero(state, sizeof(*state));\n    free(state);')
    replace('Tools/Hash.cpp', '    crypto_generichash_init(state, 0, 0, crypto_generichash_BYTES);', '    sodium_memzero(state, sizeof(*state));\n    crypto_generichash_init(state, 0, 0, crypto_generichash_BYTES);')
    replace('Processor/Machine.h', '  bool live_prep;', '  bool live_prep;\n  size_t worker_epoch = 0;')
    replace('Processor/Online-Thread.hpp', '  string id = "thread" + to_string(num);', '  string id = "thread" + to_string(num) + "epoch" + to_string(machine.worker_epoch);')
    replace('Processor/Machine.h', '  pair<DataPositions, NamedCommStats> stop_threads();', '''  pair<DataPositions, NamedCommStats> stop_threads();

  // Host-exclusive barrier. Destroy per-thread protocol/randomness/prep owners;
  // the next checked run_function collectively creates fresh ones. Does not
  // promise complete erasure of machine-global or externally retained storage.
  void retire_worker_epoch();''')
    replace('Processor/Machine.hpp', 'template<class sint, class sgf2n>\npair<DataPositions, NamedCommStats> Machine<sint, sgf2n>::stop_threads()', '''template<class sint, class sgf2n>
void Machine<sint, sgf2n>::retire_worker_epoch()
{
  // Validate before mutation. In particular, never consume someone else's job.
  if (ThreadQueue::thread_queue or threads.empty() or
      threads.size() != tinfo.size() or queues.size() != threads.size() or
      not active_threads.empty())
    throw runtime_error("epoch retirement requires initialized quiescent host");
  for (size_t i = 0; i < threads.size(); ++i)
    if (not queues[i] or not queues[i]->available() or not tinfo[i].processor)
      throw runtime_error("epoch retirement requires joined jobs");
  if (not live_prep or not opts.disk_memory.empty())
    throw runtime_error("epoch renewal requires live prep and ordinary memory");
  if (worker_epoch == size_t(-1))
    throw runtime_error("worker epoch exhausted");
  // stop_threads executes protocol checks before destroying each thread's
  // complete Processor, preprocessing, MC, and Player ownership subtrees.
  stop_threads();
  ++worker_epoch;
  tinfo.clear();
  M2.resize_s(0); M2.resize_c(0);
  Mp.resize_s(0); Mp.resize_c(0);
  Mi.resize_s(0); Mi.resize_c(0);
  bit_memories.MS.clear(); bit_memories.MC.clear();
  // Host-owned FunctionArgument/output shares deliberately survive. Memory
  // sizes and all protocol owners are rebuilt by prepare on the next call.
}

template<class sint, class sgf2n>
pair<DataPositions, NamedCommStats> Machine<sint, sgf2n>::stop_threads()''')
    replace('Tools/octetStream.h', 'void set_length(size_t len) { end = data + len; }', 'void set_length(size_t len) { end = data ? data + len : nullptr; }')
    replace('Tools/octetStream.h', 'void set_max_length(size_t mxlen) { data_end = data + mxlen; }', 'void set_max_length(size_t mxlen) { data_end = data ? data + mxlen : nullptr; }')
    replace('Tools/FlexBuffer.h', 'ptr = (char*)os.get_data() + os.get_ptr();', 'ptr = os.get_data() ? (char*)os.get_data() + os.get_ptr() : nullptr;')
    replace('Networking/Exchanger.h', '''        receive_stream.set_length(new_len);
        receive_stream.reset_read_head();''', '''        // Allocation/read failures must not publish an out-of-range or
        // partial message from a destructor during exception unwinding.
        if (length_received and received == new_len and
            (not send_socket or sent == len))
          receive_stream.set_length(new_len);
        else
          receive_stream.reset_write_head();
        receive_stream.reset_read_head();''')

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
              ROOT/'handshake_backend/ByteBufferWork/serialized-buffer.patch']
    for patch in layers:
        subprocess.run(['patch', '-p1', '-i', str(patch)], cwd=DEST, check=True)
    changes = {}
    def replace(name, old, new):
        before, after = changes.get(name, ((DEST/name).read_text(), (DEST/name).read_text()))
        assert after.count(old) == 1, (name, old[:60])
        changes[name] = before, after.replace(old, new)
    apply_edits(replace)
    patch = ''
    for name, (before, after) in changes.items():
        (DEST/name).write_text(after)
        patch += ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                            fromfile='a/'+name, tofile='b/'+name))
    (WORK/'runtime-epoch.patch').write_text(patch)
    report = {'source_archive': dependency, 'layers': {str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in layers},
              'patch_sha256':sha(patch.encode()), 'script_sha256':sha(Path(__file__).read_bytes()),
              'files':{n:{'before':sha(a.encode()), 'after':sha(b.encode())} for n,(a,b) in changes.items()},
              'abi_requires_complete_rebuild':True, 'application_execution_enabled':False,
              'full_vm_erasure_implemented':False}
    (WORK/'patch-provenance.json').write_text(json.dumps(report, indent=2)+'\n')
    print(DEST)

if __name__ == '__main__':
    main()
