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
WORK = ROOT / 'handshake_backend/TransportEpochWork'
DEST = ROOT / '.deps/tls-transport-epoch/MP-SPDZ'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def apply_edits(replace):
    replace('Tools/ErasingThreadStack.h', '#include <atomic>', '#include <atomic>\n#include <pthread.h>')
    replace('Tools/ErasingThreadStack.h', '    void erase() noexcept', '''    int start(pthread_t* thread, void* (*entry)(void*), void* arg) {
        pthread_attr_t attr;
        int result=pthread_attr_init(&attr);
        if(result) return result;
        result=pthread_attr_setstack(&attr,data,size);
        if(!result) result=pthread_create(thread,&attr,entry,arg);
        pthread_attr_destroy(&attr);
        return result;
    }
    void erase() noexcept''')
    for name in ('Receiver','Sender'):
        replace('Networking/'+name+'.h', '#include <pthread.h>', '#include <pthread.h>\n#include "Tools/ErasingThreadStack.h"')
        replace('Networking/'+name+'.h', '    pthread_t thread;', '    pthread_t thread;\n    ErasingThreadStack owned_stack{512*1024};')
        replace('Networking/'+name+'.cpp', '    pthread_create(&thread, 0, run_thread, this);', '    if (owned_stack.start(&thread, run_thread, this))\n        throw runtime_error("cannot start owned communication thread");')
    replace('Tools/Worker.h', '#include "WaitQueue.h"', '#include "WaitQueue.h"\n#include "ErasingThreadStack.h"')
    replace('Tools/Worker.h', '\tpthread_t thread;', '\tpthread_t thread;\n    ErasingThreadStack owned_stack;')
    replace('Tools/Worker.h', '\t\tpthread_create(&thread, 0, Worker::run_thread, this);', '        if (owned_stack.start(&thread, Worker::run_thread, this))\n            throw runtime_error("cannot start owned helper worker");')
    replace('Networking/ssl_sockets.h', 'boost::asio::ssl::context::tlsv12', 'boost::asio::ssl::context::tls')
    replace('Networking/ssl_sockets.h', '        string prefix = SSL_DIR + me;', '''#ifndef SSL_OP_CLEANSE_PLAINTEXT
#error Secure lifecycle candidate requires OpenSSL plaintext cleansing support
#endif
        if (!SSL_CTX_set_min_proto_version(native_handle(), TLS1_3_VERSION))
            throw runtime_error("cannot require TLS 1.3 for MPC transport");
        SSL_CTX_set_options(native_handle(), SSL_OP_CLEANSE_PLAINTEXT | SSL_OP_NO_TICKET);
        string prefix = SSL_DIR + me;''')
    replace('Protocols/SecureShuffle.h', '    int add(unsigned n_shuffles);', '    bool empty() const { return shuffles.empty(); }\n    int add(unsigned n_shuffles);')
    replace('Processor/ExternalClients.h', '  ExternalClients(int party_num);', '''  bool empty() const {
    return client_connection_servers.empty() && external_client_sockets.empty()
        && client_ports.empty() && peer_ctxs.empty();
  }
  ExternalClients(int party_num);''')
    replace('OT/OTTripleSetup.h', '    OTTripleSetup get_fresh(Player& P)', '    bool empty() const { return setups.empty(); }\n    OTTripleSetup get_fresh(Player& P)')
    replace('Networking/Player.h', '  virtual string get_id() const', '  bool has_children() const { return !children.empty(); }\n  virtual string get_id() const')
    replace('Processor/Machine.h', 'Player& get_player() { return *P; }', 'Player& get_player() { if (!P) throw runtime_error("retired host transport"); return *P; }')
    replace('Processor/Machine.hpp', '  if (worker_epoch == size_t(-1))', '''  if (not use_encryption or not shuffle_store.empty() or
      not bit_memories.shuffle_store.empty() or not external_clients.empty() or
      not ot_setup.empty() or not P or P->has_children())
    throw runtime_error("unsupported machine-global epoch state");
  P->Check_Broadcast();
  if (worker_epoch == size_t(-1))''')
    replace('Processor/Machine.hpp', '  bit_memories.MS.clear(); bit_memories.MC.clear();', '''  bit_memories.MS.clear(); bit_memories.MC.clear();
  // Retained TLS keys would decrypt older captured MPC share traffic. Destroy
  // the old host transport, then create independently handshaken epoch channels.
  auto previous_player = P;
  P = nullptr;
  delete previous_player;
  P = new CryptoPlayer(N, "machineepoch" + to_string(worker_epoch));''')
    replace('Processor/Online-Thread.hpp', '  delete processor;', '  if (not BaseMachine::ot_setup.empty())\n    throw runtime_error("OT state is outside this epoch cleanup profile");\n  delete processor;')

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
              ROOT/'handshake_backend/LifecycleWork/owned-storage.patch']
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
    (WORK/'transport-epoch.patch').write_text(patch)
    report = {'source_archive': dependency, 'layers': {str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in layers},
              'patch_sha256':sha(patch.encode()), 'script_sha256':sha(Path(__file__).read_bytes()),
              'files':{n:{'before':sha(a.encode()), 'after':sha(b.encode())} for n,(a,b) in changes.items()},
              'abi_requires_complete_rebuild':True, 'application_execution_enabled':False,
              'full_vm_erasure_implemented':False}
    (WORK/'patch-provenance.json').write_text(json.dumps(report, indent=2)+'\n')
    print(DEST)

if __name__ == '__main__':
    main()
