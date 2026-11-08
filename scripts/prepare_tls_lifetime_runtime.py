#!/usr/bin/env python3
"""Isolated fixed-field destruction cleanup layered on the VM scratch candidate."""
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
WORK=ROOT/'handshake_backend/LifetimeWork'
DEST=ROOT/'.deps/tls-lifetime-runtime/MP-SPDZ'


def sha(data):return hashlib.sha256(data).hexdigest()


def main():
    subprocess.run([sys.executable,str(ROOT/'scripts/prepare_tls_scratch_runtime.py'),
                    '--destination',str(DEST)],check=True)
    changes={}
    def replace(name,old,new):
        before,after=changes.get(name,((DEST/name).read_bytes(),(DEST/name).read_bytes()))
        assert after.count(old)==1,name
        changes[name]=(before,after.replace(old,new))
    replace('Math/gf2n.h',b'#include <stdlib.h>\r\n',b'#include <stdlib.h>\r\n#include <sodium.h>\r\n')
    replace('Math/gf2n.h',b'  gf2n_() : a(0)       {}\r\n',b'''  // Fixed-width field payload cleanup on every C++ lifetime end. This also
  // covers discarded vector elements and temporary field values. It does not
  // erase live protocol/PRNG buffers or copies serialized as raw bytes.
  gf2n_(const gf2n_&) = default;
  gf2n_& operator=(const gf2n_&) = default;
  ~gf2n_() { sodium_memzero(&a, sizeof(a)); }
  gf2n_() : a(0)       {}
'''.replace(b'\n',b'\r\n'))
    replace('Math/modp.h',b'#include "Tools/octetStream.h"\n',b'#include <sodium.h>\n#include "Tools/octetStream.h"\n')
    replace('Math/modp.h',b'  modp_()\n    { avx_memzero(x, sizeof(x)); }',b'''  modp_(const modp_&) = default;
  modp_& operator=(const modp_&) = default;
  // All fixed-width limbs are wiped, including any unused high limbs.
  ~modp_() { sodium_memzero(x, sizeof(x)); }
  modp_()
    { avx_memzero(x, sizeof(x)); }''')
    patch=b''
    for name,(before,after) in changes.items():
        (DEST/name).write_bytes(after)
        patch+=''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),
                      fromfile='a/'+name,tofile='b/'+name)).encode()
    WORK.mkdir(exist_ok=True)
    (WORK/'fixed-field-lifetime.patch').write_bytes(patch)
    report={'source_archive':json.loads((ROOT/'benchmarks/config/dependencies.json').read_text())['mp_spdz'],
            'scratch_patch_sha256':sha((ROOT/'handshake_backend/ScratchWork/vm-scratch.patch').read_bytes()),
            'patch_sha256':sha(patch),'script_sha256':sha(Path(__file__).read_bytes()),
            'files':{n:{'before':sha(a),'after':sha(b)} for n,(a,b) in changes.items()},
            'abi_requires_complete_rebuild':True,'full_vm_erasure_implemented':False,
            'scope':'destruction of constructed fixed-width modp/gf2n field payloads; no raw byte, bigint, live preprocessing or PRNG erasure'}
    (WORK/'patch-provenance.json').write_text(json.dumps(report,indent=2)+'\n')
    print(DEST)


if __name__=='__main__':main()
