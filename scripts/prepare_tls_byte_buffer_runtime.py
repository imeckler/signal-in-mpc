#!/usr/bin/env python3
"""Prepare a source-only byte-buffer candidate; never mutate frozen runtimes."""
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / 'handshake_backend/ByteBufferWork'
DEST = ROOT / '.deps/tls-byte-buffer-runtime/MP-SPDZ'

def sha(data):
    return hashlib.sha256(data).hexdigest()

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
              ROOT/'handshake_backend/LifetimeWork/fixed-field-lifetime.patch']
    for patch in layers:
        subprocess.run(['patch', '-p1', '-i', str(patch)], cwd=DEST, check=True)
    changes = {}
    def replace(name, old, new):
        before, after = changes.get(name, ((DEST/name).read_text(), (DEST/name).read_text()))
        assert after.count(old) == 1, (name, old[:60])
        changes[name] = before, after.replace(old, new)
    h = 'Tools/octetStream.h'
    replace(h, '  void reset();', '''  void reset();
  void release_storage()
  {
    if (data)
      {
        sodium_memzero(data, get_max_length());
        delete[] data;
      }
  }''')
    replace(h, '  ~octetStream() { if(data) delete[] data; }', '''  ~octetStream() { release_storage(); sodium_memzero(bits.data(), sizeof(bits)); }''')
    for name, expr in [('get_ptr', 'ptr'), ('get_length', 'end'), ('get_max_length', 'data_end')]:
        replace(h, f'return {expr} - data;', f'return data ? {expr} - data : 0;')
    replace(h, '''  auto read = get_ptr();
  auto len = get_length();''', '''  auto len = min(get_length(), l);
  auto read = min(get_ptr(), len);
  bool truncated = len != get_length();''')
    replace(h, '''      delete[] data;
    }
  data=nd;''', '''      release_storage();
    }
  if (truncated)
    bits = {};
  data=nd;''')
    replace(h, 'if (end + l > data_end)', 'if (l > get_max_length() - get_length())')
    cpp = 'Tools/octetStream.cpp'
    replace(cpp, '    end = 0;\n}', '    end = 0;\n    bits = {};\n}')
    replace(cpp, '''    if (data)
        delete[] data;
    reset();''', '''    release_storage();
    reset();''')
    replace(cpp, '''  auto read = os.get_ptr();
  if (os.get_length() >= get_max_length())
    {
      if (data)
        delete[] data;
      data=new octet[os.get_max_length()];
      set_max_length(os.get_max_length());
    }
  set_length(os.get_length());
  memcpy(data,os.data,get_length()*sizeof(octet));
  ptr = data + read;
  bits = os.bits;''', '''  if (this == &os)
    return;
  auto read = os.get_ptr();
  if (os.get_length() >= get_max_length())
    {
      // Allocate first: a failed allocation leaves this owner unchanged.
      auto replacement = new octet[os.get_max_length()];
      release_storage();
      data = replacement;
      set_max_length(os.get_max_length());
    }
  else if (data)
    sodium_memzero(data, get_max_length());
  set_length(os.get_length());
  if (get_length())
    memcpy(data,os.data,get_length()*sizeof(octet));
  ptr = data + read;
  bits = os.bits;''')
    f = 'Tools/FlexBuffer.h'
    replace(f, '''		del();
		max_len = new_len;
		buf = new char[max_len];''', '''        auto replacement = new char[new_len];
        del();
        max_len = new_len;
        buf = replacement;''')
    replace(f, '''	if (buf)
		delete[] buf;''', '''    if (buf)
    {
        sodium_memzero(buf, max_len);
        delete[] buf;
    }''')
    start = '''	char* old = buf;
	max_len = new_max_len;
	buf = new char[max_len];
	if (old)
	{
		avx_memcpy(buf, old, len);
		delete[] old;
	}
	ptr = buf + (ptr - old);'''
    replace(f, start, '''    if (new_max_len < len)
        throw length_error("cannot shrink below live buffer length");
    auto replacement = new char[new_max_len];
    auto read = buf ? ptr - buf : 0;
    if (buf)
        avx_memcpy(replacement, buf, len);
    del();
    buf = replacement;
    max_len = new_max_len;
    // del() resets all metadata; restore the preserved live prefix and cursor.
    len = saved_len;
    ptr = buf + read;'''.replace('    auto replacement', '    auto saved_len = len;\n    auto replacement', 1))
    replace('Networking/Exchanger.h', '''                receive_stream.resize(max(new_len, len));
                length_received''', '''                receive_stream.resize(max(new_len, len));
                // In-place exchange can move the shared allocation mid-send.
                data = send_stream.get_data();
                length_received''')
    patch = ''
    for name, (before, after) in changes.items():
        (DEST/name).write_text(after)
        patch += ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                            fromfile='a/'+name, tofile='b/'+name))
    (WORK/'serialized-buffer.patch').write_text(patch)
    report = {'source_archive': dependency, 'layers': {str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in layers},
              'patch_sha256':sha(patch.encode()), 'script_sha256':sha(Path(__file__).read_bytes()),
              'files':{n:{'before':sha(a.encode()), 'after':sha(b.encode())} for n,(a,b) in changes.items()},
              'abi_requires_complete_rebuild':True, 'application_execution_enabled':False,
              'full_vm_erasure_implemented':False}
    (WORK/'patch-provenance.json').write_text(json.dumps(report, indent=2)+'\n')
    print(DEST)

if __name__ == '__main__':
    main()
