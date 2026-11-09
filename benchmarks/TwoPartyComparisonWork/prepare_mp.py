"""Reproduce isolated MP-SPDZ secure-OT build on this Apple Silicon host.

No edits to canonical runtime. No insecure/KOS switches. Source acquisition
uses exact commits; dependency revision checks reject parent-repository HEADs.
"""
import hashlib
import pathlib
import shutil
import subprocess
import tarfile
import urllib.request

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
MP=BASE/'data61-MP-SPDZ-113c4e4'
COMMIT='113c4e47dd94bca9ecab029d2f0abe649bea5c52'
ARCHIVE_SHA='53cb2822dce57379f1c66647511b866e3e5db3e2f32b530a13e0c872a418ab78'
DEPS={
 'libOTe2':('mkskeller/libOTe','fe6b2ff82a976a5332b3a2efe325831588b1324a'),
 'SimplestOT_C':('mkskeller/SimplestOT_C','7ef7666909e493a18c99efe56f97cc4d13723005'),
 'simde':('simd-everywhere/simde','0ba20859e9f557cee161d2cab2728b56dca7ec38'),
 'sse2neon':('DLTcollab/sse2neon','ddca67108e3e96a288e9aa7e31bfacca2309f624')}

def run(args,cwd=ROOT):
 with open(BASE/'prepare-mp.log','a') as log:
  subprocess.run(list(map(str,args)),cwd=cwd,stdout=log,stderr=subprocess.STDOUT,check=True)

def checkout(path,repo,commit,recursive=False):
 if not (path/'.git').exists():
  if path.exists() and not any(path.iterdir()):path.rmdir()
  run(['git','clone','--no-checkout',f'https://github.com/{repo}.git',path])
 top=subprocess.check_output(['git','-C',str(path),'rev-parse','--show-toplevel'],text=True).strip()
 if pathlib.Path(top)!=path.resolve():raise ValueError('dependency repository root mismatch')
 run(['git','checkout','--detach',commit],path)
 if recursive:run(['git','submodule','update','--init','--recursive'],path)
 actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
 if actual!=commit:raise ValueError('dependency revision mismatch')

if __name__=='__main__':
 BASE.mkdir(parents=True,exist_ok=True)
 archive=ROOT/'.deps/mp-spdz-v0.4.4.tar.gz'
 if not archive.exists():urllib.request.urlretrieve(f'https://codeload.github.com/data61/MP-SPDZ/tar.gz/{COMMIT}',archive)
 if hashlib.sha256(archive.read_bytes()).hexdigest()!=ARCHIVE_SHA:raise ValueError('MP-SPDZ archive mismatch')
 if not MP.exists():
  with tarfile.open(archive) as t:t.extractall(BASE,filter='data')
 for name,(repo,commit) in DEPS.items():checkout(MP/'deps'/name,repo,commit,name=='libOTe2')
 # MP-SPDZ's build helper pins coproto/macoro/function2/libdivide. Capture and
 # verify their resolved identities in the final build receipt, not a parent HEAD.
 with tarfile.open(archive) as t:
  prefix=t.getnames()[0]
  config=t.extractfile(prefix+'/CONFIG').read().decode()
 config+='''
# Isolated 2PC comparison, secure SoftSpoken extension.
ARCH = -mcpu=native
AVX_OT = 0
USE_KOS = 0
USE_LIBOTE2 = 1
GDEBUG =
MY_CFLAGS += -I/opt/homebrew/opt/openssl@3.5/include -Wno-error=deprecated-literal-operator
MY_LDLIBS += -L/opt/homebrew/opt/openssl@3.5/lib
'''
 if (MP/'CONFIG').read_text()!=config:(MP/'CONFIG').write_text(config)
 run(['cmake','-S',MP/'deps/SimplestOT_C/ref10','-B',MP/'deps/SimplestOT_C/ref10'])
 run(['python3',ROOT/'benchmarks/TwoPartyComparisonWork/instrument_mp.py'])
 run(['make','-j','2','tinier-party.x','mascot-party.x'],MP)
 print('Built isolated candidates; verify final dependency/config/product receipt before use.')
