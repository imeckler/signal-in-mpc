"""Build separately pinned unaudited current EMP candidate and gate adapter.

Only vendor change is aggregate NetIO byte counters at destruction, including
final COT checks and sibling channels. No protocol/security parameter edits.
"""
import hashlib
import json
import pathlib
import subprocess
import tarfile
import urllib.request
import re

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
PINS={
 'emp-tool':('339bde8479842c88d115cec16ffca90a4c050c3f','66630108ca22744838c472d92ad41efcfcb3d0ad3217aad20fefdf6118f18d04'),
 'emp-ot':('5072bdab546c89a24be3368a7ce2bab1cdefec1f','22289325bd3a3ab1de50b52f90221142b9cc68ff379f9ec1a5d979795dd3548f'),
 'emp-ag2pc':('a245ca0f67abaf2d48c711e3c050ce961e60ad29','1ebb7286c42799d28b6a3eb3fe4f65a7660c43b6eb6694674cfb45cc0a886bde')}

def run(args):
 with open(BASE/'prepare-modern-emp.log','a') as log:subprocess.run(list(map(str,args)),stdout=log,stderr=subprocess.STDOUT,check=True)

if __name__=='__main__':
 BASE.mkdir(exist_ok=True)
 for name,(commit,digest) in PINS.items():
  archive=BASE/(name+'-modern.tar.gz')
  if not archive.exists():urllib.request.urlretrieve(f'https://codeload.github.com/emp-toolkit/{name}/tar.gz/{commit}',archive)
  actual=hashlib.sha256(archive.read_bytes()).hexdigest()
  if digest is not None and actual!=digest:raise ValueError('archive identity mismatch')
  if not (BASE/f'{name}-{commit}').exists():
   with tarfile.open(archive) as t:t.extractall(BASE,filter='data')
 tool=BASE/f'emp-tool-{PINS["emp-tool"][0]}'
 header=tool/'emp-tool/runtime/io/net_io_channel.h'
 with tarfile.open(BASE/'emp-tool-modern.tar.gz') as t:
  prefix=t.getnames()[0];original=t.extractfile(prefix+'/emp-tool/runtime/io/net_io_channel.h').read().decode()
 source=original.replace('#include <string>','#include <string>\n#include <atomic>')
 at='class NetIO : public IOChannel { public:'
 if source.count(at)!=1:raise ValueError('counter class source drift')
 source=source.replace(at,at+'\n\tinline static std::atomic<uint64_t> benchmark_sent{0}, benchmark_received{0};')
 at='\t~NetIO() {\n\t\tflush();'
 if source.count(at)!=1:raise ValueError('counter destructor source drift')
 source=source.replace(at,at+'\n\t\tbenchmark_sent += send_counter;\n\t\tbenchmark_received += recv_counter;')
 if header.read_text()!=source:header.write_text(source)
 # These pinned main revisions define identically named global AG helpers and
 # emp:: tool helpers. Preserve the AG helper implementations explicitly;
 # namespace qualification only, with original/overlay identities recorded.
 compatibility={}
 ag=BASE/f'emp-ag2pc-{PINS["emp-ag2pc"][0]}'
 with tarfile.open(BASE/'emp-ag2pc-modern.tar.gz') as t:
  prefix=t.getnames()[0]
  for name in ('backend/triple_pool.h','backend/protocol.h'):
   original_ag=t.extractfile(prefix+'/emp-ag2pc/'+name).read().decode()
   patched=original_ag
   for symbol in ('joinNclean','bit0_mask','bit1_mask'):
    patched=re.sub(r'(?<![\w:])'+symbol+r'\b','::'+symbol,patched)
   path=ag/'emp-ag2pc'/name
   if path.read_text()!=patched:path.write_text(patched)
   compatibility[name]={'original_sha256':hashlib.sha256(original_ag.encode()).hexdigest(),
                        'overlay_sha256':hashlib.sha256(patched.encode()).hexdigest()}
 install=BASE/'modern-install'
 for name,tests in [('emp-tool','EMP_TOOL_BUILD_TESTS'),('emp-ot','EMP_OT_BUILD_TESTS')]:
  build=BASE/f'build-modern-{name.removeprefix("emp-")}'
  run(['cmake','-S',BASE/f'{name}-{PINS[name][0]}','-B',build,f'-DCMAKE_INSTALL_PREFIX={install}',f'-DCMAKE_PREFIX_PATH={install}',
       '-DOPENSSL_ROOT_DIR=/opt/homebrew/opt/openssl@3.5',f'-D{tests}=OFF','-DEMP_TOOL_BUILD_TOOLS=OFF'])
  run(['cmake','--build',build,'--target',name,'-j','2']);run(['cmake','--install',build])
 build=BASE/'build-modern-worker'
 run(['cmake','-S',ROOT/'benchmarks/TwoPartyComparisonWork','-B',build,f'-DCMAKE_PREFIX_PATH={install}',
      f'-DEMP_AG2PC_SOURCE={BASE}/emp-ag2pc-{PINS["emp-ag2pc"][0]}','-DOPENSSL_ROOT_DIR=/opt/homebrew/opt/openssl@3.5','-DCMAKE_BUILD_TYPE=Release'])
 run(['cmake','--build',build,'--target','modern-worker','-j','2'])
 receipt={'unaudited_rewrite_warning':True,'pins':PINS,
          'archive_sha256':{n:hashlib.sha256((BASE/(n+'-modern.tar.gz')).read_bytes()).hexdigest() for n in PINS},
          'counter_original_sha256':hashlib.sha256(original.encode()).hexdigest(),'counter_overlay_sha256':hashlib.sha256(source.encode()).hexdigest(),
          'compatibility_namespace_qualification':compatibility,
          'worker_sha256':hashlib.sha256((build/'modern-worker').read_bytes()).hexdigest(),
          'worker_source_sha256':hashlib.sha256((ROOT/'benchmarks/TwoPartyComparisonWork/modern_worker.cpp').read_bytes()).hexdigest(),
          'ssp':40,'tiny_nonzero_chunks_below1024':'rejected by adapter before protocol execution',
          'worker_build_type':'Release','context_checks_enabled':True,
          'security_validation':'pending native replay and adversarial controls; no production promotion'}
 (BASE/'modern-build.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
