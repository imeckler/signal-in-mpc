"""Build pinned legacy EMP locally; explicit fail-closed diagnostic overlay."""
import hashlib
import json
import pathlib
import shutil
import subprocess
import tarfile
import urllib.request

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
PINS={
 'emp-tool':('11093a7d2160e7e7a4dcae3ffd9e6935bf2b8c1c','efa46fccf39643461078b88b82d797e7ce9f1b9357010611045b1afd0254a277'),
 'emp-ot':('52b32c8371c09c1567e3d650c0f0adfbb229a270','a625ad596ec2bc3b6ba989a632407823a90b2efc2c527e64b315f89d71aac6ce'),
 'emp-ag2pc':('356cfd824772af9334ac9a994d1eec17ab5f565a','2e6073489eab9a318d63ed1e2c4b7d96b843d3a82fade5413a7be4fe79a9e9b6')}

def run(args, log):
 with open(BASE/log,'a') as f:subprocess.run(list(map(str,args)),stdout=f,stderr=subprocess.STDOUT,check=True)

def prepare():
 BASE.mkdir(parents=True,exist_ok=True)
 for repo,(commit,digest) in PINS.items():
  archive=BASE/f'{repo}.tar.gz'
  if not archive.exists():
   urllib.request.urlretrieve(f'https://codeload.github.com/emp-toolkit/{repo}/tar.gz/{commit}',archive)
  if hashlib.sha256(archive.read_bytes()).hexdigest()!=digest:raise ValueError('archive identity mismatch')
  source=BASE/f'{repo}-{commit}'
  if not source.exists():
   with tarfile.open(archive) as t:t.extractall(BASE,filter='data')
 prefix=BASE/'install'
 for repo in ('emp-tool','emp-ot'):
  source=BASE/f'{repo}-{PINS[repo][0]}'
  build=BASE/f'build-{repo.removeprefix("emp-")}'
  run(['cmake','-S',source,'-B',build,f'-DCMAKE_INSTALL_PREFIX={prefix}',f'-DCMAKE_PREFIX_PATH={prefix}',
       '-DOPENSSL_ROOT_DIR=/opt/homebrew/opt/openssl@3.5','-DCRYPTO_IN_CIRCUIT=OFF'],f'{repo}-build.log')
  if repo=='emp-tool':run(['cmake','--build',build,'--target','emp-tool','-j','2'],f'{repo}-build.log')
  run(['cmake','--install',build],f'{repo}-build.log')
 original=BASE/f'emp-ag2pc-{PINS["emp-ag2pc"][0]}'
 overlay=BASE/'emp-ag2pc-failclosed'
 overlay.mkdir(exist_ok=True)
 shutil.copytree(original/'emp-ag2pc',overlay/'emp-ag2pc',dirs_exist_ok=True)
 path=overlay/'emp-ag2pc/2pc.h'
 source=path.read_text()
 replacements={
  'cout <<"no match! ALICE\\t"<<i<<endl;':'throw std::runtime_error("authentication-label-reject");',
  'cout <<"no match! BOB\\t"<<i<<endl;':'throw std::runtime_error("authentication-label-reject");',
  'cout <<ands <<" no match GT!"<<endl;':'throw std::runtime_error("authentication-label-reject");',
  'cout <<"no match output label!"<<endl;':'throw std::runtime_error("authentication-label-reject");',
  'cout <<"no match output label2!"<<endl;':'throw std::runtime_error("authentication-label-reject");'}
 count=0
 for old,new in replacements.items():
  if old not in source:raise ValueError('overlay source drift')
  count+=source.count(old)
  source=source.replace(old,new)
 if count!=6:raise ValueError('overlay count mismatch')
 # SSP sends5bytes but upstream comparison mask retained only20bits.
 # Retain all40 transmitted bits; this is a labeled local parameter correction,
 # not a claim of a complete end-to-end security audit.
 old='const block MASK = makeBlock(0x0ULL, 0xFFFFFULL);'
 if source.count(old)!=1:raise ValueError('mask source drift')
 source=source.replace(old,'const block MASK = makeBlock(0x0ULL, 0xFFFFFFFFFFULL);')
 path.write_text(source)
 run(['clang++','-std=c++17','-O3','-march=armv8-a+simd+crypto+crc','-I',prefix/'include','-I',overlay,
      '-I','/opt/homebrew/opt/openssl@3.5/include',ROOT/'benchmarks/TwoPartyComparisonWork/emp_worker.cpp',
      '-L',prefix/'lib','-lemp-tool','-L','/opt/homebrew/opt/openssl@3.5/lib','-lcrypto','-o',BASE/'emp-worker'], 'emp-worker-build.log')
 receipt={'pins':PINS,'overlay_replaced_branches':count,'comparison_mask_bits':40,'transmitted_check_bits':40,
          'original_2pc_sha256':hashlib.sha256((original/'emp-ag2pc/2pc.h').read_bytes()).hexdigest(),
          'overlay_2pc_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
          'worker_sha256':hashlib.sha256((BASE/'emp-worker').read_bytes()).hexdigest(),
          'worker_source_sha256':hashlib.sha256((ROOT/'benchmarks/TwoPartyComparisonWork/emp_worker.cpp').read_bytes()).hexdigest()}
 (BASE/'emp-build.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt))

if __name__=='__main__':prepare()
