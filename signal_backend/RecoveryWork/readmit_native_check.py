#!/usr/bin/env python3
"""Tiny5party rawGF128 import candidate, NOT full recovery/provider admission."""
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
HERE=Path(__file__).resolve().parent
def main():
 stage=ROOT/'.deps/signal-raw-field-import-native';stage.mkdir(exist_ok=True);runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 for name,target in [('Compiler',runtime/'Compiler'),('handshake_backend',ROOT/'handshake_backend')]:
  path=stage/name
  if not path.exists():path.symlink_to(target,target_is_directory=True)
  else:assert path.resolve()==target.resolve()
 shutil.copy2(runtime/'compile.py',stage/'compile.py');source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
 shutil.copy2(ROOT/'programs/signal_recovery_fixture_equal.mpc',source/'signal_recovery_fixture_equal.mpc')
 subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_recovery_fixture_equal'],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),check=True,timeout=120)
 manifest=stage/'fixture.manifest';manifest.write_text(build(stage,['signal_recovery_fixture_equal_16-sbv:[32x1]-sbv:[8x1]']))
 binary=ROOT/'.deps/signal-raw-field-import-fixture'
 subprocess.run(['make','-C',str(runtime),'-f',str(HERE/'Makefile'),'RECOVERY_WORK='+str(HERE),'RECOVERY_IMPORT_FIXTURE='+str(binary),str(binary)],check=True)
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[Path(__file__),HERE/'RawFieldReadmit.h',HERE/'readmit_fixture.cpp',HERE/'Makefile',HERE/'OwnShareBox.h',HERE/'CiphertextStore.h',HERE/'NativeOwnShareArchive.h',ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/StrongShamirShare.h',ROOT/'programs/signal_recovery_fixture_equal.mpc']
 before={str(p.relative_to(ROOT)):sha(p)for p in files};binary_hash=sha(binary);library_hash=sha(runtime/'libSPDZ.so')
 logs=Path(tempfile.mkdtemp(prefix='probe-',dir=stage));archives=logs/'archives';subprocess.run([str(binary),'prepare',str(manifest),str(archives)],check=True)
 hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5);data=stage/'Player-Data';data.mkdir(exist_ok=True)
 for pattern in ['*.pem','*.key','*.0']:
  for p in(runtime/'Player-Data').glob(pattern):shutil.copy2(p,data/p.name)
 timings=[];cleanup=[]
 for case in range(4):
  processes=[];streams=[];start=time.monotonic()
  try:
   for party in range(5):
    stream=(logs/f'case-{case}-party-{party}.log').open('w');streams.append(stream)
    processes.append(subprocess.Popen([str(binary),str(party),str(hosts),str(20310+case*20),str(manifest),str(archives/str(case))],cwd=stage,stdout=stream,stderr=subprocess.STDOUT))
   deadline=start+180
   while any(p.poll()is None for p in processes):
    if time.monotonic()>deadline:raise TimeoutError('raw import case timeout '+str(logs))
    if any(p.poll()not in [None,0]for p in processes):raise RuntimeError('raw import party failed '+str(logs))
    time.sleep(.1)
   assert all(p.returncode==0 for p in processes)
  finally:
   for p in processes:
    if p.poll()is None:p.kill();cleanup.append(f'case{case}-party-killed')
   for p in processes:p.wait()
   for stream in streams:stream.close()
  timings.append(time.monotonic()-start)
  for party in range(5):
   text=(logs/f'case-{case}-party-{party}.log').read_text();assert ('fresh private CCD equality passed'if case==0 else'malformed private archive rejected')in text
  print(f'RawGF128 import case{case} all5 passed',flush=True)
 assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}and binary_hash==sha(binary)and library_hash==sha(runtime/'libSPDZ.so')
 pins=[runtime/'Protocols/ShamirInput.hpp',runtime/'Protocols/SemiInput.h',runtime/'Protocols/SemiInput.hpp',runtime/'Protocols/MaliciousRepPrep.hpp',runtime/'Protocols/MaliciousShamirMC.hpp',runtime/'Math/gf2n.cpp',runtime/'Tools/random.cpp']
 report=dict(passed=True,parties=5,threshold=2,batch_original_secret_bits=16,actual_encrypted_archive_prepare_process_exited_before_MPC=True,full128bit_evaluations_privately_Shared_as_raw_GF128=True,no_bit_only_input_mask_or_AIG_guard=True,raw_field_bitness_multiply=True,secret_RLC_masks_sampled_after_input_exchange=True,raw_evaluation_or_constant_term_or_bitness_product_opened=False,opened='One secret-randomly masked aggregate per batch, andone aggregate equality bit on valid case; no restored data bit/key.',valid_fresh_owned_CCD_use=True,rejections=['one changedlocal evaluation','two changedlocal contributions','consistentdegree2 polynomial with nonbit constant2'],statistical_check_false_accept_bound='2^-128 per batch under fresh uniform secret coefficient and correct underlying maliciousMPC/input/opening primitives; not a full MPC security proof.',disposable_public_polynomial_fixtures=True,full_Signal_schema_or_phase_coordinator=False,secure_Signal_provider_restore=False,constructor_failure_and_runtime_retirement_review_complete=False,normal_provider_admitted=False,elapsed_seconds_per_case=timings,timing_scope='Tinycorrectness probe, startup included; no throughput claim.',cleanup=cleanup,logs=str(logs.relative_to(ROOT)),manifest_sha256=sha(manifest),binary_sha256=binary_hash,runtime_library_sha256=library_hash,source_sha256=before,pinned_input_guard_source_sha256={str(p.relative_to(ROOT)):sha(p)for p in pins})
 (HERE/'readmit-native-report.json').write_text(json.dumps(report,indent=2)+'\n');print('RawGF128 private import4cases/20party exits passed',flush=True)
if __name__=='__main__':main()
