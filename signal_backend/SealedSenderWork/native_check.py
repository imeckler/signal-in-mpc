#!/usr/bin/env python3
"""Five-party public fixture: computed private DH -> SSv1 -> actual relay wire."""
import hashlib,json,shutil,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from signal_backend.SealedSenderWork.shape import ServiceShape
from SignalReference.RelayServiceWork.check import metadata,oracle
from scripts.pin_tls_worker import build
HERE=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 shape=ServiceShape(260,72,1,5,13,1);stage=ROOT/'.deps/private-sealed-relay-native/260-72-1-5-13-1'
 manifest=stage/'service.manifest';assert manifest.read_text()==build(stage,[shape.descriptor])
 runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';binary=ROOT/'.deps/private-service-fixture'
 subprocess.run(['make','-C',str(runtime),'-f',str(HERE/'Makefile'),'SIGNAL_WORK='+str(HERE),
  'SIGNAL_OUTPUT='+str(binary),str(binary)],check=True)
 fixture=json.loads((ROOT/'SignalReference/RelayServiceWork/fixtures.json').read_text())['sealed'][0]
 raw=bytes.fromhex(fixture['input']);initial=bytes.fromhex(fixture['sender_secret'])+raw[64:96]+raw[:32]+raw[160:]+metadata()
 assert len(initial)==shape.input_bytes
 bad_point=initial[:64]+bytes(32)+initial[96:]
 bad_binding=initial[:32]+bytes([initial[32]^1])+initial[33:]
 data=stage/'Player-Data';data.mkdir(exist_ok=True)
 for pattern in ['*.pem','*.key','*.0']:
  for p in (runtime/'Player-Data').glob(pattern):shutil.copy2(p,data/p.name)
 logs=stage/'fixture-logs';logs.mkdir(exist_ok=True)
 hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5)
 inputs=logs/'public-fixtures.txt';inputs.write_text(''.join(x.hex()+'\n' for x in [initial,bad_point,bad_binding]))
 sources=[HERE/'native_fixture.cpp',HERE/'NativeService.h',HERE/'ServiceShape.h',HERE/'Shape.h',
  Path(__file__),ROOT/'programs/signal_sealed_export.mpc',ROOT/'handshake_backend/mixed.py',
  ROOT/'handshake_backend/field_dag.py',ROOT/'handshake_backend/NativeWorker.h']
 before={str(p.relative_to(ROOT)):sha(p) for p in sources}
 procs=[];streams=[];start=time.monotonic()
 try:
  for party in range(5):
   stream=(logs/f'party-{party}.log').open('w');streams.append(stream)
   procs.append(subprocess.Popen([str(binary),str(party),str(hosts),'19840',str(manifest),str(inputs)],
    cwd=stage,stdout=stream,stderr=subprocess.STDOUT))
  deadline=time.monotonic()+1800
  while any(p.poll() is None for p in procs):
   if time.monotonic()>deadline:raise TimeoutError('private service fixture timeout')
   if any(p.poll() not in [None,0] for p in procs):raise RuntimeError('private service party failed; inspect fixture logs')
   time.sleep(.1)
  assert all(p.returncode==0 for p in procs)
 finally:
  for p in procs:
   if p.poll() is None:p.kill()
  for p in procs:p.wait()
  for stream in streams:stream.close()
 frames=[]
 for party in range(5):
  text=(logs/f'party-{party}.log').read_text();assert 'REJECT 1' in text and 'REJECT 2' in text
  frames.append(next(line[6:] for line in text.splitlines() if line.startswith('FRAME ')))
 assert len(set(frames))==1
 decoded=oracle([{'mode':'relay','wire':frames[0]}])[0]
 assert decoded['path']=='/v1/messages/ffeeddcc-bbaa-9988-7766-554433221100?story=false'
 assert decoded['id']==0 and decoded['body']['messages'][0]['type']==6
 decrypted=oracle([{'mode':'sealed_decrypt','wire':decoded['ciphertext'],
  'recipient_secret':fixture['recipient_secret'],'root_public':fixture['root_public']}])[0]
 assert decrypted=={'inner':raw[160+260:].hex(),'certificate_valid':True}
 corrupted=bytearray.fromhex(decoded['ciphertext']);corrupted[-1]^=1
 rejected=oracle([{'mode':'sealed_decrypt','wire':corrupted.hex(),
  'recipient_secret':fixture['recipient_secret'],'root_public':fixture['root_public']}])[0]
 assert 'error' in rejected
 assert before=={str(p.relative_to(ROOT)):sha(p) for p in sources},'native sources changed during test'
 report={'passed':True,'public_fixtures_only':True,'parties':5,'threshold':2,
  'native_computed_dh_executed':True,'native_fresh_ephemeral_generation_executed':True,
  'raw_dh_or_ephemeral_scalar_inputs':False,'actual_target_decrypt_and_tamper_verified':True,
  'low_order_and_sender_identity_binding_rejected':True,'service_request_schema_and_json_verified':True,
  'elapsed_seconds':time.monotonic()-start,'timing_scope':'Local startup plus three component invocations, not persistent delivery throughput.',
  'manifest_sha256':sha(manifest),'fixture_binary_sha256':sha(binary),'source_sha256':before,
  'logs':str(logs.relative_to(ROOT)),'opened_outputs':'Synthetic final frame/status only; no computed DH or ephemeral secret opened.',
  'backend_conversion_trust_boundary':'Existing unverified checked daBit conversions and mixed runtime; cryptographic/service algorithms use proved Lean artifacts.',
  'full_actual_rust_aeneas_refinement':False,'tls_integrated':False,'http101_response_parser':False,
  'private_counter_width_policy':False,'recoverable_shared_store':False,'production_ready':False}
 (HERE/'native-report.json').write_text(json.dumps(report,indent=2)+'\n')
 print('Five-party computed-DH sealed relay fixture passed; actual native decrypt, tamper and binding checks',flush=True)
if __name__=='__main__':main()
