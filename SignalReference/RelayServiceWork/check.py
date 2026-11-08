#!/usr/bin/env python3
"""Actual target SSv1/native-schema local differential checks; no service traffic."""
import hashlib,json,re,subprocess,sys,uuid
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
from scripts.check_lean_signal_spqr_send import cases
HERE=Path(__file__).resolve().parent
ART=ROOT/'.deps/relay-service-artifacts'
ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def oracle(rows):
 p=subprocess.run([str(ORACLE)],input=''.join(json.dumps(r)+'\n' for r in rows),text=True,capture_output=True,check=True)
 return [json.loads(s) for s in p.stdout.splitlines()]
def metadata(seed=0,request_id=0):
 return uuid.UUID('ffeeddcc-bbaa-9988-7766-554433221100').bytes+hashlib.sha256(f'uak-{seed}'.encode()).digest()[:16]+(1900000000000+seed).to_bytes(8,'big')+request_id.to_bytes(8,'big')+b'\1'+(16383).to_bytes(4,'big')+bytes([17,29,53,71])
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.SealedRelay'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S):
  assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit
 (HERE/'axioms.txt').write_text(audit)
 _,raw,expected,labels,_=next(cases());inner=expected[0][73:]
 fixtures=oracle([{'mode':'sealed','seed':seed,'inner':inner.hex()} for seed in range(3)])
 assert all(f['fixture_certificate_validated'] and f['actual_decrypt_to_usmc_roundtrip'] and f['actual_tampered_envelope_rejected'] for f in fixtures)
 assert all((f['certificate_size'],f['inner_size'])==(260,72) for f in fixtures)
 # These Boolean tests intentionally supply native-generated DH fixtures. The
 # separately compiled mixed function computes all DH/key inputs privately.
 inputs=[]
 for i,f in enumerate(fixtures):
  raw=bytes.fromhex(f['input']);inputs.append(raw+raw[64:96]+metadata(i))
 invalid=[]
 for offset in [96,128]:
  bad=bytearray(inputs[0]);bad[offset:offset+32]=bytes(32);invalid.append(bytes(bad))
 bad=bytearray(inputs[0]);bad[160+260+72]^=1;invalid.append(bytes(bad))
 image=load(ART/'service-260-72-1-5-13-1.json')
 observed=evaluate_lanes(image,inputs+invalid);del image
 assert all(out[0]==255 for out in observed[:3])
 assert all(out==bytes(len(observed[0])) for out in observed[3:])
 decoded=oracle([{'mode':'relay','wire':out[1:].hex()} for out in observed[:3]])
 for i,(f,d) in enumerate(zip(fixtures,decoded)):
  assert d['path']=='/v1/messages/ffeeddcc-bbaa-9988-7766-554433221100?story=false'
  assert d['id']==0 and d['access_key']==metadata(i)[16:32].hex()
  assert d['ciphertext']==f['wire']
  assert d['body']=={'messages':[{'content':__import__('base64').b64encode(bytes.fromhex(f['wire'])).decode(),
    'destinationDeviceId':1,'destinationRegistrationId':16383,'type':6}],
    'online':False,'urgent':True,'timestamp':1900000000000+i}
 # Explicit width regression: width1 accepts id127 and rejects128. Width2
 # accepts128 and rejects127; this is NOT yet a private variable-width producer.
 boundary=[]
 for ident in [127,128]:
  meta=metadata(0,ident);boundary.append(meta[:53]+bytes.fromhex(fixtures[0]['wire'])+meta[53:])
 im=load(ART/'request-433-1-5-13-1.json');one=evaluate_lanes(im,boundary);del im
 assert one[0][0]==255 and one[1]==bytes(len(one[1]))
 second=ART/'request-433-1-5-13-2.json'
 if not second.exists():
  with second.open('w') as out:subprocess.run(['lake','env','lean','--run',str(HERE/'RequestExport.lean'),'433','1','5','13','2'],cwd=ROOT,stdout=out,check=True)
 im=load(second);two=evaluate_lanes(im,boundary);del im
 assert two[0]==bytes(len(two[0])) and two[1][0]==255
 assert oracle([{'mode':'relay','wire':two[1][1:].hex()}])[0]['id']==128
 (HERE/'fixtures.json').write_text(json.dumps({'sealed':fixtures,'service_input':[x.hex() for x in inputs],
  'service_output':[x.hex() for x in observed[:3]]},indent=2)+'\n')
 files=[HERE/'Checks.lean',Path(__file__),HERE/'SealedExport.lean',HERE/'BoundExport.lean',HERE/'RequestExport.lean',HERE/'ServiceExport.lean',HERE/'UpgradeExport.lean',
  ROOT/'TlsMpc/Signal/RelayEncoding.lean',ROOT/'TlsMpc/Signal/RelayUpgrade.lean',ROOT/'TlsMpc/Signal/RelayRequest.lean',ROOT/'TlsMpc/Signal/SealedSenderV1.lean',ROOT/'TlsMpc/Signal/SealedRelay.lean',
  ROOT/'signal_backend/Oracle/src/main.rs',ROOT/'signal_backend/Oracle/src/sealed.rs',ROOT/'signal_backend/Oracle/src/relay.rs',
  ROOT/'signal_backend/Oracle/Cargo.lock',ROOT/'signal_backend/Oracle/Cargo.toml',ROOT/'signal_backend/Oracle/build.rs']
 report={'candidate_only':True,'target':'signalapp/libsignal 904c8dc8216073b078a5f2f5090e3da8382e6a92 v0.106.1',
  'kernel_endpoints':10,'standard_axioms_only':True,'actual_ssv1_encrypt_decrypt_tamper_cases':3,
  'composed_service_success_cases':3,'zero_dh_or_sender_binding_rejections':3,'request_id_width_boundary_cases':4,
  'actual_schema_decoder_used':True,'boolean_tests_supply_native_generated_dh':True,'native_computed_dh_executed':False,
  'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'oracle_sha256':sha(ORACLE),
  'artifact_sha256':{p.name:sha(p) for p in [ART/'service-260-72-1-5-13-1.json',ART/'request-433-1-5-13-1.json',second]},
  'actual_rust_aeneas_sealed_sender_refinement':False,'private_variable_width_producer':False,
  'full_response_parser':False,'http101_upgrade':False,'recoverable_shared_store':False,
  'historical_relay_inner_session_compatibility_verified':False,'production_ready':False,'network_or_account_side_effects':False}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 print('10 kernel endpoints;3 actual SSv1 encrypt/decrypt/tamper cases;3 private service matches;3 rejections;4 id-width boundaries',flush=True)
if __name__=='__main__':main()
