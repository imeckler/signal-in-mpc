#!/usr/bin/env python3
"""Two selected-chain state sends crossing127→128 through actual SS/relay.
Public fixture evaluation only; native private DH/runtime are separate tests.
"""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
from scripts.check_lean_signal_spqr_send import cases,spqr_derive,varint
from scripts.check_lean_signal_chain_send import derive
from SignalReference.RelayServiceWork.check import metadata,oracle
HERE=Path(__file__).resolve().parent;ART=ROOT/'.deps/private-hash-artifacts'
def native_inner(i):
 co=int.from_bytes(i[1:5],'big');pc=int.from_bytes(i[105:109],'big');epoch=int.from_bytes(i[109:117],'big')
 next_pq,pq_key=spqr_derive(i[73:105],pc);next_chain,cipher,mac,iv=derive(i[41:73],pq_key)
 pq=b'\x01'+varint(epoch)+varint(pc+1)+i[117:118]
 row=dict(plain='',cipher_key=cipher.hex(),iv=iv.hex(),mac_key=mac.hex(),sender=i[118:150].hex(),receiver=i[150:182].hex(),ratchet=i[9:41].hex(),addresses='',pq=pq.hex(),version=i[0],counter=co,previous=int.from_bytes(i[5:9],'big'))
 wire=bytes.fromhex(oracle([row])[0]['wire'])
 state=next_chain+(co+1).to_bytes(4,'big')+next_pq+(pc+1).to_bytes(4,'big')
 return wire,state

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--reuse-artifact',action='store_true');args=parser.parse_args()
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateService'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit;(HERE/'axioms.txt').write_text(audit)
 path=ART/'private-service-260-0-none-none.json'
 if not args.reuse_artifact:
  with path.open('w') as stream:subprocess.run(['lake','env','lean','--run',str(HERE/'Export.lean'),'260','0','none','none'],cwd=ROOT,stdout=stream,check=True)
 fixture=oracle([dict(mode='sealed',seed=0,inner='')])[0];f=bytes.fromhex(fixture['input']);assert fixture['certificate_size']==260
 # Layout: four public-fixture curve results || certificate || selected SPQR state || request metadata.
 prefix=f[32:160]+f[160:420]
 initial=bytearray(next(cases())[1][0]);assert len(initial)==182
 initial[1:5]=(127).to_bytes(4,'big');initial[5:9]=(127).to_bytes(4,'big');initial[105:109]=(126).to_bytes(4,'big');initial[109:117]=(127).to_bytes(8,'big')
 initial[118:150]=f[64:96];initial[150:182]=f[:32]
 image=load(path);nodes=len(image['nodes']);i=bytes(initial);steps=[];first_input=None
 for step in range(2):
  inner,expected_state=native_inner(i)
  expected_sealed=oracle([dict(mode='sealed',seed=0,inner=inner.hex())])[0]
  request_meta=metadata(step,127+step)
  raw=prefix+i+request_meta
  if first_input is None:first_input=raw
  observed=evaluate_lanes(image,[raw])[0];assert observed[0]==255
  assert observed[1:73]==expected_state
  length=int.from_bytes(observed[73:75],'big');wire=observed[75:75+length]
  assert observed[75+length:]==bytes(len(observed)-75-length)
  decoded=oracle([dict(mode='relay',wire=wire.hex())])[0]
  assert decoded['id']==127+step and decoded['ciphertext']==expected_sealed['wire']
  assert decoded['access_key']==request_meta[16:32].hex()
  decrypted=oracle([dict(mode='sealed_decrypt',wire=decoded['ciphertext'],recipient_secret=fixture['recipient_secret'],root_public=fixture['root_public'])])[0]
  assert decrypted==dict(inner=inner.hex(),certificate_valid=True)
  steps.append({'signal_counter':int.from_bytes(i[1:5],'big'),'pq_counter_before':int.from_bytes(i[105:109],'big'),'inner_bytes':len(inner),'sealed_bytes':len(bytes.fromhex(decoded['ciphertext'])),'websocket_bytes':length})
  # Feed the actual first circuit result into the next selected-chain input.
  mutable=bytearray(i);mutable[41:73]=observed[1:33];mutable[1:5]=observed[33:37];mutable[73:105]=observed[37:69];mutable[105:109]=observed[69:73];i=bytes(mutable)
  print(f'step{step}: private Signal/PQ counters, actual SS decrypt and relay schema passed',flush=True)
 bad=[]
 for kind in ['sender-binding','zero-dh','exhausted-counter','zero-epoch']:
  b=bytearray(first_input)
  if kind=='sender-binding':b[32]^=1
  if kind=='zero-dh':b[64:96]=bytes(32)
  if kind=='exhausted-counter':b[388+1:388+5]=b'\xff'*4
  if kind=='zero-epoch':b[388+109:388+117]=bytes(8)
  bad.append(bytes(b))
 for raw,observed in zip(bad,evaluate_lanes(image,bad)):
  state=raw[388+41:388+73]+raw[388+1:388+5]+raw[388+73:388+105]+raw[388+105:388+109]
  assert observed[0]==0 and observed[1:73]==state and observed[73:]==bytes(len(observed)-73)
 files=[Path(__file__),HERE/'Export.lean',HERE/'Checks.lean']+[ROOT/f'TlsMpc/Signal/{x}.lean' for x in ['PrivateService','PrivateSpqrSend','PrivateSignalMessage','PrivateRelay','PrivateSealedSender','PrivateHash','PrivateBuffer','PrivateVarint','PrivateBase64','PrivateDecimal','PrivateProtobuf']]
 report={'steps':steps,'actual_output_state_reused':True,'final_status_selects_both_old_chains_on_reject':True,'rejection_cases':4,
  'numeric_aig_nodes':nodes,'output_capacity':len(observed)-75,'artifact_bytes':path.stat().st_size,'artifact_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
  'standard_axioms_only':True,'compiler_agreement_established':True,'integer_semantic_refinements_proved':False,
  'test_supplied_native_dh':True,'test_reuses_synthetic_ephemeral':True,'native_mpc_executed':False,'tls_integrated':False,
  'active_epoch_selection_and_kem_state_implemented':False,'recoverable_shared_state':False,'production_ready':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Two variable-length selected-chain service sends and4 fail-closed rejections passed',flush=True)
if __name__=='__main__':main()
