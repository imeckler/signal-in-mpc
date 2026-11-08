#!/usr/bin/env python3
"""PUBLIC model checkpoint, NOT a numeric/native/full-source refinement receipt."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BIN=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-new-dh-receive-oracle'
TEXT=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-text-recipient-oracle'
def invoke(path,rows):
 p=subprocess.run([str(path)],input=''.join(json.dumps(x)+'\n'for x in rows),text=True,capture_output=True,check=True);return list(map(json.loads,p.stdout.splitlines()))
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateNewDhReceive'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==1
 for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 requests=[]
 for seed,body in enumerate(['New DH notification ☕','Second root rotation fixture']):
  text=invoke(TEXT,[dict(mode='text',body=body.encode().hex(),timestamp=1900000000000+seed)])[0]
  requests.append(dict(seed=seed,plaintext=text['padded']))
 fixtures=invoke(BIN,requests);assert len(fixtures)==2
 rows=[];expected=[]
 for f in fixtures:
  raw=bytes.fromhex(f['input']);want=bytes.fromhex(f['expected']);assert len(raw)==976 and len(want)==608
  assert f['actual_new_DH_message_decrypt']and f['tampered_MAC_preserved_actual_store']
  rows.append(raw);expected.append(want)
  for kind in ['MAC','private-truncation','upstream-invalid','zero-receiving-DH','zero-sending-DH','wrong-PQ-epoch']:
   bad=bytearray(raw)
   if kind=='MAC':bad[720+f['wire_bytes']-1]^=1
   if kind=='private-truncation':bad[718:720]=(f['wire_bytes']-1).to_bytes(2,'big')
   if kind=='upstream-invalid':bad[717]=1
   if kind=='zero-receiving-DH':bad[653:685]=bytes(32)
   if kind=='zero-sending-DH':bad[685:717]=bytes(32)
   if kind=='wrong-PQ-epoch':bad[488]^=1
   rows.append(bytes(bad));expected.append(b'\0'+bytes(bad[:525])+bytes(82))
 result=subprocess.run(['lake','env','lean','--run',str(HERE/'Evaluate.lean')],cwd=ROOT,input=''.join(json.dumps(list(r))+'\n'for r in rows),text=True,capture_output=True,check=True,timeout=180)
 outputs=[bytes(x)for x in map(json.loads,result.stdout.splitlines())];assert len(outputs)==len(expected)
 for index,(got,want)in enumerate(zip(outputs,expected)):assert got==want,(index,got[0],want[0],len(got))
 files=[Path(__file__),HERE/'Checks.lean',HERE/'Evaluate.lean',ROOT/'TlsMpc/Signal/PrivateNewDhReceive.lean',ROOT/'signal_backend/Oracle/src/bin/signal-new-dh-receive-oracle.rs']
 report=dict(candidate=True,model_only=True,typechecks=True,selector_rejection_kernel_endpoints=1,foundation_axioms_only=True,
  actual_libsignal_new_DH_transition_matches=2,whole_output_bytes_checked=608,computed_rejection_state_preservation_cases=12,
  actual_PQXDH_initialized_DR_baseline=True,selected_established_SPQR_phase_override=True,full_fresh_session_prekey_bootstrap_implemented=False,
  actual_MAC_failure_preserved_Rust_store=True,all_authentication_PQ_CBC_masks_computed=True,
  test_supplies_actual_oracle_DH_results=True,native_DH_binding_executed=False,full_numeric_compiler_agreement_proved=False,
  actual_whole_source_refinement_proved=False,native_MPC_executed=False,recoverable_persistence=False,identity_store_callbacks_and_other_session_metadata_modeled=False,
  domain='New unknown DH ratchet, five retained receiving slots/no skipped keys, counter0,V4,noaddresses,ciphertext96,PKCS7plaintext80; selected V1kind0sameepoch exactnext PQ index, retainedcounter<2^31-1; actual wirecapacity256 with private length.',
  parser_dependency='04edbf6 versioned private parser Hom API; full take-n/source theorem remains pending under parser ownership.',
  next='Prove whole pipeline Hom/compiler, bind native computed pair/DHs to SAME actual parsed remote point, then actual private native receive/reply interoperability before provider/store admission.',
  oracle_sha256=hashlib.sha256(BIN.read_bytes()).hexdigest(),source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'model-report.json').write_text(json.dumps(report,indent=2)+'\n');print('2 actual new-DH transitions, all608 state/plaintext bytes;12 model rejections; selector kernel proof passed')
if __name__=='__main__':main()
