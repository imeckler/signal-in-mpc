#!/usr/bin/env python3
"""PUBLIC first/second actual SPQR traces, no mutation/selected phase override."""
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateInitialSpqrV1Proofs'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
 spqr=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-bootstrap-spqr-oracle';kem=ROOT/'.deps/signal-libcrux-mlkem-oracle-target/debug/signal-libcrux-mlkem-oracle'
 rows=[]
 for case in range(8):
  auth=hashlib.sha256(b'actual-initial-SPQR-auth'+bytes([case])).digest();seed=hashlib.sha512(b'actual-initial-SPQR-seed'+bytes([case])).digest()
  if case==0:auth=bytes(32);seed=bytes(64)
  if case==1:auth=bytes(range(32));seed=bytes(range(64))
  if case==2:auth=bytes([255])*32;seed=bytes([255])*64
  result=subprocess.run([str(kem)],input='mlkem768|'+seed.hex()+'|'+bytes(32).hex()+'\n',capture_output=True,text=True,check=True)
  sk,pk,*_=map(bytes.fromhex,result.stdout.strip().split('|'));assert len(sk)==2400 and len(pk)==1184
  oracle=subprocess.run([str(spqr)],input=json.dumps(dict(auth=auth.hex(),seed=seed.hex()))+'\n',capture_output=True,text=True,check=True)
  expected=json.loads(oracle.stdout);assert expected['first_entropy_bytes']==64 and expected['second_entropy_bytes']==0 and not expected['phase_override']
  first=expected['first_state'];assert bytes.fromhex(first['dk'])==sk and bytes.fromhex(first['ek'])==pk[:1152]
  header=pk[1152:]+hashlib.sha3_256(pk).digest()
  assert bytes.fromhex(expected['first_message'])[-32:]==header[:32]and bytes.fromhex(expected['second_message'])[-32:]==header[32:]
  lean=subprocess.run(['lake','env','lean','--run',str(HERE/'SpqrChecks.lean'),auth.hex(),(b'\xff'+sk+pk).hex()],cwd=ROOT,capture_output=True,text=True,check=True,timeout=120)
  actual=json.loads(lean.stdout);assert actual['rejected_reuse_preserves_state']
  for call in ['first','second']:
   for key in ['state','message','key']:
    wanted=expected[call+'_state']['wire']if key=='state'else expected[call+'_'+key]
    assert bytes(actual[call+'_'+key])==bytes.fromhex(wanted),(case,call,key)
  rows.append(dict(case=case,auth=auth.hex(),seed=seed.hex(),first_state_sha256=hashlib.sha256(bytes(actual['first_state'])).hexdigest(),second_state_sha256=hashlib.sha256(bytes(actual['second_state'])).hexdigest(),full_serialized_states_match=True,first_and_second_wire_keys_match=True,retained_state_reuse_rejected=True))
  print('actual initial SPQR case',case,'passed',flush=True)
 audit=subprocess.run(['lake','env','lean',str(HERE/'SpqrAudit.lean')],cwd=ROOT,capture_output=True,text=True,check=True)
 assert not any(x in audit.stdout for x in ['sorryAx','native_decide','Lean.ofReduceBool']);(HERE/'spqr-axioms.txt').write_text(audit.stdout)
 sources=[pathlib.Path(__file__),HERE/'SpqrChecks.lean',HERE/'SpqrAudit.lean',ROOT/'TlsMpc/Signal/PrivateInitialSpqrV1.lean',ROOT/'TlsMpc/Signal/PrivateInitialSpqrV1Proofs.lean',ROOT/'signal_backend/Oracle/src/bin/signal-bootstrap-spqr-oracle.rs',ROOT/'signal_backend/Oracle/Cargo.lock']
 for relative in ['src/lib.rs','src/v1/chunked/states.rs','src/v1/chunked/send_ek.rs','src/v1/unchunked/send_ek.rs','src/chain.rs','src/authenticator.rs','src/incremental_mlkem768.rs','src/encoding/polynomial.rs','src/proto/pq_ratchet.proto']:sources.append(ROOT/'.deps/libsignal-vendor/spqr'/relative)
 sources +=[ROOT/'.deps/libsignal-vendor/libcrux-ml-kem-0.0.10/src/ind_cca/incremental.rs',ROOT/'.deps/libsignal-vendor/libcrux-ml-kem-0.0.10/src/ind_cca/incremental/types.rs']
 report=dict(passed=True,public_numeric_cases=rows,foundation_endpoints=14,full_state_bytes=3926,typed_state_bytes=3841,first_second_entropy_bytes=[64,0],phase_override=False,native_MPC=False,whole_bootstrap=False,actual_source_refinement=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources},oracle_sha256={str(p.relative_to(ROOT)):sha(p)for p in [spqr,kem]})
 (HERE/'spqr-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
