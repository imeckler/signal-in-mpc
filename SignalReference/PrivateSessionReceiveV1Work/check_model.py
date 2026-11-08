#!/usr/bin/env python3
"""PUBLIC model preflight, one new ratchet then retained in-order messages."""
import hashlib,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];sys.path.insert(0,str(ROOT))
from SignalReference.PrivateNewDhReceiveWork.check_model import invoke,TEXT
BIN=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-session-inorder-oracle'
def main():
 text=invoke(TEXT,[dict(mode='text',body='Known ratchet notification ☕'.encode().hex(),timestamp=1900000000000)])[0]
 fixture=invoke(BIN,[dict(seed=19,plaintext=text['padded'])])[0];actual=fixture['rows'];assert len(actual)==4 and fixture['actual_replay_and_MAC_failures_preserved_store']
 rows=[];expected=[];positives=[]
 for f in actual:
  raw=bytes.fromhex(f['input']);want=bytes.fromhex(f['expected']);assert len(raw)==976 and len(want)==608
  if f['counter']>0:assert raw[:136]==want[1:137] and raw[589:717]==bytes(128) and f['root_private_preserved']
  positives.append(raw);rows.append(raw);expected.append(want)
  for kind in ['MAC','upstream','PQepoch','PQexhaustion']:
   bad=bytearray(raw);n=int.from_bytes(bad[718:720],'big')
   if kind=='MAC':bad[720+n-1]^=1
   if kind=='upstream':bad[717]=0
   if kind=='PQepoch':bad[488]^=1
   if kind=='PQexhaustion':bad[521:525]=bytes([255])*4
   rows.append(bytes(bad));expected.append(b'\0'+bad[:525]+bytes(82))
 # Valid actual old/future ciphertexts still reject in this IN-ORDER-only profile;
 # full skipped-key/OOO SPQR state support is explicitly still missing.
 for state_index,wire_index in [(2,1),(1,3)]:
  bad=positives[state_index][:717]+positives[wire_index][717:]
  rows.append(bad);expected.append(b'\0'+bad[:525]+bytes(82))
 result=subprocess.run(['lake','env','lean','--run',str(HERE/'Evaluate.lean')],cwd=ROOT,input=''.join(json.dumps(list(r))+'\n'for r in rows),text=True,capture_output=True,check=True,timeout=180)
 outputs=[bytes(x)for x in map(json.loads,result.stdout.splitlines())];assert len(outputs)==len(expected)
 for i,(got,want)in enumerate(zip(outputs,expected)):assert got==want,(i,got[0],want[0])
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[Path(__file__),HERE/'Evaluate.lean',ROOT/'TlsMpc/Signal/PrivateSessionReceiveV1.lean',ROOT/'signal_backend/Oracle/src/bin/signal-session-inorder-oracle.rs']
 report=dict(model_only=True,actual_new_DH_transitions=1,actual_known_ratchet_inorder_transitions=3,known_branch_root_private_all_sender136bytes_preserved=True,known_branch_supplied_pair_and_DH_all_zero_unused=True,whole_projected_output_bytes=608,computed_rejections=len(rows)-4,actual_Rust_MAC_and_replay_failures_preserved_store=True,valid_future_outoforder_rejected_by_declared_inorder_profile=True,skipped_key_policy='No skipped keys retained; replay/future message fails closed. Full libsignal outoforder behavior not implemented.',PQQ_counter_exhaustion_rejected=True,full_fresh_session_or_SPQR_KEM=False,recoverable_persistence=False,full_actual_source_refinement=False,native_MPC_executed=False,oracle_sha256=sha(BIN),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'model-report.json').write_text(json.dumps(report,indent=2)+'\n');print('1 actual new+3 known in-order transitions, all608 bytes;18 rejection selections passed')
if __name__=='__main__':main()
