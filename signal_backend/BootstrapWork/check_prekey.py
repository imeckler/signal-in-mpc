#!/usr/bin/env python3
"""Private variable-width PreKey envelope vs actual pinned Rust constructor."""
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivatePreKeyMessageV1'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
 oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-bootstrap-peer-oracle'
 r=subprocess.run([str(oracle)],input=json.dumps(dict(mode='reference',seed=3027))+'\n',capture_output=True,text=True,check=True);reference=json.loads(r.stdout);rows=[]
 for index,word in enumerate([0,1,127,128,255,256,2**31-1,2**32-1]):
  message=reference['rows'][index%2]['wire'];values=[word,(word+127)%2**32,(word+128)%2**32,(word+1)%2**32]
  cmd=dict(mode='construct',wire=message,registration=values[0],one_time_id=values[1],signed_id=values[2],kyber_id=values[3])
  result=subprocess.run([str(oracle)],input=json.dumps(cmd)+'\n',capture_output=True,text=True,check=True);expected=json.loads(result.stdout);assert expected['version']==4
  args=[x.to_bytes(4,'big').hex()for x in values]+[expected[k]for k in ['base','identity','ciphertext','signal']]
  result=subprocess.run(['lake','env','lean','--run',str(HERE/'PreKeyChecks.lean'),*args],cwd=ROOT,capture_output=True,text=True,timeout=120)
  if result.returncode:
   (ROOT/'.deps/bootstrap-prekey-lean-error.log').write_text(result.stdout+result.stderr)
   raise RuntimeError('PreKey Lean numeric check failed; fixed stage diagnostics saved')
  raw=bytes(json.loads(result.stdout));assert raw[0]==255;length=int.from_bytes(raw[1:3],'big');assert raw[3:3+length]==bytes.fromhex(expected['wire'])and not any(raw[3+length:])
  rows.append(dict(word=word,private_ids=values,actual_wire_bytes=length,canonical_exact_match=True));print('actual PreKey constructor word',word,'passed',flush=True)
 audit=subprocess.run(['lake','env','lean',str(HERE/'PreKeyAudit.lean')],cwd=ROOT,capture_output=True,text=True,check=True)
 assert not any(x in audit.stdout for x in ['sorryAx','native_decide','Lean.ofReduceBool']);(HERE/'prekey-axioms.txt').write_text(audit.stdout)
 files=[pathlib.Path(__file__),HERE/'PreKeyChecks.lean',HERE/'PreKeyAudit.lean',ROOT/'TlsMpc/Signal/PrivatePreKeyMessageV1.lean',ROOT/'signal_backend/Oracle/src/bin/signal-bootstrap-peer-oracle.rs',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/protocol.rs',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/proto/wire.proto']
 report=dict(passed=True,actual_constructor_cases=rows,foundation_endpoints=2,capacity=1956,private_canonical_uint32_ID_widths=True,upstream_KEM_tag_rejection_profiles=3,native_MPC=False,whole_bootstrap=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},oracle_sha256=sha(oracle))
 (HERE/'prekey-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
