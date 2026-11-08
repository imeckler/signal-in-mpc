#!/usr/bin/env python3
"""PUBLIC preflight only: two actual peer ratchets; no native secret openings."""
import hashlib,json,subprocess,sys
from pathlib import Path
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey,X25519PublicKey
from cryptography.hazmat.primitives.serialization import Encoding,PublicFormat
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.PrivateNewDhReceiveWork.check_model import invoke,TEXT
HERE=Path(__file__).resolve().parent
BIN=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-new-dh-peer-oracle'
def ask(p,row):
 p.stdin.write(json.dumps(row)+'\n');p.stdin.flush();line=p.stdout.readline()
 assert line,(p.args,p.poll());return json.loads(line)
def main():
 procs=[]
 try:
  def start(args):
   p=subprocess.Popen(args,cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True);procs.append(p);return p
  peer=start([str(BIN)])
  def lean(file,row):
   p=subprocess.run(['lake','env','lean','--run',str(HERE/file)],cwd=ROOT,input=json.dumps(row)+'\n',text=True,capture_output=True,check=True,timeout=180)
   return json.loads(p.stdout)
  init=ask(peer,dict(mode='init',seed=731));state=bytes.fromhex(init['initial_state']);sendpq=bytes.fromhex(init['sending_pq'])
  remote=bytes.fromhex(init['remote_identity']);local=bytes.fromhex(init['local_identity'])
  for round in range(2):
   plain=bytes.fromhex(invoke(TEXT,[dict(mode='text',body=f'Received private ratchet {round} ☕'.encode().hex(),timestamp=1900000000000+round)])[0]['padded'])
   response=ask(peer,dict(mode='send',plaintext=plain.hex()));wire=bytes.fromhex(response['wire']);assert wire[:4]==bytes.fromhex('440a2105')
   point=X25519PublicKey.from_public_bytes(wire[4:36]);fresh=bytearray(hashlib.sha256(f'PUBLIC fresh{round}'.encode()).digest());fresh[0]&=248;fresh[31]&=127;fresh[31]|=64
   key=X25519PrivateKey.from_private_bytes(fresh);public=key.public_key().public_bytes(Encoding.Raw,PublicFormat.Raw)
   dh=X25519PrivateKey.from_private_bytes(state[32:64]).exchange(point);senddh=key.exchange(point)
   encoded=b'\xff'+len(wire).to_bytes(2,'big')+wire+bytes(256-len(wire))
   got=bytes(lean('Evaluate.lean',list(state+remote+local+fresh+public+dh+senddh+encoded)))
   assert len(got)==608 and got[0]==255 and got[526:528]==b'\x00P' and got[528:]==plain
   state=got[1:526]
   outgoing=bytes.fromhex(invoke(TEXT,[dict(mode='text',body=f'Reply from new root {round}'.encode().hex(),timestamp=1900000000100+round)])[0]['padded'])
   result=bytes(lean('EvaluateReply.lean',list(state[:136]+sendpq+local+remote+outgoing)))
   assert result[0]==255
   n=int.from_bytes(result[73:75],'big');wire=result[75:75+n]
   answer=ask(peer,dict(mode='receive',wire=wire.hex()));assert answer['accepted'] and bytes.fromhex(answer['plaintext'])==outgoing
   # Selected DR chain/counter and send-PQ chain/counter advance while the
   # receive-derived root/private pair and receiving entries remain retained.
   state=state[:96]+result[1:33]+result[33:37]+state[132:]
   sendpq=sendpq[:8]+result[37:69]+result[69:73]
  sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
  files=[Path(__file__),HERE/'EvaluateReply.lean',HERE/'Evaluate.lean',ROOT/'signal_backend/Oracle/src/bin/signal-new-dh-peer-oracle.rs']
  report=dict(actual_peer_DH_cycles=2,actual_peer_decrypted_replies=2,PQ_both_directions_127_to_128=True,private_plaintext_bytes=80,all_public_disposable_fixtures=True,native_MPC_executed=False,DH_computed_by_public_fixture_X25519=True,fresh_session_prekey_authentication=False,selected_established_PQR_phase_override=True,full_actual_source_refinement=False,oracle_sha256=sha(BIN),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
  (HERE/'peer-preflight-report.json').write_text(json.dumps(report,indent=2)+'\n');print('2 receive/reply ratchet cycles; actual peer decrypts both replies; public model preflight only')
 finally:
  for p in procs:
   p.stdin.close()
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:p.terminate();p.wait()
if __name__=='__main__':main()
