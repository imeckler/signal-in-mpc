#!/usr/bin/env python3
"""Actual libsignal differential send checks across private counter widths."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
from scripts.check_lean_signal_send import send_cases
HERE=Path(__file__).resolve().parent;ART=ROOT/'.deps/private-hash-artifacts'
ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def main():
 path=ART/'private-send-0-0.json'
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateSend'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit;(HERE/'axioms.txt').write_text(audit)
 with path.open('w') as out:subprocess.run(['lake','env','lean','--run',str(HERE/'Export.lean'),'0','0','none'],cwd=ROOT,stdout=out,check=True)
 base=next(send_cases())[1][0];values=[0,1,126,127,128,129,16383,16384,2**21-1,2**21,2**28-1,2**28,2**32-1]
 raw=[base[:1]+n.to_bytes(4,'big')+values[-i-1].to_bytes(4,'big')+base[9:] for i,n in enumerate(values)]
 rows=[]
 for b in raw:rows.append(dict(plain='',cipher_key=b[41:73].hex(),iv=b[73:89].hex(),mac_key=b[89:121].hex(),sender=b[121:153].hex(),receiver=b[153:185].hex(),ratchet=b[9:41].hex(),addresses='',pq='',version=b[0],counter=int.from_bytes(b[1:5],'big'),previous=int.from_bytes(b[5:9],'big')))
 result=subprocess.run([str(ORACLE)],input=''.join(json.dumps(x)+'\n' for x in rows),text=True,capture_output=True,check=True)
 wires=[bytes.fromhex(json.loads(x)['wire']) for x in result.stdout.splitlines()]
 observed=evaluate_lanes(load(path),raw);cap=len(observed[0])-3
 for b,w in zip(observed,wires):assert b==b'\xff'+len(w).to_bytes(2,'big')+w+bytes(cap-len(w)),(len(w),b[:4].hex())
 files=[Path(__file__),HERE/'Export.lean',HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateSend.lean',ROOT/'TlsMpc/Signal/PrivateHash.lean',ROOT/'TlsMpc/Signal/PrivateBuffer.lean',ROOT/'TlsMpc/Signal/PrivateVarint.lean']
 report={'actual_libsignal_cases':len(raw),'counter_values':values,'previous_values':list(reversed(values)),
  'same_artifact_all_widths':True,'capacity':cap,'single_cbc_and_private_hmac':True,
  'ratchet_state_transition_executed':False,'native_mpc_executed':False,'service_integrated':False,
  'message_compiler_theorem_established':True,'standard_axioms_only':True,'buffer_integer_semantics_proved':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
  'artifact_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'oracle_sha256':hashlib.sha256(ORACLE.read_bytes()).hexdigest()}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(f'{len(raw)} actual libsignal private-counter-width sends passed; capacity{cap}',flush=True)
if __name__=='__main__':main()
