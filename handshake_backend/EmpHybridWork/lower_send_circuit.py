"""Export, check and pin the two-send Signal circuit (TlsMpc/HybridSend.lean).

Shape: 17-byte plaintexts, 5 PQ bytes, counter width 5, previous width 2, with
addresses (the non-trivial shape of scripts/check_lean_signal_chain_send.py).
The reference is independent of the circuit: HMAC/HKDF from hashlib, AES-256-CBC
from the openssl binary, and the serialization helpers of the existing fixture
scripts. Two lanes are checked and written for the MPC runner: both sends
accepted with the second using the first's returned chain key and counter, and
a rejected lane (invalid PQ-key flag) where state is preserved and wires zeroed.
"""
import hashlib,hmac,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;OUT=ROOT/'.deps/emp-hybrid-word-v1';OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT));sys.path.insert(0,str(HERE))
from hybrid_lowering import lower,flat_text,byte_bits,evaluate_bytes
from scripts.check_lean_signal_chain_send import derive
from scripts.check_lean_signal_send import content,content_size,valid,sample,address,smallest
SIZE,PQ,CW,PW=17,5,5,2
def send(fields,chain,counter_bytes,plaintext):
    version,_,pr,ratchet,_,present,pq_key,sender,receiver,_,pq,addresses=fields
    counter,previous=int.from_bytes(counter_bytes,'big'),int.from_bytes(pr,'big')
    accepted=present[0] in (0,1) and counter!=0xffffffff and valid(CW,PW,counter,previous,addresses)
    if not accepted:return b'\x00'+chain+counter_bytes+bytes(8+content_size((SIZE//16+1)*16,PQ,CW,PW,True))
    next_chain,cipher_key,mac_key,iv=derive(chain,pq_key if present==b'\x01' else bytes(32))
    ciphertext=subprocess.check_output(['openssl','enc','-aes-256-cbc','-nosalt','-K',cipher_key.hex(),'-iv',iv.hex()],input=plaintext)
    body=content(version[0],counter,previous,ratchet,ciphertext,pq,addresses)
    return b'\xff'+next_chain+(counter+1).to_bytes(4,'big')+body+hmac.digest(mac_key,b'\x05'+sender+b'\x05'+receiver+body,'sha256')[:8]
def two_sends(fields,second_plaintext):
    first=send(fields,fields[4],fields[1],fields[9]);second=send(fields,first[1:33],first[33:37],second_plaintext)
    return first+second
label='hybrid-two-sends'
base=[bytes([4]),smallest(CW).to_bytes(4,'big'),smallest(PW).to_bytes(4,'big'),sample(label+'-ratchet',32),sample(label+'-chain',32),b'\x01',
      sample(label+'-pq-key',32),sample(label+'-sender',32),sample(label+'-receiver',32),sample(label+'-plaintext-1',SIZE),sample(label+'-pq',PQ),address(label)]
second=sample(label+'-plaintext-2',SIZE)
rejected=list(base);rejected[5]=b'\x02'
lanes=[('two-accepted-sends',base),('invalid-pq-flag-preserves-state',rejected)]
subprocess.run(['lake','build','hybrid_kdf_emitter','word_mask_emitter'],cwd=ROOT,check=True,capture_output=True)
raw=subprocess.run(['lake','exe','hybrid_kdf_emitter','signal-two-sends',str(SIZE),str(PQ),str(CW),str(PW),'present'],cwd=ROOT,check=True,capture_output=True).stdout
n,gates,outputs=lower(json.loads(raw));fixtures=[]
for name,fields in lanes:
    data=b''.join(fields)+second;want=two_sends(fields,second)
    if 8*len(data)!=n or 8*len(want)!=len(outputs):raise ValueError('two-sends shape')
    if evaluate_bytes(gates,outputs,byte_bits(data))!=want:raise AssertionError(name)
    fixtures.append(dict(label=name,input=data.hex(),output=want.hex()))
if fixtures[0]['output'][0:2]!='ff' or fixtures[0]['output'][len(fixtures[0]['output'])//2:][0:2]!='ff':raise AssertionError('accepted lane not accepted')
text=flat_text(n,gates,outputs);(OUT/'signal-two-sends.flat').write_text(text);digest=hashlib.sha256(text.encode()).hexdigest()
equal=subprocess.run(['lake','exe','word_mask_emitter','equal',str(len(outputs))],cwd=ROOT,check=True,capture_output=True).stdout.decode()
(OUT/'signal-two-sends-equal.flat').write_text(equal)
profile=dict(circuit='signal-two-sends.flat',circuit_sha256=digest,equal='signal-two-sends-equal.flat',equal_sha256=hashlib.sha256(equal.encode()).hexdigest(),input_bits=n,output_bits=len(outputs),fixtures=fixtures)
(OUT/'signal-two-sends.json').write_text(json.dumps(profile,indent=2)+'\n')
report=dict(passed=True,arguments=['signal-two-sends',SIZE,PQ,CW,PW,'present'],lean_image_sha256=hashlib.sha256(raw).hexdigest(),flat_sha256=digest,and_gates=sum(g[0]=='A' for g in gates),input_bits=n,output_bits=len(outputs),lanes=[f['label'] for f in fixtures],
    reference='hashlib HMAC/HKDF, openssl AES-256-CBC, serialization helpers from scripts/check_lean_signal_send.py',
    scope='Two chained established sends as one Lean circuit; second send consumes the first send\'s returned chain key and counter. Checked against an independent reference on an accepted and a rejected lane. Lowered by the shared unverified adapter. Not a recipient-decryption test and not a session-state commit.')
(HERE/'send-circuit-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(and_gates=report['and_gates'],input_bits=n,output_bits=len(outputs))))
