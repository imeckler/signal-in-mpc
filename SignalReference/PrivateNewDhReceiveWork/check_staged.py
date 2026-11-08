#!/usr/bin/env python3
"""Public staged AIG differential; supplied oracle DH remains a model boundary."""
import gc,hashlib,hmac,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.PrivateNewDhReceiveWork.check_model import invoke,BIN,TEXT,derive
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
HERE=Path(__file__).resolve().parent
ART=ROOT/'.deps/private-hash-artifacts'
def main():
 requests=[]
 for seed,body in enumerate(['New DH notification ☕','Second root rotation fixture']):
  text=invoke(TEXT,[dict(mode='text',body=body.encode().hex(),timestamp=1900000000000+seed)])[0]
  requests.append(dict(seed=seed,plaintext=text['padded']))
 fixtures=invoke(BIN,requests);assert len(fixtures)==2
 # Actual Prost truncates a decoded uint64 to uint32. Re-MAC a counter2^32
 # encoding with independently derived public-fixture keys; actual Rust must
 # accept it as counter0 and produce the same receiving transition.
 first=fixtures[0];raw=bytes.fromhex(first['input']);wire=raw[720:720+first['wire_bytes']]
 assert wire[36:38]==b'\x10\x00'
 content=wire[:37]+b'\x80\x80\x80\x80\x10'+wire[38:-8]
 _,_,mac,_=derive(bytes.fromhex(first['sender_chain_before']),bytes.fromhex(first['actual_pq_key']))
 tag=hmac.new(mac,b'\x05'+raw[525:557]+b'\x05'+raw[557:589]+content,hashlib.sha256).digest()[:8]
 overflow=invoke(BIN,[dict(requests[0],wire_override=(content+tag).hex())])[0]
 assert overflow['wire_bytes']==first['wire_bytes']+4
 fixtures.append(overflow)
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

 summary_path=ART/'private-new-dh-summary-256.json'
 crypto_path=ART/'private-new-dh-crypto-256-5.json'
 image=load(summary_path);assert image['input_bits']==259*8 and len(image['outputs'])==75*8
 summaries=evaluate_lanes(image,[r[717:] for r in rows]);summary_nodes=len(image['nodes'])
 del image;gc.collect()
 image=load(crypto_path);assert image['input_bits']==1051*8 and len(image['outputs'])==608*8
 outputs=evaluate_lanes(image,[r+s for r,s in zip(rows,summaries)])
 for i,(got,want)in enumerate(zip(outputs,expected)):assert got==want,(i,got[0],want[0])
 files=[Path(__file__),HERE/'SummaryExport.lean',HERE/'CryptoExport.lean',ROOT/'TlsMpc/Signal/PrivateNewDhReceiveSplit.lean',ROOT/'TlsMpc/Signal/PrivateNewDhReceiveSplitProofs.lean']
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 report=dict(actual_transition_matches=3,uint64_to_uint32_counter_fixture=True,rejections_preserve_all_old_state=18,output_bytes=608,summary_bytes=75,summary_nodes=summary_nodes,crypto_nodes=len(image['nodes']),parse_once=True,oracle_DH_supplied_in_public_differential=True,native_computed_DH_binding_executed=False,full_actual_source_refinement=False,artifact_sha256={p.name:sha(p) for p in [summary_path,crypto_path]},source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'staged-report.json').write_text(json.dumps(report,indent=2)+'\n')
 print('Staged AIG: 3 actual transitions +18 rejection state selections, all608 bytes')
if __name__=='__main__':main()
