#!/usr/bin/env python3
"""Steady established SPQR+Signal send costs for the100k logical messages/hour target.

No handshake/KEM initialization is charged per established send. A logical send
may require several recipient-device encryptions; this script records the per-
device primitive. Private HTTP/2 request framing and TLS record sealing remain
separate costs. AND depth is a circuit dependency metric, not measured RTTs.
"""
import argparse,json,hmac,re,subprocess,sys
from array import array
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_spqr_send import varint,spqr_derive
from scripts.check_lean_signal_chain_send import derive
from scripts.check_lean_signal_send import sample,address,content
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import _plan,_xor_sources,statistics

def fixture(size,lane):
    label=f'100k-steady-send-{size}-{lane}';counter=2**14+lane;previous=2**14;epoch=2**14;pq_counter=2**14-1+lane
    ratchet=sample(label+'ratchet',32);chain=sample(label+'chain',32);pq_chain=sample(label+'pqchain',32)
    sender=sample(label+'sender',32);receiver=sample(label+'receiver',32);plain=sample(label+'plain',size);addresses=address(label)
    raw=b'\x04'+counter.to_bytes(4,'big')+previous.to_bytes(4,'big')+ratchet+chain+pq_chain+pq_counter.to_bytes(4,'big')+epoch.to_bytes(8,'big')+b'\0'+sender+receiver+plain+addresses
    next_pq,pq_key=spqr_derive(pq_chain,pq_counter);pq=b'\1'+varint(epoch)+varint(pq_counter+1)+b'\0'
    next_chain,cipher_key,mac_key,iv=derive(chain,pq_key)
    ciphertext=subprocess.check_output(['openssl','enc','-aes-256-cbc','-nosalt','-K',cipher_key.hex(),'-iv',iv.hex()],input=plain)
    body=content(4,counter,previous,ratchet,ciphertext,pq,addresses)
    tag=hmac.digest(mac_key,b'\5'+sender+b'\5'+receiver+body,'sha256')[:8]
    out=b'\xff'+next_chain+(counter+1).to_bytes(4,'big')+next_pq+(pq_counter+1).to_bytes(4,'big')+body+tag
    return raw,out

def depth(image):
    nodes=image['nodes'];kinds=_plan(nodes,image['outputs'],True);levels=array('I',[0])*len(nodes)
    for index,node in enumerate(nodes):
        if not kinds[index] or node[0]!=2:continue
        left,_,right,_=_xor_sources(nodes,node) if kinds[index]==2 else node[1:]
        levels[index]=max(levels[left],levels[right])+(kinds[index]==1)
    return max((levels[node] for node,_ in image['outputs']),default=0)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--sizes',nargs='+',type=int,default=[256,1024]);args=ap.parse_args()
    directory=ROOT/'.deps/signal-steady-send-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for size in args.sizes:
        assert 0<=size<=1024
        command=['signal-spqr-send',str(size),'3','3','3','3','0','none','present'];path=directory/('-'.join(command)+'.json')
        with path.open('w') as out:subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),*command],stdout=out,check=True,timeout=600)
        fixtures=[fixture(size,lane) for lane in range(2)];image=load(path)
        assert evaluate_lanes(image,[x for x,_ in fixtures])==[y for _,y in fixtures]
        fp=path.with_name(path.stem+'-fixtures.json');fp.write_text(json.dumps([{'input':x.hex(),'output':y.hex()}for x,y in fixtures],indent=2)+'\n')
        ops=statistics(image);and_depth=depth(image);rate=100000/3600
        row={'arguments':command,'payload_bytes':size,'signal_ciphertext_wire_bytes':len(fixtures[0][1])-73,'shared_state_output_bytes':73,'artifact_sha256':digest(path),'fixture_sha256':digest(fp),'adapter_operations':ops,'and_dependency_depth':and_depth,'all_fixture_outputs_match':True,'minimum_required_boolean_and_evaluations_per_second_by_fanout':{str(f):rate*f*ops['executed_and_gates']for f in(1,2,4,10)}}
        rows.append(row);print(json.dumps(row),flush=True)
    files={Path(__file__),ROOT/'TlsMpc/Signal/Export.lean',ROOT/'scripts/check_lean_signal_spqr_send.py',ROOT/'backend_adapter/aig.py',ROOT/'backend_adapter/boolean.py'}
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for name in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(name)
    visit('TlsMpc.Signal.SpqrSend')
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'target_logical_messages_per_hour':100000,'target_logical_messages_per_second':100000/3600,'cases':rows,'source_sha256':{str(p.relative_to(ROOT)):digest(p)for p in sorted(files)},'steady_state':'existing classical and SPQR chains; no epoch/KEM rollover; retained TLS session; public sizes and widths; identities/address bytes remain shared','device_fanout':'separate recipient-device encryptions plus any sender-device sync copies; logical message rate multiplied by effective fanout','batching':'independent sessions/recipient devices can share SIMD lanes; consecutive messages on one ratchet remain state dependent','excluded_costs':['private H2 request framing and HPACK/policy','TLS1.3 AES128GCM record sealing','server control/ack traffic','new sessions and KEM epoch rollover','mobile share refresh and native VM erasure'],'native_mpc_executed':False,'wan_throughput_measured':False,'and_dependency_depth_is_not_measured_network_rtt':True}
    (ROOT/'benchmarks/results/lean-signal-steady-send-costs.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
