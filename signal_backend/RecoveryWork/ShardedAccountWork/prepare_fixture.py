#!/usr/bin/env python3
"""Assemble ONLY the NEW public disposable two-peer source fixture."""
import hashlib,json,pathlib,sys,uuid
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'SignalReference/PrivateRecordWork'))
from check import make,record
from check_send import flatten
from check_binding import service
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes

def main():
 source=ROOT/'signal_backend/RecoveryWork/FreshShardedFixtureWork';client=json.loads((source/'client.json').read_text());peer=json.loads((source/'recipient.json').read_text());assert client['domain']=='fresh-sharded-account-v1-seeds91-97'
 store=client['account_global_store'];global_store=bytes.fromhex(store['global_store_v1']);assert len(global_store)<=8192 and len(store['trusted_peers'])==2
 cursor=(2**63+0x910000).to_bytes(8,'big');global_raw=uuid.UUID(client['client_uuid']).bytes+bytes.fromhex(client['client_password_hex'])+bytes.fromhex(store['identity_private_public65'])+b'\xff'+len(global_store).to_bytes(2,'big')+global_store.ljust(8192,b'\0')+cursor;assert len(global_raw)==8306
 conversations=[];services=[];texts=[]
 for slot,(c,p)in enumerate(zip(client['conversations'],peer['conversations'],strict=True)):
  row=c['rows'][0];raw=service(row,0);raw[32:292]=bytes.fromhex(client['certificate']);raw[474:554]=bytes(80)
  meta=uuid.UUID(p['recipient_uuid']).bytes+bytes.fromhex(p['access_key'])+bytes(8)+cursor+bytes([p['device_id']])+p['registration_id'].to_bytes(4,'big')+bytes(4);assert len(meta)==57
  raw[554:611]=meta;binding=meta[:16]+meta[49:53]+b'\x05'+raw[442:474]+meta[16:32]
  canonical=bytes(flatten(make(bytes.fromhex(row['sender_record_before']),record)));selected=bytes.fromhex(row['sender_selected_before']);assert len(canonical)==5550 and len(selected)==525 and len(raw)==611
  conv=bytes(binding)+canonical+raw+selected+bytes(612+5240+4);assert len(conv)==12611
  conversations.append(conv);services.append(bytes(raw));texts.append([bytes.fromhex(x)for x in c['text_inputs']]);assert len(texts[-1])==6 and all(len(x)==59 for x in texts[-1])
 stage=ROOT/'.deps/private-shard-validation-native/v1-candidate-3'
 assert evaluate_lanes(load(stage/'outbox-global.json'),[global_raw])==[b'\xff']
 assert evaluate_lanes(load(stage/'outbox-conversation.json'),[global_raw+c for c in conversations])==[b'\xff']*2
 def decode(raw):return 'decode("'+raw.hex()+'")'
 output=['#pragma once','// NEW PUBLIC DISPOSABLE account only; never a production importer.','#include <vector>','#include <string>','#include <stdexcept>','namespace signal_mpc::recovery::sharded {','struct FreshFixture {','static std::vector<unsigned char> decode(const std::string& text){std::vector<unsigned char> out;for(size_t i=0;i<text.size();i+=2)out.push_back(std::stoul(text.substr(i,2),nullptr,16));return out;}','static std::vector<unsigned char> global(){return '+decode(global_raw)+';}']
 for name,values in [('conversation',conversations),('service',services)]:
  output.append('static std::vector<unsigned char> '+name+'(size_t slot){switch(slot){')
  output.extend('case '+str(i)+':return '+decode(v)+';'for i,v in enumerate(values));output.append('default:throw std::runtime_error("fresh fixture slot");}}')
 output.append('static std::vector<unsigned char> text(size_t slot,size_t round){if(slot>=2||round>=6)throw std::runtime_error("fresh fixture text");switch(slot*6+round){')
 for i,values in enumerate(texts):output.extend('case '+str(i*6+j)+':return '+decode(v)+';'for j,v in enumerate(values))
 output.extend(['default:throw std::runtime_error("fresh fixture text");}}','};','}']);(HERE/'FreshFixture.h').write_text('\n'.join(output)+'\n')
 report=dict(prepared=True,NEW_fixture_only=True,existing_head3_untouched=True,conversations=2,texts=12,exact_initial_shard_AIG_cases=3,private_MPC_bootstrap=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [pathlib.Path(__file__),source/'client.json',source/'recipient.json',HERE/'FreshFixture.h']});(HERE/'fixture-report.json').write_text(json.dumps(report,indent=2)+'\n');print('prepared NEW two-conversation source fixture')
if __name__=='__main__':main()
