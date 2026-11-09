#!/usr/bin/env python3
"""Paired fixed-work accounting; never sum inclusive/nested RPC metrics."""
from pathlib import Path
import collections,hashlib,json,re
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent

def rows(path,prefix):
 return [json.loads(line[len(prefix):])for line in path.read_text().splitlines()if line.startswith(prefix)]
def summarize(path):
 report=json.loads(path.read_text());assert report['passed']and report['source_integrity_verified']and not report['cleanup_errors']
 assert report['messages']==8 and report['controller_exit_codes']==[0]*5
 log=ROOT/report['logs']/'party-0.log';metrics=rows(log,'TLS_METRIC ');domains=rows(log,'TLS_DOMAIN_METRIC ')
 top=[r for r in metrics if re.fullmatch(r'rpc\.\d+',r['stage'])]
 topdomains=[r for r in domains if re.fullmatch(r'rpc\.\d+',r['stage'])]
 assert len(top)==len(topdomains)and all(a['stage']==b['stage']for a,b in zip(top,topdomains))
 producer='rpc.26'if report['producer_execution']=='batch'else'rpc.24';batch=2 if producer=='rpc.26'else 1
 first=next(i for i,r in enumerate(top)if r['stage']==producer);last=max(i for i,r in enumerate(top)if r['stage']=='rpc.25')
 window=top[first:last+1];domainwindow=topdomains[first:last+1];assert sum(r['stage']==producer for r in window)*batch==8
 grouped={}
 for stage in sorted({r['stage']for r in window}):
  selected=[r for r in window if r['stage']==stage]
  grouped[stage]={'calls':len(selected),'worker_rpc_seconds':sum(r['elapsed_ns']for r in selected)/1e9,'payload_bytes':sum(r['worker_payload_bytes']+r['host_payload_bytes']for r in selected)}
 name='provider.crypto.batch'if batch==2 else'provider.crypto';producerrows=[r for r in metrics if r['stage']==name];producerdomains=[r for r in domains if r['stage']==name]
 assert len(producerrows)==len(producerdomains)==8//batch
 calls=[{'messages':batch,'elapsed_seconds':a['elapsed_ns']/1e9,'payload_bytes':a['worker_payload_bytes']+a['host_payload_bytes'],'prepare_seconds':b['prepare_ns']/1e9,'load_seconds':b['load_ns']/1e9,'domain_phase_bytes':b['bytes']}for a,b in zip(producerrows,producerdomains)]
 bins=[sum(r['bytes'][i]for r in domainwindow)for i in range(9)];payload=sum(r['worker_payload_bytes']+r['host_payload_bytes']for r in window)
 assert sum(bins)==payload+sum(r['initialization_reset_bytes']for r in domainwindow),'byte counter reconciliation failed'
 worker_seconds=sum(r['elapsed_ns']for r in window)/1e9
 return {'report':str(path.relative_to(ROOT)),'logs':report['logs'],'messages':8,'producer_execution':report['producer_execution'],'full_inclusive_elapsed_seconds':report['elapsed_seconds'],'full_inclusive_messages_per_second':8/report['elapsed_seconds'],'persistent_window':{'definition':'first producer RPC through last response RPC; top-level metrics ONLY','payload_bytes_party0':payload,'payload_bytes_per_message_party0':payload/8,'worker_rpc_seconds':worker_seconds,'worker_RPC_only_msg_s_upper_bound':8/worker_seconds,'wall_window_timestamps_available':False,'domain_phase_bytes':bins,'domain_payload_total':sum(bins),'domain_minus_legacy_payload_residual':sum(bins)-payload,'initialization_reset_bytes':sum(r['initialization_reset_bytes']for r in domainwindow),'loader_seconds':sum(r['load_ns']for r in domainwindow)/1e9,'prepare_seconds':sum(r['prepare_ns']for r in domainwindow)/1e9,'RPC_groups':grouped},'producer_calls':calls,'producer_repeated_after_first':{'messages':(len(calls)-1)*batch,'elapsed_seconds':sum(r['elapsed_seconds']for r in calls[1:]),'load_seconds':sum(r['load_seconds']for r in calls[1:]),'payload_bytes':sum(r['payload_bytes']for r in calls[1:])},'all_reported_epoch_renewals':len([r for r in metrics if r['stage']=='epoch.renew']),'endpoint':report['endpoint'],'canonical_runtime_sha256':report['canonical_runtime_sha256'],'manifest_digest':next(v for k,v in report['source_and_product_sha256'].items()if k.endswith('/programs.manifest')),'fixed_source_and_product_sha256':{k:v for k,v in report['source_and_product_sha256'].items()if not k.startswith('benchmarks/results/raw/')}}

def main():
 sequential=summarize(ROOT/'benchmarks/results/tls-native-text-throughput-sequential.json');batch=summarize(ROOT/'benchmarks/results/tls-native-text-throughput-batch.json')
 assert sequential['fixed_source_and_product_sha256']==batch['fixed_source_and_product_sha256'],'paired source/product mismatch'
 assert sequential['manifest_digest']==batch['manifest_digest']and sequential['canonical_runtime_sha256']==batch['canonical_runtime_sha256']
 report={'passed':True,'same_source_worker_runtime_manifest':True,'sequential':sequential,'batch':batch,'full_inclusive_throughput_ratio_batch_over_sequential':sequential['full_inclusive_elapsed_seconds']/batch['full_inclusive_elapsed_seconds'],'persistent_payload_ratio_batch_over_sequential':batch['persistent_window']['payload_bytes_party0']/sequential['persistent_window']['payload_bytes_party0'],'scope':'Eight messages/two conversations/local5party+local actual recipient; NOT steadyWAN or100k/hour evidence. Same every-record renewal policy; producer checkpoint is once per group, reported separately. Program load/prep times are inclusive nested durations. Generated/discarded triple COUNTS unavailable; preprocessing bytes include their traffic. Domain bytes reconcile exactly to legacy payload plus recorded initialization-reset bytes. Transport link overhead remains unmeasured.','next_priority':'Compact Boolean backend/primary LN17-CHI23 verification+conversion audit; repeated program reload cache is separate CPU optimization, not a bytes reduction.'}
 (WORK/'comparison-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k]for k in ['passed','full_inclusive_throughput_ratio_batch_over_sequential','persistent_payload_ratio_batch_over_sequential']},indent=2))
if __name__=='__main__':main()
