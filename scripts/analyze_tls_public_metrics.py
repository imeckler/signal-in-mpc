"""Summarize public instrumentation from a frozen native TLS run (no private data)."""
import argparse,json
from pathlib import Path

def analyze(directory):
 parties=[]
 for path in sorted(directory.glob('party-*.log')):
  metrics=[];functions=[];resources=[];complete=[];current_descriptor=None
  for line in path.read_text().splitlines():
   for prefix,target in [('TLS_METRIC ',metrics),('TLS_RESOURCE_META ',functions),('TLS_RESOURCE ',resources),('TLS_RESOURCE_COMPLETE ',complete)]:
    if line.startswith(prefix):
     item=json.loads(line[len(prefix):])
     if prefix=='TLS_RESOURCE_META ':current_descriptor=item['descriptor']
     if prefix=='TLS_RESOURCE ':item['descriptor']=current_descriptor
     target.append(item);break
  functions=list({f['descriptor']:f for f in functions}.values())
  resources=list({(r['descriptor'],r['source'],r['field'],r['kind']):r for r in resources}.values())
  rpc=[m for m in metrics if m['stage'].startswith('rpc.')]
  first=next((i for i,m in enumerate(rpc) if m['stage']=='rpc.24'),None)
  last=max((i for i,m in enumerate(rpc) if m['stage']=='rpc.25'),default=-1)
  window=rpc[first:last+1] if first is not None and last>=first else []
  successful=sum(m['stage']=='rpc.24' and m['success'] for m in window)
  elapsed=sum(m['elapsed_ns'] for m in window)/1e9
  stages={}
  for m in metrics:
   total=stages.setdefault(m['stage'],{'calls':0,'elapsed_seconds':0,'failed':0})
   total['calls']+=1;total['elapsed_seconds']+=m['elapsed_ns']/1e9;total['failed']+=not m['success']
  parties.append({'party_log':path.name,'stage_totals':stages,
    'persistent_rpc_window':{'successful_productions':successful,'sum_rpc_seconds':elapsed,
      'messages_per_cpp_rpc_clock_second':successful/elapsed if elapsed and successful else None,
      'worker_payload_bytes':sum(m.get('worker_payload_bytes',0) for m in window),
      'scope':'first produce to last response; C++ steady_clock includes system suspend on this macOS runtime; excludes controller inter-call time; not active steady-state throughput; stage/epoch subtotals overlap'},
    'function_totals':functions,'resource_rows':resources,'resource_complete':complete,
    'all_reported_counters_monotone':all(m['counters_monotone'] for m in metrics),
    'rpc_protocol_payload_bytes':{key:sum(m.get(key,0) for m in rpc) for key in ['worker_payload_bytes','host_payload_bytes','communication_operations']}})
 return {'scope':'public worker metadata only; no long-run steady-state/WAN/100k-hour claim',
   'target_messages_per_second':100000/3600,
   'counter_limits':'protocol payload counters exclude TLS/socket overhead and retirement-tail traffic; operations are sums, not network critical-path rounds; resource demand is compiler-declared unless actual_available=true',
   'resource_snapshot_limits':'idempotent abort can emit the same cumulative snapshot twice; only the latest row per descriptor/source/field/kind is retained; zero-call failed lookups are not actual usage evidence',
   'clock_limits':'driver Python3.9 mach_absolute_time excludes macOS suspend; C++ steady_clock uses CLOCK_MONOTONIC_RAW and includes it; do not compare or infer cold-start cost from mismatched totals',
   'functions_timing_limits':'verification and Machine.run timings are separate; Machine.run includes loading plus execution, so loader-only time is not isolated',
   'parties':parties}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('--output',type=Path);args=ap.parse_args()
 result=analyze(args.directory);text=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 else:print(text,end='')
