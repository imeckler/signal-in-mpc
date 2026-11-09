#!/usr/bin/env python3
import pathlib,json,re,hashlib
work=pathlib.Path(__file__).parent;root=work.resolve().parents[1]
r=json.loads((work/'compact-warm-native-report.json').read_text());out={}
for name,case in r['cases'].items():
 raw=root/r['raw']/name;stdout=(raw/'party0.stdout').read_text();stderr=(raw/'party0.stderr').read_text();b=case['parties'][0]['bytes'];assert len(b)==9
 used=int(re.search(r'Type bit\s+(\d+)\s+Triples',stderr).group(1));left=int(re.search(r'(\d+) triples of .* left',stderr).group(1));warm=float(re.search(r'Stopped timer 1 at ([0-9.]+)',stdout).group(1))
 out[name]={'logical_ANDs':430075,'logical_ANDs_warmed_window':344060,'binary_online_bytes':b[7],'binary_preprocessing_bytes':b[8],'unattributed_bytes':b[0],'total_bytes':sum(b),'whole_run_bytes_per_logical_AND':sum(b)/430075,'runtime_reported_used_triples':used,'runtime_reported_left_triples':left,'runtime_resource_units_identical_across_backends':False,'exact_generated_triple_counts_available':False,'warmed_seconds':warm,'warmed_logical_ANDs_per_local_second':344060/warm,'raw_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in raw.glob('party*')if p.suffix in ['.stdout','.stderr']}}
a=out['ccd128'];b=out['rep3-stat40'];report={'passed':r['passed'],'scope':'optional weaker n3/t1/stat40 comparator vs n5/t2/stat128; not application throughput or secure backend promotion','whole_run_same_logical_work':True,'setup_excluded_from_warmed_timer':True,'timer_communication_counters_valid':False,'generated_discarded_batch_traffic_included':True,'profiles':out,'ratios':{'binary_online':a['binary_online_bytes']/b['binary_online_bytes'],'total':a['total_bytes']/b['total_bytes'],'local_warmed_seconds':a['warmed_seconds']/b['warmed_seconds']}}
(work/'compact-warm-comparison.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report['ratios']))
