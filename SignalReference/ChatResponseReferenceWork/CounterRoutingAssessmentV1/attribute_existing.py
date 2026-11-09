#!/usr/bin/env python3
"""Read-only output-cone attribution of the frozen measured byte candidate."""
from pathlib import Path
from array import array
import json,hashlib,sys
H=Path(__file__).resolve().parent;ROOT=H.parents[2];C=H.parent/'ParserCircuitCandidateV1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path.insert(0,str(ROOT))
from backend_adapter.aig import statistics,_plan,_xor_sources
receipt=C/'profile-audit.json';r=json.loads(receipt.read_text());row=next(x for x in r['cases']if x['mode']=='candidate');p=Path(row['artifact_path']);assert sha(p)==row['artifact_sha256']
assert sha(ROOT/'backend_adapter/aig.py')==r['source_sha256']['backend_adapter/aig.py']
im=json.loads(p.read_text());plan=_plan(im['nodes'],im['outputs'],True);level=array('I',[0])*len(im['nodes'])
for i,node in enumerate(im['nodes']):
 if not plan[i]or node[0]!=2:continue
 left,_,right,_=_xor_sources(im['nodes'],node)if plan[i]==2 else node[1:]
 level[i]=max(level[left],level[right])+(plan[i]==1)
base=statistics(im)['executed_and_gates'];assert base==40529
retained=lambda i:i if i<73 else 73+8*((i-73)//4)+4+(i-73)%4 if i<473 else i+400
groups={'mux-valid':[(0,1)],'parser-valid-finish':[(1,5)],'modes-positions':[(5,19)],'varint-value-tag':[(19,35)],'response-remaining':[(41,49)],'budget':[(49,57)],'skip':[(57,65)],'group-depth':[(65,73)],'stack':[(73,873)],'type-value':[(873,881)],'id-expected-status':[(884,908)],'body-length':[(909,917)],'utf-header':[(918,933)],'slots-queue':[(933,982)],'event-masks':[(982,985)]}
rows=[]
for name,ranges in groups.items():
 indices={j for j in range(585)if any(lo<=retained(j)<hi for lo,hi in ranges)}
 outputs=[x for bit,x in enumerate(im['outputs'])if bit//8 in indices]
 rest=[x for bit,x in enumerate(im['outputs'])if bit//8 not in indices]
 only={**im,'outputs':outputs};without={**im,'outputs':rest}
 rows.append({'field':name,'compact_output_bytes':len(indices),'max_and_depth':max((level[node]for node,_ in outputs),default=0),'fanin_executed_ands_nonadditive':statistics(only)['executed_and_gates'],'exclusive_output_ands':base-statistics(without)['executed_and_gates']})
report={'scope':'Exact frozen byte-graph output cone/depth attribution. Fanin counts overlap and are not additive; exclusive nodes mean output pruning only, not an implemented parser optimization.','artifact_sha256':sha(p),'artifact_path':str(p),'inherited_profile_sha256':sha(receipt),'baseline_executed_ands':base,'baseline_and_depth':max(level[node]for node,_ in im['outputs']),'groups':rows,'source_sha256':{str(Path(__file__).resolve().relative_to(ROOT)):sha(Path(__file__).resolve()),'backend_adapter/aig.py':sha(ROOT/'backend_adapter/aig.py')}}
(H/'output-cones.json').write_text(json.dumps(report,indent=2)+'\n')
for row in rows:print(row)
