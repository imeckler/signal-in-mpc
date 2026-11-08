#!/usr/bin/env python3
"""Fresh affected closure check; a successful receipt is not full parser acceptance."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=['SuccessScan','Intervals','SkipTotality','DispatcherTotality','KnownTotality','MessageTotality','Suffix','FieldSuffix',
 'Numeric.Fixed','Numeric.Group','Numeric.Stack','Numeric.Reference','Numeric.GroupReference',
 'GeneratedDriver.TypesExternal','GeneratedDriver.Types','GeneratedDriver.FunsExternal','GeneratedDriver.Funs',
 'DriverTrace','DriverTotality','MessageSuffix','TraceUniqueness','Observed','ObservedProofs','ObservedCircuit','ErrorProjection','KeyErrors','KeyErrorTable','SkipErrorDomain','KnownErrorDomain','MessageErrorDomain','DriverErrorDomain','Numeric.Fields','Numeric.TopPlan','FieldProjection','FieldTransition','ErrorMutation','DispatcherMutation','Masks','StateMasks','ScanMasks','PlanFailure','CursorGuard','KeyFailureCursor','KeyRow','NumericLeaf','NestedVarintScan','NestedFixedScan','NestedLengthScan','Frames','UnknownFields','GroupNumeric','GroupHeaderScan','ScanState','SkipStrict','SkipScanLeaves','SkipScanHeaders','SuccessfulSkipScan','ActualSkipScan','DecoderTransport','KnownSuccess','MessageReplacement','KnownDispatchSuccess','TopLeafState','TopScalarScan','TopBytesScan','KnownMessageScan','UnknownShadow','UnknownTopScan','UnknownMessageScan','SuccessfulMessageScan','InitialScan']
receipt=json.loads((H/'driver-translation.json').read_text())
for name,digest in receipt['generated_sha256'].items():assert sha(H/'GeneratedDriver'/name)==digest,name
for item in json.loads((H/'replay.json').read_text()):
 assert sha(Path(item['original']))==item['original_sha256'],item['original']
 assert sha(H/Path(*item['module'].split('.')).with_suffix('.lean'))==item['replayed_sha256'],item['module']
extend='--extend' in sys.argv
base=None
if extend:
 base=json.loads((H/'proof-report.json').read_text())
 for name,digest in base['source_sha256'].items():
  if name.endswith('.lean') and name[:-5].replace('/','.') in base['modules']:assert sha(H/name)==digest,name
 assert sha(H/'full-check.log')==base['log_sha256']
 extra=[name for name in modules if name not in base['modules']]
 modules=list(dict.fromkeys(base['modules']+extra))
 previous=(H/'extension-check.log').read_text() if base.get('extension_log_sha256') else ''
 if previous:assert sha(H/'extension-check.log')==base['extension_log_sha256']
else:extra=modules;previous=''
log=H/('extension-new.log' if extend else 'full-check.log')
with log.open('w') as f:
 run=subprocess.run([sys.executable,str(H/'check.py'),*(['--only'] if extend else ['--fresh']),*extra],stdout=f,stderr=subprocess.STDOUT)
text=log.read_text();assert run.returncode==0,'Lean failed; see '+str(log)
if extend:
 (H/'extension-check.log').write_text(previous+text)
 log=H/'extension-check.log'
 text=(H/'full-check.log').read_text()+previous+text
endpoints={}
for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S):
 used=[s.strip() for s in axioms.split(',') if s.strip()]
 assert set(used)<= {'propext','Classical.choice','Quot.sound'},(name,used)
 endpoints[name]=used
assert endpoints,'No checked endpoints'
sources={}
for p in H.rglob('*'):
 if not p.is_file() or any(x in p.relative_to(H).parts for x in ['Build','Artifacts','__pycache__']):continue
 if p.suffix not in ['.lean','.py']:continue
 module=str(p.relative_to(H).with_suffix('')).replace('/','.')
 if p.suffix=='.lean' and module not in modules and module not in ['KeyCircuit','Table','DecoderTable'] and not module.startswith('Skip.'):continue
 sources[str(p.relative_to(H))]=sha(p)
report={'candidate_only':True,'full_parser_refinement':False,'lean_exit_code':run.returncode,
 'modules':modules,'endpoints':endpoints,'source_sha256':sources,'log_sha256':sha(H/'full-check.log'),
 'extension_log_sha256':sha(log) if extend else None,
 'model_search_order':['ProtoParseWork/ModelCandidate/Build','.lake/build/lib/lean','FullParserV3Work/Build','pinned Aeneas'],
 'remaining':['Prove full numeric scan and group induction against actual driver trace, including v2 error state and exact cursor.','Connect private observed-state compiler theorem to actual driver; derive production masked-output theorem by erasure.'],
 'domain':'contiguous valid U8 slices; parser composition target body <=512, six initial absent fields, recursion budget100; modeled successful bounded allocation; diagnostic stack text quotient only'}
(H/'proof-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'checked_endpoints':len(endpoints),'full_parser_refinement':False}))
