#!/usr/bin/env python3
"""One bounded isolated audit of the completed private parser proof closure."""
from pathlib import Path
import hashlib,json,os,re,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[2];REF=ROOT/'SignalReference'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted=H.parent/'FullParserV3Work';review=ROOT/'benchmarks/results/signal-full-parser-root-review.json'
old=json.loads((accepted/'proof-report.json').read_text());rootReview=json.loads(review.read_text())
assert rootReview['exit_code']==0 and sha(accepted/'proof-report.json')==rootReview['proof_report_sha256']
# Verify this composition's inherited frozen dependency receipt, without rerunning
# translator extraction or the historical 390-endpoint audit.
inherited={}
for group,base in [('source_sha256',accepted),('core_source_sha256',ROOT),('core_object_sha256',ROOT)]:
 for name,digest in old[group].items():
  path=base/name;assert sha(path)==digest,str(path);inherited[str(path.relative_to(ROOT))]=digest
model=H.parent/'ModelCandidate'
for path,key in [(model/'build-report.json','model_receipt_sha256'),(model/'Aeneas/Std/Slice.lean','model_override_source_sha256'),(model/'Build/Aeneas/Std/Slice.olean','model_override_object_sha256')]:
 assert sha(path)==old[key],str(path);inherited[str(path.relative_to(ROOT))]=sha(path)
modules=['TlsMpc.Signal.PrivateReadAtV1','TlsMpc.Signal.PrivateProtoParseV1','TlsMpc.Signal.PrivateProtoParseV1Proofs',
 'Padding','Plan','BoundedBytes','DecoderPadding','Table','Select','Stack','Lookup','Step','Scan','ActualBody','Read','Framing','Metadata','Wire','CompiledActual']
sources=[(ROOT/Path(*n.split('.')).with_suffix('.lean') if n.startswith('TlsMpc.') else H/Path(*n.split('.')).with_suffix('.lean')) for n in modules]
sources += [H/'check.py',Path(__file__).resolve(),H/'README.md']
before={str(p.relative_to(ROOT)):sha(p) for p in sources}
OUT=H/'Revisions/final';env=os.environ.copy();env['PRIVATE_PARSE_OUTPUT_ROOT']=str(OUT)
log=H/'final-audit.log'
with log.open('w') as f:r=subprocess.run(['python3',str(H/'check.py'),*modules],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=900)
assert r.returncode==0,log
text=log.read_text();assert not re.search(r'error[:(]|sorryAx',text),log
allowed={'propext','Classical.choice','Quot.sound'};endpoints={}
for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S):
 values=[s.strip() for s in axioms.split(',') if s.strip()];assert set(values)<=allowed,(name,values);endpoints[name]=values
for name in re.findall(r"'([^']+)' does not depend on any axioms",text):endpoints[name]=[]
required=['PrivateLengthV1.Scan.parseBody_take','PrivateLengthV1.Wire.parseCore_take','PrivateLengthV1.CompiledActual.compiled_actual_private_parser']
assert all(n in endpoints for n in required)
assert before=={str(p.relative_to(ROOT)):sha(p) for p in sources},'new sources changed during check'
for name,digest in inherited.items():assert sha(ROOT/name)==digest,name
objects={}
for n in modules:
 module=n if n.startswith('TlsMpc.') else 'ProtoParseWork.PrivateLengthV1Work.'+n
 p=OUT/Path(*module.split('.')).with_suffix('.olean');objects[module]=sha(p)
report={'candidate_only':True,'functional_private_parser_refinement':True,'independent_root_review_pending':True,
 'exit_code':0,'modules':modules,'endpoints':endpoints,'source_sha256':before,'object_sha256':objects,
 'inherited_accepted_receipt_sha256':sha(accepted/'proof-report.json'),'inherited_root_review_sha256':sha(review),
 'verified_inherited_sha256':inherited,'log_sha256':sha(log),'output_directory':str(OUT.relative_to(ROOT)),
 'domain':'Every n<=public wire capacity<=512; BE16 length representation; arbitrary upstream validity with canonical eqMask acceptance; target capacity256',
 'observation':'Exact native default-merge trace, suffix, error ctor/params and mutated Options; private state equality modulo zero stack extension; compiled production acceptance/released metadata; diagnostic text quotient inherited only',
 'constructor_boundary':'Explicit six-None record and default recursion100; actual generated dispatcher and default merge; Message::decode/Default wrapper not assumed',
 'model_boundary':'Inherited accepted contiguous safe-index slice and successful bounded allocation/content models; no new correctness/termination axiom',
 'remaining':['Independent root review','Native capacity256 receive integration validation (crypto owner)','Separate typed decode/default wrapper and whole-session/security obligations','Chat response schema refinement remains queued'],
 'active_handles':[]}
(H/'proof-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'exit_code':0,'module_count':len(modules),'endpoint_count':len(endpoints),'functional_private_parser_refinement':True}))
