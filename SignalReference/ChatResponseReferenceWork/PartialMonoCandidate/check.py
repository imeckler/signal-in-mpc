#!/usr/bin/env python3
"""Scoped tool checkpoint: regression kernel proof, Rust comparisons, Prost extraction."""
from pathlib import Path
import os,json,subprocess,hashlib,difflib
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
run=lambda a,**kw:subprocess.run(a,check=True,timeout=240,**kw)
# Verify source/model boundary rather than accepting a similarly named crate.
vendor=ROOT/'.deps/libsignal-vendor/prost-0.14.4';checks=json.loads((vendor/'.cargo-checksum.json').read_text())['files']
for name,digest in checks.items():assert sha(vendor/name)==digest,name
run(['python3',str(H/'test.py')])
build=json.loads((H/'build-report.json').read_text());source=H/'Source/charon';base=ROOT/build['source_path'];diff=''
for name,hashes in build['modified_sources'].items():
 assert sha(base/name)==hashes['pinned'];assert sha(source/name)==hashes['candidate']
 diff+=''.join(difflib.unified_diff((base/name).read_text().splitlines(True),(source/name).read_text().splitlines(True),fromfile='pinned/'+name,tofile='candidate/'+name))
(H/'tool.diff').write_text(diff)
translator=H.parent/'TranslatorCandidate/Bin/candidate';receipt=json.loads((H.parent/'TranslatorCandidate/build-report.json').read_text());assert sha(translator)==receipt['binary_sha256']
translations=[]
for stem,dest,namespace in [('candidate-static','Generated','PartialMonoRegression'),('prost','GeneratedProst','PartialMonoProst')]:
 raw=H/'Artifacts'/(stem+'.llbc');named=H/'Artifacts'/(stem+'-named.llbc')
 run(['python3',str(H/'name_specializations.py'),str(raw),str(named)])
 command=[str(translator),'-backend','lean',str(named),'-dest',str(ROOT/'SignalReference'),'-subdir','/ChatResponseReferenceWork/PartialMonoCandidate/'+dest,'-namespace',namespace,'-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
 with (H/(stem+'-translate.log')).open('w') as f:run(command,stdout=f,stderr=subprocess.STDOUT)
 translations.append({'input_sha256':sha(raw),'named_sha256':sha(named),'names_receipt_sha256':sha(named.with_suffix('.names.json')),'command':command,'exit_code':0,'generated_sha256':{p.name:sha(p) for p in (H/dest).glob('*.lean')}})
output=H/'Build/final-lean';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
modules=['PartialMonoCandidate.Generated.Types','PartialMonoCandidate.Generated.Funs','PartialMonoCandidate.RegressionReference']
with (H/'kernel.log').open('w') as f:run(['python3',str(H.parent/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT)
log=(H/'kernel.log').read_text();assert "entry_reference' depends on axioms: [propext, Classical.choice, Quot.sound]" in log and 'sorryAx' not in log
for name,digest in checks.items():assert sha(vendor/name)==digest,name
files=[H/p for p in ['build.py','closed_adapter_patch.py','name_specializations.py','test.py','check.py','tool.diff','Regression/src/lib.rs','Regression/src/bin/check.rs','RegressionReference.lean','build-report.json','test-report.json']]+sorted((H/'Generated').glob('*.lean'))+sorted((H/'GeneratedProst').glob('*.lean'))
report={'candidate_only':True,'scope':'Selected closed-Self actual adapter specialization; abstract/mixed borrowed generic methods fail closed. Minimal result+exact-buffer kernel proof; unchanged Prost extraction and translation. Not full String/response refinement.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'pinned_prost_files_verified':len(checks),'pinned_prost_encoding_sha256':sha(vendor/'src/encoding.rs'),'translator_sha256':sha(translator),'translations':translations,'kernel_log':log,'object_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules},'whole_generated_prost_kernel_checked':False,'remaining':['Std UTF8 executable-spec boundary and Vec/String allocation content models.','Actual generated opaque &mut Buf.advance interface versus its trait field needs separate check; no assumed forwarding adapter.','Precise error DropGuard observation and full schema/streaming induction remain separate.']}
(H/'audit.json').write_text(json.dumps(report,indent=2)+'\n');print('scoped Charon adapter candidate PASS; full response remains open')
