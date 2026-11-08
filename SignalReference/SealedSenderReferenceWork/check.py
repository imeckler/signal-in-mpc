from pathlib import Path
import os,subprocess,re,json,hashlib
w=Path(__file__).resolve().parent;r=w.parents[1];b=w/'Build';cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages');paths=[b,r/'.lake/build/lib/lean',r/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in cache.iterdir() if (p/'.lake/build/lib/lean').is_dir()];env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)))
for n in ['Generated/EncryptWrapper/Types','PrimitiveModels','Generated/EncryptWrapper/FunsExternal','Generated/EncryptWrapper/Funs','WrapperReference']:
 o=b/('SealedSenderReferenceWork/'+n+'.olean');o.parent.mkdir(parents=True,exist_ok=True);subprocess.run(['lean','-o',str(o),str(w/(n+'.lean'))],env=env,cwd=r/'SignalReference',check=True)

audit=subprocess.check_output(['lean',str(w/'Checks.lean')],env=env,cwd=r/'SignalReference',text=True)
groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S)
# Lean prints axiom-free endpoints separately.
assert audit.count('depends on axioms:')+audit.count('does not depend on any axioms')==7,audit
for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'},audit
assert 'sorryAx' not in audit and '_native' not in audit
(w/'axioms.txt').write_text(audit)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inventory=json.loads((w/'Artifacts/EncryptWrapper/inventory.json').read_text())
assert inventory['charon_exit_code']==0 and inventory['aeneas_exit_code']==0 and not inventory['has_errors']
for name,digest in inventory['generated_files'].items():assert sha(r/'SignalReference'/name)==digest,name
for name,digest in inventory['source_sha256'].items():assert sha(r/name)==digest,name
files=[p for p in w.rglob('*') if p.is_file() and 'Build' not in p.parts and p.suffix in {'.lean','.py','.llbc'}]
report={'candidate_only':True,'kernel_endpoints':7,'foundation_axioms_only':True,'unchanged_actual_generated_wrapper':True,'source_patches':[],
 'actual_implementation':'signalapp/libsignal904c8dc crypto.rs56..65 aes256_ctr_hmacsha256_encrypt',
 'proved':'Actual generated Result/Try/checked MAC slice/Vec clone+append, wrong cipher-key error, exact symmetric-envelope bytes under executable primitive interpretation.',
 'explicit_trust_boundary':['Actual AES-CTR and HMAC bodies are opaque extraction slots interpreted by executable circuit primitive models. Their implementation agreements remain UNPROVED.','Official pinned Aeneas Slice/Vec/Array and translator correctness boundary.','Whole sealed_sender KDF/certificate/envelope and session implementation refinement remain UNPROVED.'],
 'source_refinement_domain':'Intended SS profile plaintext<=8192,key32,MACkey32; model-relative wrapper theorem uses allocation bound msg.length+10<=Usize.max.',
 'source_sha256':{str(p.relative_to(r)):sha(p) for p in files}}
(w/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print('7 kernel endpoints; unchanged actual SS symmetric wrapper and explicit primitive model boundary passed')
