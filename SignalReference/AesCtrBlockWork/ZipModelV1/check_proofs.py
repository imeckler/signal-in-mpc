#!/usr/bin/env python3
"""Actual AES round-key loop versus word XOR, relative to narrow trusted Std Zip."""
import hashlib,importlib.util,json,pathlib,shutil,subprocess,sys,tempfile,re
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sys.path.insert(0,str(REF));from AesAddRoundKeyWork.inspect_metadata import select
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 artifacts=HERE/'Artifacts';artifacts.mkdir(exist_ok=True)
 original=artifacts/'original.llbc';old=REF/'AesAddRoundKeyWork/Artifacts/IncludeXor/add_round_key.llbc'
 if not original.exists():shutil.copy2(old,original)
 prior=json.loads((REF/'AesAddRoundKeyWork/proof-check.json').read_text());assert sha(original)==prior['reference']['original_llbc_sha256']
 selected,changes=select(json.loads(original.read_text()),'IncludeXor');assert len(changes)==4
 path=artifacts/'selected.llbc';serialized=json.dumps(selected,separators=(',',':'))+'\n'
 if path.exists():assert path.read_text()==serialized
 else:path.write_text(serialized)
 assert selected['translated']['fun_decls']==json.loads(original.read_text())['translated']['fun_decls']
 pins=json.loads((REF/'pins.json').read_text());a=(REF/pins['aeneas']['directory']/'aeneas').resolve()
 with tempfile.TemporaryDirectory(prefix='aes-zip-source-replay-')as tmp:
  tmp=pathlib.Path(tmp);args=[str(a),'-backend','lean',str(path),'-dest',str(tmp),'-subdir','/AesZipInvestigation/Generated/Baseline','-split-files','-namespace','RustCryptoAesZipDiagnostic','-warnings-as-errors','-no-progress-bar'];r=subprocess.run(args,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
  for name in ['Types.lean','Funs.lean']:assert(tmp/'AesZipInvestigation/Generated/Baseline'/name).read_bytes()==(REF/'AesZipInvestigation/Generated/Baseline'/name).read_bytes()
 subprocess.run(['python3',str(HERE/'prepare.py')],check=True)
 model=json.loads((HERE/'model-report.json').read_text());assert model['passed']and model['pinned_Std_source_archive_verified']and not model['extracted_Zip_proof']
 for name,want in model['source_sha256'].items():assert sha(ROOT/name)==want,name
 modules=['AesZipInvestigation/Generated/Baseline/Types']+['AesCtrBlockWork/ZipModelV1/'+m for m in ['StdBorrowZip','ActualRoundKey','ModelSemantics','RoundKeyReference']]
 for module in modules:
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(out),str(REF/(module+'.lean'))],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=30);assert r.returncode==0,r.stdout+r.stderr
 groups={'IndexedZipStd':['back_none','back_shared','back_cursors','back_length','back_updated','back_untouched','next_exhausted','next_valid'],'AesRoundKeyStdZip':['body_step','body_done','setup','actual_add_round_key','rejects_bad_key_length','numeric_words']}
 names=[ns+'.'+name for ns,values in groups.items()for name in values];audit=base.BUILD/'RoundKeyStdZipAxioms.lean';audit.write_text('import AesCtrBlockWork.ZipModelV1.ModelSemantics\nimport AesCtrBlockWork.ZipModelV1.RoundKeyReference\n'+''.join('#print axioms LibSignalReference.Candidate.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 sources=[pathlib.Path(__file__),REF/'AesAddRoundKeyWork/inspect_metadata.py',original,path,HERE/'model-report.json',HERE/'import-replay.json',*[REF/(module+'.lean')for module in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),foundation_axioms_only=True,actual_assertion_XOR_loop_bodies_retained=True,imports_only_replay=True,metadata_unused_zip_slots_removed=4,all_actual_fun_declarations_identical=True,actual_all8word_xor_agreement=True,trusted_Std_content_borrow_model=True,extracted_Zip_proof=False,whole_AES_CTR_proof=False,public_Rust_differential_cases=model['cases'],source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources}),indent=2)+'\n');print('PASS14 foundational endpoints +actual all8word XOR loop; trusted indexed Std boundary, not extracted Zip proof')
if __name__=='__main__':main()
