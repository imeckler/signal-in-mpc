#!/usr/bin/env python3
import hashlib,json,os,pathlib,re,subprocess,tarfile
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[1];BUILD=HERE/'Build';cache=pathlib.Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages');paths=[BUILD,ROOT/'.lake/build/lib/lean',ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean'for p in cache.iterdir()if(p/'.lake/build/lib/lean').is_dir()];environment=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)))
def main():
 pins=json.loads((ROOT/'SignalReference/pins.json').read_text());archive=ROOT/'.deps/libsignal-v0.106.1.tar.gz';assert hashlib.sha256(archive.read_bytes()).hexdigest()==pins['libsignal']['archive_sha256']
 with tarfile.open(archive)as release:
  prefix=release.getmembers()[0].name.split('/')[0]
  for name in ['Cargo.lock','Cargo.toml','rust/protocol/Cargo.toml','rust/protocol/src/crypto.rs']:
   assert release.extractfile(prefix+'/'+name).read()==(ROOT/'.deps/libsignal-v0.106.1'/name).read_bytes()
 extraction=json.loads((HERE/'Artifacts/remaining_pinned_v1/inventory.json').read_text());assert extraction['charon_exit_code']==0 and extraction['actual_zeroize_feature_enabled'] and not extraction['has_errors']
 original=json.loads((HERE/'Artifacts/remaining_pinned_v1/ctr.llbc').read_text());selected=json.loads((HERE/'Artifacts/ConversionFinal/conversion.llbc').read_text());restored=json.loads(json.dumps(selected));restored['translated']['ordered_decls']=original['translated']['ordered_decls'];assert restored==original
 assert selected['translated']['ordered_decls']==[{'Type':{'NonRec':7}},{'Type':{'NonRec':8}},{'Fun':{'NonRec':27}}]
 review=json.loads((HERE/'Artifacts/ConversionFinal/review.json').read_text());assert review['aeneas_exit_code']==0
 digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 assert digest(HERE/'Artifacts/remaining_pinned_v1/ctr.llbc')==review['original_llbc_sha256'] and digest(HERE/'Artifacts/ConversionFinal/conversion.llbc')==review['selected_llbc_sha256']
 for name,want in extraction['source_sha256'].items():assert digest(ROOT/name)==want
 for name,want in review['generated_sha256'].items():assert digest(ROOT/'SignalReference'/name)==want
 for module in ['Generated/ConversionFinal/Types','Generated/ConversionFinal/Funs','ConversionReference']:
  out=BUILD/('CtrReferenceV1Work/'+module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);subprocess.run(['lean','-o',str(out),str(HERE/(module+'.lean'))],cwd=ROOT/'SignalReference',env=environment,check=True)
 audit=HERE/'ConversionChecks.lean';names=['max_value','actual_widen_ok','actual_widen_value','remaining_prefix_success','remaining_prefix_never_err','exhaustion_exact','bounded_ss_blocks','initial_counter_capacity'];audit.write_text('import CtrReferenceV1Work.ConversionReference\n'+''.join('#print axioms LibSignalReference.Candidate.CtrConversionV1.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=ROOT/'SignalReference',env=environment,text=True)
 assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'conversion-axioms.txt').write_text(text);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();files=[HERE/'Artifacts/remaining_pinned_v1/inventory.json',HERE/'Artifacts/ConversionFinal/review.json',pathlib.Path(__file__),HERE/'ConversionReference.lean',audit,HERE/'select_conversion.py',*list((HERE/'Generated/ConversionFinal').glob('*.lean'))]
 (HERE/'conversion-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),foundation_axioms_only=True,actual_unchanged_generated_u32_usize_conversion=True,pinned_release_caller_and_lock_verified=True,ctr_zeroize_feature_observed=True,remaining_prefix_arithmetic_model_relative=True,remaining_prefix_err_unreachable=True,generic_Result_ok_Drop_assumed=False,full_actual_remaining_or_CTR_AES_HMAC_wrapper=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS: 8 foundation-only endpoints; actual cast and bounded remaining prefix')
if __name__=='__main__':main()
