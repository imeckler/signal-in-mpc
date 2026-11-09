#!/usr/bin/env python3
"""Unified actual CTR state-machine replay; explicit typed Std value models, not full AES/stream wrapper."""
import hashlib,importlib.util,json,pathlib,re,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('conversion',HERE/'check_conversion.py');env=importlib.util.module_from_spec(spec);spec.loader.exec_module(env)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 art=HERE/'Artifacts/StateUnifiedV1';gen=HERE/'Generated/StateUnifiedV1'
 inventory=json.loads((art/'inventory.json').read_text());assert inventory['charon_exit_code']==0 and sha(art/'ctr.llbc')==inventory['llbc_sha256']
 for name,want in inventory['source_sha256'].items():assert sha(ROOT/name)==want,name
 for name in ['Cargo.toml','lib.rs']:assert sha(HERE/'Source'/name)==inventory['source_sha256'][str((HERE/'Source'/name).relative_to(ROOT))]
 assert 'features=["zeroize"]'in(HERE/'Source/Cargo.toml').read_text().replace(' ','')
 pins=json.loads((ROOT/'SignalReference/pins.json').read_text());aeneas=(ROOT/'SignalReference'/pins['aeneas']['directory']/'aeneas').resolve()
 with tempfile.TemporaryDirectory(prefix='ctr-source-replay-')as tmp:
  tmp=pathlib.Path(tmp);named=tmp/'named.llbc'
  subprocess.run(['python3',str(HERE/'replay_mono_names.py'),str(art/'ctr.llbc'),str(named)],check=True,capture_output=True)
  assert named.read_bytes()==(art/'named.llbc').read_bytes()
  args=[str(aeneas),'-backend','lean',str(named),'-dest',str(tmp),'-subdir','/CtrReferenceV1Work/Generated/StateUnifiedV1','-split-files','-namespace','CtrStateV1','-warnings-as-errors','-no-progress-bar']
  result=subprocess.run(args,cwd=ROOT,capture_output=True,text=True,timeout=60);assert result.returncode==0,result.stdout+result.stderr
  replay=tmp/'CtrReferenceV1Work/Generated/StateUnifiedV1'
  for name in ['Types.lean','Funs.lean','FunsExternal_Template.lean']:assert(replay/name).read_bytes()==(gen/name).read_bytes(),name
 before=sha(gen/'FunsExternal.lean');subprocess.run(['python3',str(HERE/'bind_state_models.py')],check=True,capture_output=True);assert sha(gen/'FunsExternal.lean')==before
 for name in ['Generated/ConversionFinal/Types','Generated/ConversionFinal/Funs','ConversionReference','Generated/StateUnifiedV1/Types','Generated/StateUnifiedV1/FunsExternal','Generated/StateUnifiedV1/Funs','StateReference','StateInitReference','StateRemainingReference','StateCircuitAgreement','StreamCounterReference','StdSuccessReference']:
  out=env.BUILD/'CtrReferenceV1Work'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  result=subprocess.run(['lean','-o',str(out),str(HERE/(name+'.lean'))],cwd=ROOT/'SignalReference',env=env.environment,capture_output=True,text=True)
  assert result.returncode==0,result.stdout+result.stderr
 groups={
 'CtrState':['chunk_size','body_done','body_step0','body_step1','body_step2','body_step3','actual_current_zero_nonce','actual_next_zero_nonce','increment_value','increment_no_wrap','increment_wrap','counter_circuit','actual_current_circuit'],
 'CtrStateInit':['body_step0','body_step1','body_step2','body_step3','body_done','actual_from_zero_nonce'],
 'CtrStateRemaining':['actual_body_remaining','exhaustion_exact','supported_blocks'],
 'CtrStreamCounter':['run_counters','remaining_authorizes','sealed_sender_profile_bound'],
 'CtrStdSuccess':['literal_same','result_ok_success','expect_success','slice_copy_four','actual_widen_success']}
 names=[ns+'.'+name for ns,values in groups.items()for name in values]
 audit=env.BUILD/'StateAxioms.lean';audit.write_text('import CtrReferenceV1Work.StreamCounterReference\nimport CtrReferenceV1Work.StdSuccessReference\n'+''.join('#print axioms LibSignalReference.Candidate.'+n+'\n'for n in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=ROOT/'SignalReference',env=env.environment,text=True)
 assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 files=[pathlib.Path(__file__),*[HERE/(n+'.lean')for n in ['StateReference','StateInitReference','StateRemainingReference','StateCircuitAgreement','StreamCounterReference','StdSuccessReference']],HERE/'bind_state_models.py',HERE/'replay_mono_names.py',*gen.glob('*.lean'),art/'inventory.json',art/'ctr.llbc',art/'named.llbc']
 (HERE/'state-model-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,actual_generated_Funs_Types_replayed_unchanged=True,name_only_LLBC_replay=True,kernel_endpoints=len(names),foundation_axioms_only=True,model_boundary='Official Std Array/Slice/Range content; fixed typed Result expect/ok success-only models; actual widening leaf reused; native little endian; address/layout/Drop/resource effects excluded',actual_zero_nonce_current_block_circuit_agreement=True,actual_next_nonce_preservation_and_increment_wrap=True,actual_from_zero_nonce_body_relative_to_typed_Std_models=True,actual_remaining_body_relative_to_typed_Std_models=True,actual_repeated_next_calls_circuit_sequence=True,generic_Result_Drop_proved=False,actual_StreamCipherCore_wrapper_proved=False,generic_nonce_current_block_refinement=False,full_remaining_stream_AES_HMAC_refinement=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n')
 print('PASS 30 foundation-only CTR state/composition endpoints; explicit typed Std success boundaries; AES/actual stream wrapper OPEN')
if __name__=='__main__':main()
