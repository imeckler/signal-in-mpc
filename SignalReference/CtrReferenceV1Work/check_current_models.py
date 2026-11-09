#!/usr/bin/env python3
"""Intermediate actual CTR loop extraction/model replay, NOT full CTR refinement."""
import hashlib,importlib.util,json,pathlib,re,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('conversion',HERE/'check_conversion.py');env=importlib.util.module_from_spec(spec);spec.loader.exec_module(env)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 art=HERE/'Artifacts/CurrentModelViewsV1';gen=HERE/'Generated/CurrentModelViewsV1'
 inventory=json.loads((art/'inventory.json').read_text());assert inventory['charon_exit_code']==0 and sha(art/'ctr.llbc')==inventory['llbc_sha256']
 pins=json.loads((ROOT/'SignalReference/pins.json').read_text());aeneas=(ROOT/'SignalReference'/pins['aeneas']['directory']/'aeneas').resolve()
 with tempfile.TemporaryDirectory(prefix='ctr-source-replay-')as tmp:
  tmp=pathlib.Path(tmp);named=tmp/'named.llbc'
  subprocess.run(['python3',str(HERE/'replay_mono_names.py'),str(art/'ctr.llbc'),str(named)],check=True,capture_output=True)
  assert named.read_bytes()==(art/'named.llbc').read_bytes()
  args=[str(aeneas),'-backend','lean',str(named),'-dest',str(tmp),'-subdir','/CtrReferenceV1Work/Generated/CurrentModelViewsV1','-split-files','-namespace','CtrCurrentV1','-warnings-as-errors','-no-progress-bar']
  result=subprocess.run(args,cwd=ROOT,capture_output=True,text=True,timeout=60);assert result.returncode==0,result.stdout+result.stderr
  replay=tmp/'CtrReferenceV1Work/Generated/CurrentModelViewsV1'
  for name in ['Types.lean','Funs.lean','FunsExternal_Template.lean']:assert(replay/name).read_bytes()==(gen/name).read_bytes(),name
 before=sha(gen/'FunsExternal.lean');subprocess.run(['python3',str(HERE/'bind_current_models.py')],check=True,capture_output=True);assert sha(gen/'FunsExternal.lean')==before
 for name in ['Generated/CurrentModelViewsV1/Types','Generated/CurrentModelViewsV1/FunsExternal','Generated/CurrentModelViewsV1/Funs','CurrentReference']:
  out=env.BUILD/'CtrReferenceV1Work'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  subprocess.run(['lean','-o',str(out),str(HERE/(name+'.lean'))],cwd=ROOT/'SignalReference',env=env.environment,check=True,capture_output=True)
 audit=env.BUILD/'CurrentAxioms.lean';audit.write_text('import CtrReferenceV1Work.CurrentReference\n#print axioms LibSignalReference.Candidate.CtrCurrent.chunk_size\n#print axioms LibSignalReference.Candidate.CtrCurrent.body_done\n')
 text=subprocess.check_output(['lean',str(audit)],cwd=ROOT/'SignalReference',env=env.environment,text=True)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 files=[pathlib.Path(__file__),HERE/'CurrentReference.lean',HERE/'bind_current_models.py',HERE/'replay_mono_names.py',*gen.glob('*.lean'),art/'inventory.json',art/'ctr.llbc',art/'named.llbc']
 (HERE/'current-model-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,actual_generated_Funs_Types_replayed_unchanged=True,name_only_LLBC_replay=True,kernel_endpoints=2,foundation_axioms_only=True,model_boundary='Official Aeneas Array/Slice/Range functional content; hybrid raw views/default bound to fixed valid arrays; pinned native little endian; address/layout/Drop/resource effects excluded',full_current_block_refinement=False,full_remaining_stream_AES_HMAC_refinement=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n')
 print('PASS unchanged generated actual CTR loop, explicit Std models, two kernel endpoints; full loop agreement OPEN')
if __name__=='__main__':main()
