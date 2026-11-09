#!/usr/bin/env python3
"""Replay actual AES entry source frontier; deliberately NOT an AES proof."""
import hashlib,json,pathlib,re,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parent;ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 art=HERE/'Artifacts/EncryptLeafBoundariesV1';gen=HERE/'Generated/EncryptNamedV1';original=json.loads((art/'report.json').read_text());assert original['charon_exit_code']==0 and not original['has_errors']and original['counts']['ordered_decls']
 assert sha(art/'aes.llbc')==original['llbc_sha256']
 pins=json.loads((REF/'pins.json').read_text());a=(REF/pins['aeneas']['directory']/'aeneas').resolve()
 with tempfile.TemporaryDirectory(prefix='aes-source-frontier-')as tmp:
  tmp=pathlib.Path(tmp);named=tmp/'named.llbc';subprocess.run(['python3',str(REF/'CtrReferenceV1Work/replay_mono_names.py'),str(art/'aes.llbc'),str(named)],check=True,capture_output=True)
  assert named.read_bytes()==(art/'named.llbc').read_bytes()
  # Actual partial-mono graph has item-name table aliases differing from declaration names.
  # This catches the previous inverse replay bug without changing any computations.
  rawzip=REF/'AesZipInvestigation/Artifacts/MutAll/add_round_key.llbc';zipout=tmp/'zip-named.llbc'
  subprocess.run(['python3',str(REF/'CtrReferenceV1Work/replay_mono_names.py'),str(rawzip),str(zipout)],check=True,capture_output=True)
  assert zipout.read_bytes()==(HERE/'Artifacts/AddRoundKeyMutNamedV1/named.llbc').read_bytes()
  args=[str(a),'-backend','lean',str(named),'-dest',str(tmp),'-subdir','/AesCtrBlockWork/Generated/EncryptNamedV1','-split-files','-namespace','RustCryptoAesCtrBlock','-warnings-as-errors','-no-progress-bar'];p=subprocess.run(args,capture_output=True,text=True,timeout=60);assert p.returncode==0,p.stdout+p.stderr
  for name in ['Types.lean','Funs.lean','FunsExternal_Template.lean']:assert(tmp/'AesCtrBlockWork/Generated/EncryptNamedV1'/name).read_bytes()==(gen/name).read_bytes()
 template=(gen/'FunsExternal_Template.lean').read_text();external=re.findall(r'axiom\s+([\w.]+)\s*:',template);leaves=[n for n in external if n.startswith('soft.fixslice.')];assert len(leaves)==9
 assert not(gen/'FunsExternal.lean').exists(),'No assumed crypto binding may be silently admitted'
 diagnostic=HERE/'Artifacts/AddRoundKeyMutTypeV1/diagnostic.log';assert 'InterpReduceCollapse.ml, line 1137'in diagnostic.read_text()
 for name in ['AddRoundKeyMutNamedV1','AddRoundKeyMutTypeV1']:
  r=json.loads((HERE/'Artifacts'/name/'report.json').read_text());assert r['aeneas_exit_code']==2 and r['accepted']==False
 files=[pathlib.Path(__file__),HERE/'extract.py',HERE/'extract_zip_type.py',REF/'CtrReferenceV1Work/replay_mono_names.py',art/'aes.llbc',art/'named.llbc',art/'named.names.json',art/'report.json',*gen.glob('*.lean'),diagnostic]
 report=dict(passed_source_replay=True,candidate_only=True,accepted_AES_refinement=False,actual_entry_body_translated=True,manual_generated_body_edits=False,name_only_LLBC_replay=True,unbound_actual_crypto_leaves=leaves,leaf_agreement_assumed=False,actual_add_round_key_loop_proved=False,actual_inv_bitslice_wrapper_proved=False,concrete_tool_boundary='lifetime-preserving actual mutable-Zip graph: pinned Aeneas InterpReduceCollapse.ml1137 marker-elimination sanity check; original opaque-Zip variant has unknown-region-mutability error',source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'frontier-report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS exact actual AES entry replay; 9 UNBOUND leaf dependencies; mutable-Zip translator boundary retained')
if __name__=='__main__':main()
