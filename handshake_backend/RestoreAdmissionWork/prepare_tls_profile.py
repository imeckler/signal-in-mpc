#!/usr/bin/env python3
"""Freeze PUBLIC complete worker closure before any account certification.
Never copy Player-Data, local archives, journals, secret shares or runtime state.
"""
import hashlib,json,pathlib,shutil
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 stage=ROOT/'.deps/tls-authorized-account-native/v1-candidate-1';assert not stage.exists(),'preserve existing candidate'
 old=ROOT/'benchmarks/results/raw/tls-native-text-throughput-batch/dab1d7d574ab28f9'
 receipt=json.loads((ROOT/'benchmarks/results/tls-native-text-throughput-batch.json').read_text());boot=old/'programs.manifest';assert sha(boot)==receipt['source_and_product_sha256'][str(boot.relative_to(ROOT))]
 manifests=[(old/'working',boot),
  (ROOT/'.deps/private-variable-conversation-native/260-80-0-0/batch-2-sha-gate-efficient',ROOT/'.deps/private-variable-conversation-native/260-80-0-0/batch-2-sha-gate-efficient/service.manifest'),
  (ROOT/'.deps/private-record-binding-native/v1-candidate-1',ROOT/'.deps/private-record-binding-native/v1-candidate-1/binding.manifest'),
  (ROOT/'.deps/private-account-admission-native/v2-candidate-1',ROOT/'.deps/private-account-admission-native/v2-candidate-1/account.manifest'),
  (ROOT/'.deps/tls-outbox-remask-native/v1-candidate-1',ROOT/'.deps/tls-outbox-remask-native/v1-candidate-1/remask.manifest')]
 # Validate every input before publishing a new stage/manifest.
 files={};source_pins={}
 for source,manifest in manifests:
  assert manifest.read_text().splitlines()[0]=='tls-mpc-pinned-files-v1';source_pins[str(manifest.relative_to(ROOT))]=sha(manifest)
  for line in manifest.read_text().splitlines()[1:]:
   digest,name=line.split(' ',1);path=pathlib.PurePosixPath(name);assert not path.is_absolute()and'..'not in path.parts
   assert name.startswith(('Programs/Functions/','Programs/Schedules/','Programs/Bytecode/','Worker-Public/'))
   assert sha(source/name)==digest,(name,'changed input')
   if name in files:assert files[name][0]==digest,(name,'immutable collision')
   else:files[name]=(digest,source/name)
 config_path=old/'working/Worker-Public/tls-shape-toolchain.json';config=json.loads(config_path.read_text());toolchain={}
 assert sha(pathlib.Path(config['python']['path']))==config['python']['sha256']
 for name,digest in config['files'].items():
  path=pathlib.PurePosixPath(name);assert not path.is_absolute()and'..'not in path.parts
  assert name.startswith(('Compiler/','backend_adapter/','handshake_backend/','Programs/Source/','Worker-Public/'))or name=='compile.py'
  source=old/'working'/name;assert sha(source)==digest,(name,'toolchain changed');toolchain[name]=(digest,source)
 stage.mkdir(parents=True)
 for name,(digest,source)in {**files,**toolchain}.items():
  if name in files and name in toolchain:assert files[name][0]==toolchain[name][0]
  target=stage/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);shutil.copymode(source,target);assert sha(target)==digest
 manifest=stage/'programs.manifest';manifest.write_text('tls-mpc-pinned-files-v1\n'+''.join(digest+' '+name+'\n'for name,(digest,_)in sorted(files.items())))
 assert not(stage/'Player-Data').exists()
 functions=[p for p in files if p.startswith('Programs/Functions/')]
 required=['signal_private_account_admit_v2_c1-','signal_private_record_bind_v1-','signal_private_variable_conversation_260_80_0_0-','signal_private_variable_batch_2_signal_private_variable_conversation_260_80_0_0-','tls_binary_tls_websocket_remask_1290-','signal_relay_upgrade_22-']
 assert all(any(pathlib.Path(p).name.startswith(prefix)for p in functions)for prefix in required)
 report={'prepared':True,'native_MPC_executed':False,'account_certificate_created':False,'stage':str(stage.relative_to(ROOT)),'manifest':str(manifest.relative_to(ROOT)),'manifest_sha256':sha(manifest),'input_manifest_sha256':source_pins,'pinned_files':len(files),'functions':len(functions),'archived_toolchain_files':len(toolchain),'copied_secret_state':False,'includes_historical_unused_public_functions':True,'scope':'Frozen public complete TLS/parser/upgrade/requestID/text/single+B2service/binding/c1accountvalidator/remask closure. Account genesis/head must certify THIS digest before any account import/provider capability. Runtime/worker source pins are a separate required execution receipt.'}
 (HERE/'tls-profile-report.json').write_text(json.dumps(report,indent=2)+'\n');(stage/'public-profile-receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'manifest':str(manifest),'sha256':sha(manifest),'files':len(files),'functions':len(functions)}))
if __name__=='__main__':main()
