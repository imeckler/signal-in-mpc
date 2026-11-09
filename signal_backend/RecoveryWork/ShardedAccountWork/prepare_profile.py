#!/usr/bin/env python3
"""Freeze PUBLIC closure for a genuinely NEW fixture account before genesis."""
import hashlib,json,pathlib,shutil
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 base=ROOT/'.deps/tls-authorized-account-native/v1-candidate-2';assert sha(base/'programs.manifest')=='a41455546132840185159061c880095c3ac2111b55d6862afe0419091e74e006'
 stage=ROOT/'.deps/tls-sharded-account-native/v1-candidate-1';assert not stage.exists(),'preserve existing account/program domain'
 manifests=[base/'programs.manifest',ROOT/'.deps/private-reusable-outbox-native/v1-candidate-1/outbox.manifest',ROOT/'.deps/private-shard-validation-native/v1-candidate-3/validation.manifest',ROOT/'.deps/private-shard-route-native/v1-candidate-2/route.manifest']
 files={};pins={}
 for manifest in manifests:
  lines=manifest.read_text().splitlines();assert lines[0]=='tls-mpc-pinned-files-v1';pins[str(manifest.relative_to(ROOT))]=sha(manifest)
  for line in lines[1:]:
   digest,name=line.split(' ',1);path=pathlib.PurePosixPath(name);assert not path.is_absolute()and'..'not in path.parts and name.startswith(('Programs/Functions/','Programs/Schedules/','Programs/Bytecode/','Worker-Public/'))
   source=manifest.parent/name;assert sha(source)==digest
   if name in files:assert files[name][0]==digest,('immutable collision',name)
   else:files[name]=(digest,source)
 config=json.loads((base/'Worker-Public/tls-shape-toolchain.json').read_text());assert sha(pathlib.Path(config['python']['path']))==config['python']['sha256'];toolchain={}
 for name,digest in config['files'].items():
  path=pathlib.PurePosixPath(name);assert not path.is_absolute()and'..'not in path.parts;source=base/name;assert sha(source)==digest;toolchain[name]=(digest,source)
 stage.mkdir(parents=True)
 for name,(digest,source)in {**toolchain,**files}.items():
  if name in toolchain and name in files:assert toolchain[name][0]==files[name][0]
  target=stage/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);shutil.copymode(source,target);assert sha(target)==digest
 manifest=stage/'programs.manifest';manifest.write_text('tls-mpc-pinned-files-v1\n'+''.join(digest+' '+name+'\n'for name,(digest,_)in sorted(files.items())))
 names=[pathlib.Path(name).name for name in files if name.startswith('Programs/Functions/')]
 required=['signal_private_variable_conversation_260_80_0_0-','signal_private_variable_batch_2_signal_private_variable_conversation_260_80_0_0-','signal_private_record_bind_v1-','tls_binary_tls_websocket_remask_1290-','signal_private_shard_validate_v1_global-','signal_private_shard_validate_v1_conversation-']+[f'signal_private_reusable_outbox_v1_o{i}-'for i in range(4)]+[f'signal_private_shard_route_v1_o{i}-'for i in range(4)]
 assert all(any(n.startswith(prefix)for n in names)for prefix in required);assert not(stage/'Player-Data').exists()
 report=dict(prepared=True,NEW_fixture_domain_only=True,old_head3_untouched=True,private_account_state_copied=False,account_certificate_created=False,native_MPC=False,stage=str(stage.relative_to(ROOT)),manifest_sha256=sha(manifest),input_manifest_sha256=pins,pinned_files=len(files),functions=len(names),toolchain_files=len(toolchain),source_sha256=sha(pathlib.Path(__file__)))
 (HERE/'profile-report.json').write_text(json.dumps(report,indent=2)+'\n');(stage/'public-profile-receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
