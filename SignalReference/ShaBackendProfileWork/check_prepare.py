#!/usr/bin/env python3
"""Exercise actual compiler rejection and immutable profile artifact admission."""
from pathlib import Path
import json,os,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from signal_backend.VariableServiceWork import prepare
from signal_backend.VariableServiceWork.shape import VariableShape
shape=VariableShape(260,80,0,0)
with tempfile.TemporaryDirectory(prefix='sha-profile-admission-') as folder:
 base=Path(folder)
 for name,value in [('missing',{}),('reference',{'sha_profile':'reference'}),('latency',{'padding':'x'*100000,'sha_profile':'latency'})]:
  path=base/(name+'.json');path.write_text(json.dumps(value));assert prepare.artifact_profile(path)==value.get('sha_profile')
 runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 for name,target in [('Compiler',runtime/'Compiler'),('backend_adapter',ROOT/'backend_adapter'),('handshake_backend',ROOT/'handshake_backend'),('signal_backend',ROOT/'signal_backend')]: (base/name).symlink_to(target)
 (base/'compile.py').write_bytes((runtime/'compile.py').read_bytes())
 (base/'Programs/Source').mkdir(parents=True)
 (base/'Programs/Source/profile_guard.mpc').write_bytes((ROOT/'programs/signal_variable_service.mpc').read_bytes())
 image=ROOT/'.deps/sha-backend-profiles/latency-block.json'
 command=[sys.executable,'-B',str(base/'compile.py'),'-M','-X','-P',str(2**255-19),'profile_guard',str(ROOT/'.deps/relay-service-artifacts/x25519-field.json'),str(image),*map(str,shape.values),'reference']
 result=subprocess.run(command,cwd=base,capture_output=True,text=True,timeout=60)
 assert result.returncode!=0 and 'SHA artifact/profile mismatch' in result.stdout+result.stderr,result.stdout+result.stderr
 for selected in ['reference','latency']:
  folder=base/('sha-'+selected);folder.mkdir();target=folder/'private-conversation-260-80-none-none.json';target.write_text('{}')
 # An existing product lacking receipt must be preserved rather than overwritten.
 oldroot=prepare.ROOT;prepare.ROOT=base
 (base/'lean-toolchain').write_text('test')
 (base/'SignalReference/PrivateConversationWork').mkdir(parents=True)
 (base/'SignalReference/PrivateConversationWork/Export.lean').write_text('')
 (base/'.deps/private-hash-artifacts/sha-latency').mkdir(parents=True)
 product=base/'.deps/private-hash-artifacts/sha-latency/private-conversation-260-80-none-none.json';product.write_text('preserve')
 try:
  try:prepare.emit_profile_artifact(shape,'latency');raise AssertionError('missing receipt accepted')
  except RuntimeError as error:assert 'no immutable source receipt'in str(error)
  assert product.read_text()=='preserve'
 finally:prepare.ROOT=oldroot
print('profile routing, actual compiler mismatch, immutable admission passed')
