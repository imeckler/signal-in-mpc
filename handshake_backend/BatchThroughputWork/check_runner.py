#!/usr/bin/env python3
"""Runner guards and immutable selected-profile cache/loader checks; no MPC."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'scripts'))
from check_native_text_mux_profile import provision,digest
script=ROOT/'scripts/check_native_text_mux_profile.py'
for arguments,reason in [(['--execution','batch'],'requires explicit pinned closure'),(['--rounds','4'],'requires unique result name'),(['--result-name','../escape'],'invalid result name')]:
 result=subprocess.run([sys.executable,str(script),*arguments],cwd=ROOT,capture_output=True,text=True)
 assert result.returncode!=0 and reason in result.stderr,(arguments,result.stderr)
stage=ROOT/'.deps/throughput-provision-check-v1';selected=ROOT/'.deps/private-variable-conversation-native/260-80-0-0/sha-latency/service.manifest'
assert (stage/'programs.manifest').exists(),'run the archived-cache provisioning check first'
# Reject an unknown replacement; the old known descriptor is the ONLY allowed
# cache substitution. Restore public fixture bytes even if assertion fails.
name=next(line.split(' ',1)[1]for line in selected.read_text().splitlines()[1:]if ' Programs/Functions/signal_private_variable_conversation_'in line)
target=stage/name;before=target.read_bytes()
try:
 target.write_bytes(b'unknown public descriptor fixture')
 try:provision(stage,selected);raise AssertionError('unknown collision accepted')
 except AssertionError as error:assert 'public closure collision'in str(error)
finally:target.write_bytes(before)
with tempfile.TemporaryDirectory(prefix='tls-runner-loader-')as folder:
 path=Path(folder);library=ROOT/'.deps/tls-backend-diagnostic-runtime-v4/MP-SPDZ/libSPDZ.so';(path/'libSPDZ.so').symlink_to(library)
 result=subprocess.run([str(ROOT/'.deps/tls-backend-diagnostic-runtime-v4/tls-text-throughput-fixture-worker')],cwd=path,capture_output=True,text=True)
 assert result.returncode==2,(result.returncode,result.stderr)
report={'passed':True,'native_MPC_executed':False,'public_cache_actual_provisioning_verified':True,'unknown_function_collision_rejected':True,'selected_runtime_loader_invalid_argc_check':True,'scope':'Historical completed latency closure used ONLY as a public provisioning fixture; no latency native run. Equal-work8text gateefficient sequential/batch execution remains pending.','source_sha256':{str(p.relative_to(ROOT)):digest(p)for p in [script,ROOT/'handshake_backend/PublicMetrics.h',ROOT/'handshake_backend/BatchThroughputWork/TextExtendedMuxFixtureFactory.cpp',ROOT/'handshake_backend/BatchThroughputWork/Makefile',Path(__file__)]},'public_provision_manifest_sha256':digest(stage/'programs.manifest'),'fixture_commit':'1e7667a'}
Path(__file__).with_name('runner-report.json').write_text(json.dumps(report,indent=2)+'\n');print('runner guards, actual cache collision, selected runtime loader passed; no MPC')
