#!/usr/bin/env python3
"""Public configuration/codec checks; never runs an MPC protocol."""
import hashlib,json,pathlib,subprocess
root=pathlib.Path(__file__).resolve().parents[2]
runtime=root/'.deps/tls-backend-diagnostic-runtime-v4/MP-SPDZ'
binary=runtime.parent/'tls-small-field-guard'
cases=[]
for degree,security,rejected in [(8,128,1),(40,128,1),(128,128,0),(40,40,0)]:
    p=subprocess.run([str(binary),str(degree),str(security),str(rejected)],cwd=runtime,text=True,capture_output=True,check=True)
    result=json.loads(p.stdout)
    assert result['public_field_codec_bytes']==(8 if degree<=64 else 16)
    cases.append(result)
paths=['Math/gf2n.h','Protocols/mac_key.hpp','Protocols/MaliciousRepPrep.hpp','Protocols/SpdzWise.hpp','GC/MaliciousCcdShare.h','GC/MaliciousCcdSecret.h','GC/CcdPrep.h']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'scope':'public field-size guard and codec only; no parties, preprocessing, authentication or MPC security validation',
'upstream_revision':'113c4e47dd94bca9ecab029d2f0abe649bea5c52','runtime':'isolated diagnostic v4; unchanged',
'cases':cases,'source_hashes':{p:sha(runtime/p) for p in paths},
'fixture_hashes':{p.name:sha(p) for p in [pathlib.Path(__file__),pathlib.Path(__file__).with_name('field_guard.cpp')]},
'binary_sha256':sha(binary),'production_configuration_changed':False}
pathlib.Path(__file__).with_name('guard-report.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS 4 public configuration/codec cases; no MPC executed')
