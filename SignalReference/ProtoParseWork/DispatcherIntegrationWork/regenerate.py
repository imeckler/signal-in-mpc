#!/usr/bin/env python3
import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];MESSAGE=HERE.parent/'MessageReferenceWork'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
build=json.loads((MESSAGE/'FnItemRound2/build-report.json').read_text());binary=ROOT/build['binary_path'];assert sha(binary)==build['binary_sha256']
llbc=HERE/'Artifacts/dispatch_error_models/prost.llbc'
command=[str(binary),'-backend','lean',str(llbc),'-dest',str(ROOT/'SignalReference'),'-subdir','/ProtoParseWork/DispatcherIntegrationWork/Generated','-split-files','-namespace','SignalMessageIntegration','-warnings-as-errors','-no-progress-bar','-sequential']
with (HERE/'translate.log').open('w') as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
report={'candidate_only':True,'command':command,'exit_code':r.returncode,'binary_sha256':sha(binary),'llbc_sha256':sha(llbc),'generated_sha256':{p.name:sha(p) for p in (HERE/'Generated').glob('*.lean') if p.name not in ['TypesExternal.lean','FunsExternal.lean']},'manual_generated_edits':False}
(HERE/'translation.json').write_text(json.dumps(report,indent=2)+'\n');raise SystemExit(r.returncode)
