#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[2];S=H.parent/'SkipTranslatorWork'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
binary=S/'Bin/candidate';receipt=json.loads((S/'candidate-build-report.json').read_text());assert sha(binary)==receipt['binary_sha256']
src=H/'Artifacts/driver/prost.llbc';command=[str(binary.resolve()),'-backend','lean',str(src.resolve()),'-dest',str(ROOT/'SignalReference'),'-subdir','/ProtoParseWork/FullParserV3Work/GeneratedDriver','-namespace','ActualMessageDriver','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'driver-translate.log').open('w') as f:r=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
report={'candidate_only':True,'exit_code':r.returncode,'command':command,'binary_sha256':sha(binary),'llbc_sha256':sha(src),'generated_sha256':{p.name:sha(p) for p in (H/'GeneratedDriver').glob('*.lean') if p.name not in ['TypesExternal.lean','FunsExternal.lean']},'manual_generated_body_edits':False}
(H/'driver-translation.json').write_text(json.dumps(report,indent=2)+'\n');raise SystemExit(r.returncode)
