#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parent;ROOT=H.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['lake','build','TlsMpc.Signal.ProtoParseProofs'],cwd=ROOT,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
r=subprocess.run([sys.executable,str(H/'check.py')],text=True,capture_output=True)
log=r.stdout+r.stderr;(H/'audit.log').write_text(log);r.check_returncode()
entries=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log,re.S)
new=[e for e in entries if e[0].startswith(('ParserErrorStateV2.','TlsMpc.Signal.ProtoParse.'))]
assert len(new)>=18,len(new)
for name,axs in entries:assert {a.strip() for a in axs.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'},(name,axs)
files=[ROOT/'TlsMpc/Signal/ProtoParse.lean',ROOT/'TlsMpc/Signal/ProtoParseProofs.lean']
files += [ROOT/'.deps/libsignal-vendor/prost-0.14.4/src'/name for name in ['encoding.rs','encoding/varint.rs','message.rs']]
files += [p for p in H.rglob('*') if p.is_file() and not any(part in ['Build','.lake','__pycache__','Artifacts'] for part in p.relative_to(H).parts) and p.suffix in ['.lean','.py','.json','.toml','.rs','.lock'] and p.name not in ['proof-report.json','lake-manifest.json']]
report={'candidate_only':True,'kernel_exit_code':0,'new_audited_endpoints':len(new),'all_logged_endpoints':len(entries),'allowed_axioms':['propext','Classical.choice','Quot.sound'],'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(files)},'full_actual_rust_parser_refinement':False,'skip_totality_proved':False,'native_mpc_executed':False}
(H/'proof-report.json').write_text(json.dumps(report,indent=2)+'\n');print(f'{len(new)} v2/compiler endpoints pass; foundational axioms only')
