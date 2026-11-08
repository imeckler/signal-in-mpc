#!/usr/bin/env python3
"""Actual unchanged constructor input through separately reviewed loop candidate."""
import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 binary=ROOT/'SignalReference/ProtoParseWork/SkipTranslatorWork/Bin/candidate'
 assert sha(binary)=='5ea6276549fac0be5c55ac6608ae8b4efa1dd1b147c15a988543871d8094bbec'
 llbc=HERE/'Artifacts/ContentConstructor/ss_content.llbc';inventory=json.loads((llbc.parent/'inventory.json').read_text())
 assert inventory['charon_exit_code']==0 and not inventory['has_errors'] and inventory['counts']['ordered_decls']>0 and sha(llbc)==inventory['llbc_sha256']
 dest=HERE/'LoopCandidate';dest.mkdir(exist_ok=True)
 command=[str(binary),'-backend','lean',str(llbc),'-dest',str(dest),'-subdir','/Generated','-split-files','-namespace','SealedSenderPackaging','-warnings-as-errors','-no-progress-bar']
 with (dest/'aeneas.log').open('w') as out:r=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 report={'candidate_only':True,'accepted_reference':False,'binary_sha256':sha(binary),'input_llbc_sha256':sha(llbc),'manual_generated_body_edits':False,'llbc_edits':False,'command':command,'exit_code':r.returncode,'script_sha256':sha(Path(__file__)),'generated_sha256':{str(p.relative_to(ROOT)):sha(p) for p in (dest/'Generated').glob('*.lean')}}
 (dest/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Actual constructor loop candidate exit',r.returncode,flush=True)
 return r.returncode
if __name__=='__main__':raise SystemExit(main())
