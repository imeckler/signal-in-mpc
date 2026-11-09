#!/usr/bin/env python3
"""Isolated composition of immutable service/binding closures and fixture check."""
import hashlib,json,pathlib,shutil,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
HERE=pathlib.Path(__file__).resolve().parent

def main():
 stage=ROOT/'.deps/private-canonical-owner-native/v1-candidate-1'
 if stage.exists():raise RuntimeError('preserve prior candidate stage')
 stage.mkdir(parents=True)
 service=ROOT/'.deps/private-variable-conversation-native/260-80-0-0/batch-2-sha-gate-efficient'
 binding=ROOT/'.deps/private-record-binding-native/v1-candidate-1'
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files={}
 for source,manifest in [(service,'service.manifest'),(binding,'binding.manifest')]:
  for line in (source/manifest).read_text().splitlines()[1:]:
   digest,path=line.split(' ',1);assert sha(source/path)==digest
   if path in files:assert files[path]==digest
   else:
    target=stage/path;target.parent.mkdir(parents=True,exist_ok=True)
    # Independent immutable copy; do not alter historical products.
    shutil.copyfile(source/path,target);files[path]=digest
 for folder in ['Compiler','backend_adapter','handshake_backend']:
  shutil.copytree(binding/folder,stage/folder,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 shutil.copyfile(binding/'compile.py',stage/'compile.py')
 source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(ROOT/'programs/signal_canonical_fixture_equal.mpc',source/'signal_canonical_fixture_equal.mpc')
 with (stage/'equal-compile.log').open('w')as out:subprocess.run([sys.executable,'-B','compile.py','-M','-X','signal_canonical_fixture_equal','53488'],cwd=stage,stdout=out,stderr=subprocess.STDOUT,check=True,timeout=120)
 descriptor='signal_canonical_fixture_equal_53488-sbv:[106976x1]-sbv:[8x1]'
 equality=build(stage,[descriptor]);all_files=dict(files)
 for line in equality.splitlines()[1:]:
  digest,path=line.split(' ',1);assert path not in all_files or all_files[path]==digest;all_files[path]=digest
 manifest=stage/'owner.manifest';manifest.write_text('tls-mpc-pinned-files-v1\n'+''.join(v+' '+k+'\n'for k,v in sorted(all_files.items())))
 report=dict(prepared=True,native_MPC=False,provider_admission=False,manifest_sha256=sha(manifest),upstream_manifest_sha256={str(p.relative_to(ROOT)):sha(p)for p in [service/'service.manifest',binding/'binding.manifest']},source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),ROOT/'programs/signal_canonical_fixture_equal.mpc']})
 (HERE/'canonical-native-prepare-report.json').write_text(json.dumps(report,indent=2)+'\n');print(manifest)
if __name__=='__main__':main()
