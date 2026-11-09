#!/usr/bin/env python3
"""Immutable isolated restore-test closure. Does not authorize account restore."""
import hashlib,json,pathlib,shutil
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def main():
 stage=ROOT/'.deps/private-canonical-restore-native/v1-candidate-1'
 if stage.exists():raise RuntimeError('preserve prior restore candidate')
 base=ROOT/'.deps/private-canonical-owner-native/v1-candidate-1';admission=ROOT/'.deps/private-record-admission-native/v1-candidate-1'
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 old=json.loads((HERE.parent/'canonical-native-report.json').read_text());assert old['passed'] and sha(base/'owner.manifest')==old['manifest_sha256']
 runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';runtime_receipt=ROOT/'handshake_backend/ExceptionWork/native-report.json';r=json.loads(runtime_receipt.read_text());assert r['passed'] and r['candidate_only'] and r['integrity_verified']
 key=str((runtime/'libSPDZ.so').relative_to(ROOT));assert sha(runtime/'libSPDZ.so')==r['source_product_sha256'][key]
 stage.mkdir(parents=True);files={}
 for source,name,target_name in [(base,'owner.manifest','base.manifest'),(admission,'admission.manifest','extension.manifest')]:
  for line in (source/name).read_text().splitlines()[1:]:
   digest,path=line.split(' ',1);assert sha(source/path)==digest
   if path in files:assert files[path]==digest
   else:
    target=stage/path;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source/path,target);files[path]=digest
  shutil.copyfile(source/name,stage/target_name)
 report=dict(prepared=True,candidate_only=True,normal_backend_promoted=False,native_MPC=False,full_account=False,quorum_recovery=False,stage=str(stage.relative_to(ROOT)),runtime=str(runtime.relative_to(ROOT)),runtime_library_sha256=sha(runtime/'libSPDZ.so'),exception_report_sha256=sha(runtime_receipt),original_native_report_sha256=sha(HERE.parent/'canonical-native-report.json'),source_archive_logs=old['logs'],base_manifest_sha256=sha(stage/'base.manifest'),extension_manifest_sha256=sha(stage/'extension.manifest'),source_sha256={str(pathlib.Path(__file__).relative_to(ROOT)):sha(pathlib.Path(__file__))})
 (HERE/'restore-prepare-report.json').write_text(json.dumps(report,indent=2)+'\n');print(stage)
if __name__=='__main__':main()
