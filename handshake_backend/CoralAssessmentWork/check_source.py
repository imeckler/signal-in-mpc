#!/usr/bin/env python3
"""Read-only archive/blob provenance and reachable-source assessment; not a security test."""
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
REV='9da23b7dca5ab8638428c91b65ebd405a65a046e'
BASE=ROOT/'.deps/boolean-backend-research'/('OpenCoral-'+REV)
TREE=pathlib.Path('/tmp/opencoral-tree.json')
def digest(b): return hashlib.sha256(b).hexdigest()
def main():
 tree=json.loads(TREE.read_text()); entries={e['path']:e for e in tree['tree']}
 files={}
 for p in sorted(BASE.rglob('*')):
  if not p.is_file(): continue
  rel=p.relative_to(BASE).as_posix(); b=p.read_bytes()
  assert rel in entries,rel
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert blob==entries[rel]['sha'],rel
  files[rel]={'sha256':digest(b),'git_blob':blob,'bytes':len(b)}
 needles={
 'missing_mac_equation':('GC/RmfeMC.h','// [zico] Need to update'),
 'two_party_preprocessing':('TinyOT/tinyotprep.cpp','1 - this->P->my_num()'),
 'two_party_conversion':('Protocols/RmfeShareConverter.hpp','q[i] = input.finalize(0) + input.finalize(1)'),
 'two_party_normal_pairs':('GC/RmfeSharePrep.hpp','normals[i] = input.finalize(0) + input.finalize(1)'),
 'passive_auth_fole_argument':('GC/RmfeMultiplier.hpp','auth_ot_ext(generator.players[thread_num], BOTH, true'),
 'conversion_calls_destination_check':('Protocols/RmfeShareConverter.hpp','dst_mc->Check(P)'),
 'normal_pairs_call_check':('GC/RmfeSharePrep.hpp','MC->Check(P)'),
 }
 findings={}
 for key,(p,n) in needles.items():
  lines=(BASE/p).read_text().splitlines(); hits=[i+1 for i,l in enumerate(lines) if n in l]
  assert hits,key
  findings[key]={'path':p,'lines':hits}
 report={'revision':REV,'repository':'https://github.com/AntCPLab/OpenCoral','source_files':files,
 'submodules':{k:v['sha'] for k,v in entries.items() if v.get('mode')=='160000'},
 'findings':findings,'source_blob_verification':True,'native_execution':False,
 'malicious_backend_validated':False,'n5_t2_conversion_validated':False,
 'scope':'Selected exact upstream blobs; source reachability/provenance only. No MAC/triple/conversion tamper test and no protocol performance claim.'}
 out=pathlib.Path(__file__).with_name('source-report.json');out.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'verified_files':len(files),'findings':len(findings),'native_execution':False}))
if __name__=='__main__':main()
