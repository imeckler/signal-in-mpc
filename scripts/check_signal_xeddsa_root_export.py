#!/usr/bin/env python3
"""Verify root dispatch emits byte-identical frozen XEdDSA stage artifacts."""
import hashlib,json,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
WORK=ROOT/'SignalReference/XEdDsaWork'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 frozen=json.loads((WORK/'completion.json').read_text())
 rows=[]
 for report in ['report.json','challenge-report.json','binding-report.json']:
  data=json.loads((WORK/report).read_text())
  for row in data['profiles']:
   if row['profile'] not in {r['profile'] for r in rows}:rows.append(row)
 result=[]
 with tempfile.TemporaryDirectory(prefix='signal-xeddsa-root-') as tmp:
  for row in rows:
   name=row['profile'];args=name.removeprefix('signal-xeddsa-').split('-')
   reference=WORK/'Artifacts'/(name+'.json')
   assert sha(reference)==row['sha256'],name
   output=Path(tmp)/(name+'.json')
   with output.open('wb') as out:subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),'signal-xeddsa',*args],stdout=out,check=True,timeout=600)
   digest=sha(output);assert digest==row['sha256'],(name,digest,row['sha256'])
   result.append({'profile':name,'sha256':digest,'bytes':output.stat().st_size})
   print(name,'identical',flush=True)
 # Confirm unrelated TLS dispatch remains functional using its concrete nonce shape.
 tls=subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),'tls-nonce'],capture_output=True,check=True)
 assert json.loads(tls.stdout)['name']=='tls-nonce'
 report={'schema':1,'scope':'Root CLI byte-identical to frozen standalone XEdDSA stage exports; no mixed-runtime or actual Rust refinement claim.',
  'completion_sha256':sha(WORK/'completion.json'),'emitter_sha256':sha(ROOT/'.lake/build/bin/emit_mpc'),
  'sources':{p:sha(ROOT/p) for p in ['Main.lean','TlsMpc.lean','TlsMpc/Signal/XEdDsaExport.lean','SignalReference/XEdDsaExport.lean','scripts/check_signal_xeddsa_root_export.py']},
  'all_equal':True,'profile_count':len(result),'profiles':result,'tls_nonce_dispatch':True}
 (ROOT/'benchmarks/results/lean-signal-xeddsa-root-export.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
