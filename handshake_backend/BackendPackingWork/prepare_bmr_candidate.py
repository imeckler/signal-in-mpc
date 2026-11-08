"""Fresh primary-source BMR component candidate; no application capability."""
from pathlib import Path
import hashlib,json,shutil
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent
BASE=ROOT/'.deps/tls-backend-diagnostic-runtime-v3/MP-SPDZ';DEST=ROOT/'.deps/tls-bmr128-candidate/MP-SPDZ'
def prepare():
 if DEST.exists():raise SystemExit('preserve existing BMR candidate')
 source={};products={}
 for p in BASE.rglob('*'):
  n=p.relative_to(BASE)
  if any(x in ['deps','local','Player-Data','Memory','Programs'] for x in n.parts)or not p.is_file():continue
  public_source=p.suffix in ['.h','.hpp','.cpp','.c','.S']or p.name in ['Makefile','CONFIG','CONFIG.mine']
  public_product=p.suffix in ['.o','.d']or p.name=='libSPDZ.so'
  if not(public_source or public_product):continue
  (source if public_source else products)[str(n)]=hashlib.sha256(p.read_bytes()).hexdigest()
  out=DEST/n;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,out)
 for directory in ['deps','local']:(DEST/directory).symlink_to((BASE/directory).resolve(),target_is_directory=True)
 p=DEST/'BMR/config.h';old=p.read_text();assert old.count('#define MAX_N_PARTIES 3')==1;p.write_text(old.replace('#define MAX_N_PARTIES 3','#define MAX_N_PARTIES 5'))
 report={'scope':'unverified BMR128 pure-binary component candidate; not mixed-Fp/session/lifecycle capability','base_source_sha256':source,'reused_public_build_product_sha256':products,'modified_source_sha256':{'BMR/config.h':hashlib.sha256(p.read_bytes()).hexdigest()},'planned_parties':5,'planned_threshold':2,'planned_statistical_security':128,'backend':'RealProgramParty<MaliciousShamirShare<gf2n_long>>','native_executed':False,'application_gate_opened':False}
 (WORK/'bmr-candidate-prepare.json').write_text(json.dumps(report,indent=2)+'\n');print(DEST)
if __name__=='__main__':prepare()
