#!/usr/bin/env python3
"""Exact root CLI numeric equivalence for completed KEM components."""
import json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_root_export import digest,numeric_digest

def main():
    subprocess.run(['lake','build','emit_mpc'],cwd=ROOT,check=True)
    sources=[ROOT/'Main.lean',ROOT/'TlsMpc.lean',ROOT/'TlsMpc/Signal/Export.lean',Path(__file__)];snapshot={str(p.relative_to(ROOT)):digest(p) for p in sources}
    profiles=[]
    for category in ('keccak','mlkem-arithmetic','mlkem-ntt','mlkem-encoding','mlkem-sample','kem-wire'):
        report_path=ROOT/f'benchmarks/results/lean-signal-{category}-checks.json';report=json.loads(report_path.read_text())
        for path,h in report['source_sha256'].items():assert digest(ROOT/path)==h,path
        for row in report['cases']:
            matches=[p for p in (ROOT/f'.deps/signal-{category}-artifacts').glob('*.json') if not p.name.endswith('-fixtures.json') and digest(p)==row['artifact_sha256']]
            assert len(matches)==1,(category,row);reference=matches[0]
            if category=='mlkem-arithmetic':args=['signal-mlkem',row['mode'],str(row['eta'])]
            elif category=='mlkem-sample':args=['signal-mlkem-sample',row['mode'],str(row['count']),str(row['pairs'])]
            else:args=reference.stem.split('-')
            if category=='keccak':
                name=reference.stem.removeprefix('signal-keccak-');mode,size,count=name.rsplit('-',2);args=['signal-keccak',mode,size,count]
            elif category=='mlkem-ntt':args=['signal-mlkem-ntt',row['mode']]
            elif category=='mlkem-encoding':args=['signal-mlkem-encoding',row['mode'],str(row['width'])]
            elif category=='kem-wire':args=['signal-kem-wire',row['mode'],row['variant']]
            profiles.append((args,reference,report_path))
    for mode in ('add','sub'):
        profiles.append((['signal-mlkem-poly',mode],ROOT/f'.deps/signal-mlkem-poly-artifacts/signal-mlkem-poly-{mode}.json',None))
    rows=[];directory=ROOT/'.deps/signal-root-kem-artifacts';directory.mkdir(exist_ok=True)
    for args,reference,report in profiles:
        path=directory/('-'.join(args)+'.json')
        with path.open('w') as out:subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),*args],stdout=out,check=True,timeout=600)
        assert numeric_digest(path)==numeric_digest(reference),args
        rows.append({'arguments':args,'numeric_sha256':numeric_digest(path),'independent_export_sha256':digest(reference),'independent_report_sha256':digest(report) if report else None});print('PASS',*args,flush=True)
    invalid=[['signal-keccak','sha3-256','0','64'],['signal-keccak','shake128','4097','32'],['signal-mlkem','noise','1'],['signal-mlkem-ntt','invalid'],['signal-mlkem-poly','invalid'],['signal-mlkem-encoding','encode','0'],['signal-mlkem-encoding','encode','13'],['signal-mlkem-sample','matrix','257','168'],['signal-mlkem-sample','matrix','256','337'],['signal-kem-wire','encapsulate','mlkem512']]
    for args in invalid:
        result=subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),*args],capture_output=True,text=True,timeout=30);assert result.returncode!=0 and not result.stdout,args
    assert snapshot=={str(p.relative_to(ROOT)):digest(p) for p in sources}
    result={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':snapshot,'profiles':rows,'profile_count':len(rows),'invalid_shapes_rejected':len(invalid),'all_numeric_exports_identical':True,'native_mpc_executed':False}
    (ROOT/'benchmarks/results/lean-signal-kem-root-export-checks.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
