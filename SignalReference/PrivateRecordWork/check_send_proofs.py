#!/usr/bin/env python3
"""Kernel/axiom audit for model-relative private record send compilation."""
import hashlib,json,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
SOURCES=['TlsMpc/Signal/PrivateRecordRestoreV1Proofs.lean','TlsMpc/Signal/PrivateRecordProjectionV1Proofs.lean','TlsMpc/Signal/PrivateRecordOperationsV1Proofs.lean','TlsMpc/Signal/PrivateRecordSendV1Proofs.lean','TlsMpc/Signal/PrivateRecordSnapshotV1Proofs.lean','SignalReference/PrivateRecordWork/SendChecks.lean']
def main():
    subprocess.run(['lake','build','TlsMpc.Signal.PrivateRecordRestoreV1Proofs'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
    run=subprocess.run(['lake','env','lean',SOURCES[-1]],cwd=ROOT,text=True,capture_output=True,check=True)
    audit=run.stdout
    entries=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",audit,re.S)
    assert len(entries)==13,(audit,entries)
    for name,axioms in entries:
        assert set(x.strip() for x in axioms.split(',')) <= {'propext','Classical.choice','Quot.sound'},(name,axioms)
    pending=[ROOT/s for s in SOURCES]; closure={}
    while pending:
        path=pending.pop(); relative=str(path.relative_to(ROOT))
        if relative in closure: continue
        closure[relative]=hashlib.sha256(path.read_bytes()).hexdigest()
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                for module in line[7:].split():
                    target=ROOT/(module.replace('.','/')+'.lean')
                    if target.is_file(): pending.append(target)
    report={'passed':True,'endpoints':len(entries),'scope':'Generic model-relative send-update/restore/flatten Hom and symbolic byte-circuit agreement. Does not prove Rust SessionRecord refinement, restore coherence, full binding, native execution, durable recovery or admission.','axiom_audit':audit,'source_sha256':closure}
    (ROOT/'SignalReference/PrivateRecordWork/send-proof-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: 13 foundation-only private record send/flatten proof endpoints')
if __name__=='__main__': main()
