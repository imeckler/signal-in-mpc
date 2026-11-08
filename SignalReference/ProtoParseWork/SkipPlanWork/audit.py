#!/usr/bin/env python3
"""Rebuild and audit the conditional numeric parser-plan/actual-skip bridge."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    replay=json.loads((HERE/'key-replay.json').read_text());source=ROOT/replay['source']
    assert digest(source)==replay['source_sha256']
    body=source.read_text()
    for old,new in replay['substitutions']:body=body.replace(old,new)
    target=HERE/'Modules/SkipPlanWork/KeyCircuit.lean'
    assert target.read_text()==body and digest(target)==replay['target_sha256']
    run=subprocess.run([sys.executable,str(HERE/'check.py')],capture_output=True,text=True,check=True)
    log=HERE/'check.log';log.write_text(run.stdout+run.stderr)
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log.read_text(),re.S)
    assert len(entries)==36,len(entries)
    for name,axioms in entries:assert set(a.strip()for a in axioms.split(','))<={'propext','Classical.choice','Quot.sound'},(name,axioms)
    paths=[*sorted((HERE/'Modules').rglob('*.lean')),HERE/'check.py',Path(__file__),HERE/'key-replay.json',ROOT/'TlsMpc/Signal/ProtoParse.lean',ROOT/'TlsMpc/Signal/Word64.lean',HERE.parent/'SkipTranslatorWork/freeze-manifest.json',HERE.parent/'SkipTranslatorWork/root-review.json',HERE.parent/'KeyReferenceWork/root-review.json']
    report={'candidate_only':True,'accepted_reference':False,'checked_endpoints':len(entries),'allowed_foundational_axioms':['propext','Classical.choice','Quot.sound'],'source_sha256':{str(p.relative_to(ROOT)):digest(p)for p in paths},'rebuilt_olean_sha256':{str(p.relative_to(ROOT)):digest(p)for p in sorted((HERE/'Build').rglob('*.olean'))},'check_log_sha256':digest(log),'scope':'Numeric existing ProtoParse.plan fixed32/fixed64/varint/length masks and cursors inside groups, bounded arithmetic, recursion-limit rejection; group start/end masks, exact stack lookup/write, depth and cursor updates, nested fields unchanged, actual matching/mismatching end-tag outcomes; exact accepted actual skip outcomes under explicit decoded-key/payload correspondence and buffer-length premises. No extra models or translator edits.','not_established':['Decoder table/lookup establishes all correspondence premises for an arbitrary body.','Top-level unknown-field cases and whole scan/table/cursor/stack preservation invariant.','Whole Signal parser or numeric AIG artifact refinement.']}
    (HERE/'proof-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Passed',len(entries),'kernel endpoints with foundational axioms only.')
if __name__=='__main__':main()
