#!/usr/bin/env python3
"""Current candidate kernel audit; not an acceptance or whole skip/parser proof."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
import check,replay
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--report-only',action='store_true',help='Audit already built modules without repeating the full kernel rebuild');args=ap.parse_args()
    if not args.report_only:replay.main();check.main()
    source=HERE/'Modules/SkipTranslatorWork/ProofAudit.lean';out=HERE/'axioms-current.txt'
    result=subprocess.run(['lean',str(source)],cwd=HERE/'Modules',env=check.env(),capture_output=True,text=True,check=True);out.write_text(result.stdout+result.stderr)
    endpoints=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out.read_text(),re.S)
    empty=re.findall(r"'([^']+)' does not depend on any axioms",out.read_text())
    assert len(endpoints)+len(empty)==18,(len(endpoints),empty)
    for name,axioms in endpoints:assert set(x.strip()for x in axioms.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'},(name,axioms)
    files=[*sorted((HERE/'Modules').rglob('*.lean')),*sorted((HERE/'Trees/candidate').rglob('*.lean')),HERE/'check.py',HERE/'replay.py',Path(__file__),HERE/'continuation-pass.diff']
    report={'candidate_only':True,'accepted_reference':False,'kernel_check_passed':True,'full_rebuild_in_this_invocation':not args.report_only,'new_audit_endpoints':len(endpoints)+len(empty),'allowed_foundational_axioms':['propext','Classical.choice','Quot.sound'],'source_sha256':{str(p.relative_to(ROOT)):digest(p)for p in files},'axiom_audit_sha256':digest(out),'scope':'Actual unchanged skip translation compiles; varint proof replay identical computational prefix; exact recursion-limit-first, EndGroup rejection, varint success/error, fixed32/fixed64 bounds and length-delimited success/error buffer transitions. Group recursive semantic equivalence and circuit skip/parser bridge remain incomplete.','trust_boundary':'Quarantined extra invocation of existing translator remove_useless_joins pass before update_loops; explicit core::result::Result::map external model (used with empty closure); accepted byte-slice Buf and valid-usize unsafe-index model assumptions inherited. New loop monotonicity lemma is kernel-proved without altering loop definition. No global translation soundness proof or arbitrary Buf claim.'}
    (HERE/'kernel-check-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
