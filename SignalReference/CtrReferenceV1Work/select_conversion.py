#!/usr/bin/env python3
"""Exact root selection of actual uint32→usize conversion; no declaration edits."""
import copy,hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REFERENCE=HERE.parent;ROOT=REFERENCE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 source=HERE/'Artifacts/remaining_pinned_v1/ctr.llbc';original=json.loads(source.read_text());assert not original['has_errors'];c=original['translated'];function=c['fun_decls'][27]
 assert function['generics']['trait_clauses']==[]and function['generics']['types']==[]
 names=[n['Ident'][0]for n in function['item_meta']['name']if'Ident'in n];assert names==['core','convert','num','ptr_try_from_impls','try_from']
 assert 'Structured'in function['body'];selected=copy.deepcopy(original);selected['translated']['ordered_decls']=[{'Type':{'NonRec':7}},{'Type':{'NonRec':8}},{'Fun':{'NonRec':27}}]
 restored=copy.deepcopy(selected);restored['translated']['ordered_decls']=c['ordered_decls'];assert restored==original
 dest=HERE/'Artifacts/ConversionFinal';assert not dest.exists();dest.mkdir(parents=True);llbc=dest/'conversion.llbc';llbc.write_text(json.dumps(selected,separators=(',',':')))
 pins=json.loads((REFERENCE/'pins.json').read_text());aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve();generated=HERE/'Generated/ConversionFinal';generated.mkdir(parents=True)
 command=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REFERENCE),'-subdir','/CtrReferenceV1Work/Generated/ConversionFinal','-split-files','-namespace','CtrConversionV1','-warnings-as-errors','-no-progress-bar']
 with(dest/'aeneas.log').open('w')as out:result=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,timeout=30)
 report=dict(candidate_only=True,accepted_reference=False,selection='only ordered types7,8 and function27; every declaration including body/signature unchanged',original_llbc_sha256=sha(source),selected_llbc_sha256=sha(llbc),selected_function_body_sha256=hashlib.sha256(json.dumps(function['body'],sort_keys=True).encode()).hexdigest(),inverse_checked=True,manual_generated_body_edits=False,aeneas_exit_code=result.returncode,aeneas_command=[x.replace(str(ROOT),'$WORKSPACE')for x in command],generated_sha256={str(p.relative_to(REFERENCE)):sha(p)for p in generated.glob('*.lean')},full_remaining_or_CTR_refinement=False)
 (dest/'review.json').write_text(json.dumps(report,indent=2)+'\n');print('Conversion actual Aeneas exit',result.returncode);return result.returncode
if __name__=='__main__':raise SystemExit(main())
