#!/usr/bin/env python3
"""Private canonical varint semantics plus actual selected prost reference."""
import hashlib,importlib.util,json,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];PROST=HERE.parent/'ProstEncodingWork'
def main():
 spec=importlib.util.spec_from_file_location('prost_checker',PROST/'check.py');prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
 before,selection,provenance=prior.check_selection();vec,vecProvenance=prior.check_vec(before)
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateVarintSemantics'],cwd=ROOT,check=True)
 modules=[f'ProstEncodingWork/Generated/{kind}/{name}' for kind in ['EncodeSelected','VecPutSlice'] for name in ['Types','Funs']]
 modules += ['ProstEncodingWork/'+n for n in ['Reference','NatBridge','VecBridge','CircuitBridge']]
 modules += ['PrivateVarintSemanticsWork/'+n for n in ['Reference','Checks']]
 audit=subprocess.check_output([sys.executable,str(ROOT/'.deps/run-signal-lean.py'),*modules],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S)
 assert len(groups)+audit.count('does not depend on any axioms')==19,audit
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'},audit
 assert 'sorryAx' not in audit and '_native' not in audit
 (HERE/'axioms.txt').write_text(audit)
 files=[Path(__file__),HERE/'Reference.lean',HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateVarintSemantics.lean',ROOT/'TlsMpc/Signal/PrivateVarint.lean',ROOT/'TlsMpc/Signal/Varint.lean',ROOT/'TlsMpc/Signal/Varint64.lean']+provenance+vecProvenance
 files += [PROST/(n+'.lean') for n in ['Reference','NatBridge','VecBridge','CircuitBridge']]
 files += [PROST/'Generated'/kind/(n+'.lean') for kind in ['EncodeSelected','VecPutSlice'] for n in ['Types','Funs']]
 report={'kernel_endpoints':19,'foundation_axioms_only':True,'native_reflection_used':False,
 'private_packing_domain':'All canonical groups of lengths1..10; all uint32 values have canonical width witness; uint64 wire theorem under mathematical canonical-width condition.',
 'proved':'Actual active suffix masks, private16-bit counting, validity255, exact BE16 width, continuation bytes and zero capacity tail. Total private uint32 wire equals actual selected prost encoder appended bytes for every uint32, without width/validity circuit inputs. Numeric uint32 artifact endpoint composes with actual selected prost reference.',
 'actual_reference_boundary':'Existing reviewed eleven reversible metadata changes for prost loop and actual selected Vec methods; unchanged retained computational bodies, official pinned Aeneas standard models and translator trust boundary.',
 'remaining':['Total uint64 actual prost bridge still to close.','Canonical base64/decimal arithmetic semantics remain separate.','Actual AES-CTR/HMAC/whole sealed-sender/session refinement remains blocked and unproved.'],
 'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('19 kernel endpoints; total private uint32 actual prost wire and canonical private packing passed')
if __name__=='__main__':main()
