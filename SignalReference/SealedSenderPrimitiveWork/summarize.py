#!/usr/bin/env python3
"""Compact, fail-closed diagnostic receipt; no primitive agreement acceptance."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
profiles={}
for directory in sorted((HERE/'Artifacts').iterdir()):
 p=directory/'inventory.json'
 if not p.exists():continue
 d=json.loads(p.read_text());profiles[directory.name]={k:d[k] for k in ['charon_exit_code','aeneas_exit_code','has_errors','llbc_sha256','dependencies','opaque_primitives','charon_command','aeneas_command','rustflags'] if k in d}
 profiles[directory.name]['log_sha256']={log.name:sha(log) for log in directory.glob('*.log')}
 assert profiles[directory.name].get('aeneas_exit_code',1)!=0
report={'candidate_only':True,'actual_AES_CTR_HMAC_implementation_agreement_established':False,'pinned_libsignal':'904c8dc8216073b078a5f2f5090e3da8382e6a92','profiles':profiles,
 'blockers':['CTR original: unsupported ArraySize GAT; scoped guard advances to associated-array/lifetime analysis. Monomorphization: actual mutable Zip substitution type errors.','HMAC generic: associated-array/lifetime analysis. Specialized actual HMAC: Option<(&mut[u8],&u32)>, hybrid_array::from_fn::Guard and block_buffer::ResetGuard borrow/type analysis.','Extracting opaque standard-library bodies introduces actual zeroize readonly compiler barrier asm and MaybeUninit/NonNull unions; opacity of that barrier alone does not close the remaining memory model.'],
 'translator_candidate':'Only missing-declaration Default-array recognizer guard. No crypto/body/LLBC edits; exact successful generated wrapper baseline preserved. Not independently accepted.',
 'next_required_implementation_work':'Actual wrapper translation needs supported associated-array and nested mutable-borrow guard handling before existing AES/SHA leaves can compose. Do not fill these gaps with assumed primitive correctness.',
 'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in [HERE/'extract.py',Path(__file__),HERE/'TranslatorCandidate/build.py',HERE/'TranslatorCandidate/check.py',HERE/'TranslatorCandidate/patch.diff']}}
(HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('All actual primitive trials fail closed; precise blockers recorded')
