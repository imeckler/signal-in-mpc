#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;out=H/'Replayed';out.mkdir(exist_ok=True);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=(H/'Generated/Types.lean').read_text();(out/'Types.lean').write_text(s)
s=(H/'Generated/Funs.lean').read_text().replace('import Generated.Types','import ChatResponseReferenceWork.FnMutBorrowV1.Replayed.Types').replace('import Generated.FunsExternal','import ChatResponseReferenceWork.FnMutBorrowV1.Projection')
s=s.replace('import Aeneas','import ChatResponseReferenceWork.FnMutBorrowV1.Projection',1)
start=s.index('/-- [fnmut_borrow_regression::actual::{impl core::ops::function::FnMut')
end=s.index('/-- [fnmut_borrow_regression::actual::{impl core::ops::function::FnOnce',start)
raw=s[start:end]
head=s[:s.index('namespace FnMutBorrowV1')]
(out/'Raw.lean').write_text(head+'namespace FnMutBorrowV1.Raw\n'+raw+'\nend FnMutBorrowV1.Raw\n')
s=s[:start]+s[end:]
s=s.replace('import ChatResponseReferenceWork.FnMutBorrowV1.Projection','import ChatResponseReferenceWork.FnMutBorrowV1.ActualProjection')
for trait in ['FnOnce','FnMut']:
 # Narrowly typed signature occurrences only; leave computational bodies intact.
 pattern=rf'core\.ops\.function\.{trait} (\S+) \(Std\.U32 × Std\.U32 × Std\.U32\)\s+Std\.U32'
 s,n=re.subn(pattern,rf'ChatResponseReference.FnMutBorrowV1.Borrow{trait} \1 Std.U32 Std.U32 Std.U32 Std.U32',s)
 assert n=={'FnOnce':1,'FnMut':2}[trait],(trait,n)
(out/'Funs.lean').write_text(s)
(H/'replay.json').write_text(json.dumps({'candidate_only':True,'scope':'Exact borrowed-triple trait type specialization; raw generated helper moved unchanged to Raw namespace; its public identifier is a tagged proved projection. Generated caller and helper computational bodies unchanged.','script_sha256':sha(Path(__file__)),'generated_sha256':{p.name:sha(p) for p in (H/'Generated').glob('*.lean')},'replayed_sha256':{p.name:sha(p) for p in out.glob('*.lean')}},indent=2)+'\n')
