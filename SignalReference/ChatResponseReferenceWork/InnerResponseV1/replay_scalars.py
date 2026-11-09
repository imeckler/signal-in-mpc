#!/usr/bin/env python3
"""Replay only actual accepted generated scalar bodies, qualification unchanged."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;ROOT=H.parents[2];CHAT=H.parent
items=[('uint32',ROOT/'SignalReference/ProtoParseWork/DispatcherIntegrationWork/FieldReplay/Funs.lean'),('uint64',CHAT/'GeneratedUint64/Funs.lean')]
s='import ChatResponseReferenceWork.InnerResponseV1.BufferBridge\nopen Aeneas Aeneas.Std Result\nnamespace ActualInnerResponseV1\n';report=[]
for kind,p in items:
 text=p.read_text();a=text.index('def encoding.'+kind+'.merge');b=text.find('\n/--',a)
 if b<0:b=text.index('\nend ',a)
 body=text[a:b].strip();mapped=re.sub(r'(?<![.\w])encoding\.', 'prost.encoding.',body);mapped=re.sub(r'(?<![.\w])error\.', 'prost.error.',mapped)
 s+='\n/-- Actual pinned generated '+kind+' body; namespace qualification only. -/\nnoncomputable '+mapped+'\n'
 report.append({'source':str(p.relative_to(ROOT)),'source_file_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'body_sha256':hashlib.sha256(body.encode()).hexdigest(),'qualified_body_sha256':hashlib.sha256(mapped.encode()).hexdigest()})
s+='\nend ActualInnerResponseV1\n';(H/'ScalarSource.lean').write_text(s)
(H/'scalar-source.json').write_text(json.dumps({'scope':'Unchanged actual generated uint32/uint64 body replay, namespace qualification only; decoder delegates actual accepted varint.','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'bodies':report},indent=2)+'\n')
