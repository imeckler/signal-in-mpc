#!/usr/bin/env python3
from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent;native_path=H.parent/'SchemaV1/Artifacts/schema.llbc';data=json.loads(native_path.read_text())['translated'];receipt=json.loads((H.parent/'SchemaV1/Artifacts/specialized.push.json').read_text());s='import ChatResponseReferenceWork.InnerResponseV1.Replayed.Types\nimport ChatResponseReferenceWork.SchemaV1.DiagnosticModel\nopen Aeneas Aeneas.Std Result\nnamespace ActualInnerResponseV1\n';frames=[]
for call in receipt['changes']:
 message,field=call['literals']
 if message!='WebSocketResponseMessage':continue
 f=data['fun_decls'][call['caller']];tid=f['signature']['inputs'][0]['Untagged']['Adt']['id']['Adt'];name,index=data['type_decls'][tid]['item_meta']['name'][-1]['Ident'];assert name=='closure'
 frame=lambda text:'(⟨['+','.join(str(c)+'#u8' for c in text.encode('ascii'))+'],by simp; scalar_tac⟩ : Str)'
 s+=f'\ndef diagnosticFrame{index} : Str × Str := ({frame(message)},{frame(field)})\n'
 suffix='' if index==0 else '_'+str(index);closure=f'chat_websocket.MessageWebSocketResponseMessage.merge_field.closure{suffix}'
 s+=f'''/-- Explicit native diagnostic content-model boundary: {message}.{field}. -/
def {closure}.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorDecodeError.call_once
    {{B : Type}} (_ : bytes.buf.buf_impl.Buf B) (_ : {closure} B) (error : prost.error.DecodeError) :
    Result prost.error.DecodeError :=
  ChatResponseReference.SchemaV1.Diagnostic.push error diagnosticFrame{index}
''';frames.append({'source_caller':call['caller'],'index':index,'message':message,'field':field})
assert sorted(f['index'] for f in frames)==list(range(5));s+='\nend ActualInnerResponseV1\n';(H/'Callbacks.lean').write_text(s)
(H/'callback-models.json').write_text(json.dumps({'scope':'Exact executable diagnostic stack model; static-reference source bridge remains open. Literal frame bytes are ASCII from actual inspected callbacks, with no native_decide proof.','native_original_llbc_sha256':hashlib.sha256(native_path.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'callbacks':frames},indent=2)+'\n')
