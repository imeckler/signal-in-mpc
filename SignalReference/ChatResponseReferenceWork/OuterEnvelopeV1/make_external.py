#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent
aliases={
 'P.Insts.CoreOpsFunctionFnOnceTupleU64.call_once':'ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleU64.call_once',
 'P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once':'ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once',
 'P.Insts.CoreOpsFunctionFnOnceTupleString.call_once':'ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleString.call_once',
 'P.Insts.CoreOpsFunctionFnOnceTupleBytes.call_once':'ActualInnerResponseV1.P.Insts.CoreOpsFunctionFnOnceTupleBytes.call_once',
 'core.option.Option.get_or_insert_with':'ActualInnerResponseV1.core.option.Option.get_or_insert_with',
 'core.result.Result.map_err':'ActualInnerResponseV1.core.result.Result.map_err',
 'alloc.string.String.Insts.CoreDefaultDefault.default':'ActualInnerResponseV1.alloc.string.String.Insts.CoreDefaultDefault.default',
 'bytes.bytes.Bytes.Insts.CoreDefaultDefault.default':'ActualInnerResponseV1.bytes.bytes.Bytes.Insts.CoreDefaultDefault.default',
 'prost.encoding.varint.decode_varint':'ActualInnerResponseV1.prost.encoding.varint.decode_varint',
 'prost.encoding.wire_type.check_wire_type':'ActualInnerResponseV1.prost.encoding.wire_type.check_wire_type',
 'prost.encoding.skip_field':'ActualInnerResponseV1.prost.encoding.skip_field',
 'prost.encoding.uint64.merge':'ActualInnerResponseV1.prost.encoding.uint64.merge',
 'prost.encoding.uint32.merge':'ActualInnerResponseV1.prost.encoding.uint32.merge',
 'prost.encoding.string.merge':'ActualInnerResponseV1.prost.encoding.string.merge',
 'prost.encoding.string.merge_repeated':'ActualInnerResponseV1.prost.encoding.string.merge_repeated',
 'prost.encoding.message.merge':'ActualSubmessageV1.prost.encoding.message.merge',
 'bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with':'ActualInnerResponseV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with',
 'bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.len':'ActualInnerResponseV1.bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.len'}
s='''import ChatResponseReferenceWork.OuterEnvelopeV1.Callbacks
import ChatResponseReferenceWork.InnerResponseV1.Replayed.FunsExternal
open Aeneas Aeneas.Std Result
noncomputable section
namespace ActualOuterEnvelopeV1
abbrev P.Insts.CoreOpsFunctionFnOnceTupleI32.call_once (value : Result I32) (_ : Unit) := value
def core.option.Option.as_ref {T : Type} (value : Option T) : Result (Option T) := .ok value
def core.option.Option.map_or {T U F : Type} (inst : core.ops.function.FnOnce F T U)
    (value : Option T) (fallback : U) (closure : F) : Result U :=
  match value with | none => .ok fallback | some value => inst.call_once closure value
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type) : Result (Option T) := .ok none
def innerBytesAdapter {T : Type} (inst : prost.encoding.BytesAdapter T) : ActualInnerResponseV1.prost.encoding.BytesAdapter T :=
  ⟨⟨inst.sealedBytesAdapterInst.coredefaultDefaultInst,inst.sealedBytesAdapterInst.len,
     inst.sealedBytesAdapterInst.replace_with,fun _ _ _ => .fail .undef⟩⟩
noncomputable def prost.encoding.bytes.merge {T B : Type} (adapter : prost.encoding.BytesAdapter T)
    (inst : bytes.buf.buf_impl.Buf B) := ActualInnerResponseV1.prost.encoding.bytes.merge (innerBytesAdapter adapter) inst
'''
for name,target in aliases.items():s+=f'abbrev {name} := @{target}\n'
implemented=set(aliases)|{'P.Insts.CoreOpsFunctionFnOnceTupleI32.call_once','core.option.Option.as_ref','core.option.Option.map_or','core.option.Option.Insts.CoreDefaultDefault.default','prost.encoding.bytes.merge'}
text=(H/'Generated/FunsExternal_Template.lean').read_text();dead=[];callbacks=[]
for block in re.split(r'(?=^/--)',text,flags=re.M):
 m=re.search(r'\baxiom\s+([\w.]+)',block)
 if not m:continue
 name=m.group(1)
 if name in implemented:continue
 if '.merge_field.closure' in name:callbacks.append(name);continue
 assert '.encode' in name or name in ['alloc.vec.Vec.clear','bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.append_to'],name
 definition=block[block.index('axiom'):].replace('axiom','def',1).strip()
 s+='\n/-- Unused encoding/clear slot: fail closed, outside parser observation. -/\n'+definition+' := by intros; exact .fail .undef\n';dead.append(name)
s+='\nend ActualOuterEnvelopeV1\n';(H/'Replayed/FunsExternal.lean').write_text(s)
(H/'external-models.json').write_text(json.dumps({'scope':'Parser dependencies alias actual proved implementations; explicit diagnostic content model. Unused encode/clear slots fail closed, no encoding/clear correctness claim.','actual_aliases':aliases,'diagnostic_callbacks':callbacks,'fail_closed_unused':dead,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2)+'\n')
