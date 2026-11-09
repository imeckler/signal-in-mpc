import ChatResponseReferenceWork.InnerResponseV1.Replayed.Funs
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.InnerResponseV1
open ActualInnerResponseV1
abbrev Message := chat_websocket.WebSocketResponseMessage
abbrev Error := prost.error.DecodeError
abbrev Frame := Str × Str

def stamp (frame : Frame) (result : core.result.Result Unit Error) : Result (core.result.Result Unit Error) :=
  match result with
  | .Ok unit => .ok (.Ok unit)
  | .Err error => do let next ← SchemaV1.Diagnostic.push error frame; .ok (.Err next)

def optionalField {T B : Type} (old : Option T) (defaultValue : Result T)
    (run : T → Result (core.result.Result Unit Error × T × B))
    (set : T → Message) (frame : Frame) : Result (core.result.Result Unit Error × Message × B) := do
  let initial ← match old with | some value => .ok value | none => defaultValue
  let (result,value,after) ← run initial
  let observed ← stamp frame result
  .ok (observed,set value,after)

noncomputable def fieldSpec {B : Type} (inst : bytes.buf.buf_impl.Buf B) (state : Message)
    (tag : U32) (wire : prost.encoding.wire_type.WireType) (before : B) (ctx : prost.encoding.DecodeContext) :
    Result (core.result.Result Unit Error × Message × B) :=
  match tag with
  | 1#uscalar => optionalField state.id (.ok core.default.DefaultU64.default)
      (fun old => prost.encoding.uint64.merge inst wire old before ctx)
      (fun value => {state with id := some value}) diagnosticFrame0
  | 2#uscalar => optionalField state.status (.ok core.default.DefaultU32.default)
      (fun old => prost.encoding.uint32.merge inst wire old before ctx)
      (fun value => {state with status := some value}) diagnosticFrame1
  | 3#uscalar => optionalField state.message (.ok (alloc.vec.Vec.new U8))
      (fun old => prost.encoding.string.merge inst wire old before ctx)
      (fun value => {state with message := some value}) diagnosticFrame2
  | 4#uscalar => optionalField state.body (bytes.bytes.Bytes.Insts.CoreDefaultDefault.default)
      (fun old => prost.encoding.bytes.merge bytes.bytes.Bytes.Insts.ProstEncodingBytesAdapter inst wire old before ctx)
      (fun value => {state with body := some value}) diagnosticFrame3
  | 5#uscalar => do
      let (result,value,after) ← prost.encoding.string.merge_repeated inst wire state.headers before ctx
      let observed ← stamp diagnosticFrame4 result
      .ok (observed,{state with headers := value},after)
  | _ => do
      let (result,after) ← prost.encoding.skip_field inst wire tag before ctx
      .ok (result,state,after)

/-- Exact optional initializer semantics, including None becoming Some(default)
on a subsequent primitive error; existing fields retain their old initial value. -/
theorem optional_error_initialization {T B : Type} (old : Option T) (fallback : T) (ctx : Message)
    (set : T → Message) (frame : Frame) (error : Error) (after : B)
    (run : T → Result (core.result.Result Unit Error × T × B))
    (failure : run (old.getD fallback) = .ok (.Err error,old.getD fallback,after)) :
    optionalField old (.ok fallback) run set frame =
      (do let result ← stamp frame (.Err error); .ok (result,set (old.getD fallback),after)) := by
  cases old with
  | none =>
    change run fallback = .ok (.Err error,fallback,after) at failure
    simp only [optionalField,bind_tc_ok]
    rw [failure]
    rfl
  | some value =>
    change run value = .ok (.Err error,value,after) at failure
    simp only [optionalField,bind_tc_ok]
    rw [failure]
    rfl

#print axioms optional_error_initialization
end ChatResponseReference.InnerResponseV1
