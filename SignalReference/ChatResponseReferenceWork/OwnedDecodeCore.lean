-- Exact generated native declarations; replay_owned_decode.py records provenance.
import ChatResponseReferenceWork.GeneratedOwnedDecode.Types
namespace ActualChatResponseOwned_decode
open Aeneas Aeneas.Std Result
/-- Standard mutable-reference Buf forwarding in the content observation.
The unused nested backward closure in the opaque template is not exposed by
this Buf dictionary ABI; no buffer operation is executed by wrapping it. -/
def Mut0T.Insts.BytesBufBuf_implBuf.remaining {T : Type} (b : bytes.buf.buf_impl.Buf T) := b.remaining
def Mut0T.Insts.BytesBufBuf_implBuf.chunk {T : Type} (b : bytes.buf.buf_impl.Buf T) := b.chunk
def Mut0T.Insts.BytesBufBuf_implBuf.advance {T : Type} (b : bytes.buf.buf_impl.Buf T) := b.advance
/-- Result.map runs its closure only on success; every error is unchanged. -/
def core.result.Result.map {T E U F : Type} (f : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (closure : F) : Result (core.result.Result U E) := do
  match r with
  | .Ok value => let value1 ← f.call_once closure value; .ok (.Ok value1)
  | .Err error => .ok (.Err error)
def Mut0T.Insts.BytesBufBuf_implBuf {T : Type} (BufInst :
  bytes.buf.buf_impl.Buf T) : bytes.buf.buf_impl.Buf T := {
  remaining := Mut0T.Insts.BytesBufBuf_implBuf.remaining BufInst
  chunk := Mut0T.Insts.BytesBufBuf_implBuf.chunk BufInst
  advance := Mut0T.Insts.BytesBufBuf_implBuf.advance BufInst
}


def
  message.Message.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTupleSelf.call_once
  {Self : Type} {T1 : Type} (MessageInst : message.Message Self)
  (coredefaultDefaultInst : core.default.Default Self) (bytesbufbuf_implBufInst
  : bytes.buf.buf_impl.Buf T1) (c : message.Message.decode.closure Self T1)
  (_ : Unit) :
  Result Self
  := do
  ok c

/-- Trait implementation: [prost::message::Message::decode::{impl core::ops::function::FnOnce<((),), Self> for prost::message::Message::decode::closure<Self, T1>}]
    Source: 'src/message.rs', lines 110:48-110:59 -/
@[reducible]
def message.Message.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTupleSelf
  {Self : Type} {T1 : Type} (MessageInst : message.Message Self)
  (coredefaultDefaultInst : core.default.Default Self) (bytesbufbuf_implBufInst
  : bytes.buf.buf_impl.Buf T1) : core.ops.function.FnOnce
  (message.Message.decode.closure Self T1) Unit Self := {
  call_once :=
    message.Message.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTupleSelf.call_once
    MessageInst coredefaultDefaultInst bytesbufbuf_implBufInst
}

/-- [prost::message::Message::decode]:
    Source: 'src/message.rs', lines 105:4-111:5
    Visibility: public -/
@[trait_default]
def message.Message.decode.default
  {Self : Type} {T1 : Type} (MessageInst : message.Message Self)
  (coredefaultDefaultInst : core.default.Default Self) (bytesbufbuf_implBufInst
  : bytes.buf.buf_impl.Buf T1) (buf : T1) :
  Result (core.result.Result Self error.DecodeError)
  := do
  let message ← coredefaultDefaultInst.default
  let (r, message1, _) ←
    MessageInst.merge (Mut0T.Insts.BytesBufBuf_implBuf bytesbufbuf_implBufInst)
      message buf
  core.result.Result.map
    (message.Message.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTupleSelf
    MessageInst coredefaultDefaultInst bytesbufbuf_implBufInst) r message1


end ActualChatResponseOwned_decode
