#!/usr/bin/env python3
"""Replay exact native owned-decode wrapper, excluding unrelated trait methods."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;source=H/'GeneratedOwnedDecode/Funs.lean';s=source.read_text()
def fragment(start,stop):
 i=s.index(start);j=s.index(stop,i);return s[i:j]
buf=fragment('def Mut0T.Insts.BytesBufBuf_implBuf {','\n/--')
start='def\n  message.Message.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTupleSelf.call_once'
i=s.index(start);j=s.index('/-- [prost::message::Message::decode_length_delimited]',i)
body=s[i:j]
prelude='''-- Exact generated native declarations; replay_owned_decode.py records provenance.
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
'''
out=H/'OwnedDecodeCore.lean';out.write_text(prelude+buf+'\n\n'+body+'\nend ActualChatResponseOwned_decode\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(H/'owned-decode-replay.json').write_text(json.dumps({'candidate_only':True,'generated_source_sha256':sha(source),'translation_receipt_sha256':sha(H/'owned_decode-translation.json'),'output_sha256':sha(out),'native_declarations_unchanged':True,'fragment_sha256':[hashlib.sha256(x.encode()).hexdigest() for x in [buf,body]],'merge_correctness_assumed':False,'scope':'Owned decode wrapper only; universal over dictionary-supplied merge/default/buffer operations'},indent=2)+'\n')
