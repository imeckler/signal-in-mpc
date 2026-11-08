#!/usr/bin/env python3
"""Scoped owned-slice specialization of actual Prost decode control flow.
Only an unobserved local immutable-slice buffer is transferred by value.
This is not a general transformation for buffers with Drop/observable state.
"""
from pathlib import Path
import hashlib,json,difflib
H=Path(__file__).resolve().parent;ROOT=H.parents[1]
source=ROOT/'.deps/libsignal-vendor/prost-0.14.4/src/message.rs';text=source.read_text()
start=text.index('    fn decode(mut buf: impl Buf) -> Result<Self, DecodeError>')
opening=text.index('{',start);depth=1;end=opening+1
while depth:
 depth+=(text[end]=='{')-(text[end]=='}');end+=1
original=text[start:end];body=text[opening+1:end-1]
old='Self::merge(&mut message, &mut buf).map(|_| message)'
assert body.count(old)==1
special=body.replace('Self::default()','M::default()').replace(old,'M::merge(&mut message, buf).map(|_| message)')
output=H/'Rust/src/owned_slice_replay.rs'
output.write_text('''// Mechanically specialized from pinned prost/message.rs. See owned-slice-replay.json.
use prost::{Message, DecodeError};
use crate::chat_websocket::WebSocketMessage as MessageProto;
/// Transfer the local shared slice because neither its cursor nor Drop is
/// observable from owned Result. Actual parsing/default implementations remain.
pub fn decode_buffer<M: Message + Default, B: bytes::Buf>(buf: B) -> Result<M, DecodeError> {'''+special+'}\n\npub fn decode_slice(buf: &[u8]) -> Result<MessageProto, DecodeError> { decode_buffer::<MessageProto, _>(buf) }\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(H/'owned-slice-transfer.diff').write_text(''.join(difflib.unified_diff(body.splitlines(True),special.splitlines(True),fromfile='actual/prost/decode-body',tofile='specialized/shared-slice-owned-buffer-body')))
(H/'owned-slice-replay.json').write_text(json.dumps({'candidate_only':True,'source':str(source.relative_to(ROOT)),'source_sha256':sha(source),'original_function_sha256':hashlib.sha256(original.encode()).hexdigest(),'original_body_sha256':hashlib.sha256(body.encode()).hexdigest(),'output_sha256':sha(output),'diff_sha256':sha(H/'owned-slice-transfer.diff'),'script_sha256':sha(Path(__file__)),'domain':'Actual generated WebSocketMessage; immutable contiguous &[u8]; default Message::merge; no observable buffer cursor or slice destructor','changes':['Rename Self to the explicit generic Message type; expose the actual generated message and shared-slice Rust wrapper.','Move the local slice into the same actual default merge instead of creating an unobserved mutable-reference forwarding wrapper.'],'parse_computation_changes':False,'hand_edited_generated_lean':False,'general_buffer_transformation_claim':False},indent=2)+'\n')
