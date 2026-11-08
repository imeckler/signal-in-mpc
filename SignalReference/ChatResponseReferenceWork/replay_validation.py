#!/usr/bin/env python3
"""Replay pinned private validation after an explicit decoded-message boundary.
The schema decoder is composed separately; this does not call the private API.
"""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;ROOT=H.parents[1]
source=ROOT/'.deps/libsignal-v0.106.1/rust/net/src/chat/ws.rs'
text=source.read_text()
def block(start):
 i=text.index(start); opening=text.index('{',i); depth=1;j=opening+1
 while depth:
  depth+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[i:j]
error=block('pub(super) enum ChatProtoDataError')
message=block('pub(super) enum ChatMessageProto')
original=block('pub(super) fn decode_and_validate(')
old='pub(super) fn decode_and_validate(data: &[u8]) -> Result<ChatMessageProto, ChatProtoDataError> {\n    let msg = MessageProto::decode(data).map_err(ChatProtoDataError::InvalidProtobuf)?;'
new='pub(super) fn validate_decoded(msg: MessageProto) -> Result<ChatMessageProto, ChatProtoDataError> {'
assert original.startswith(old)
transformed=original.replace(old,new,1)
assert transformed[len(new):]==original[len(old):]
prefix='''// Replayed mechanically from pinned net/chat/ws.rs; see validation-replay.json.
use crate::chat_websocket::{WebSocketMessage as MessageProto,
    WebSocketRequestMessage as RequestProto, WebSocketResponseMessage as ResponseProto};
use crate::chat_websocket::web_socket_message::Type as ChatMessageType;
'''
output=H/'Rust/src/validation_replay.rs'
output.write_text(prefix+error+'\n\n'+message+'\n\n'+transformed+'\n')
sha=lambda b:hashlib.sha256(b).hexdigest()
(H/'validation-replay.json').write_text(json.dumps({
 'source':str(source.relative_to(ROOT)),'source_sha256':sha(source.read_bytes()),
 'output':str(output.relative_to(ROOT)),'output_sha256':sha(output.read_bytes()),
 'private_api_called':False,'decoded_boundary_explicit':True,
 'changes':['Replace decode_and_validate(data) signature and first Message::decode statement with validate_decoded(msg).','Supply imported generated type aliases; replay both enums unchanged without display derives.'],
 'validation_suffix_identical':True,'original_function_sha256':sha(original.encode()),
 'validation_suffix_sha256':sha(original[len(old):].encode())},indent=2)+'\n')
