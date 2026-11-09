//! Extraction entry points only. Generated implementations are unchanged.
pub mod chat_websocket {
    include!(concat!(env!("OUT_DIR"), "/signal.proto.chat_websocket.rs"));
}
pub fn merge_envelope<B: bytes::Buf>(
    message: &mut chat_websocket::WebSocketMessage,
    tag: u32,
    wire: prost::encoding::WireType,
    input: &mut B,
    context: prost::encoding::DecodeContext,
) -> Result<(), prost::DecodeError> {
    prost::Message::merge_field(message, tag, wire, input, context)
}
pub fn merge_response<B: bytes::Buf>(
    message: &mut chat_websocket::WebSocketResponseMessage,
    tag: u32,
    wire: prost::encoding::WireType,
    input: &mut B,
    context: prost::encoding::DecodeContext,
) -> Result<(), prost::DecodeError> {
    prost::Message::merge_field(message, tag, wire, input, context)
}


pub fn default_response() -> chat_websocket::WebSocketResponseMessage {
    Default::default()
}

pub fn default_envelope() -> chat_websocket::WebSocketMessage { Default::default() }
