pub mod chat_websocket { include!(concat!(env!("OUT_DIR"), "/signal.proto.chat_websocket.rs")); }
pub fn merge_response_submessage(
    wire: prost::encoding::WireType, value: &mut chat_websocket::WebSocketResponseMessage,
    input: &mut &[u8], context: prost::encoding::DecodeContext,
) -> Result<(), prost::DecodeError> {
    prost::encoding::message::merge(wire, value, input, context)
}
