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

/// Source API composition used by net/chat.rs status validation. This entry
/// introduces no status predicate; both checks call the pinned actual methods.
pub fn checked_status(raw: u32) -> Result<(u16, bool), ()> {
    let narrowed: u16 = raw.try_into().map_err(|_| ())?;
    let status = http::StatusCode::from_u16(narrowed).map_err(|_| ())?;
    Ok((status.as_u16(), status.is_success()))
}

pub fn checked_utf8(input: &[u8]) -> bool {
    core::str::from_utf8(input).is_ok()
}

/// Functional model boundary for the native shared-slice metadata primitive.
pub fn slice_metadata_len(input: &[u8]) -> usize { input.len() }
pub fn reference_length_seed(input: &[u8]) -> usize { slice_metadata_len(input) }
pub fn slice_metadata_positive(input: &[u8]) -> usize { input.len() }
pub fn slice_metadata_negative_u16(input: &[u16]) -> usize { input.len() }
pub fn slice_metadata_negative_raw(input: *const [u8]) -> usize { input.len() }

mod validation_replay;
