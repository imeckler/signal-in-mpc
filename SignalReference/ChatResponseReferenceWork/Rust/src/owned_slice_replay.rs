// Mechanically specialized from pinned prost/message.rs. See owned-slice-replay.json.
use prost::{Message, DecodeError};
use crate::chat_websocket::WebSocketMessage as MessageProto;
/// Transfer the local shared slice because neither its cursor nor Drop is
/// observable from owned Result. Actual parsing/default implementations remain.
pub fn decode_buffer<M: Message + Default, B: bytes::Buf>(buf: B) -> Result<M, DecodeError> {
        let mut message = M::default();
        M::merge(&mut message, buf).map(|_| message)
    }

pub fn decode_slice(buf: &[u8]) -> Result<MessageProto, DecodeError> { decode_buffer::<MessageProto, _>(buf) }
