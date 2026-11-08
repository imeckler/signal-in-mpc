// Replayed mechanically from pinned net/chat/ws.rs; see validation-replay.json.
use crate::chat_websocket::{WebSocketMessage as MessageProto,
    WebSocketRequestMessage as RequestProto, WebSocketResponseMessage as ResponseProto};
use crate::chat_websocket::web_socket_message::Type as ChatMessageType;
pub(super) enum ChatProtoDataError {
    /// protobuf decode failed
    InvalidProtobuf(prost::DecodeError),
    /// unrecognized message type {0}
    InvalidMessageType(i32),
    /// request-type message has response value
    RequestHasResponse,
    /// response-type messages has request value
    ResponseHasRequest,
    /// message type was unknown
    UnknownMessageType,
    /// request was missing payload
    MissingPayload,
}

pub(super) enum ChatMessageProto {
    Request(RequestProto),
    Response(ResponseProto),
}

pub(super) fn validate_decoded(msg: MessageProto) -> Result<ChatMessageProto, ChatProtoDataError> {
    let MessageProto {
        r#type,
        request,
        response,
    } = msg;

    let message_type = ChatMessageType::try_from(r#type.unwrap_or_default())
        .map_err(|e| ChatProtoDataError::InvalidMessageType(e.0))?;

    match (message_type, request, response) {
        (ChatMessageType::Unknown, _, _) => Err(ChatProtoDataError::UnknownMessageType),
        (ChatMessageType::Request, Some(req), None) => Ok(ChatMessageProto::Request(req)),
        (ChatMessageType::Response, None, Some(res)) => Ok(ChatMessageProto::Response(res)),

        (ChatMessageType::Request, None, None) | (ChatMessageType::Response, None, None) => {
            Err(ChatProtoDataError::MissingPayload)
        }
        (ChatMessageType::Request, _, Some(_)) => Err(ChatProtoDataError::RequestHasResponse),
        (ChatMessageType::Response, Some(_), _) => Err(ChatProtoDataError::ResponseHasRequest),
    }
}
