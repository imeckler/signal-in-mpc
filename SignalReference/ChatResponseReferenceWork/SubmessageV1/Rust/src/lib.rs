//! Extraction wrapper for the unchanged pinned generic submessage merger.
pub fn merge_submessage<M: prost::Message + Default, B: bytes::Buf>(
    wire: prost::encoding::WireType, value: &mut M, input: &mut B,
    context: prost::encoding::DecodeContext,
) -> Result<(), prost::DecodeError> {
    prost::encoding::message::merge(wire, value, input, context)
}
