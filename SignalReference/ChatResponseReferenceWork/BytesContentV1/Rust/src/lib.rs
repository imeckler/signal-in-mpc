//! Concrete wrapper only: native Bytes field and exact borrowed input suffix.
pub fn merge_bytes(
    wire: prost::encoding::WireType,
    mut value: bytes::Bytes,
    mut input: &[u8],
    context: prost::encoding::DecodeContext,
) -> (Result<(), prost::DecodeError>, bytes::Bytes, &[u8]) {
    let result = prost::encoding::bytes::merge(wire, &mut value, &mut input, context);
    (result, value, input)
}
