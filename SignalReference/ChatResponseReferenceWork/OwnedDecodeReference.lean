import ChatResponseReferenceWork.OwnedDecodeCore
namespace ChatResponseReference.OwnedDecode
open Aeneas Aeneas.Std ActualChatResponseOwned_decode

/-- The actual generic native Message::decode wrapper. This equation assumes
no parser correctness and preserves failure/divergence of supplied operations.
The merged partial record is returned only on Ok; a merge error discards it. -/
theorem actual_owned_decode {Record Buffer : Type}
    (instance : message.Message Record) (default : core.default.Default Record)
    (buffer : bytes.buf.buf_impl.Buf Buffer) (input : Buffer) :
    message.Message.decode.default instance default buffer input = (do
      let initial ← default.default
      let (outcome, partial) ← instance.merge buffer initial input
      match outcome with
      | .Ok () => .ok (.Ok partial)
      | .Err error => .ok (.Err error)) := by
  rfl

#print axioms actual_owned_decode
end ChatResponseReference.OwnedDecode
