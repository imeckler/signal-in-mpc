import ChatResponseReferenceWork.GeneratedUint64.Types
/-- Immutable Bytes content model under successful bounded allocation.
Reference counts, ownership and allocation are outside the observation. -/
def bytes.bytes.Bytes := List Aeneas.Std.U8
/-- Preserve every decoded-error constructor/parameter and its diagnostic stack
using the existing extracted Prost error type. -/
def prost.error.DecodeError := ActualChatResponseUint64.error.DecodeError
