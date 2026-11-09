import ChatResponseReferenceWork.StreamingV1.OpaqueKinds
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Every nonempty complete String payload rejected by the executable UTF8
grammar rejects the actual streaming Core, including an incomplete final scalar.
Source content/error mutation and std validator-body boundaries remain separate. -/
theorem string_payload_utf_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (nonempty : bytes ≠ []) (bounded : bytes.length < 2^64)
    (modes : state.modes = lane 3) (skip : state.skip = BitVec.ofNat 64 bytes.length)
    (kindsShape : state.kinds.length = 4)
    (stringKind : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 2)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 3) = 255)
    (utf : state.utf = Utf8.encode .ready) (bad : Utf8.accepts bytes = false) :
    (feed state bytes).valid = 0 := by
  let leading := bytes.dropLast
  let byte := bytes.getLast nonempty
  have span : leading ++ [byte] = bytes := List.dropLast_concat_getLast nonempty
  have proper : leading.length < bytes.length := by
    have result := congrArg List.length span
    simp only [List.length_append,List.length_singleton] at result
    omega
  let current := feed state leading
  have inside := opaque_prefix_inside state leading bytes.length bounded proper modes skip
  have currentModes : current.modes = lane 3 := inside.1
  have currentSkip : current.skip = BitVec.ofNat 64 1 := by
    rw [inside.2]
    congr 1
    have result := congrArg List.length span
    simp only [List.length_append,List.length_singleton] at result
    omega
  have currentKinds : current.kinds = state.kinds := opaque_prefix_kinds state leading bytes.length bounded (by omega) modes skip kindsShape
  have currentKind : TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsWebSocketUpgrade.get ByteAuth.concrete current.kinds 2)
      (TlsWebSocketUpgrade.get ByteAuth.concrete current.kinds 3) = 255 := by rw [currentKinds]; exact stringKind
  have currentUtf := string_utf_prefix state leading bytes.length .ready bounded (by omega) modes skip kindsShape stringKind utf
  have currentShape : current.utf.length = 8 := by
    rw [currentUtf]
    cases Utf8.run .ready leading <;> rfl
  have point := string_utf_step current byte currentModes currentKind currentShape
  have complete := string_utf_complete state bytes bytes.length bounded (by omega) modes skip kindsShape stringKind utf
  rw [bad] at complete
  have whole : feed state bytes = (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete current byte).state := by
    rw [←span]
    simp only [current,feed,List.foldl_append,List.foldl_cons,List.foldl_nil]
  have badNext : TlsWebSocketUpgrade.get ByteAuth.concrete (TlsWebSocketFrame.utfStep ByteAuth.concrete current.utf byte) 0 = 0 := by
    rw [←point,←whole]
    exact complete
  rw [whole]
  exact string_utf_terminal_reject current byte currentModes currentSkip currentKind badNext

#print axioms string_payload_utf_reject
end ChatResponseReference.StreamingV1
