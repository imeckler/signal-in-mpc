import ChatResponseReferenceWork.ByteMasks
open TlsMpc
namespace ChatResponseReference.Utf8
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exhaustive finite transition proof, reduced by Lean's kernel. No native
proof oracle or assumed UTF8 correctness is used. -/
theorem step_encoding (phase : Phase) : ∀ byte : BitVec 8,
    TlsWebSocketFrame.utfStep ByteAuth.concrete (encode phase) byte = encode (next phase byte) := by
  cases phase <;> simp only [TlsWebSocketFrame.utfStep,member_flag,eq_flag] <;> decide +kernel

theorem fold_encoding (bytes : List (BitVec 8)) (phase : Phase) :
    bytes.foldl (TlsWebSocketFrame.utfStep ByteAuth.concrete) (encode phase) = encode (run phase bytes) := by
  induction bytes generalizing phase with
  | nil => rfl
  | cons byte rest ih => rw [List.foldl_cons,step_encoding]; exact ih _

theorem encoding_complete (phase : Phase) :
    TlsWebSocketUpgrade.get ByteAuth.concrete (encode phase) 0 = if phase = .ready then 255 else 0 := by
  cases phase <;> rfl

theorem encoding_live (phase : Phase) :
    TlsWebSocketUpgrade.any ByteAuth.concrete (encode phase) = if phase = .dead then 0 else 255 := by
  cases phase <;> rfl

/-- Exact final acceptance for arbitrary byte lists, including malformed and
truncated sequences. The statement is not restricted to successful inputs. -/
theorem machine_accepts_spec (bytes : List (BitVec 8)) :
    TlsWebSocketUpgrade.get ByteAuth.concrete (circuitRun bytes) 0 = if accepts bytes then 255 else 0 := by
  unfold circuitRun
  rw [fold_encoding,encoding_complete]
  simp [accepts]

theorem machine_prefix_rejection (bytes : List (BitVec 8)) :
    TlsWebSocketUpgrade.any ByteAuth.concrete (circuitRun bytes) = if run .ready bytes = .dead then 0 else 255 := by
  unfold circuitRun
  rw [fold_encoding,encoding_live]

#print axioms step_encoding
#print axioms fold_encoding
#print axioms machine_accepts_spec
#print axioms machine_prefix_rejection
end ChatResponseReference.Utf8
