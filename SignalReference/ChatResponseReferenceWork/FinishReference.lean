import TlsMpc.TlsChatResponse
namespace ChatResponseReference.Finish
open TlsMpc TlsMpc.Signal
/-- Structural completion and private-ID binding only. HTTP status remains
unconstrained, so valid non-2xx replies are included in the theorem. -/
structure Ready (s : TlsChatResponse.State (BitVec 8) (BitVec 64)) : Prop where
  valid : s.valid = 255
  seen : s.seen = 255
  finished : s.finished = 0
  mode : TlsWebSocketUpgrade.get ByteAuth.concrete s.modes 0 = 255
  position : TlsWebSocketUpgrade.get ByteAuth.concrete s.positions 0 = 255
  inner : s.inner = 0
  depth : s.depth = 0
  typeValue : s.typeValue = 2
  request : s.requestPresent = 0
  response : s.responsePresent = 255
  idPresent : s.idPresent = 255
  id : s.id = s.expected
private theorem eq_self (x : BitVec 64) : Word64.eq Word64.concrete ByteAuth.concrete x x = 255 := by
  unfold Word64.eq
  rw [ByteAuth.equalMask_value]
  simp
/-- Core acceptance validates the native HTTP range, separately from is_success.
In particular an HTTP error response is not a malformed protobuf reply. -/
theorem core_status_range (s : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (h : Ready s) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete s).valid =
      if 100 ≤ s.status.toNat ∧ s.status.toNat ≤ 999 then 255 else 0 := by
  simp only [TlsChatResponse.finish,TlsChatResponse.weq,h.valid,h.seen,h.finished,
    h.mode,h.position,h.inner,h.depth,h.typeValue,h.request,h.response,h.idPresent,h.id]
  simp only [show Word64.concrete.const 0 = (0 : BitVec 64) from rfl,
    show Word64.concrete.const 2 = (2 : BitVec 64) from rfl]
  simp only [eq_self,Word64.ule_value]
  simp only [show (Word64.concrete.const 100).toNat = 100 from rfl,
    show (Word64.concrete.const 999).toNat = 999 from rfl]
  by_cases hl : 100 ≤ s.status.toNat <;> by_cases hu : s.status.toNat ≤ 999 <;>
    simp [hl,hu,ByteAuth.concrete]
theorem core_success_range (s : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (h : Ready s) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete s).successful =
      if 200 ≤ s.status.toNat ∧ s.status.toNat ≤ 299 then 255 else 0 := by
  change ByteAuth.concrete.and
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete s).valid
    (ByteAuth.concrete.and (Word64.concrete.ule (Word64.concrete.const 200) s.status)
      (Word64.concrete.ule s.status (Word64.concrete.const 299))) = _
  rw [core_status_range s h,Word64.ule_value,Word64.ule_value]
  simp only [show (Word64.concrete.const 200).toNat = 200 from rfl,
    show (Word64.concrete.const 299).toNat = 299 from rfl]
  by_cases hl : 100 ≤ s.status.toNat <;> by_cases hu : s.status.toNat ≤ 999 <;>
    by_cases sl : 200 ≤ s.status.toNat <;> by_cases su : s.status.toNat ≤ 299 <;>
    simp [hl,hu,sl,su,ByteAuth.concrete] <;> omega
/-- A representative native valid HTTP error remains a valid Core response.
Application abort policy belongs to Mux and is deliberately not equated here. -/
theorem http_error_is_valid (s : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (h : Ready s) (status : s.status = 400) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete s).valid = 255 ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete s).successful = 0 := by
  rw [core_status_range s h,core_success_range s h,status]
  decide
#print axioms core_status_range
#print axioms core_success_range
#print axioms http_error_is_valid
end ChatResponseReference.Finish
