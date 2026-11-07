import TlsMpc.Boolean

/-!
Initial protocol specifications and their connection to the Boolean compiler.
These theorems do not verify AES, SHA, the Python implementations, or a backend.
Bit-vector indices in this module count from the least significant bit.
-/

namespace TlsMpc.Tls13

/-- RFC 8446 section 5.3: XOR the IV with the zero-extended sequence number. -/
def nonce (iv : BitVec 96) (sequence : BitVec 64) : BitVec 96 :=
  iv ^^^ sequence.setWidth 96

theorem nonce_injective (iv : BitVec 96) (a b : BitVec 64)
    (h : nonce iv a = nonce iv b) : a = b := by
  have hwidth : a.setWidth 96 = b.setWidth 96 := (BitVec.xor_right_inj iv).mp h
  apply BitVec.eq_of_toNat_eq
  have hnat := congrArg BitVec.toNat hwidth
  simpa only [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 96)] using hnat

/-- Inputs 0..95 hold the IV; inputs 96..159 hold the sequence. -/
def nonceInputs (iv : BitVec 96) (sequence : BitVec 64) (i : Fin 160) : Bool :=
  if i.val < 96 then iv.getLsbD i.val else sequence.getLsbD (i.val - 96)

def nonceExpr (bit : Fin 96) : Boolean.Expr 160 :=
  .xor (.input ⟨bit.val, by omega⟩)
    (if h : bit.val < 64 then .input ⟨96 + bit.val, by omega⟩ else .literal false)

theorem nonceExpr_correct (iv : BitVec 96) (sequence : BitVec 64) (bit : Fin 96) :
    (nonceExpr bit).eval (nonceInputs iv sequence) = (nonce iv sequence).getLsbD bit.val := by
  by_cases h : bit.val < 64
  · simp [nonceExpr, h, Boolean.Expr.eval, nonceInputs, nonce, bit.isLt,
          show ¬96 + bit.val < 96 by omega]
  · simp [nonceExpr, h, Boolean.Expr.eval, nonceInputs, nonce, bit.isLt,
          BitVec.getLsbD_of_ge sequence bit.val (by omega : 64 ≤ bit.val)]

/-- A TLS operation compiled with the proved compiler, for all keys and sequences. -/
theorem compiled_nonce_correct (iv : BitVec 96) (sequence : BitVec 64)
    (bit : Fin 96) (stack : Boolean.Stack height) :
    (Boolean.compile (nonceExpr bit) height).run (nonceInputs iv sequence) stack =
      .cons ((nonce iv sequence).getLsbD bit.val) stack := by
  rw [Boolean.compile_correct, nonceExpr_correct]

/-- Pure sequence reservation; 2^64 is an exhausted sentinel, never wrapped to 0.
The controller must persist the returned state before publishing a record. -/
def reserveSequence (next : Nat) : Option (Nat × Nat) :=
  if next < 2 ^ 64 then some (next, next + 1) else none

theorem reservation_advances (next used after : Nat)
    (h : reserveSequence next = some (used, after)) :
    used = next ∧ after = next + 1 ∧ used < 2 ^ 64 := by
  unfold reserveSequence at h
  split at h
  · cases h
    exact ⟨rfl, rfl, by assumption⟩
  · contradiction

theorem reservation_exhausted (next : Nat) (h : 2 ^ 64 ≤ next) :
    reserveSequence next = none := by
  simp [reserveSequence, show ¬next < 2 ^ 64 by omega]

/-- Two consecutive reservations cannot emit the same sequence number. -/
theorem reservations_distinct (next a middle b after : Nat)
    (ha : reserveSequence next = some (a, middle))
    (hb : reserveSequence middle = some (b, after)) : a ≠ b := by
  have h₁ := reservation_advances next a middle ha
  have h₂ := reservation_advances middle b after hb
  omega

end TlsMpc.Tls13

namespace TlsMpc.Authenticated

/-- Shared conditional release: a failed authentication yields a zero buffer. -/
def releaseBit (valid plaintext : Boolean.Expr inputs) : Boolean.Expr inputs :=
  .select valid plaintext (.literal false)

theorem compiled_release_correct (valid plaintext : Boolean.Expr inputs)
    (env : Fin inputs → Bool) (stack : Boolean.Stack height) :
    (Boolean.compile (releaseBit valid plaintext) height).run env stack =
      .cons (if valid.eval env then plaintext.eval env else false) stack := by
  rw [Boolean.compile_correct]
  rfl

theorem rejected_release_zero (valid plaintext : Boolean.Expr inputs)
    (env : Fin inputs → Bool) (stack : Boolean.Stack height) (h : valid.eval env = false) :
    (Boolean.compile (releaseBit valid plaintext) height).run env stack =
      .cons false stack := by
  simp [compiled_release_correct, h]

/-- Receive-state writeback: authenticate before selecting any candidate state. -/
def commitBit (valid old candidate : Boolean.Expr inputs) : Boolean.Expr inputs :=
  .select valid candidate old

theorem rejected_commit_preserves (valid old candidate : Boolean.Expr inputs)
    (env : Fin inputs → Bool) (stack : Boolean.Stack height) (h : valid.eval env = false) :
    (Boolean.compile (commitBit valid old candidate) height).run env stack =
      .cons (old.eval env) stack := by
  simp [Boolean.compile_correct, commitBit, Boolean.Expr.eval, h]

end TlsMpc.Authenticated
