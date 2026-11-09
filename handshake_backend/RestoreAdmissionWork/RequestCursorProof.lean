import TlsMpc.TlsPrivateRequestId
namespace TlsMpc.TlsPrivateRequestId.Batch
open Signal
-- The exact repeated existing `next` operation used in allocation order.
def cursorAfter : Nat → BitVec 64 → BitVec 64
  | 0, id => id
  | n+1, id => (next Word64.concrete ByteAuth.concrete (cursorAfter n id)).2

theorem cursorAfter_exact (n : Nat) (id : BitVec 64)
    (lower : 2^63 ≤ id.toNat) (room : id.toNat+n < 2^64) :
    (cursorAfter n id).toNat = id.toNat+n := by
  induction n with
  | zero => simp [cursorAfter]
  | succ n ih =>
    have old := ih (by omega)
    have bound : 2^63 ≤ (cursorAfter n id).toNat ∧
        (cursorAfter n id).toNat ≤ 2^64-2 := by omega
    have step := (next_increases (cursorAfter n id) bound).2
    change (next Word64.concrete ByteAuth.concrete (cursorAfter n id)).2.toNat = _
    omega

theorem accepted_at (count i : Nat) (id : BitVec 64)
    (lower : 2^63 ≤ id.toNat) (room : id.toNat+count < 2^64) (inside : i<count) :
    (next Word64.concrete ByteAuth.concrete (cursorAfter i id)).1 = 255 := by
  have exact := cursorAfter_exact i id lower (by omega)
  exact (next_increases (cursorAfter i id) (by omega)).1

theorem allocation_distinct (count i j : Nat) (id : BitVec 64)
    (lower : 2^63 ≤ id.toNat) (room : id.toNat+count < 2^64)
    (hi : i<count) (hj : j<count) (different : i≠j) :
    cursorAfter i id ≠ cursorAfter j id := by
  intro equal
  have left := cursorAfter_exact i id lower (by omega)
  have right := cursorAfter_exact j id lower (by omega)
  have same := congrArg BitVec.toNat equal
  omega

-- Covers the runtime's public1..4 admission profile; the arithmetic theorem
-- itself holds for any accepted bounded range, without a private-ID opening.
theorem staged_batch (count : Nat) (id : BitVec 64)
    (_capacity : 1≤count ∧ count≤4) (lower : 2^63≤id.toNat)
    (room : id.toNat+count<2^64) :
    (cursorAfter count id).toNat=id.toNat+count ∧
    (∀ i, i<count → (next Word64.concrete ByteAuth.concrete (cursorAfter i id)).1=255) ∧
    (∀ i j, i<count → j<count → i≠j → cursorAfter i id≠cursorAfter j id) := by
  exact ⟨cursorAfter_exact count id lower room,
    fun i hi => accepted_at count i id lower room hi,
    fun i j hi hj different => allocation_distinct count i j id lower room hi hj different⟩

theorem rejected_next (id : BitVec 64)
    (outside : ¬(2^63≤id.toNat ∧ id.toNat≤2^64-2)) :
    next Word64.concrete ByteAuth.concrete id = (0,0) := by
  simp only [next,allowed_value,if_neg outside,Word64.select_reject]
  rfl

#print axioms staged_batch
#print axioms rejected_next
#print axioms compiled_next_correct
end TlsMpc.TlsPrivateRequestId.Batch
