/-!
# The agreed clock of the two controllers

Each controller reads its own clock (milliseconds since the Unix epoch), sends it to the other
(`swap`, SECURITY_MAP A.2 rows 1485, 2114, 2992), and both use the later of the two, provided the
two are within two minutes; otherwise the session ends. Both parties compute the same value
(`agree_symm`), and that value is never more than two minutes ahead of either party's own clock
(`agreed_within`): the other party cannot push this party's back-off, keepalive or message
timestamps further than that (SECURITY_MAP D.11).

This is `Policy/Clock` of REORGANIZATION_PLAN.md (stage S4), brought forward in S0 to fix
`agreedClock`, which took the later clock without the check. Pure: no I/O.
-/

namespace TlsMpc.Node.Policy.Clock

/-- The largest difference between the two parties' clocks a session accepts, in milliseconds. -/
def maxSkew : Nat := 120000

/-- The session's clock from this party's reading `mine` and the other's `theirs`: the later of
the two, or an error when they differ by more than `maxSkew`. -/
def agree (mine theirs : Nat) : Except String Nat :=
  if mine ≤ theirs + maxSkew ∧ theirs ≤ mine + maxSkew then .ok (max mine theirs)
  else .error "the two parties' clocks differ by more than two minutes"

/-- An agreed clock is at least this party's own and at most `maxSkew` ahead of it. -/
theorem agreed_within {mine theirs t : Nat} (h : agree mine theirs = .ok t) :
    mine ≤ t ∧ t ≤ mine + maxSkew := by
  unfold agree at h
  split at h
  · cases h
    omega
  · cases h

/-- Both parties agree on the same value (or both refuse). -/
theorem agree_symm (mine theirs : Nat) : agree mine theirs = agree theirs mine := by
  unfold agree
  by_cases h : mine ≤ theirs + maxSkew ∧ theirs ≤ mine + maxSkew
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, Nat.max_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]

/-- Clocks within the bound always agree, on the later one. -/
theorem agree_ok {mine theirs : Nat} (h₁ : mine ≤ theirs + maxSkew) (h₂ : theirs ≤ mine + maxSkew) :
    agree mine theirs = .ok (max mine theirs) := by
  unfold agree
  rw [if_pos ⟨h₁, h₂⟩]

end TlsMpc.Node.Policy.Clock
