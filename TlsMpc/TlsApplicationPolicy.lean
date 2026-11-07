import TlsMpc.Protocols

/-! Public application traffic state for the AES-128-GCM TLS profile.
RFC9846 sections4.7.3,5.3,5.5. Sending uses a conservative2^24-record budget,
including controls. One slot is reserved for KeyUpdate/close. Receive enforces
only sequence exhaustion, not the sender's record/epoch policy. State must be
reserved before effects; an uncertain effect aborts instead of rolling back.
-/
namespace TlsMpc.TlsApplicationPolicy

def recordLimit : Nat := 2^24
def maxSendEpoch : Nat := 2^48-1

structure State where
  sendEpoch : Nat := 0
  sendNext : Nat := 0
  receiveEpoch : Nat := 0
  receiveNext : Nat := 0
  responseDue : Bool := false
  requestOutstanding : Bool := false
  sendClosed : Bool := false
  receiveClosed : Bool := false
  pendingUpdate : Option Bool := none
  aborted : Bool := false
  deriving BEq, Repr

structure Reservation where
  epoch : Nat
  sequence : Nat
  deriving BEq, Repr

def abort (s : State) : State := { s with aborted := true }

def needsUpdate (s : State) : Bool := s.responseDue || s.sendNext ≥ recordLimit-1

def reserveApplication (s : State) : Option (Reservation × State) :=
  if !s.aborted && !s.sendClosed && s.pendingUpdate.isNone && !needsUpdate s then
    some (⟨s.sendEpoch,s.sendNext⟩, { s with sendNext := s.sendNext+1 })
  else none

def reserveUpdate (s : State) (request : Bool) : Option (Reservation × State) :=
  if !s.aborted && !s.sendClosed && s.pendingUpdate.isNone &&
      s.sendEpoch < maxSendEpoch && s.sendNext < recordLimit &&
      !(request && (s.requestOutstanding || s.responseDue)) then
    some (⟨s.sendEpoch,s.sendNext⟩,
      { s with sendNext := s.sendNext+1, pendingUpdate := some request })
  else none

/-- Called only after sealing/sending with OLD keys and installing NEW keys. -/
def commitUpdate (s : State) : Option State :=
  if s.aborted || s.sendClosed then none
  else s.pendingUpdate.map fun request =>
    { s with
      sendEpoch := s.sendEpoch+1
      sendNext := 0
      pendingUpdate := none
      responseDue := false
      requestOutstanding := s.requestOutstanding || request }

def reserveReceive (s : State) : Option (Reservation × State) :=
  if !s.aborted && !s.receiveClosed && s.receiveNext < 2^64 then
    some (⟨s.receiveEpoch,s.receiveNext⟩, { s with receiveNext := s.receiveNext+1 })
  else none

/-- Authenticated complete KeyUpdate only. Receiving epoch counts are unbounded.
Any peer update satisfies an outstanding request. At the sending epoch ceiling
ignore a response request, as RFC9846 permits, then close at the send-use limit. -/
def receiveUpdate (s : State) (request : Bool) : State :=
  { s with
    receiveEpoch := s.receiveEpoch+1
    receiveNext := 0
    requestOutstanding := false
    responseDue := s.responseDue || (request && s.sendEpoch < maxSendEpoch) }

def reserveClose (s : State) : Option (Reservation × State) :=
  if !s.aborted && !s.sendClosed && s.pendingUpdate.isNone && s.sendNext < recordLimit then
    some (⟨s.sendEpoch,s.sendNext⟩, { s with sendNext := s.sendNext+1, sendClosed := true })
  else none

def receiveClose (s : State) : State := { s with receiveClosed := true }

theorem application_reservation (s after : State) (ticket : Reservation)
    (h : reserveApplication s = some (ticket,after)) :
    ticket.epoch = s.sendEpoch ∧ ticket.sequence = s.sendNext ∧
    after.sendNext = s.sendNext+1 ∧ ticket.sequence < recordLimit-1 ∧
    after.sendEpoch = s.sendEpoch := by
  unfold reserveApplication at h
  split at h
  · rename_i valid
    cases h
    simp [needsUpdate] at valid
    exact ⟨rfl,rfl,rfl,by change s.sendNext < recordLimit-1; omega,rfl⟩
  · contradiction

theorem consecutive_application_distinct (s mid after : State) (a b : Reservation)
    (ha : reserveApplication s = some (a,mid))
    (hb : reserveApplication mid = some (b,after)) : a.sequence ≠ b.sequence := by
  have h₁ := application_reservation _ _ _ ha
  have h₂ := application_reservation _ _ _ hb
  omega

theorem update_uses_old_epoch (s after : State) (ticket : Reservation) (request : Bool)
    (h : reserveUpdate s request = some (ticket,after)) :
    ticket.epoch = s.sendEpoch ∧ after.sendEpoch = s.sendEpoch ∧
    after.sendNext = s.sendNext+1 ∧ after.pendingUpdate = some request := by
  unfold reserveUpdate at h
  split at h
  · cases h; exact ⟨rfl,rfl,rfl,rfl⟩
  · contradiction

theorem requested_update_not_response (s after : State) (ticket : Reservation)
    (h : reserveUpdate s true = some (ticket,after)) :
    s.requestOutstanding = false ∧ s.responseDue = false := by
  unfold reserveUpdate at h
  split at h
  · rename_i valid
    simp at valid
    exact valid.2
  · contradiction

theorem commit_changes_epoch (s after : State) (h : commitUpdate s = some after) :
    after.sendEpoch = s.sendEpoch+1 ∧ after.sendNext = 0 ∧
    after.pendingUpdate = none ∧ after.responseDue = false := by
  unfold commitUpdate at h
  split at h
  · contradiction
  · cases hp : s.pendingUpdate <;> simp [hp] at h
    cases h; exact ⟨rfl,rfl,rfl,rfl⟩

theorem pending_blocks_application (s : State) (request : Bool)
    (h : s.pendingUpdate = some request) : reserveApplication s = none := by
  simp [reserveApplication,h]

theorem response_blocks_application (s : State) (h : s.responseDue = true) :
    reserveApplication s = none := by simp [reserveApplication,needsUpdate,h]

theorem aborted_blocks (s : State) : reserveApplication (abort s) = none ∧
    reserveUpdate (abort s) false = none ∧ reserveUpdate (abort s) true = none ∧
    reserveReceive (abort s) = none ∧ reserveClose (abort s) = none := by
  simp [abort,reserveApplication,reserveUpdate,reserveReceive,reserveClose]

theorem receive_reservation (s after : State) (ticket : Reservation)
    (h : reserveReceive s = some (ticket,after)) :
    ticket.sequence = s.receiveNext ∧ after.receiveNext = s.receiveNext+1 ∧ ticket.sequence < 2^64 := by
  unfold reserveReceive at h
  split at h
  · rename_i valid
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
    exact ⟨rfl,rfl,valid.2⟩
  · contradiction

theorem receive_update_resets (s : State) (request : Bool) :
    (receiveUpdate s request).receiveEpoch = s.receiveEpoch+1 ∧
    (receiveUpdate s request).receiveNext = 0 ∧
    (receiveUpdate s request).requestOutstanding = false := ⟨rfl,rfl,rfl⟩

theorem receive_close_preserves_send (s : State) :
    (receiveClose s).sendClosed = s.sendClosed ∧
    (receiveClose s).sendEpoch = s.sendEpoch ∧ (receiveClose s).sendNext = s.sendNext := ⟨rfl,rfl,rfl⟩

end TlsMpc.TlsApplicationPolicy
