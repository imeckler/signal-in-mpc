import ChatResponseReferenceWork.ParserCircuitCandidateV1.StackMath
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1

def Canonical (mask : BitVec 8) : Prop := mask = 0 ∨ mask = 255
def CanonicalList (masks : List (BitVec 8)) : Prop := ∀ mask ∈ masks, Canonical mask

theorem canonical_zero : Canonical 0 := .inl rfl
theorem canonical_hot : Canonical 255 := .inr rfl

theorem canonical_and (x y : BitVec 8) (hx : Canonical x) (hy : Canonical y) :
    Canonical (ByteAuth.concrete.and x y) := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> first | exact .inl rfl | exact .inr rfl

theorem canonical_not (x : BitVec 8) (hx : Canonical x) : Canonical (ByteAuth.concrete.not x) := by
  rcases hx with rfl|rfl
  · exact .inr rfl
  · exact .inl rfl

theorem canonical_either (x y : BitVec 8) (hx : Canonical x) (hy : Canonical y) :
    Canonical (TlsWebSocketUpgrade.either ByteAuth.concrete x y) :=
  canonical_not _ (canonical_and _ _ (canonical_not _ hx) (canonical_not _ hy))

theorem canonical_select (mask yes no : BitVec 8) (hm : Canonical mask) (hy : Canonical yes) (hn : Canonical no) :
    Canonical (TlsInner.select ByteAuth.concrete mask yes no) := by
  rcases hm with rfl|rfl
  · rw [TlsInner.select_reject]; exact hn
  · rw [TlsInner.select_accept]; exact hy

theorem canonical_zeroMask : ∀ byte : BitVec 8, Canonical (ByteAuth.zeroMask ByteAuth.concrete byte) := by
  unfold Canonical
  decide +kernel

theorem canonical_terminal : ∀ byte : BitVec 8, Canonical (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)) := by
  unfold Canonical
  decide +kernel

theorem canonical_byte_eq (x y : BitVec 8) : Canonical (ByteAuth.eqMask ByteAuth.concrete x y) := canonical_zeroMask _

theorem canonical_get (masks : List (BitVec 8)) (index : Nat) (all : CanonicalList masks) :
    Canonical (TlsWebSocketUpgrade.get ByteAuth.concrete masks index) := by
  unfold TlsWebSocketUpgrade.get
  cases read : masks[index]? with
  | none => exact canonical_zero
  | some value => exact all value (List.mem_of_getElem? read)

theorem canonical_any_from (masks : List (BitVec 8)) (acc : BitVec 8) (all : CanonicalList masks) (initial : Canonical acc) :
    Canonical (masks.foldl (TlsWebSocketUpgrade.either ByteAuth.concrete) acc) := by
  induction masks generalizing acc with
  | nil => exact initial
  | cons mask rest ih =>
    exact ih _ (by intro x member; exact all x (by simp [member])) (canonical_either _ _ initial (all mask (by simp)))

theorem canonical_any (masks : List (BitVec 8)) (all : CanonicalList masks) :
    Canonical (TlsWebSocketUpgrade.any ByteAuth.concrete masks) := canonical_any_from masks 0 all canonical_zero

theorem canonical_equalMask (left right : List (BitVec 8)) : Canonical (ByteAuth.equalMask ByteAuth.concrete left right) := by
  induction left generalizing right with
  | nil => cases right <;> first | exact canonical_hot | exact canonical_zero
  | cons value rest ih =>
    cases right with
    | nil => exact canonical_zero
    | cons other tail => exact canonical_and _ _ (canonical_byte_eq value other) (ih tail)

theorem canonical_word_eq (left right : BitVec 64) : Canonical (Word64.eq Word64.concrete ByteAuth.concrete left right) :=
  canonical_equalMask _ _

theorem canonical_weq (word : BitVec 64) (number : Nat) :
    Canonical (TlsChatResponse.weq Word64.concrete ByteAuth.concrete word number) := canonical_word_eq _ _

theorem canonical_choose (mask : BitVec 8) (yes no : List (BitVec 8))
    (hm : Canonical mask) (hy : CanonicalList yes) (hn : CanonicalList no) :
    CanonicalList (TlsWebSocketUpgrade.choose ByteAuth.concrete mask yes no) := by
  induction yes generalizing no with
  | nil => intro value member; cases member
  | cons value rest ih =>
    cases no with
    | nil => intro value member; cases member
    | cons other tail =>
      intro result member
      change result ∈ TlsInner.select ByteAuth.concrete mask value other :: TlsWebSocketUpgrade.choose ByteAuth.concrete mask rest tail at member
      rcases List.mem_cons.mp member with rfl|later
      · exact canonical_select _ _ _ hm (hy value (by simp)) (hn other (by simp))
      · exact ih tail (by intro x member; exact hy x (by simp [member])) (by intro x member; exact hn x (by simp [member])) result later

#print axioms canonical_zeroMask
#print axioms canonical_terminal
#print axioms canonical_word_eq
#print axioms canonical_choose
end ChatResponseReference.ParserCircuitCandidateV1
