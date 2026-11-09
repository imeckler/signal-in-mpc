import ChatResponseReferenceWork.StreamingV1.TerminalKey
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def wireLane (wire : Nat) : Nat :=
  if wire = 0 then 1 else if wire = 2 then 2 else if wire = 3 ∨ wire = 4 then 0 else 3

/-- Actual lexer control transition for each protobuf wire kind. Schema
recognition, wrong-wire rejection and recursion checks are separate validity
conditions; no successful-parse premise hides those conditions here. -/
theorem key_terminal_modes (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (wire : Nat) (wireBound : wire ≤ 5)
    (modes : state.modes = lane 0)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (kind : coreDecoded state byte &&& 7 = BitVec.ofNat 64 wire) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.modes =
      lane (wireLane wire) := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  unfold coreDecoded at kind
  simp only [TlsChatResponse.step]
  rw [ended,modes]
  change Word64.concrete.band
    (VarintDecode.Spqr.concrete.orWord state.value
      (TlsChatResponse.contribution VarintDecode.Spqr.concrete ByteAuth.concrete state.positions byte))
    (Word64.concrete.const 7) = Word64.concrete.const wire at kind
  rw [kind]
  have cases : wire = 0 ∨ wire = 1 ∨ wire = 2 ∨ wire = 3 ∨ wire = 4 ∨ wire = 5 := by omega
  rcases cases with h|h|h|h|h|h <;> subst wire <;>
    simp [wireLane,lane,TlsWebSocketUpgrade.get,TlsWebSocketUpgrade.either,TlsChatResponse.weq,
      Word64.eq,Word64.bytes,Word64.concrete,ByteAuth.concrete] <;> rfl

theorem key_terminal_tag (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 0)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.tag =
      coreDecoded state byte >>> 3 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  change Word64.concrete.select
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
    (Word64.concrete.shift (coreDecoded state byte) 3) state.tag = _
  rw [modes,ended]
  exact Word64.select_accept _ _

theorem terminal_value_reset (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (role : Nat) (roleBound : role < 3)
    (modes : state.modes = lane role) (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.value = 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  have active : TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3) = 255 := by
    rw [modes]; exact lane_active role roleBound
  change Word64.concrete.select
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) 0 _ = 0
  rw [ended,active]
  exact Word64.select_accept _ _

open Aeneas Aeneas.Std
open LibSignalReference.Candidate.ProstSkipKey
/-- Successful source key validation supplies the wire-kind equality needed by
Core's control transition. It is derived from the actual validation branch. -/
theorem native_key_kind (native : U64) (tag : U32) (wire : WireType)
    (accepted : keyResult native = .Ok (tag,wire)) :
    native.bv &&& 7 = BitVec.ofNat 64 (wireNumber wire) := by
  have fields := key_success_fields native tag wire accepted
  apply BitVec.eq_of_toNat_eq
  have small : wireNumber wire < 2^64 := by cases wire <;> decide
  simp only [BitVec.toNat_and,UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  change native.val &&& (2^3-1) = wireNumber wire
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact fields.2.2.2.symm

theorem native_key_modes (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (native : U64) (tag : U32) (wire : WireType)
    (modes : state.modes = lane 0) (terminal : VarintDecode.Spqr.terminates byte = true)
    (value : native.bv = coreDecoded state byte)
    (accepted : keyResult native = .Ok (tag,wire)) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.modes =
      lane (wireLane (wireNumber wire)) := by
  apply key_terminal_modes state byte (wireNumber wire) (by cases wire <;> decide) modes terminal
  rw [←value]
  exact native_key_kind native tag wire accepted

theorem native_key_tag (native : U64) (tag : U32) (wire : WireType)
    (accepted : keyResult native = .Ok (tag,wire)) :
    native.bv >>> 3 = BitVec.ofNat 64 tag.val := by
  have fields := key_success_fields native tag wire accepted
  apply BitVec.eq_of_toNat_eq
  have small : tag.val < 2^64 := by have bound := fields.1.1; have tagValue := fields.2.2.1; omega
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,UScalar.bv_toNat,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  exact fields.2.2.1.symm

theorem native_tag_transition (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (native : U64) (tag : U32) (wire : WireType)
    (modes : state.modes = lane 0) (terminal : VarintDecode.Spqr.terminates byte = true)
    (value : native.bv = coreDecoded state byte)
    (accepted : keyResult native = .Ok (tag,wire)) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.tag =
      BitVec.ofNat 64 tag.val := by
  rw [key_terminal_tag state byte modes terminal,←value]
  exact native_key_tag native tag wire accepted

#print axioms key_terminal_modes
#print axioms key_terminal_tag
#print axioms terminal_value_reset
#print axioms native_key_kind
#print axioms native_key_modes
#print axioms native_key_tag
#print axioms native_tag_transition
end ChatResponseReference.StreamingV1
