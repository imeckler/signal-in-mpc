import ChatResponseReferenceWork.StreamingV1.VarintReference
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

def lane (index : Nat) : List (BitVec 8) :=
  (List.range 4).map (fun i => if i = index then 255 else 0)

theorem lane_active (index : Nat) (bound : index < 3) :
    TlsWebSocketUpgrade.any ByteAuth.concrete ((lane index).take 3) = 255 := by
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases cases with h|h|h <;> subst index <;> rfl

theorem core_value_continue (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (role group : Nat) (roleBound : role < 3) (groupBound : group < 10) (byte : BitVec 8)
    (modes : state.modes = lane role) (positions : state.positions = oneHot group)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.value =
      state.value ||| VarintDecode.Spqr.payload byte group := by
  have active : TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3) = 255 := by
    rw [modes]; exact lane_active role roleBound
  have terminal : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 0 := by
    rw [terminal_exact byte,continues]; rfl
  change Word64.concrete.select
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) 0
    (Word64.concrete.select (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
      (VarintDecode.Spqr.concrete.orWord state.value
        (TlsChatResponse.contribution VarintDecode.Spqr.concrete ByteAuth.concrete state.positions byte)) state.value) = _
  rw [active,terminal,positions,contribution_one_hot group groupBound byte]
  change Word64.concrete.select 0 0 (Word64.concrete.select 255 (state.value ||| VarintDecode.Spqr.payload byte group) state.value) = _
  rw [Word64.select_reject,Word64.select_accept]

theorem core_positions_continue (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (role group : Nat) (roleBound : role < 3) (groupBound : group < 9) (byte : BitVec 8)
    (modes : state.modes = lane role) (positions : state.positions = oneHot group)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.positions =
      oneHot (group+1) := by
  have active : TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3) = 255 := by
    rw [modes]; exact lane_active role roleBound
  have terminal : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 0 := by
    rw [terminal_exact byte,continues]; rfl
  change TlsWebSocketUpgrade.choose ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
    (TlsWebSocketUpgrade.initial ByteAuth.concrete 9)
    (TlsWebSocketUpgrade.choose ByteAuth.concrete
      (TlsWebSocketUpgrade.any ByteAuth.concrete (state.modes.take 3))
      (0::state.positions.take 9) state.positions) = _
  rw [active,terminal,positions]
  have cases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 ∨ group = 5 ∨ group = 6 ∨ group = 7 ∨ group = 8 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h <;> subst group <;> rfl

theorem core_modes_continue (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (role : Nat) (roleBound : role < 3) (byte : BitVec 8)
    (modes : state.modes = lane role)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.modes = lane role := by
  have terminal : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 0 := by
    rw [terminal_exact byte,continues]; rfl
  simp only [TlsChatResponse.step]
  rw [terminal,modes]
  have cases : role = 0 ∨ role = 1 ∨ role = 2 := by omega
  rcases cases with h|h|h <;> subst role <;>
    simp [lane,TlsWebSocketUpgrade.get,TlsWebSocketUpgrade.any,TlsWebSocketUpgrade.either,ByteAuth.concrete] <;> rfl

noncomputable def feed (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (bytes : List (BitVec 8)) :=
  bytes.foldl (fun state byte => (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state) state

def accumulated (bytes : List (BitVec 8)) (index : Nat) (value : BitVec 64) : BitVec 64 :=
  match bytes with
  | [] => value
  | byte::rest => accumulated rest (index+1) (value ||| VarintDecode.Spqr.payload byte index)

/-- Actual Core prefix invariant in key/scalar/length lanes: all nonterminating
prefix bytes preserve the lane, advance the private group position, and accumulate
exact varint payload. No response/schema-validity assumption is supplied. -/
theorem core_prefix_invariant (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (role group : Nat) (roleBound : role < 3)
    (bound : group + bytes.length ≤ 9) (modes : state.modes = lane role)
    (positions : state.positions = oneHot group)
    (continues : ∀ byte ∈ bytes, VarintDecode.Spqr.terminates byte = false) :
    (feed state bytes).modes = lane role ∧
    (feed state bytes).positions = oneHot (group + bytes.length) ∧
    (feed state bytes).value = accumulated bytes group state.value := by
  induction bytes generalizing state group with
  | nil => exact ⟨modes,positions,rfl⟩
  | cons byte rest ih =>
    have byteContinues := continues byte (by simp)
    have groupBound : group < 9 := by simp only [List.length_cons] at bound; omega
    have nextModes := core_modes_continue state role roleBound byte modes byteContinues
    have nextPositions := core_positions_continue state role group roleBound groupBound byte modes positions byteContinues
    have nextValue := core_value_continue state role group roleBound (by omega) byte modes positions byteContinues
    have next := ih (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
      (group+1) (by simp only [List.length_cons] at bound; omega) nextModes nextPositions
      (by intro byte member; exact continues byte (by simp [member]))
    simpa only [feed,List.foldl_cons,List.length_cons,accumulated,nextValue,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
#print axioms core_value_continue
#print axioms core_modes_continue
#print axioms core_prefix_invariant
end ChatResponseReference.StreamingV1
