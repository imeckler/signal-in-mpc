import ChatResponseReferenceWork.StreamingV1.AbsoluteCursor
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

theorem terminal_lookup (leading tail : List (BitVec 8)) (byte : BitVec 8) :
    (leading ++ byte::tail)[leading.length]? = some byte := by
  have span : (leading ++ byte::tail).drop leading.length = byte::tail := by simp
  simpa only [List.head?_drop,List.head?_cons] using congrArg (fun bytes : List (BitVec 8) => bytes.head?) span

theorem reader_terminal_state (leading tail : List (BitVec 8)) (byte : BitVec 8)
    (bound : leading.length ≤ 9)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    VarintDecode.Spqr.decode (leading ++ byte::tail) =
      ⟨accumulated leading 0 0 ||| VarintDecode.Spqr.payload byte leading.length,leading.length+1,true⟩ := by
  let wire := leading ++ byte::tail
  have before := spec_run_prefix wire leading (byte::tail) 0 0 (by rfl) continues
  simp only [Nat.zero_add] at before
  have through : VarintDecode.Spqr.run wire (leading.length+1) 0 0 false =
      ⟨accumulated leading 0 0 ||| VarintDecode.Spqr.payload byte leading.length,leading.length+1,true⟩ := by
    rw [spec_run_add wire leading.length 1 0 0 false,before]
    simp only [wire,VarintDecode.Spqr.run,Bool.false_eq_true,if_false,terminal_lookup,Option.getD_some,terminal]
  have enough : leading.length+1 ≤ min 10 wire.length := by
    simp only [wire,List.length_append,List.length_cons]
    omega
  unfold VarintDecode.Spqr.decode
  change VarintDecode.Spqr.run wire (min 10 wire.length) 0 0 false = _
  rw [show min 10 wire.length = (leading.length+1)+(min 10 wire.length-(leading.length+1)) from by omega,
    spec_run_add,through]
  exact spec_run_done _ _ _ _

/-- The terminal byte and the independent strict tenth-byte guard construct the
actual accepted numeric row, including noncanonical encodings. No native result
or response validity is assumed. -/
theorem strict_terminal_row (leading tail : List (BitVec 8)) (byte : BitVec 8)
    (bound : leading.length ≤ 9)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (tenth : leading.length = 9 → byte.toNat < 2) :
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (leading ++ byte::tail) 0 =
      ⟨255,BitVec.ofNat 64 (leading.length+1),accumulated leading 0 0 ||| VarintDecode.Spqr.payload byte leading.length⟩ := by
  apply LibSignalReference.Candidate.ProstSkipSlice.prefix_accepted _ _ _
    (reader_terminal_state leading tail byte bound continues terminal) (by omega)
  intro ten
  have nine : leading.length = 9 := by omega
  have lookup := terminal_lookup leading tail byte
  rw [nine] at lookup
  rw [lookup]
  exact tenth nine

def coreDecoded (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) : BitVec 64 :=
  VarintDecode.Spqr.concrete.orWord state.value
    (TlsChatResponse.contribution VarintDecode.Spqr.concrete ByteAuth.concrete state.positions byte)

/-- Actual Core leading and terminal accumulation construct the strict reader row
used by the proved native Prost bridge. This closes the lexer value/count link,
without asserting the yet-unproved whole schema-streaming relation. -/
theorem core_terminal_row (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading tail : List (BitVec 8)) (byte : BitVec 8) (role : Nat) (roleBound : role < 3)
    (bound : leading.length ≤ 9) (modes : state.modes = lane role)
    (positions : state.positions = oneHot 0) (value : state.value = 0)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (tenth : leading.length = 9 → byte.toNat < 2) :
    ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (leading ++ byte::tail) 0 =
      ⟨255,BitVec.ofNat 64 (leading.length+1),coreDecoded (feed state leading) byte⟩ := by
  have raw := core_prefix_invariant state leading role 0 roleBound (by omega) modes positions continues
  have afterPositions : (feed state leading).positions = oneHot leading.length := by
    simpa only [Nat.zero_add] using raw.2.1
  have afterValue : (feed state leading).value = accumulated leading 0 0 := by
    simpa only [value] using raw.2.2
  rw [strict_terminal_row leading tail byte bound continues terminal tenth]
  simp only [coreDecoded,afterPositions,afterValue,contribution_one_hot leading.length (by omega) byte]
  rfl
#print axioms reader_terminal_state
#print axioms strict_terminal_row
#print axioms core_terminal_row
end ChatResponseReference.StreamingV1
