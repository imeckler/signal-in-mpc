import TlsMpc.ByteAuth

/-! Operation-level model for pinned SPQR's concrete slice decoder. In
particular, a terminating tenth byte is accepted even when its high payload
bits are truncated by the u64 shift. This is not Prost's stricter decoder. -/
namespace TlsMpc.Signal.VarintDecode.Spqr

structure State where
  value : BitVec 64
  index : Nat
  done : Bool
  deriving DecidableEq, Repr

def payload (byte : BitVec 8) (index : Nat) : BitVec 64 :=
  ((byte.setWidth 64) &&& 127) <<< (7 * index)

def terminates (byte : BitVec 8) : Bool := byte &&& 128 == 0

def run (bytes : List (BitVec 8)) : Nat → Nat → BitVec 64 → Bool → State
  | 0, index, value, done => ⟨value, index, done⟩
  | fuel + 1, index, value, done =>
      if done then ⟨value, index, true⟩
      else
        let byte := bytes[index]?.getD 0
        run bytes fuel (index + 1) (value ||| payload byte index) (terminates byte)

def decode (bytes : List (BitVec 8)) : State :=
  run bytes (min 10 bytes.length) 0 0 false

def valueBytes (value : BitVec 64) : List (BitVec 8) :=
  (List.range 8).map (fun i => value.extractLsb' (8 * (7 - i)) 8)

def encodeResult (state : State) : List (BitVec 8) :=
  if state.done then 255 :: BitVec.ofNat 8 state.index :: valueBytes state.value
  else List.replicate 10 0

theorem run_index_bounds (bytes : List (BitVec 8)) (fuel index : Nat)
    (value : BitVec 64) (done : Bool) :
    index ≤ (run bytes fuel index value done).index ∧
    (run bytes fuel index value done).index ≤ index + fuel := by
  induction fuel generalizing index value done with
  | zero => simp [run]
  | succ fuel ih =>
      cases done
      · simp only [run, Bool.false_eq_true, if_false]
        have h := ih (index + 1) (value ||| payload (bytes[index]?.getD 0) index)
          (terminates (bytes[index]?.getD 0))
        exact ⟨by omega, by omega⟩
      · simp [run]

theorem encodeResult_length (state : State) : (encodeResult state).length = 10 := by
  unfold encodeResult
  split <;> simp [valueBytes]

end TlsMpc.Signal.VarintDecode.Spqr
