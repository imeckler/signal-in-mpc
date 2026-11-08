import TlsMpc.Signal.PrivateProtoParseV1
namespace PrivateLengthV1.Padding
open TlsMpc TlsMpc.Signal

/-- Continuation-only padding contributes no payload, stop bit or count at any
index. This property is why zero padding is unsuitable for private bounds. -/
theorem sentinel_step (index : Nat)
    (state : VarintDecode.Spqr.CircuitState (BitVec 8) (BitVec 64)) :
    VarintDecode.Spqr.step VarintDecode.Spqr.concrete ByteAuth.concrete index 128 state = state := by
  rcases state with ⟨value,count,accepted⟩
  simp [VarintDecode.Spqr.step,VarintDecode.Spqr.concrete,ByteAuth.concrete,
    VarintDecode.Spqr.payload,BitVec.setWidth_and,BitVec.and_assoc]


def runSeq (bytes : List (BitVec 8)) (index : Nat)
    (state : VarintDecode.Spqr.CircuitState (BitVec 8) (BitVec 64)) :
    VarintDecode.Spqr.CircuitState (BitVec 8) (BitVec 64) :=
  match bytes with
  | [] => state
  | byte::rest => runSeq rest (index+1)
      (VarintDecode.Spqr.step VarintDecode.Spqr.concrete ByteAuth.concrete index byte state)

theorem runCore_seq (bytes : List (BitVec 8)) (fuel index : Nat)
    (state : VarintDecode.Spqr.CircuitState (BitVec 8) (BitVec 64))
    (bound : index+fuel ≤ bytes.length) :
    VarintDecode.Spqr.runCore VarintDecode.Spqr.concrete ByteAuth.concrete bytes fuel index state =
      runSeq ((bytes.drop index).take fuel) index state := by
  induction fuel generalizing index state with
  | zero => simp [VarintDecode.Spqr.runCore,runSeq]
  | succ fuel ih =>
    have inside : index < bytes.length := by omega
    rw [VarintDecode.Spqr.runCore,ih (index+1) _ (by omega)]
    rw [List.drop_eq_getElem_cons inside,List.take_succ_cons]
    simp [runSeq,List.getElem?_eq_getElem inside]

theorem seq_append (left right : List (BitVec 8)) (index : Nat)
    (state : VarintDecode.Spqr.CircuitState (BitVec 8) (BitVec 64)) :
    runSeq (left++right) index state = runSeq right (index+left.length) (runSeq left index state) := by
  induction left generalizing index state with
  | nil => simp [runSeq]
  | cons byte rest ih => simp [runSeq,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem seq_sentinel (count index : Nat)
    (state : VarintDecode.Spqr.CircuitState (BitVec 8) (BitVec 64)) :
    runSeq (List.replicate count 128) index state = state := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ,runSeq]
    rw [sentinel_step]
    exact ih (index+1)

theorem decodeCore_sentinel (bytes : List (BitVec 8)) (count : Nat) :
    VarintDecode.Spqr.decodeCore VarintDecode.Spqr.concrete ByteAuth.concrete
      (bytes++List.replicate count 128) =
    VarintDecode.Spqr.decodeCore VarintDecode.Spqr.concrete ByteAuth.concrete bytes := by
  have decode_seq (input : List (BitVec 8)) :
      VarintDecode.Spqr.decodeCore VarintDecode.Spqr.concrete ByteAuth.concrete input =
      VarintDecode.Spqr.finish VarintDecode.Spqr.concrete ByteAuth.concrete
        (runSeq (input.take 10) 0 ⟨0,0,0⟩) := by
    unfold VarintDecode.Spqr.decodeCore
    rw [runCore_seq _ _ _ _ (by omega)]
    simp only [List.drop_zero]
    by_cases short : input.length ≤ 10
    · simp [Nat.min_eq_right short,List.take_of_length_le short,VarintDecode.Spqr.concrete,ByteAuth.concrete]
    · have long : 10 ≤ input.length := by omega
      simp [Nat.min_eq_left long,VarintDecode.Spqr.concrete,ByteAuth.concrete]
  rw [decode_seq,decode_seq,List.take_append]
  simp only [List.take_replicate,seq_append]
  rw [seq_sentinel]

#print axioms sentinel_step
#print axioms decodeCore_sentinel
end PrivateLengthV1.Padding
