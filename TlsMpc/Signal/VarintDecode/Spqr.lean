import TlsMpc.Signal.VarintDecode.Spec

/-! Shared-input SPQR varint prefix decoding. All loops and indexing use public
lengths/positions; status, consumed count, value, and all intermediate masks
remain shared. The ten-byte output is status || count || valueBE8, zero on
MsgDecode. Noncanonical encodings and tenth-byte truncation match SPQR. -/
namespace TlsMpc.Signal.VarintDecode.Spqr
open Std.Tactic.BVDecide

structure Ops (B W : Type) where
  zero : W
  orByte : B → B → B
  orWord : W → W → W
  payload : B → Nat → W
  unpack : W → Nat → B

def concrete : Ops (BitVec 8) (BitVec 64) where
  zero := 0
  orByte := (· ||| ·)
  orWord := (· ||| ·)
  payload := payload
  unpack value i := value.extractLsb' (8 * (7 - i)) 8

def symbolic : Ops (BVExpr 8) (BVExpr 64) where
  zero := .const 0
  orByte x y := BvConstruct.bin x .or y
  orWord x y := BvConstruct.bin x .or y
  payload byte i := .shiftLeft
    (BvConstruct.bin (BvConstruct.extract 0 64 byte) .and (.const 127))
    (.const (BitVec.ofNat (7 * i + 1) (7 * i)))
  unpack value i := BvConstruct.extract (8 * (7 - i)) 8 value

structure Hom (o : Ops B W) (o' : Ops B' W') (f : B → B') (fw : W → W') : Prop where
  zero : fw o.zero = o'.zero
  orByte : ∀ x y, f (o.orByte x y) = o'.orByte (f x) (f y)
  orWord : ∀ x y, fw (o.orWord x y) = o'.orWord (fw x) (fw y)
  payload : ∀ byte i, fw (o.payload byte i) = o'.payload (f byte) i
  unpack : ∀ value i, f (o.unpack value i) = o'.unpack (fw value) i

def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  constructor
  · rfl
  · intros; simp [symbolic, concrete]
  · intros; simp [symbolic, concrete]
  · intro byte i
    have hn : 7 * i < 2 ^ (7 * i + 1) :=
      Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self (by decide))
    simp [symbolic, concrete, payload, BVExpr.eval_shiftLeft,
      ← BitVec.setWidth_ushiftRight_eq_extractLsb, Nat.mod_eq_of_lt hn]
  · intros; simp [symbolic, concrete]

structure CircuitState (B W : Type) where
  value : W
  count : B
  accepted : B

def CircuitState.map (f : B → B') (fw : W → W') (state : CircuitState B W) : CircuitState B' W' :=
  ⟨fw state.value, f state.count, f state.accepted⟩

def step (o : Ops B W) (a : ByteAuth.Ops B) (index : Nat) (byte : B)
    (state : CircuitState B W) : CircuitState B W :=
  let active := a.not state.accepted
  let stop := a.and active (a.not (a.maskBit byte 7))
  ⟨o.orWord state.value (o.payload (a.and active byte) index),
   o.orByte state.count (a.and stop (a.const (index + 1))),
   o.orByte state.accepted stop⟩

def runCore (o : Ops B W) (a : ByteAuth.Ops B) (bytes : List B) :
    Nat → Nat → CircuitState B W → CircuitState B W
  | 0, _, state => state
  | fuel + 1, index, state =>
      runCore o a bytes fuel (index + 1)
        (step o a index (bytes[index]?.getD (a.const 0)) state)

def finish (o : Ops B W) (a : ByteAuth.Ops B) (state : CircuitState B W) : List B :=
  state.accepted :: a.and state.accepted state.count ::
    (List.range 8).map (fun i => a.and state.accepted (o.unpack state.value i))

def decodeCore (o : Ops B W) (a : ByteAuth.Ops B) (bytes : List B) : List B :=
  finish o a (runCore o a bytes (min 10 bytes.length) 0 ⟨o.zero, a.const 0, a.const 0⟩)

section Refinement
variable {o : Ops B W} {o' : Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (ho : Hom o o' f fw) (ha : ByteAuth.Hom a a' f)
include ho ha

theorem step_map (index : Nat) (byte : B) (state : CircuitState B W) :
    (step o a index byte state).map f fw = step o' a' index (f byte) (state.map f fw) := by
  simp [step, CircuitState.map, ho.orWord, ho.orByte, ho.payload,
    ha.and, ha.not, ha.maskBit, ha.const]

theorem runCore_map (bytes : List B) (fuel index : Nat) (state : CircuitState B W) :
    (runCore o a bytes fuel index state).map f fw =
      runCore o' a' (bytes.map f) fuel index (state.map f fw) := by
  induction fuel generalizing index state with
  | zero => rfl
  | succ fuel ih =>
      simp only [runCore, ih, step_map ho ha, List.getElem?_map]
      cases bytes[index]? <;> simp [ha.const]

theorem finish_map (state : CircuitState B W) :
    (finish o a state).map f = finish o' a' (state.map f fw) := by
  simp [finish, CircuitState.map, List.map_map, Function.comp_def, ha.and, ho.unpack]

theorem decodeCore_map (bytes : List B) :
    (decodeCore o a bytes).map f = decodeCore o' a' (bytes.map f) := by
  unfold decodeCore
  rw [finish_map ho ha, runCore_map ho ha]
  simp only [List.length_map, CircuitState.map, ho.zero, ha.const]

end Refinement

theorem decodeCore_length (o : Ops B W) (a : ByteAuth.Ops B) (bytes : List B) :
    (decodeCore o a bytes).length = 10 := by simp [decodeCore, finish]

def stateOf (state : State) : CircuitState (BitVec 8) (BitVec 64) :=
  ⟨state.value, if state.done then BitVec.ofNat 8 state.index else 0,
    if state.done then 255 else 0⟩

@[simp] theorem byte_allOnes_and (byte : BitVec 8) : (255 : BitVec 8) &&& byte = byte :=
  BitVec.allOnes_and

@[simp] theorem byte_ofNat_allOnes_and (byte : BitVec 8) : BitVec.ofNat 8 255 &&& byte = byte :=
  BitVec.allOnes_and

theorem byte_ofNat_zero : BitVec.ofNat 8 0 = (0 : BitVec 8) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stopMask_value (byte : BitVec 8) :
    ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) =
      if terminates byte then 255 else 0 := by
  have all : ∀ byte : BitVec 8,
      ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) =
        if terminates byte then 255 else 0 := by decide +kernel
  exact all byte

theorem step_stopped (index : Nat) (byte count : BitVec 8) (value : BitVec 64) :
    step concrete ByteAuth.concrete index byte ⟨value, count, 255⟩ = ⟨value, count, 255⟩ := by
  simp [step, concrete, ByteAuth.concrete, payload]

theorem step_active (index : Nat) (byte : BitVec 8) (value : BitVec 64) :
    step concrete ByteAuth.concrete index byte ⟨value, 0, 0⟩ =
      stateOf ⟨value ||| payload byte index, index + 1, terminates byte⟩ := by
  simp only [step, stopMask_value]
  cases terminates byte <;> simp [concrete, ByteAuth.concrete, stateOf]

theorem runCore_stopped (bytes : List (BitVec 8)) (fuel index : Nat)
    (count : BitVec 8) (value : BitVec 64) :
    runCore concrete ByteAuth.concrete bytes fuel index ⟨value, count, 255⟩ = ⟨value, count, 255⟩ := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih => simp only [runCore, step_stopped, ih]

theorem runCore_spec (bytes : List (BitVec 8)) (fuel index : Nat) (value : BitVec 64) (done : Bool) :
    runCore concrete ByteAuth.concrete bytes fuel index (stateOf ⟨value, index, done⟩) =
      stateOf (run bytes fuel index value done) := by
  induction fuel generalizing index value done with
  | zero => rfl
  | succ fuel ih =>
      cases done with
      | true => simpa only [run, stateOf, if_true] using runCore_stopped bytes (fuel + 1) index (BitVec.ofNat 8 index) value
      | false =>
          change runCore concrete ByteAuth.concrete bytes (fuel + 1) index ⟨value, 0, 0⟩ = _
          rw [runCore]
          change runCore concrete ByteAuth.concrete bytes fuel (index + 1)
            (step concrete ByteAuth.concrete index (bytes[index]?.getD 0) ⟨value,0,0⟩) = _
          rw [step_active]
          exact ih (index + 1) (value ||| payload (bytes[index]?.getD 0) index) (terminates (bytes[index]?.getD 0))

theorem finish_spec (state : State) :
    finish concrete ByteAuth.concrete (stateOf state) = encodeResult state := by
  cases state with
  | mk value index done =>
      cases done <;> simp [finish, stateOf, encodeResult, valueBytes, concrete, ByteAuth.concrete]
      rfl

theorem decodeCore_spec (bytes : List (BitVec 8)) :
    decodeCore concrete ByteAuth.concrete bytes = encodeResult (decode bytes) := by
  change finish concrete ByteAuth.concrete
    (runCore concrete ByteAuth.concrete bytes (min 10 bytes.length) 0 (stateOf ⟨0,0,false⟩)) = _
  rw [runCore_spec, finish_spec]
  rfl

theorem compiled_decodeCore_correct (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (decodeCore symbolic ByteAuth.symbolic bytes).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (decodeCore symbolic ByteAuth.symbolic bytes))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (decodeCore symbolic ByteAuth.symbolic bytes))).vec.get index hi)) =
      (ByteCircuit.joinValue (encodeResult (decode (bytes.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,
    decodeCore_map (evaluationHom assign) (ByteAuth.evaluationHom assign), decodeCore_spec]

end TlsMpc.Signal.VarintDecode.Spqr
