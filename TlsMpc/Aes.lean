import TlsMpc.AesSbox
import TlsMpc.ByteCircuit

/-!
AES encryption specification, FIPS 197-upd1 sections 4.2, 5.1 and 5.2.
Bytes are in standard column-major state order. Key schedule control and every
array index are public. The checked interface accepts AES-128 and AES-256.
AES-192 is not exposed by this implementation. There is no I/O or reveal.
-/

namespace TlsMpc.Aes
open Std.Tactic.BVDecide

structure Ops (B : Type) where
  const : Nat → B
  xor : B → B → B
  sbox : B → B
  xtime : B → B

/-- Multiply by x modulo x^8+x^4+x^3+x+1. -/
def xtimeValue (x : BitVec 8) : BitVec 8 :=
  (x <<< (1 : BitVec 1)) ^^^ (BitVec.replicate 8 (x.extractLsb' 7 1) &&& 0x1b)

def xtimeExpr (x : BVExpr 8) : BVExpr 8 :=
  BvConstruct.bin (.shiftLeft x (.const (1 : BitVec 1))) .xor
    (BvConstruct.bin (.replicate 8 (BvConstruct.extract 7 1 x) rfl) .and (.const 0x1b))

def concrete : Ops (BitVec 8) := ⟨BitVec.ofNat 8, (· ^^^ ·), AesSbox.spec, xtimeValue⟩
def symbolic : Ops (BVExpr 8) :=
  ⟨(fun n => .const (BitVec.ofNat 8 n)), (fun a b => BvConstruct.bin a .xor b),
    AesSbox.expr, xtimeExpr⟩

def get (o : Ops B) (xs : List B) (i : Nat) : B := xs[i]?.getD (o.const 0)

def subBytes (o : Ops B) (state : List B) : List B := state.map o.sbox

def shiftRows (o : Ops B) (state : List B) : List B :=
  (List.range 16).map (fun i => get o state (4 * ((i / 4 + i % 4) % 4) + i % 4))

def mixByte (o : Ops B) (a b c d : B) : B :=
  o.xor (o.xor (o.xor (o.xtime a) (o.xor (o.xtime b) b)) c) d

def mixColumns (o : Ops B) (state : List B) : List B :=
  (List.range 16).map (fun i =>
    let col := 4 * (i / 4)
    let row := i % 4
    mixByte o (get o state (col + row)) (get o state (col + (row + 1) % 4))
      (get o state (col + (row + 2) % 4)) (get o state (col + (row + 3) % 4)))

def addRoundKey (o : Ops B) (state key : List B) : List B := List.zipWith o.xor state key

def roundConstants : List Nat := [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]

def scheduleByte (o : Ops B) (nk i : Nat) (expanded : List B) (j : Nat) : B :=
  let previous := get o expanded (4 * (i - 1) + (if i % nk = 0 then (j + 1) % 4 else j))
  let temp := if i % nk = 0 then
      o.xor (o.sbox previous) (o.const (if j = 0 then roundConstants[i / nk - 1]?.getD 0 else 0))
    else if nk = 8 ∧ i % nk = 4 then o.sbox previous else previous
  o.xor (get o expanded (4 * (i - nk) + j)) temp

def scheduleStep (o : Ops B) (nk i : Nat) (expanded : List B) : List B :=
  expanded ++ (List.range 4).map (scheduleByte o nk i expanded)

def scheduleLoop (o : Ops B) (nk : Nat) : Nat → Nat → List B → List B
  | 0, _, expanded => expanded
  | n + 1, i, expanded => scheduleLoop o nk n (i + 1) (scheduleStep o nk i expanded)

def expandKey (o : Ops B) (nk rounds : Nat) (key : List B) : List B :=
  scheduleLoop o nk (4 * (rounds + 1) - nk) nk key

def round (o : Ops B) (key state : List B) : List B :=
  addRoundKey o (mixColumns o (shiftRows o (subBytes o state))) key

def middleRounds (o : Ops B) (expanded : List B) : Nat → Nat → List B → List B
  | 0, _, state => state
  | n + 1, index, state => middleRounds o expanded n (index + 1)
      (round o ((expanded.drop (16 * index)).take 16) state)

/-- Reuse the secret expanded key across blocks, as required for practical GCM. -/
def encryptExpanded (o : Ops B) (rounds : Nat) (expanded block : List B) : List B :=
  let initial := addRoundKey o block (expanded.take 16)
  let state := middleRounds o expanded (rounds - 1) 1 initial
  addRoundKey o (shiftRows o (subBytes o state)) ((expanded.drop (16 * rounds)).take 16)

/-- Internal total function. Use nk=4, rounds=10 or nk=8, rounds=14, with
exact key and block lengths; `encrypt` checks those public preconditions. -/
def encryptCore (o : Ops B) (nk rounds : Nat) (key block : List B) : List B :=
  encryptExpanded o rounds (expandKey o nk rounds key) block

def encrypt (o : Ops B) (key block : List B) : Option (List B) :=
  if block.length = 16 then
    if key.length = 16 then some (encryptCore o 4 10 key block)
    else if key.length = 32 then some (encryptCore o 8 14 key block)
    else none
  else none

structure Hom (a : Ops B) (b : Ops B') (f : B → B') : Prop where
  const : ∀ n, f (a.const n) = b.const n
  xor : ∀ x y, f (a.xor x y) = b.xor (f x) (f y)
  sbox : ∀ x, f (a.sbox x) = b.sbox (f x)
  xtime : ∀ x, f (a.xtime x) = b.xtime (f x)

def evaluationHom (assign : BVExpr.Assignment) : Hom symbolic concrete (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [symbolic, concrete, AesSbox.expr_refines, xtimeExpr, xtimeValue]

section Refinement
variable {a : Ops B} {b : Ops B'} {f : B → B'} (h : Hom a b f)
include h

theorem get_map (xs : List B) (i : Nat) : f (get a xs i) = get b (xs.map f) i := by
  simp [get, ← h.const 0]

theorem subBytes_map (state : List B) : (subBytes a state).map f = subBytes b (state.map f) := by
  simp [subBytes, List.map_map, Function.comp_def, h.sbox]

theorem shiftRows_map (state : List B) : (shiftRows a state).map f = shiftRows b (state.map f) := by
  simp [shiftRows, List.map_map, Function.comp_def, get_map h]

theorem mixByte_map (x y z w : B) :
    f (mixByte a x y z w) = mixByte b (f x) (f y) (f z) (f w) := by
  simp [mixByte, h.xor, h.xtime]

theorem mixColumns_map (state : List B) : (mixColumns a state).map f = mixColumns b (state.map f) := by
  simp [mixColumns, List.map_map, Function.comp_def, mixByte_map h, get_map h]

theorem addRoundKey_map (state key : List B) :
    (addRoundKey a state key).map f = addRoundKey b (state.map f) (key.map f) := by
  induction state generalizing key with
  | nil => simp [addRoundKey]
  | cons x xs ih =>
      cases key with
      | nil => rfl
      | cons k ks =>
          change f (a.xor x k) :: (addRoundKey a xs ks).map f =
            b.xor (f x) (f k) :: addRoundKey b (xs.map f) (ks.map f)
          rw [h.xor, ih]

theorem scheduleByte_map (nk i : Nat) (expanded : List B) (j : Nat) :
    f (scheduleByte a nk i expanded j) = scheduleByte b nk i (expanded.map f) j := by
  by_cases hi : i % nk = 0
  · simp only [scheduleByte, if_pos hi, h.xor, h.sbox, h.const, get_map h]
  · by_cases hk : nk = 8 ∧ i % nk = 4
    · simp only [scheduleByte, if_neg hi, if_pos hk, h.xor, h.sbox, get_map h]
    · simp only [scheduleByte, if_neg hi, if_neg hk, h.xor, get_map h]

theorem scheduleStep_map (nk i : Nat) (expanded : List B) :
    (scheduleStep a nk i expanded).map f = scheduleStep b nk i (expanded.map f) := by
  simp [scheduleStep, List.map_map, Function.comp_def, scheduleByte_map h]

theorem scheduleLoop_map (nk n i : Nat) (expanded : List B) :
    (scheduleLoop a nk n i expanded).map f = scheduleLoop b nk n i (expanded.map f) := by
  induction n generalizing i expanded with
  | zero => rfl
  | succ n ih => simp [scheduleLoop, ih, scheduleStep_map h]

theorem expandKey_map (nk rounds : Nat) (key : List B) :
    (expandKey a nk rounds key).map f = expandKey b nk rounds (key.map f) := by
  exact scheduleLoop_map h _ _ _ _

theorem round_map (key state : List B) :
    (round a key state).map f = round b (key.map f) (state.map f) := by
  simp [round, addRoundKey_map h, mixColumns_map h, shiftRows_map h, subBytes_map h]

theorem middleRounds_map (expanded : List B) (n index : Nat) (state : List B) :
    (middleRounds a expanded n index state).map f =
      middleRounds b (expanded.map f) n index (state.map f) := by
  induction n generalizing index state with
  | zero => rfl
  | succ n ih => simp [middleRounds, ih, round_map h]

theorem encryptExpanded_map (rounds : Nat) (expanded block : List B) :
    (encryptExpanded a rounds expanded block).map f =
      encryptExpanded b rounds (expanded.map f) (block.map f) := by
  simp [encryptExpanded, addRoundKey_map h, shiftRows_map h, subBytes_map h, middleRounds_map h]

theorem encryptCore_map (nk rounds : Nat) (key block : List B) :
    (encryptCore a nk rounds key block).map f = encryptCore b nk rounds (key.map f) (block.map f) := by
  simp [encryptCore, encryptExpanded_map h, expandKey_map h]

theorem encrypt_map (key block : List B) :
    (encrypt a key block).map (List.map f) = encrypt b (key.map f) (block.map f) := by
  by_cases hb : block.length = 16
  · by_cases h16 : key.length = 16
    · simp [encrypt, hb, h16, encryptCore_map h]
    · by_cases h32 : key.length = 32 <;> simp [encrypt, hb, h16, h32, encryptCore_map h]
  · simp [encrypt, hb]

end Refinement

theorem scheduleLoop_length (o : Ops B) (nk n i : Nat) (expanded : List B) :
    (scheduleLoop o nk n i expanded).length = expanded.length + 4 * n := by
  induction n generalizing i expanded with
  | zero => simp [scheduleLoop]
  | succ n ih => simp [scheduleLoop, ih, scheduleStep]; omega

theorem expandKey_length (o : Ops B) (nk rounds : Nat) (key : List B)
    (hk : key.length = 4 * nk) (hn : nk ≤ 4 * (rounds + 1)) :
    (expandKey o nk rounds key).length = 16 * (rounds + 1) := by
  rw [expandKey, scheduleLoop_length, hk]
  omega

theorem encryptExpanded_length (o : Ops B) (rounds : Nat) (expanded block : List B)
    (he : expanded.length = 16 * (rounds + 1)) :
    (encryptExpanded o rounds expanded block).length = 16 := by
  have hn : 16 * (rounds + 1) - 16 * rounds = 16 := by omega
  simp [encryptExpanded, addRoundKey, shiftRows, he, hn]

theorem encryptCore_length (o : Ops B) (nk rounds : Nat) (key block : List B)
    (hk : key.length = 4 * nk) (hn : nk ≤ 4 * (rounds + 1)) :
    (encryptCore o nk rounds key block).length = 16 := by
  exact encryptExpanded_length o rounds _ block (expandKey_length o nk rounds key hk hn)

theorem encrypt_result_length (o : Ops B) (key block result : List B)
    (accepted : encrypt o key block = some result) : result.length = 16 := by
  by_cases hb : block.length = 16
  · by_cases h16 : key.length = 16
    · have he : encryptCore o 4 10 key block = result := by simpa [encrypt, hb, h16] using accepted
      rw [← he]
      exact encryptCore_length o 4 10 key block (by omega) (by omega)
    · by_cases h32 : key.length = 32
      · have he : encryptCore o 8 14 key block = result := by
          simpa [encrypt, hb, h16, h32] using accepted
        rw [← he]
        exact encryptCore_length o 8 14 key block (by omega) (by omega)
      · simp [encrypt, hb, h16, h32] at accepted
  · simp [encrypt, hb] at accepted

theorem compiled_encryptCore_correct (nk rounds : Nat) (key block : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (encryptCore symbolic nk rounds key block).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (encryptCore symbolic nk rounds key block))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (encryptCore symbolic nk rounds key block))).vec.get index hi)) =
    (ByteCircuit.joinValue (encryptCore concrete nk rounds (key.map (BVExpr.eval assign))
      (block.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, encryptCore_map (evaluationHom assign)]

end TlsMpc.Aes
