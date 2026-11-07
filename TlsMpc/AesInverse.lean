import TlsMpc.Aes

/-!
AES-128/AES-256 inverse cipher using the existing forward key schedule.
All indices, lengths and round counts are public. Expanded secret keys can be
reused across CBC blocks. These definitions and their compiler refinement do
not claim equivalence to the currently unsupported RustCrypto decrypt wrapper.
-/

namespace TlsMpc.AesInverse
open Std.Tactic.BVDecide

/-- Inverse of the AES S-box's affine output transform, including its constant. -/
def inverseAffineValue (x : BitVec 8) : BitVec 8 :=
  ((x.rotateRight 7 ^^^ x.rotateRight 5) ^^^ x.rotateRight 2) ^^^ 0x05

def inverseAffineExpr (x : BVExpr 8) : BVExpr 8 :=
  BvConstruct.bin
    (BvConstruct.bin
      (BvConstruct.bin (BvConstruct.un (.rotateRight 7) x) .xor
        (BvConstruct.un (.rotateRight 5) x)) .xor (BvConstruct.un (.rotateRight 2) x))
    .xor (.const 0x05)

/-- One existing 32-AND forward S-box, surrounded by linear byte transforms. -/
def invSboxValue (x : BitVec 8) : BitVec 8 :=
  inverseAffineValue (AesSbox.spec (inverseAffineValue x))

def invSboxExpr (x : BVExpr 8) : BVExpr 8 :=
  inverseAffineExpr (AesSbox.expr (inverseAffineExpr x))

theorem inverseAffineExpr_refines (assign : BVExpr.Assignment) (x : BVExpr 8) :
    (inverseAffineExpr x).eval assign = inverseAffineValue (x.eval assign) := by
  simp [inverseAffineExpr, inverseAffineValue]

theorem invSboxExpr_refines (assign : BVExpr.Assignment) (x : BVExpr 8) :
    (invSboxExpr x).eval assign = invSboxValue (x.eval assign) := by
  simp only [invSboxExpr, invSboxValue, inverseAffineExpr_refines, AesSbox.expr_refines]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem invSbox_forward : ∀ x : BitVec 8, invSboxValue (AesSbox.spec x) = x := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forward_invSbox : ∀ x : BitVec 8, AesSbox.spec (invSboxValue x) = x := by
  decide +kernel

structure Ops (B : Type) where
  aes : Aes.Ops B
  invSbox : B → B

def concrete : Ops (BitVec 8) := ⟨Aes.concrete, invSboxValue⟩
def symbolic : Ops (BVExpr 8) := ⟨Aes.symbolic, invSboxExpr⟩

def invSubBytes (o : Ops B) (state : List B) : List B := state.map o.invSbox

def invShiftRows (o : Ops B) (state : List B) : List B :=
  (List.range 16).map (fun i =>
    Aes.get o.aes state (4 * ((i / 4 + 3 * (i % 4)) % 4) + i % 4))

/-- The two double-xtime corrections share work within a column; the remaining
operation is the existing forward MixColumns linear map. -/
def invMixColumn (o : Aes.Ops B) (a b c d : B) : List B :=
  let u := o.xtime (o.xtime (o.xor a c))
  let v := o.xtime (o.xtime (o.xor b d))
  let a1 := o.xor a u
  let b1 := o.xor b v
  let c1 := o.xor c u
  let d1 := o.xor d v
  [Aes.mixByte o a1 b1 c1 d1, Aes.mixByte o b1 c1 d1 a1,
   Aes.mixByte o c1 d1 a1 b1, Aes.mixByte o d1 a1 b1 c1]

def invMixColumns (o : Ops B) (state : List B) : List B :=
  (List.range 4).flatMap (fun column =>
    invMixColumn o.aes (Aes.get o.aes state (4 * column))
      (Aes.get o.aes state (4 * column + 1))
      (Aes.get o.aes state (4 * column + 2))
      (Aes.get o.aes state (4 * column + 3)))

def round (o : Ops B) (key state : List B) : List B :=
  invMixColumns o (Aes.addRoundKey o.aes (invSubBytes o (invShiftRows o state)) key)

def middleRounds (o : Ops B) (expanded : List B) : Nat → Nat → List B → List B
  | 0, _, state => state
  | count + 1, index, state => middleRounds o expanded count (index - 1)
      (round o ((expanded.drop (16 * index)).take 16) state)

/-- Use the forward expanded key unchanged, visiting its round keys in reverse. -/
def decryptExpanded (o : Ops B) (rounds : Nat) (expanded block : List B) : List B :=
  let initial := Aes.addRoundKey o.aes block ((expanded.drop (16 * rounds)).take 16)
  let state := middleRounds o expanded (rounds - 1) (rounds - 1) initial
  Aes.addRoundKey o.aes (invSubBytes o (invShiftRows o state)) (expanded.take 16)

def decryptCore (o : Ops B) (nk rounds : Nat) (key block : List B) : List B :=
  decryptExpanded o rounds (Aes.expandKey o.aes nk rounds key) block

/-- Public shape validation. Accepted sizes are AES-128 and AES-256. -/
def decrypt (o : Ops B) (key block : List B) : Option (List B) :=
  if block.length = 16 then
    if key.length = 16 then some (decryptCore o 4 10 key block)
    else if key.length = 32 then some (decryptCore o 8 14 key block)
    else none
  else none

structure Hom (a : Ops B) (b : Ops B') (f : B → B') : Prop where
  aes : Aes.Hom a.aes b.aes f
  invSbox : ∀ x, f (a.invSbox x) = b.invSbox (f x)

set_option maxRecDepth 100000 in
def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) := by
  constructor
  · exact Aes.evaluationHom assign
  · intro x
    simpa only [symbolic, concrete] using invSboxExpr_refines assign x

section Refinement
variable {a : Ops B} {b : Ops B'} {f : B → B'} (h : Hom a b f)
include h

theorem invSubBytes_map (state : List B) :
    (invSubBytes a state).map f = invSubBytes b (state.map f) := by
  simp [invSubBytes, List.map_map, Function.comp_def, h.invSbox]

theorem invShiftRows_map (state : List B) :
    (invShiftRows a state).map f = invShiftRows b (state.map f) := by
  simp [invShiftRows, List.map_map, Function.comp_def, Aes.get_map h.aes]

theorem invMixColumn_map (x y z w : B) :
    (invMixColumn a.aes x y z w).map f = invMixColumn b.aes (f x) (f y) (f z) (f w) := by
  simp [invMixColumn, Aes.mixByte_map h.aes, h.aes.xor, h.aes.xtime]

theorem invMixColumns_map (state : List B) :
    (invMixColumns a state).map f = invMixColumns b (state.map f) := by
  simp [invMixColumns, List.map_flatMap, invMixColumn_map h, Aes.get_map h.aes]

theorem round_map (key state : List B) :
    (round a key state).map f = round b (key.map f) (state.map f) := by
  simp [round, invMixColumns_map h, Aes.addRoundKey_map h.aes,
    invSubBytes_map h, invShiftRows_map h]

theorem middleRounds_map (expanded : List B) (count index : Nat) (state : List B) :
    (middleRounds a expanded count index state).map f =
      middleRounds b (expanded.map f) count index (state.map f) := by
  induction count generalizing index state with
  | zero => rfl
  | succ count ih => simp [middleRounds, ih, round_map h]

theorem decryptExpanded_map (rounds : Nat) (expanded block : List B) :
    (decryptExpanded a rounds expanded block).map f =
      decryptExpanded b rounds (expanded.map f) (block.map f) := by
  simp [decryptExpanded, Aes.addRoundKey_map h.aes, invSubBytes_map h,
    invShiftRows_map h, middleRounds_map h]

theorem decryptCore_map (nk rounds : Nat) (key block : List B) :
    (decryptCore a nk rounds key block).map f =
      decryptCore b nk rounds (key.map f) (block.map f) := by
  simp [decryptCore, decryptExpanded_map h, Aes.expandKey_map h.aes]

theorem decrypt_map (key block : List B) :
    (decrypt a key block).map (List.map f) = decrypt b (key.map f) (block.map f) := by
  by_cases hb : block.length = 16
  · by_cases h16 : key.length = 16
    · simp [decrypt, hb, h16, decryptCore_map h]
    · by_cases h32 : key.length = 32 <;> simp [decrypt, hb, h16, h32, decryptCore_map h]
  · simp [decrypt, hb]

end Refinement

theorem invMixColumns_length (o : Ops B) (state : List B) :
    (invMixColumns o state).length = 16 := by
  simp [invMixColumns, invMixColumn, List.range_succ]

theorem decryptExpanded_length (o : Ops B) (rounds : Nat) (expanded block : List B)
    (he : expanded.length = 16 * (rounds + 1)) :
    (decryptExpanded o rounds expanded block).length = 16 := by
  simp [decryptExpanded, Aes.addRoundKey, invSubBytes, invShiftRows, he]
  omega

theorem decryptCore_length (o : Ops B) (nk rounds : Nat) (key block : List B)
    (hk : key.length = 4 * nk) (hn : nk ≤ 4 * (rounds + 1)) :
    (decryptCore o nk rounds key block).length = 16 := by
  exact decryptExpanded_length o rounds _ block (Aes.expandKey_length o.aes nk rounds key hk hn)

theorem decrypt_result_length (o : Ops B) (key block result : List B)
    (accepted : decrypt o key block = some result) : result.length = 16 := by
  by_cases hb : block.length = 16
  · by_cases h16 : key.length = 16
    · have he : decryptCore o 4 10 key block = result := by simpa [decrypt, hb, h16] using accepted
      rw [← he]
      exact decryptCore_length o 4 10 key block (by omega) (by omega)
    · by_cases h32 : key.length = 32
      · have he : decryptCore o 8 14 key block = result := by
          simpa [decrypt, hb, h16, h32] using accepted
        rw [← he]
        exact decryptCore_length o 8 14 key block (by omega) (by omega)
      · simp [decrypt, hb, h16, h32] at accepted
  · simp [decrypt, hb] at accepted

theorem compiled_decryptExpanded_correct (rounds : Nat) (expanded block : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (decryptExpanded symbolic rounds expanded block).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (decryptExpanded symbolic rounds expanded block))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (decryptExpanded symbolic rounds expanded block))).vec.get index hi)) =
    (ByteCircuit.joinValue (decryptExpanded concrete rounds (expanded.map (BVExpr.eval assign))
      (block.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, decryptExpanded_map (evaluationHom assign)]

theorem compiled_decryptCore_correct (nk rounds : Nat) (key block : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (decryptCore symbolic nk rounds key block).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (decryptCore symbolic nk rounds key block))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (decryptCore symbolic nk rounds key block))).vec.get index hi)) =
    (ByteCircuit.joinValue (decryptCore concrete nk rounds (key.map (BVExpr.eval assign))
      (block.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, decryptCore_map (evaluationHom assign)]

end TlsMpc.AesInverse
