import TlsMpc.ByteCircuit
import TlsMpc.Signal.Varint64

/-! Shared Keccak-f[1600], SHA3-256/512 and SHAKE128/256. Public byte lengths
and output lengths determine sponge work; every input, state lane and digest
remains secret. This supplies the Boolean hashing component needed by ML-KEM.
Compiler refinement below is independent of actual libcrux implementation
refinement; no cryptographic security or Rust wrapper equivalence is asserted. -/
namespace TlsMpc.Signal.Keccak
open Std.Tactic.BVDecide

structure Ops (B W : Type) where
  byteConst : Nat → B
  wordConst : Nat → W
  xor : W → W → W
  and : W → W → W
  not : W → W
  rotate : W → Nat → W
  pack : B → B → B → B → B → B → B → B → W
  unpack : W → Nat → B

def concrete : Ops (BitVec 8) (BitVec 64) where
  byteConst := BitVec.ofNat 8
  wordConst := BitVec.ofNat 64
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := (~~~ ·)
  rotate := BitVec.rotateLeft
  pack a b c d e f g h := Varint64.concrete.pack h g f e d c b a
  unpack x i := x.extractLsb' (8*i) 8

def symbolic : Ops (BVExpr 8) (BVExpr 64) where
  byteConst n := .const (BitVec.ofNat 8 n)
  wordConst n := .const (BitVec.ofNat 64 n)
  xor a b := BvConstruct.bin a .xor b
  and a b := BvConstruct.bin a .and b
  not a := BvConstruct.un .not a
  rotate a n := BvConstruct.un (.rotateLeft n) a
  pack a b c d e f g h := Varint64.symbolic.pack h g f e d c b a
  unpack x i := BvConstruct.extract (8*i) 8 x

structure Hom (s : Ops B W) (t : Ops B' W') (f : B → B') (g : W → W') : Prop where
  byteConst : ∀ n, f (s.byteConst n) = t.byteConst n
  wordConst : ∀ n, g (s.wordConst n) = t.wordConst n
  xor : ∀ x y, g (s.xor x y) = t.xor (g x) (g y)
  and : ∀ x y, g (s.and x y) = t.and (g x) (g y)
  not : ∀ x, g (s.not x) = t.not (g x)
  rotate : ∀ x n, g (s.rotate x n) = t.rotate (g x) n
  pack : ∀ a b c d e h i j, g (s.pack a b c d e h i j) = t.pack (f a) (f b) (f c) (f d) (f e) (f h) (f i) (f j)
  unpack : ∀ x i, f (s.unpack x i) = t.unpack (g x) i

def evaluationHom (assign : BVExpr.Assignment) : Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [symbolic,concrete,Varint64.symbolic,Varint64.concrete]

def constants : List Nat := [
  0x0000000000000001,0x0000000000008082,0x800000000000808a,0x8000000080008000,
  0x000000000000808b,0x0000000080000001,0x8000000080008081,0x8000000000008009,
  0x000000000000008a,0x0000000000000088,0x0000000080008009,0x000000008000000a,
  0x000000008000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,
  0x8000000000008002,0x8000000000000080,0x000000000000800a,0x800000008000000a,
  0x8000000080008081,0x8000000000008080,0x0000000080000001,0x8000000080008008]

def rotations : List Nat := [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14]

def get (s : Ops B W) (state : List W) (x y : Nat) : W :=
  state[x%5+5*(y%5)]?.getD (s.wordConst 0)
def column (s : Ops B W) (state : List W) (x : Nat) : W :=
  s.xor (s.xor (s.xor (s.xor (get s state x 0) (get s state x 1)) (get s state x 2)) (get s state x 3)) (get s state x 4)
def round (s : Ops B W) (state : List W) (rc : Nat) : List W :=
  let c := (List.range 5).map (column s state)
  let t := (List.range 25).map (fun i =>
    let x := i%5
    let d := s.xor (c[(x+4)%5]?.getD (s.wordConst 0)) (s.rotate (c[(x+1)%5]?.getD (s.wordConst 0)) 1)
    s.xor (get s state x (i/5)) d)
  let b := (List.range 25).map (fun i =>
    let x := (i%5+3*(i/5))%5
    let y := i%5
    s.rotate (get s t x y) (rotations[x+5*y]?.getD 0))
  (List.range 25).map (fun i =>
    let x := i%5
    let y := i/5
    let v := s.xor (get s b x y) (s.and (s.not (get s b (x+1) y)) (get s b (x+2) y))
    if i = 0 then s.xor v (s.wordConst rc) else v)

def permute (s : Ops B W) (state : List W) : List W := constants.foldl (round s) state

def lane (s : Ops B W) (block : List B) (i : Nat) : W :=
  let b := fun j => block[8*i+j]?.getD (s.byteConst 0)
  s.pack (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7)
def absorbBlock (s : Ops B W) (state : List W) (block : List B) : List W :=
  permute s ((List.range 25).map (fun i => s.xor (get s state (i%5) (i/5)) (lane s block i)))
def absorb (s : Ops B W) (rate : Nat) : Nat → List B → List W → List W
  | 0, _, state => state
  | fuel+1, input, state => absorb s rate fuel (input.drop rate) (absorbBlock s state (input.take rate))
def stateBytes (s : Ops B W) (state : List W) : List B :=
  (List.range 200).map (fun i => s.unpack (get s state ((i/8)%5) ((i/8)/5)) (i%8))
def squeeze (s : Ops B W) (rate : Nat) : Nat → Nat → List W → List B
  | 0, _, _ => []
  | fuel+1, count, state => (stateBytes s state).take (min count rate) ++
    squeeze s rate fuel (count-rate) (permute s state)

def padded (s : Ops B W) (rate delimiter : Nat) (input : List B) : List B :=
  let remaining := rate-input.length%rate
  input ++ (if remaining = 1 then [s.byteConst (delimiter+128)]
    else s.byteConst delimiter :: (List.replicate (remaining-2) (s.byteConst 0) ++ [s.byteConst 128]))
def hash (s : Ops B W) (rate delimiter outputBytes : Nat) (input : List B) : List B :=
  let state := absorb s rate (input.length/rate+1) (padded s rate delimiter input) (List.replicate 25 (s.wordConst 0))
  squeeze s rate ((outputBytes+rate-1)/rate) outputBytes state

def sha3_256 (s : Ops B W) (input : List B) := hash s 136 6 32 input
def sha3_512 (s : Ops B W) (input : List B) := hash s 72 6 64 input
def shake128 (s : Ops B W) (outputBytes : Nat) (input : List B) := hash s 168 31 outputBytes input
def shake256 (s : Ops B W) (outputBytes : Nat) (input : List B) := hash s 136 31 outputBytes input

theorem stateBytes_length (s : Ops B W) (state : List W) : (stateBytes s state).length = 200 := by
  simp [stateBytes]
theorem squeeze_length (s : Ops B W) (rate fuel count : Nat) (state : List W)
    (hr : rate ≤ 200) (hc : count ≤ fuel*rate) : (squeeze s rate fuel count state).length = count := by
  induction fuel generalizing count state with
  | zero => simp only [Nat.zero_mul,Nat.le_zero_eq] at hc; simp [squeeze,hc]
  | succ fuel ih =>
    simp only [squeeze,List.length_append,List.length_take,stateBytes_length]
    rw [ih (count-rate) (permute s state) (by simpa only [Nat.succ_mul] using (show count-rate ≤ fuel*rate by
      rw [Nat.succ_mul] at hc
      omega))]
    omega

theorem hash_length (s : Ops B W) (rate delimiter outputBytes : Nat) (input : List B)
    (hpos : 0 < rate) (hmax : rate ≤ 200) : (hash s rate delimiter outputBytes input).length = outputBytes := by
  unfold hash
  apply squeeze_length s _ _ _ _ hmax
  have hm := Nat.mod_lt (outputBytes+rate-1) hpos
  have hd := Nat.mod_add_div (outputBytes+rate-1) rate
  rw [Nat.mul_comm rate] at hd
  omega

theorem getD_map (f : X → Y) (o : Option X) (x : X) : f (o.getD x) = (o.map f).getD (f x) := by
  cases o <;> rfl

section
variable {s : Ops B W} {t : Ops B' W'} {f : B → B'} {g : W → W'} (h : Hom s t f g)
include h

theorem get_map (state : List W) (x y : Nat) : g (get s state x y) = get t (state.map g) x y := by
  simp only [get,List.getElem?_map,getD_map g,h.wordConst]
theorem column_map (state : List W) (x : Nat) : g (column s state x) = column t (state.map g) x := by
  simp only [column,h.xor,get_map h]
theorem round_map (state : List W) (rc : Nat) : (round s state rc).map g = round t (state.map g) rc := by
  simp only [round,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  split <;> simp only [h.xor,h.and,h.not,get_map h,List.map_map,Function.comp_def,
    h.rotate,List.getElem?_map,getD_map g,h.wordConst,Option.map_map,column_map h]
theorem rounds_map (rcs : List Nat) (state : List W) : (rcs.foldl (round s) state).map g = rcs.foldl (round t) (state.map g) := by
  induction rcs generalizing state with
  | nil => rfl
  | cons rc rest ih => simp only [List.foldl_cons,ih,round_map h]
theorem permute_map (state : List W) : (permute s state).map g = permute t (state.map g) := rounds_map h constants state

theorem lane_map (block : List B) (i : Nat) : g (lane s block i) = lane t (block.map f) i := by
  simp only [lane,h.pack,List.getElem?_map,getD_map f,h.byteConst]
theorem absorbBlock_map (state : List W) (block : List B) :
    (absorbBlock s state block).map g = absorbBlock t (state.map g) (block.map f) := by
  simp only [absorbBlock,permute_map h,List.map_map,Function.comp_def,h.xor,get_map h,lane_map h]
theorem absorb_map (rate fuel : Nat) (input : List B) (state : List W) :
    (absorb s rate fuel input state).map g = absorb t rate fuel (input.map f) (state.map g) := by
  induction fuel generalizing input state with
  | zero => rfl
  | succ fuel ih => simp only [absorb,ih,List.map_drop,List.map_take,absorbBlock_map h]
theorem stateBytes_map (state : List W) : (stateBytes s state).map f = stateBytes t (state.map g) := by
  simp only [stateBytes,List.map_map,Function.comp_def,h.unpack,get_map h]
theorem squeeze_map (rate fuel count : Nat) (state : List W) :
    (squeeze s rate fuel count state).map f = squeeze t rate fuel count (state.map g) := by
  induction fuel generalizing count state with
  | zero => rfl
  | succ fuel ih => simp only [squeeze,List.map_append,List.map_take,stateBytes_map h,ih,permute_map h]
theorem padded_map (rate delimiter : Nat) (input : List B) :
    (padded s rate delimiter input).map f = padded t rate delimiter (input.map f) := by
  simp only [padded,List.map_append,List.length_map]
  split <;> simp only [List.map_cons,List.map_nil,List.map_append,List.map_replicate,h.byteConst]
theorem hash_map (rate delimiter outputBytes : Nat) (input : List B) :
    (hash s rate delimiter outputBytes input).map f = hash t rate delimiter outputBytes (input.map f) := by
  simp only [hash,squeeze_map h,absorb_map h,padded_map h,List.map_replicate,h.wordConst,List.length_map]
end

theorem compiled_hash_correct (rate delimiter outputBytes : Nat) (input : List (BVExpr 8))
    (assign : BVExpr.Assignment) (bit : Nat) (hi : bit < 8*(hash symbolic rate delimiter outputBytes input).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (hash symbolic rate delimiter outputBytes input))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (hash symbolic rate delimiter outputBytes input))).vec.get bit hi)) =
      (ByteCircuit.joinValue (hash concrete rate delimiter outputBytes (input.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct,hash_map (evaluationHom assign)]
end TlsMpc.Signal.Keccak
