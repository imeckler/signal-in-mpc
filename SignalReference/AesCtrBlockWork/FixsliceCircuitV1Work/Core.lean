import AesCtrBlockWork.EncryptBoundV1.EntryReference
namespace LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
open LibSignalReference.Candidate
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- All shifts/rotations in the round core are multiples of four. Keeping this
public unit explicit permits a proved 64→16 lane projection for one-block use. -/
structure Ops (W : Type) where
 bits : AesSbox.Ops W
 mask : W→BitVec 64→W
 bor : W→W→W
 rotate4 : W→Fin 16→W
 left4 : W→Fin 16→W
 right4 : W→Fin 16→W
structure Hom (a : Ops W) (b : Ops W') (f : W→W') : Prop where
 bits : AesSbox.Hom a.bits b.bits f
 mask : ∀ x m, f (a.mask x m)=b.mask (f x) m
 bor : ∀ x y, f (a.bor x y)=b.bor (f x) (f y)
 rotate4 : ∀ x n, f (a.rotate4 x n)=b.rotate4 (f x) n
 left4 : ∀ x n, f (a.left4 x n)=b.left4 (f x) n
 right4 : ∀ x n, f (a.right4 x n)=b.right4 (f x) n

def concrete64 : Ops (BitVec 64) where
 bits := AesRawSub.vectorOps
 mask := (· &&& ·)
 bor := (· ||| ·)
 rotate4 x n := x.rotateRight (4*n.val)
 left4 x n := x <<< (4*n.val)
 right4 x n := x >>> (4*n.val)

def fromList (zero : W) (xs : List W) : Words W :=
 ⟨xs[0]?.getD zero,xs[1]?.getD zero,xs[2]?.getD zero,xs[3]?.getD zero,
  xs[4]?.getD zero,xs[5]?.getD zero,xs[6]?.getD zero,xs[7]?.getD zero⟩
def substitute (o : Ops W) (words : Words W) : Words W :=
 fromList o.bits.zero (AesRawSub.rawRun o.bits words.list)
def addKey (o : Ops W) (a b : Words W) : Words W :=
 ⟨o.bits.xor a.w0 b.w0,o.bits.xor a.w1 b.w1,o.bits.xor a.w2 b.w2,o.bits.xor a.w3 b.w3,
  o.bits.xor a.w4 b.w4,o.bits.xor a.w5 b.w5,o.bits.xor a.w6 b.w6,o.bits.xor a.w7 b.w7⟩
def rotateFirst (o : Ops W) (phase : Nat) (x : W) : W :=
 match phase with
 | 0=>o.rotate4 x 4
 | 1=>o.bor (o.mask (o.rotate4 x 5) 0x0fff0fff0fff0fff) (o.mask (o.rotate4 x 1) 0xf000f000f000f000)
 | 2=>o.bor (o.mask (o.rotate4 x 6) 0x00ff00ff00ff00ff) (o.mask (o.rotate4 x 2) 0xff00ff00ff00ff00)
 | _=>o.bor (o.mask (o.rotate4 x 7) 0x000f000f000f000f) (o.mask (o.rotate4 x 3) 0xfff0fff0fff0fff0)
def rotateSecond (o : Ops W) (phase : Nat) (x : W) : W :=
 match phase with
 | 0 | 2=>o.rotate4 x 8
 | _=>o.bor (o.mask (o.rotate4 x 10) 0x00ff00ff00ff00ff) (o.mask (o.rotate4 x 6) 0xff00ff00ff00ff00)
def mix (o : Ops W) (phase : Nat) (a : Words W) : Words W :=
 let b:=mapWords (rotateFirst o phase) a
 let c:=addKey o a b
 ⟨o.bits.xor (o.bits.xor b.w0 c.w7) (rotateSecond o phase c.w0),
  o.bits.xor (o.bits.xor (o.bits.xor b.w1 c.w0) c.w7) (rotateSecond o phase c.w1),
  o.bits.xor (o.bits.xor b.w2 c.w1) (rotateSecond o phase c.w2),
  o.bits.xor (o.bits.xor (o.bits.xor b.w3 c.w2) c.w7) (rotateSecond o phase c.w3),
  o.bits.xor (o.bits.xor (o.bits.xor b.w4 c.w3) c.w7) (rotateSecond o phase c.w4),
  o.bits.xor (o.bits.xor b.w5 c.w4) (rotateSecond o phase c.w5),
  o.bits.xor (o.bits.xor b.w6 c.w5) (rotateSecond o phase c.w6),
  o.bits.xor (o.bits.xor b.w7 c.w6) (rotateSecond o phase c.w7)⟩
def shift2 (o : Ops W) (words : Words W) : Words W :=
 mapWords (fun x=>let t:=o.mask (o.bits.xor x (o.right4 x 2)) 0x00ff000000ff0000
                  o.bits.xor x (o.bits.xor t (o.left4 t 2))) words
def round (o : Ops W) (phase : Nat) (words key : Words W) : Words W :=
 addKey o (mix o phase (substitute o words)) key
def four (o : Ops W) (keys : Nat→Words W) (r : Nat) (words : Words W) : Words W :=
 round o 0 (round o 3 (round o 2 (round o 1 words (keys r)) (keys (r+1))) (keys (r+2))) (keys (r+3))
def rounds (o : Ops W) (keys : Nat→Words W) (words : Words W) : Words W :=
 round o 1 (four o keys 9 (four o keys 5 (four o keys 1 words))) (keys 13)
def encrypt (o : Ops W) (keys : Nat→Words W) (words : Words W) : Words W :=
 addKey o (substitute o (shift2 o (rounds o keys (addKey o words (keys 0))))) (keys 14)

theorem map_list (f : W→W') (words : Words W) :
 (mapWords f words).list=words.list.map f := rfl

theorem fromList_map (f : W→W') (zero : W) (xs : List W) :
 mapWords f (fromList zero xs)=fromList (f zero) (xs.map f) := by
 simp only [fromList,mapWords,AesSbox.get_map]

theorem substitute_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (words : Words W) :
 mapWords f (substitute a words)=substitute b (mapWords f words) := by
 simp only [substitute,fromList_map,h.bits.zero,←AesRawSub.rawRun_map h.bits,map_list]

theorem addKey_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (x y : Words W) :
 mapWords f (addKey a x y)=addKey b (mapWords f x) (mapWords f y) := by
 simp only [addKey,mapWords,h.bits.xor]

theorem first_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (phase : Nat) (x : W) :
 f (rotateFirst a phase x)=rotateFirst b phase (f x) := by
 cases phase with
 | zero=>simp only [rotateFirst,h.rotate4]
 | succ n=>cases n with
   | zero=>simp only [rotateFirst,h.bor,h.mask,h.rotate4]
   | succ n=>cases n <;>simp only [rotateFirst,h.bor,h.mask,h.rotate4]

theorem second_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (phase : Nat) (x : W) :
 f (rotateSecond a phase x)=rotateSecond b phase (f x) := by
 cases phase with
 | zero=>simp only [rotateSecond,h.rotate4]
 | succ n=>cases n with
   | zero=>simp only [rotateSecond,h.bor,h.mask,h.rotate4]
   | succ n=>cases n <;>simp only [rotateSecond,h.bor,h.mask,h.rotate4]

theorem mix_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (phase : Nat) (words : Words W) :
 mapWords f (mix a phase words)=mix b phase (mapWords f words) := by
 simp only [mix,addKey,mapWords,h.bits.xor,first_map h,second_map h]

theorem shift2_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (words : Words W) :
 mapWords f (shift2 a words)=shift2 b (mapWords f words) := by
 simp only [shift2,mapWords,h.bits.xor,h.mask,h.right4,h.left4]

theorem round_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (phase : Nat) (words key : Words W) :
 mapWords f (round a phase words key)=round b phase (mapWords f words) (mapWords f key) := by
 simp only [round,addKey_map h,mix_map h,substitute_map h]

theorem four_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (keys : Nat→Words W) (r : Nat) (words : Words W) :
 mapWords f (four a keys r words)=four b (fun i=>mapWords f (keys i)) r (mapWords f words) := by
 simp only [four,round_map h]

theorem rounds_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (keys : Nat→Words W) (words : Words W) :
 mapWords f (rounds a keys words)=rounds b (fun i=>mapWords f (keys i)) (mapWords f words) := by
 simp only [rounds,round_map h,four_map h]

theorem encrypt_map {a : Ops W} {b : Ops W'} {f : W→W'} (h : Hom a b f) (keys : Nat→Words W) (words : Words W) :
 mapWords f (encrypt a keys words)=encrypt b (fun i=>mapWords f (keys i)) (mapWords f words) := by
 simp only [encrypt,addKey_map h,substitute_map h,shift2_map h,rounds_map h]

theorem concrete_substitute (words : Words (BitVec 64)) :
 substitute concrete64 words=AesRawSub.rawWords words := rfl

theorem concrete_add (a b : Words (BitVec 64)) :
 addKey concrete64 a b=AesRoundModel.xorWords a b := rfl

theorem concrete_mix0 (words : Words (BitVec 64)) :
 mix concrete64 0 words=TlsMpc.Signal.AesLinear.mixWords words := rfl

theorem concrete_mix1 (words : Words (BitVec 64)) :
 mix concrete64 1 words=TlsMpc.Signal.AesRemainingLinear.mixWords 1 words := rfl

theorem concrete_mix2 (words : Words (BitVec 64)) :
 mix concrete64 2 words=TlsMpc.Signal.AesRemainingLinear.mixWords 2 words := rfl

theorem concrete_mix3 (words : Words (BitVec 64)) :
 mix concrete64 3 words=TlsMpc.Signal.AesRemainingLinear.mixWords 3 words := rfl

theorem concrete_shift (words : Words (BitVec 64)) :
 shift2 concrete64 words=mapWords TlsMpc.Signal.AesLinear.shiftWord2 words := rfl

/-- Exact connection to the proved actual raw fixslice model, factored before
composition to avoid unfolding the substitution network during unification. -/
theorem concrete_matches (keys : Nat→Words (BitVec 64)) (words : Words (BitVec 64)) :
 encrypt concrete64 keys words =
 AesRoundModel.xorWords (AesRawSub.rawWords (mapWords TlsMpc.Signal.AesLinear.shiftWord2
  (AesLoopReference.loopResult keys (AesRoundModel.xorWords words (keys 0))))) (keys 14) := by
 simp only [encrypt,rounds,four,round,concrete_add,concrete_substitute,concrete_shift,
  concrete_mix0,concrete_mix1,concrete_mix2,concrete_mix3,
  AesLoopReference.loopResult,AesLoopReference.fourRounds,
  AesLoopReference.round0,AesLoopReference.round1,AesLoopReference.round2,AesLoopReference.round3]
end LibSignalReference.Candidate.FixsliceCircuitV1
