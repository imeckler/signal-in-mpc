import TlsMpc.ByteCircuit

/-! Pure byte/word layout used to relate the unchanged Rust bitslice function
to a fixed permutation of secret bits. This module depends only on Std. -/

namespace TlsMpc.Signal.AesLayout

structure Words (W : Type) where
  w0 : W
  w1 : W
  w2 : W
  w3 : W
  w4 : W
  w5 : W
  w6 : W
  w7 : W

def Words.list (w : Words W) : List W := [w.w0,w.w1,w.w2,w.w3,w.w4,w.w5,w.w6,w.w7]

def Words.at (w : Words W) : Nat → W
  | 0 => w.w0
  | 1 => w.w1
  | 2 => w.w2
  | 3 => w.w3
  | 4 => w.w4
  | 5 => w.w5
  | 6 => w.w6
  | _ => w.w7

def readReordered (input : Nat → BitVec 8) : BitVec 64 :=
  (input 0).setWidth 64 ||| ((input 1).setWidth 64 <<< 16) |||
  ((input 2).setWidth 64 <<< 32) ||| ((input 3).setWidth 64 <<< 48) |||
  ((input 8).setWidth 64 <<< 8) ||| ((input 9).setWidth 64 <<< 24) |||
  ((input 10).setWidth 64 <<< 40) ||| ((input 11).setWidth 64 <<< 56)

def deltaSwap (a b : BitVec 64) (shift : Nat) (mask : BitVec 64) :
    BitVec 64 × BitVec 64 :=
  let t := (a ^^^ (b >>> shift)) &&& mask
  (a ^^^ t, b ^^^ (t <<< shift))

def transpose (t : Words (BitVec 64)) : Words (BitVec 64) :=
  let (t11, t01) := deltaSwap t.w1 t.w0 1 0x5555555555555555
  let (t31, t21) := deltaSwap t.w3 t.w2 1 0x5555555555555555
  let (t51, t41) := deltaSwap t.w5 t.w4 1 0x5555555555555555
  let (t71, t61) := deltaSwap t.w7 t.w6 1 0x5555555555555555
  let (t22, t02) := deltaSwap t21 t01 2 0x3333333333333333
  let (t32, t12) := deltaSwap t31 t11 2 0x3333333333333333
  let (t62, t42) := deltaSwap t61 t41 2 0x3333333333333333
  let (t72, t52) := deltaSwap t71 t51 2 0x3333333333333333
  let (t43, t03) := deltaSwap t42 t02 4 0x0f0f0f0f0f0f0f0f
  let (t53, t13) := deltaSwap t52 t12 4 0x0f0f0f0f0f0f0f0f
  let (t63, t23) := deltaSwap t62 t22 4 0x0f0f0f0f0f0f0f0f
  let (t73, t33) := deltaSwap t72 t32 4 0x0f0f0f0f0f0f0f0f
  ⟨t03,t13,t23,t33,t43,t53,t63,t73⟩

def prepare (input : Nat → Nat → BitVec 8) : Words (BitVec 64) :=
  ⟨readReordered (input 0), readReordered (input 1),
    readReordered (input 2), readReordered (input 3),
    readReordered (fun n => input 0 (n + 4)), readReordered (fun n => input 1 (n + 4)),
    readReordered (fun n => input 2 (n + 4)), readReordered (fun n => input 3 (n + 4))⟩

def network (input : Nat → Nat → BitVec 8) : Words (BitVec 64) :=
  transpose (prepare input)

end TlsMpc.Signal.AesLayout
