import TlsMpc.BvConstruct

/-!
AES S-box: FIPS 197-upd1 table 4 and Boyar-Peralta's 32-AND circuit.
The fixed numeric program is transcribed from BearSSL v0.6 aes_ct.c.
All 256 byte inputs are checked by Lean kernel reduction, not native_decide.
The generic interpreter is used for concrete values and symbolic bits.
-/

/-
Copyright (c) 2016 Thomas Pornin <pornin@bolet.org>

Permission is hereby granted, free of charge, to any person obtaining 
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be 
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, 
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND 
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

namespace TlsMpc.AesSbox
open Std.Tactic.BVDecide

inductive Gate where
  | xor (left right : Nat)
  | and (left right : Nat)
  | not (arg : Nat)
  deriving DecidableEq

structure Ops (B : Type) where
  zero : B
  xor : B → B → B
  and : B → B → B
  not : B → B

def gate (o : Ops B) (values : List B) : Gate → B
  | .xor a b => o.xor (values[a]?.getD o.zero) (values[b]?.getD o.zero)
  | .and a b => o.and (values[a]?.getD o.zero) (values[b]?.getD o.zero)
  | .not a => o.not (values[a]?.getD o.zero)

def run (o : Ops B) : List Gate → List B → List B
  | [], values => values
  | g :: gs, values => run o gs (values ++ [gate o values g])

def program : List Gate := [
  .xor 4 2,
  .xor 7 1,
  .xor 7 4,
  .xor 7 2,
  .xor 6 5,
  .xor 12 0,
  .xor 13 4,
  .xor 9 8,
  .xor 13 7,
  .xor 13 1,
  .xor 17 11,
  .xor 3 15,
  .xor 19 2,
  .xor 19 6,
  .xor 20 0,
  .xor 20 12,
  .xor 21 10,
  .xor 0 24,
  .xor 23 24,
  .xor 23 11,
  .xor 12 24,
  .xor 9 28,
  .xor 7 28,
  .and 15 20,
  .and 18 22,
  .xor 32 31,
  .and 14 0,
  .xor 34 31,
  .and 9 28,
  .and 17 13,
  .xor 37 36,
  .and 16 25,
  .xor 39 36,
  .and 10 24,
  .and 8 26,
  .xor 42 41,
  .and 11 23,
  .xor 44 41,
  .xor 33 43,
  .xor 35 45,
  .xor 38 43,
  .xor 40 45,
  .xor 46 21,
  .xor 47 27,
  .xor 48 29,
  .xor 49 30,
  .xor 50 51,
  .and 50 52,
  .xor 53 55,
  .and 54 56,
  .xor 57 51,
  .xor 52 53,
  .xor 51 55,
  .and 60 59,
  .xor 61 53,
  .xor 52 62,
  .xor 56 62,
  .and 53 64,
  .xor 65 63,
  .xor 56 65,
  .and 58 67,
  .xor 54 68,
  .xor 69 66,
  .xor 58 62,
  .xor 58 69,
  .xor 62 66,
  .xor 71 70,
  .and 73 20,
  .and 66 22,
  .and 62 0,
  .and 72 28,
  .and 69 13,
  .and 58 25,
  .and 71 24,
  .and 74 26,
  .and 70 23,
  .and 73 15,
  .and 66 18,
  .and 62 14,
  .and 72 9,
  .and 69 17,
  .and 58 16,
  .and 71 10,
  .and 74 8,
  .and 70 11,
  .xor 90 91,
  .xor 85 86,
  .xor 80 88,
  .xor 84 85,
  .xor 77 87,
  .xor 77 80,
  .xor 82 83,
  .xor 75 78,
  .xor 81 82,
  .xor 91 92,
  .xor 87 95,
  .xor 97 100,
  .xor 79 93,
  .xor 78 101,
  .xor 93 104,
  .xor 89 104,
  .xor 99 105,
  .xor 96 105,
  .xor 79 106,
  .xor 108 109,
  .xor 76 110,
  .xor 106 110,
  .not 109,
  .xor 103 115,
  .not 107,
  .xor 95 117,
  .xor 111 112,
  .xor 100 113,
  .xor 98 113,
  .xor 94 112,
  .not 120,
  .xor 111 123,
  .not 119,
  .xor 102 125]

def outputIndices : List Nat := [118, 116, 122, 121, 120, 126, 124, 114]

def circuit (o : Ops B) (input : List B) : List B :=
  let values := run o program input
  outputIndices.map (fun i => values[i]?.getD o.zero)

def concrete : Ops (BitVec 1) := ⟨0, (· ^^^ ·), (· &&& ·), (~~~ ·)⟩

def symbolic : Ops (BVExpr 1) :=
  ⟨.const 0, (fun a b => BvConstruct.bin a .xor b),
    (fun a b => BvConstruct.bin a .and b), BvConstruct.un .not⟩

def packValue (v : List (BitVec 1)) : BitVec 8 :=
  let q : Nat → BitVec 1 := fun i => v[i]?.getD 0
  ((q 7 ++ q 6) ++ (q 5 ++ q 4)) ++ ((q 3 ++ q 2) ++ (q 1 ++ q 0))

def packExpr (v : List (BVExpr 1)) : BVExpr 8 :=
  let q : Nat → BVExpr 1 := fun i => v[i]?.getD (.const 0)
  BvConstruct.append
    (BvConstruct.append (BvConstruct.append (q 7) (q 6)) (BvConstruct.append (q 5) (q 4)))
    (BvConstruct.append (BvConstruct.append (q 3) (q 2)) (BvConstruct.append (q 1) (q 0)))

def value (x : BitVec 8) : BitVec 8 :=
  packValue (circuit concrete ((List.range 8).map (fun i => x.extractLsb' i 1)))

def expr (x : BVExpr 8) : BVExpr 8 :=
  packExpr (circuit symbolic ((List.range 8).map (fun i => BvConstruct.extract i 1 x)))

structure Hom (a : Ops B) (b : Ops B') (f : B → B') : Prop where
  zero : f a.zero = b.zero
  xor : ∀ x y, f (a.xor x y) = b.xor (f x) (f y)
  and : ∀ x y, f (a.and x y) = b.and (f x) (f y)
  not : ∀ x, f (a.not x) = b.not (f x)

theorem get_map (f : B → B') (values : List B) (i : Nat) (zero : B) :
    ((values.map f)[i]?).getD (f zero) = f (values[i]?.getD zero) := by
  simp only [List.getElem?_map]
  cases values[i]? <;> rfl

section Map
variable {B B' : Type} {a : Ops B} {b : Ops B'} {f : B → B'}

theorem gate_map (h : Hom a b f) (values : List B) (g : Gate) :
    f (gate a values g) = gate b (values.map f) g := by
  cases g <;> simp [gate, ← h.zero, h.xor, h.and, h.not]

theorem run_map (h : Hom a b f) (gs : List Gate) (values : List B) :
    (run a gs values).map f = run b gs (values.map f) := by
  induction gs generalizing values with
  | nil => rfl
  | cons g gs ih => simp [run, ih, gate_map h]

theorem circuit_map (h : Hom a b f) (input : List B) :
    (circuit a input).map f = circuit b (input.map f) := by
  simp only [circuit, ← run_map h, List.map_map, Function.comp_def, ← h.zero, get_map]

end Map

def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [symbolic, concrete]

theorem packExpr_refines (assign : BVExpr.Assignment) (values : List (BVExpr 1)) :
    BVExpr.eval assign (packExpr values) = packValue (values.map (BVExpr.eval assign)) := by
  have hget (i : Nat) :
      BVExpr.eval assign (values[i]?.getD (.const 0)) =
        ((values.map (BVExpr.eval assign))[i]?).getD 0 := by
    exact (get_map (BVExpr.eval assign) values i (.const 0)).symm
  simp only [packExpr, packValue, BvConstruct.eval_append, hget]

/-- FIPS 197-upd1, table 4, indexed by the input byte. -/
def table : List Nat := [
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

def spec (x : BitVec 8) : BitVec 8 := BitVec.ofNat 8 (table[x.toNat]?.getD 0)

def packedOps : Ops (BitVec 256) := ⟨0, (· ^^^ ·), (· &&& ·), (~~~ ·)⟩

def packedInputs : List (BitVec 256) := [
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def packedOutputs : List (BitVec 256) := [
  0x4f1ead396f247a0410bdb210c006eab568ab4bfa8acb7a13b14ede67096c6eed,
  0xc870974094ead8a96a450b2ef33486b4e61a4c5e97816f7a7bae007d4c53fc7d,
  0xac39b6c0d6ce2efc577d64e03b0c3ffb23a869a2a428c424a16387fb3b48b4c6,
  0x4e9ddb76c892fb1be9da849cf6ac6c1b2568ea2effa8527d109020a2193d586a,
  0xf210a3aece472e532624b286bc48ecb4f7f17a494ce30f58c2b0f97752b8b11e,
  0x54b248130b4f256f7d8dcc4706319e086bc2aa4e0d787aa4f8045f7b6d98dd7f,
  0x21e0b833255917823f6bcb91b30db559e4851b3bf3ab2560980a3cc2c2fdb4ff,
  0x52379de7b844e3e14cb3770196ca0329e7bac28f866aac825caa2ec7bf977090]

def lane (n : Nat) (x : BitVec 256) : BitVec 1 := x.extractLsb' n 1

def laneHom (n : Nat) (hn : n < 256) : Hom packedOps concrete (lane n) := by
  constructor
  · simp [lane, packedOps, concrete]
  · intros; simp [lane, packedOps, concrete, BitVec.extractLsb'_xor]
  · intros; simp [lane, packedOps, concrete, BitVec.extractLsb'_and]
  · intro x
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 1
    · have he : i = 0 := by omega
      subst i
      simp [lane, packedOps, concrete, hn]
    · simp [lane, packedOps, concrete, BitVec.getLsbD_not, hi]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem packed_correct : circuit packedOps packedInputs = packedOutputs := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inputs_at_lane : ∀ x : BitVec 8,
    packedInputs.map (lane x.toNat) = (List.range 8).map (fun i => x.extractLsb' i 1) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem outputs_at_lane : ∀ x : BitVec 8,
    packValue (packedOutputs.map (lane x.toNat)) = spec x := by decide +kernel

/-- All 256 cases, proved through a 256-lane bit-sliced evaluation. -/
theorem value_eq_spec (x : BitVec 8) : value x = spec x := by
  rw [value, ← inputs_at_lane x, ← circuit_map (laneHom x.toNat x.isLt),
    packed_correct, outputs_at_lane]

theorem expr_refines (assign : BVExpr.Assignment) (x : BVExpr 8) :
    BVExpr.eval assign (expr x) = spec (BVExpr.eval assign x) := by
  rw [expr, packExpr_refines, circuit_map (evaluationHom assign)]
  simpa only [List.map_map, Function.comp_def, BvConstruct.eval_extract, value] using
    value_eq_spec (BVExpr.eval assign x)

theorem nonlinear_count :
    (program.filter (fun g => match g with | .and .. => true | _ => false)).length = 32 := by decide

end TlsMpc.AesSbox
