import TlsMpc.Signal.MlKem
import TlsMpc.ModAdd
import TlsMpc.Sha256Ripple

/-!
ML-KEM / Kyber encapsulation with arithmetic made for q = 3329.

`TlsMpc/Signal/MlKem.lean` is the specification: coefficients are 32-bit words
and every operation ends in a generic 32-bit remainder. Here a coefficient is a
12-bit word, always in 0..3328, and each operation is a small circuit:

* `addMod`, `subMod`: one 12-bit addition or subtraction and one conditional
  correction;
* `mulConst c`: multiplication by a PUBLIC constant (every NTT root) with the
  quotient estimated from a precomputed `c·2^12/q`;
* `mulMod`: a 12×12 multiplier and a Barrett reduction of the 24-bit product;
* `compress`: multiplication by a public reciprocal.

The polynomial layer (`forward`, `inverse`, `baseMultiply`, `dot`) has the
shape of the specification's, operation for operation, so the two can be
compared coefficient by coefficient (`TlsMpc/MlKemFastProofs.lean`).

Matrix sampling keeps the first 256 candidates below q with a compaction
network (`compact`): every candidate carries the number of rejected candidates
before it and moves left by that distance, one binary digit per stage.

Everything is generic in an operation record (`Ops`) with a circuit instance
(`symbolic`) and a value instance (`concrete`), related by `evaluationHom`.
The stage functions at the end are the bodies of the kernels in
`TlsMpc/MlKemFastKernels.lean`.
-/
namespace TlsMpc.Signal.MlKemFast
open Std.Tactic.BVDecide

/-- `B`: byte, `T`: bit, `W`: coefficient (12 bits). -/
structure Ops (B T W : Type) where
  zero : T
  one : T
  xor : T → T → T
  and : T → T → T
  byteBits : B → List T
  bitsByte : List T → B
  ofBits : List T → W
  bits : W → List T
  const : Nat → W
  addMod : W → W → W
  subMod : W → W → W
  mulMod : W → W → W
  mulConst : Nat → W → W
  compress : Nat → W → W
  ltQ : W → T
  select : T → W → W → W

/-! ### Values -/

def packValue : (n : Nat) → (Nat → BitVec 1) → BitVec n
  | 0, _ => 0#0
  | n + 1, bit => (bit n ++ packValue n bit).cast (by omega)

/-- `s mod q` for `s < 2q`. -/
def condSub (s : BitVec 13) : BitVec 12 :=
  let d : BitVec 14 := (0#1 ++ s) + 13055#14
  let low := d.extractLsb' 0 12
  low ^^^ ((s.extractLsb' 0 12 ^^^ low) &&& BitVec.replicate 12 (d.extractLsb' 13 1))

/-- `x - y` on 13 bits, by one addition. -/
def sub13 (x y : BitVec 13) : BitVec 13 := ~~~(~~~x + y)

def addValue (x y : BitVec 12) : BitVec 12 := condSub ((0#1 ++ x) + (0#1 ++ y))

def subValue (x y : BitVec 12) : BitVec 12 :=
  let d := sub13 (0#1 ++ x) (0#1 ++ y)
  d.extractLsb' 0 12 + (3329#12 &&& BitVec.replicate 12 (d.extractLsb' 12 1))

/-- The first `n` rows of the 12×12 multiplier, as a 24-bit sum. -/
def mulRows (x y : BitVec 12) : Nat → BitVec 24
  | 0 => 0#24
  | n + 1 => mulRows x y n +
      (((0#12 ++ x) <<< BitVec.ofNat 5 n) &&& BitVec.replicate 24 (y.extractLsb' n 1))

/-- `v mod q` for any 24-bit `v` (Barrett: the quotient is estimated from the top 15 bits). -/
def reduce24 (v : BitVec 24) : BitVec 12 :=
  let t : BitVec 28 := (0#13 ++ v.extractLsb' 9 15) * 5039#28
  let k : BitVec 13 := t.extractLsb' 15 13 * 3329#13
  condSub (sub13 (v.extractLsb' 0 13) k)

def mulValue (x y : BitVec 12) : BitVec 12 := reduce24 (mulRows x y 12)

/-- `c · x mod q` for a public `c < q`. -/
def mulConstValue (c : Nat) (x : BitVec 12) : BitVec 12 :=
  let p : BitVec 24 := (0#12 ++ x) * BitVec.ofNat 24 (c * 4096 / 3329)
  let lo : BitVec 13 := (0#1 ++ x) * BitVec.ofNat 13 c
  let k : BitVec 13 := (0#1 ++ p.extractLsb' 12 12) * 3329#13
  condSub (sub13 lo k)

/-- `round(x · 2^d / q) mod 2^d` for d = 11 and d = 5 (other widths: unchanged). -/
def compressValue (d : Nat) (x : BitVec 12) : BitVec 12 :=
  if d = 11 then 0#1 ++ (((0#18 ++ x) * 161271#30 + 131032#30).extractLsb' 18 11)
  else if d = 5 then 0#7 ++ (((0#9 ++ x) * 315#21 + 16384#21).extractLsb' 15 5)
  else x

def ltQValue (x : BitVec 12) : BitVec 1 := ~~~(((0#1 ++ x) + 767#13).extractLsb' 12 1)

def selectValue (c : BitVec 1) (x y : BitVec 12) : BitVec 12 := y ^^^ ((x ^^^ y) &&& BitVec.replicate 12 c)

def concrete : Ops (BitVec 8) (BitVec 1) (BitVec 12) where
  zero := 0#1
  one := 1#1
  xor := (· ^^^ ·)
  and := (· &&& ·)
  byteBits b := (List.range 8).map (fun i => b.extractLsb' i 1)
  bitsByte l := packValue 8 (fun i => l.getD i 0#1)
  ofBits l := packValue 12 (fun i => l.getD i 0#1)
  bits x := (List.range 12).map (fun i => x.extractLsb' i 1)
  const n := BitVec.ofNat 12 n
  addMod := addValue
  subMod := subValue
  mulMod := mulValue
  mulConst := mulConstValue
  compress := compressValue
  ltQ := ltQValue
  select := selectValue

/-! ### Circuits -/

def zx (k : Nat) (x : BVExpr w) : BVExpr (k + w) := .append (.const 0#k) x rfl
def condSubExpr (s : BVExpr 13) : BVExpr 12 :=
  let d : BVExpr 14 := .bin (zx 1 s) .add (.const 13055#14)
  let low : BVExpr 12 := .extract 0 12 d
  .bin low .xor (.bin (.bin (.extract 0 12 s) .xor low) .and (.replicate 12 (.extract 13 1 d) rfl))
def sub13Expr (x y : BVExpr 13) : BVExpr 13 := .un .not (.bin (.un .not x) .add y)
def addExpr (x y : BVExpr 12) : BVExpr 12 := condSubExpr (.bin (zx 1 x) .add (zx 1 y))
def subExpr (x y : BVExpr 12) : BVExpr 12 :=
  let d := sub13Expr (zx 1 x) (zx 1 y)
  .bin (.extract 0 12 d) .add (.bin (.const 3329#12) .and (.replicate 12 (.extract 12 1 d) rfl))
def mulRowsExpr (x y : BVExpr 12) : Nat → BVExpr 24
  | 0 => .const 0#24
  | n + 1 => .bin (mulRowsExpr x y n) .add
      (.bin (.shiftLeft (zx 12 x) (.const (BitVec.ofNat 5 n))) .and (.replicate 24 (.extract n 1 y) rfl))
def reduce24Expr (v : BVExpr 24) : BVExpr 12 :=
  let t : BVExpr 28 := .bin (zx 13 (.extract 9 15 v)) .mul (.const 5039#28)
  let k : BVExpr 13 := .bin (.extract 15 13 t) .mul (.const 3329#13)
  condSubExpr (sub13Expr (.extract 0 13 v) k)
def mulExpr (x y : BVExpr 12) : BVExpr 12 := reduce24Expr (mulRowsExpr x y 12)
def mulConstExpr (c : Nat) (x : BVExpr 12) : BVExpr 12 :=
  let p : BVExpr 24 := .bin (zx 12 x) .mul (.const (BitVec.ofNat 24 (c * 4096 / 3329)))
  let lo : BVExpr 13 := .bin (zx 1 x) .mul (.const (BitVec.ofNat 13 c))
  let k : BVExpr 13 := .bin (zx 1 (.extract 12 12 p)) .mul (.const 3329#13)
  condSubExpr (sub13Expr lo k)
def compressExpr (d : Nat) (x : BVExpr 12) : BVExpr 12 :=
  if d = 11 then zx 1 (.extract 18 11 (.bin (.bin (zx 18 x) .mul (.const 161271#30)) .add (.const 131032#30)))
  else if d = 5 then zx 7 (.extract 15 5 (.bin (.bin (zx 9 x) .mul (.const 315#21)) .add (.const 16384#21)))
  else x
def ltQExpr (x : BVExpr 12) : BVExpr 1 := .un .not (.extract 12 1 (.bin (zx 1 x) .add (.const 767#13)))
def selectExpr (c : BVExpr 1) (x y : BVExpr 12) : BVExpr 12 :=
  .bin y .xor (.bin (.bin x .xor y) .and (.replicate 12 c rfl))

def symbolic : Ops (BVExpr 8) (BVExpr 1) (BVExpr 12) where
  zero := .const 0#1
  one := .const 1#1
  xor x y := BvConstruct.bin x .xor y
  and x y := BvConstruct.bin x .and y
  byteBits b := (List.range 8).map (fun i => BvConstruct.extract i 1 b)
  bitsByte l := ModAdd.packBits 8 (fun i => l.getD i (.const 0#1))
  ofBits l := ModAdd.packBits 12 (fun i => l.getD i (.const 0#1))
  bits x := (List.range 12).map (fun i => BvConstruct.extract i 1 x)
  const n := .const (BitVec.ofNat 12 n)
  addMod := addExpr
  subMod := subExpr
  mulMod := mulExpr
  mulConst := mulConstExpr
  compress := compressExpr
  ltQ := ltQExpr
  select := selectExpr

structure Hom (o : Ops B T W) (o' : Ops B' T' W') (fb : B → B') (ft : T → T') (fw : W → W') : Prop where
  zero : ft o.zero = o'.zero
  one : ft o.one = o'.one
  xor : ∀ x y, ft (o.xor x y) = o'.xor (ft x) (ft y)
  and : ∀ x y, ft (o.and x y) = o'.and (ft x) (ft y)
  byteBits : ∀ b, (o.byteBits b).map ft = o'.byteBits (fb b)
  bitsByte : ∀ l, fb (o.bitsByte l) = o'.bitsByte (l.map ft)
  ofBits : ∀ l, fw (o.ofBits l) = o'.ofBits (l.map ft)
  bits : ∀ x, (o.bits x).map ft = o'.bits (fw x)
  const : ∀ n, fw (o.const n) = o'.const n
  addMod : ∀ x y, fw (o.addMod x y) = o'.addMod (fw x) (fw y)
  subMod : ∀ x y, fw (o.subMod x y) = o'.subMod (fw x) (fw y)
  mulMod : ∀ x y, fw (o.mulMod x y) = o'.mulMod (fw x) (fw y)
  mulConst : ∀ c x, fw (o.mulConst c x) = o'.mulConst c (fw x)
  compress : ∀ d x, fw (o.compress d x) = o'.compress d (fw x)
  ltQ : ∀ x, ft (o.ltQ x) = o'.ltQ (fw x)
  select : ∀ c x y, fw (o.select c x y) = o'.select (ft c) (fw x) (fw y)

theorem eval_zx (assign : BVExpr.Assignment) (k : Nat) (x : BVExpr w) :
    (zx k x).eval assign = 0#k ++ x.eval assign := rfl

theorem eval_packBits (assign : BVExpr.Assignment) (n : Nat) (bit : Nat → BVExpr 1) :
    (ModAdd.packBits n bit).eval assign = packValue n (fun i => (bit i).eval assign) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ModAdd.packBits, packValue, Sha256Ripple.eval_append_cast, ih]

theorem eval_getD (assign : BVExpr.Assignment) (l : List (BVExpr 1)) (i : Nat) :
    (l.getD i (.const 0#1)).eval assign = (l.map (BVExpr.eval assign)).getD i 0#1 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem eval_condSub (assign : BVExpr.Assignment) (s : BVExpr 13) :
    (condSubExpr s).eval assign = condSub (s.eval assign) := by
  simp only [condSubExpr, condSub, BVExpr.eval_bin, BVExpr.eval_extract, BVExpr.eval_replicate,
    BVExpr.eval_const, eval_zx, BVBinOp.eval]

theorem eval_sub13 (assign : BVExpr.Assignment) (x y : BVExpr 13) :
    (sub13Expr x y).eval assign = sub13 (x.eval assign) (y.eval assign) := by
  simp only [sub13Expr, sub13, BVExpr.eval_bin, BVExpr.eval_un, BVBinOp.eval, BVUnOp.eval]

theorem eval_mulRows (assign : BVExpr.Assignment) (x y : BVExpr 12) (n : Nat) :
    (mulRowsExpr x y n).eval assign = mulRows (x.eval assign) (y.eval assign) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [mulRowsExpr, mulRows, BVExpr.eval_bin, BVExpr.eval_extract, BVExpr.eval_replicate,
        BVExpr.eval_const, BVExpr.eval_shiftLeft, eval_zx, BVBinOp.eval, ih]

theorem eval_reduce24 (assign : BVExpr.Assignment) (v : BVExpr 24) :
    (reduce24Expr v).eval assign = reduce24 (v.eval assign) := by
  simp only [reduce24Expr, reduce24, eval_condSub, eval_sub13, BVExpr.eval_bin, BVExpr.eval_extract,
    BVExpr.eval_const, eval_zx, BVBinOp.eval]

def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) (BVExpr.eval assign) where
  zero := rfl
  one := rfl
  xor x y := BvConstruct.eval_bin assign x .xor y
  and x y := BvConstruct.eval_bin assign x .and y
  byteBits b := by
    simp only [symbolic, concrete, List.map_map, Function.comp_def, BvConstruct.eval_extract]
  bitsByte l := by
    simp only [symbolic, concrete, eval_packBits, eval_getD]
  ofBits l := by
    simp only [symbolic, concrete, eval_packBits, eval_getD]
  bits x := by
    simp only [symbolic, concrete, List.map_map, Function.comp_def, BvConstruct.eval_extract]
  const n := rfl
  addMod x y := by
    simp only [symbolic, concrete, addExpr, addValue, eval_condSub, BVExpr.eval_bin, eval_zx, BVBinOp.eval]
  subMod x y := by
    simp only [symbolic, concrete, subExpr, subValue, eval_sub13, BVExpr.eval_bin, BVExpr.eval_extract,
      BVExpr.eval_replicate, BVExpr.eval_const, eval_zx, BVBinOp.eval]
  mulMod x y := by
    simp only [symbolic, concrete, mulExpr, mulValue, eval_reduce24, eval_mulRows]
  mulConst c x := by
    simp only [symbolic, concrete, mulConstExpr, mulConstValue, eval_condSub, eval_sub13, BVExpr.eval_bin,
      BVExpr.eval_extract, BVExpr.eval_const, eval_zx, BVBinOp.eval]
  compress d x := by
    simp only [symbolic, concrete, compressExpr, compressValue]
    split
    · simp only [BVExpr.eval_bin, BVExpr.eval_extract, BVExpr.eval_const, eval_zx, BVBinOp.eval]
    · split
      · simp only [BVExpr.eval_bin, BVExpr.eval_extract, BVExpr.eval_const, eval_zx, BVBinOp.eval]
      · rfl
  ltQ x := by
    simp only [symbolic, concrete, ltQExpr, ltQValue, BVExpr.eval_bin, BVExpr.eval_un, BVExpr.eval_extract,
      BVExpr.eval_const, eval_zx, BVBinOp.eval, BVUnOp.eval]
  select c x y := by
    simp only [symbolic, concrete, selectExpr, selectValue, BVExpr.eval_bin, BVExpr.eval_replicate, BVBinOp.eval]

/-! ### Polynomials (the shape of `MlKemNtt` and `MlKemPke`) -/

abbrev Poly (W : Type) := List W

def get (o : Ops B T W) (poly : Poly W) (i : Nat) : W := poly[i]?.getD (o.const 0)

def forwardLayer (o : Ops B T W) (level : Nat) (poly : Poly W) : Poly W :=
  let length := 128/2^level
  (List.range 256).map (fun i =>
    let position := i%(2*length)
    let group := i/(2*length)
    let root := MlKemNtt.zeta (2^level+group)
    if position < length then o.addMod (get o poly i) (o.mulConst root (get o poly (i+length)))
    else o.subMod (get o poly (i-length)) (o.mulConst root (get o poly i)))

def inverseLayer (o : Ops B T W) (level : Nat) (poly : Poly W) : Poly W :=
  let length := 2*2^level
  (List.range 256).map (fun i =>
    let position := i%(2*length)
    let group := i/(2*length)
    let root := MlKemNtt.zeta (128/2^level-1-group)
    if position < length then o.addMod (get o poly i) (get o poly (i+length))
    else o.mulConst root (o.subMod (get o poly i) (get o poly (i-length))))

def forward (o : Ops B T W) (poly : Poly W) : Poly W :=
  (List.range 7).foldl (fun state level => forwardLayer o level state) poly

def inverse (o : Ops B T W) (poly : Poly W) : Poly W :=
  ((List.range 7).foldl (fun state level => inverseLayer o level state) poly).map (o.mulConst 3303)

def baseMultiply (o : Ops B T W) (left right : Poly W) : Poly W :=
  (List.range 256).map (fun i =>
    let pair := i/2
    let a0 := get o left (2*pair)
    let a1 := get o left (2*pair+1)
    let b0 := get o right (2*pair)
    let b1 := get o right (2*pair+1)
    if i%2 = 0 then o.addMod (o.mulMod a0 b0)
      (o.mulConst (17^(2*MlKemNtt.reverseBits 7 pair+1)%3329) (o.mulMod a1 b1))
    else o.addMod (o.mulMod a0 b1) (o.mulMod a1 b0))

def zeroPoly (o : Ops B T W) : Poly W := List.replicate 256 (o.const 0)
def add (o : Ops B T W) (x y : Poly W) : Poly W := List.zipWith o.addMod x y
def sum (o : Ops B T W) (polys : List (Poly W)) : Poly W := polys.foldl (add o) (zeroPoly o)
def dot (o : Ops B T W) (rank : Nat) (left right : Nat → Poly W) : Poly W :=
  sum o ((List.range rank).map (fun i => baseMultiply o (left i) (right i)))

/-! ### Bits, bytes and coefficients -/

def bitsOf (o : Ops B T W) (bytes : List B) : List T := bytes.flatMap o.byteBits
def chunk (l : List α) (size i : Nat) : List α := (l.drop (size*i)).take size

/-- `count` coefficients of 12 bits each from a little-endian bit string
(`ByteDecode_12`; also the candidates of the matrix sampler). -/
def decode12 (o : Ops B T W) (count : Nat) (bytes : List B) : Poly W :=
  let bits := bitsOf o bytes
  (List.range count).map (fun i => o.ofBits (chunk bits 12 i))

/-- The low `width` bits of every coefficient, packed (`ByteEncode_width`). -/
def encode (o : Ops B T W) (width : Nat) (poly : Poly W) : List B :=
  let bits := poly.flatMap (fun x => (o.bits x).take width)
  (List.range (width*poly.length/8)).map (fun j => o.bitsByte (chunk bits 8 j))

/-- Centered binomial sample with η = 2 from 128 bytes. -/
def cbd (o : Ops B T W) (bytes : List B) : Poly W :=
  let bits := bitsOf o bytes
  (List.range 256).map (fun i =>
    let b := fun j => bits.getD (4*i+j) o.zero
    o.subMod (o.ofBits [o.xor (b 0) (b 1), o.and (b 0) (b 1)]) (o.ofBits [o.xor (b 2) (b 3), o.and (b 2) (b 3)]))

/-- `Decompress_1`: 1665 for a set bit. -/
def messagePoly (o : Ops B T W) (bytes : List B) : Poly W :=
  (bitsOf o bytes).map (fun b => o.ofBits ((List.range 12).map (fun i => if (1665).testBit i then b else o.zero)))

/-- 255 or 0. -/
def maskByte (o : Ops B T W) (t : T) : B := o.bitsByte (List.replicate 8 t)

/-- Every coefficient is below q. -/
def allBelow (o : Ops B T W) (poly : Poly W) : T := (poly.map o.ltQ).foldl o.and o.one

/-! ### Matrix sampling by compaction -/

structure Cell (T W : Type) where
  valid : T
  dist : List T
  data : W

def Cell.map (ft : T → T') (fw : W → W') (c : Cell T W) : Cell T' W' := ⟨ft c.valid, c.dist.map ft, fw c.data⟩

def distBits : Nat := 9

def emptyCell (o : Ops B T W) : Cell T W := ⟨o.zero, List.replicate distBits o.zero, o.const 0⟩
def notT (o : Ops B T W) (t : T) : T := o.xor t o.one
/-- `c ? x : y` -/
def selT (o : Ops B T W) (c x y : T) : T := o.xor y (o.and c (o.xor x y))

/-- Add one bit to a little-endian counter. -/
def increment (o : Ops B T W) : List T → T → List T
  | [], _ => []
  | b :: rest, carry => o.xor b carry :: increment o rest (o.and b carry)

/-- Each candidate with its validity and the number of rejected candidates before it. -/
def cells (o : Ops B T W) : List W → List T → List (Cell T W)
  | [], _ => []
  | c :: rest, count =>
      let valid := o.ltQ c
      ⟨valid, count, c⟩ :: cells o rest (increment o count (notT o valid))

/-- Stage `s`: a valid cell whose distance has digit `s` set moves `2^s` places left. -/
def stage (o : Ops B T W) (s : Nat) (state : List (Cell T W)) : List (Cell T W) :=
  List.zipWith (fun a b =>
    let take := o.and b.valid (b.dist.getD s o.zero)
    let keep := o.and a.valid (notT o (a.dist.getD s o.zero))
    ⟨selT o take b.valid keep, List.zipWith (selT o take) b.dist a.dist, o.select take b.data a.data⟩)
    state (state.drop (2^s) ++ List.replicate (2^s) (emptyCell o))

def compact (o : Ops B T W) (state : List (Cell T W)) : List (Cell T W) :=
  (List.range distBits).foldl (fun state s => stage o s state) state

/-- The first `count` candidates below q, and whether there were that many
(otherwise all zero). -/
def sample (o : Ops B T W) (count : Nat) (candidates : List W) : T × Poly W :=
  let final := compact o (cells o candidates (List.replicate distBits o.zero))
  let ok := ((final.drop (count-1)).headD (emptyCell o)).valid
  (ok, (final.take count).map (fun c => o.select ok c.data (o.const 0)))

/-- One matrix entry: SHAKE128 of `seed`, four blocks (448 candidates). -/
def entry (o : Ops B T W) (k : Keccak.Ops B K) (seed : List B) : T × Poly W :=
  sample o 256 (decode12 o 448 (Keccak.shake128 k 672 seed))

/-! ### Stages (kernel bodies) -/

/-- The sampler alone, on a given 672-byte stream: the coefficients (384 bytes) and the status.
Only for checking the compaction on streams SHAKE128 would never produce. -/
def sampleStage (o : Ops B T W) (stream : List B) : List (List B) :=
  let e := sample o 256 (decode12 o 448 stream)
  [encode o 12 e.2, [maskByte o e.1]]

def noise (o : Ops B T W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (coins : List B) (nonce : Nat) : Poly W :=
  cbd o (Keccak.shake256 k 128 (coins ++ [a.const nonce]))

def polyAt (o : Ops B T W) (bytes : List B) (j : Nat) : Poly W :=
  decode12 o 256 ((bytes.drop (384*j)).take 384)

/-- `message` (32), `kbar` (32), `coins` (32), `keyValid` (1). -/
def hashStage (o : Ops B T W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (kyber : Bool)
    (key entropyA entropyB : List B) : List (List B) :=
  let entropy := List.zipWith a.xor entropyA entropyB
  let message := if kyber then Keccak.sha3_256 k entropy else entropy
  let expanded := Keccak.sha3_512 k (message ++ Keccak.sha3_256 k key)
  [message, expanded.take 32, expanded.drop 32,
    [maskByte o (allBelow o (decode12 o 1024 (key.take 1536)))]]

/-- `rhat`: the NTT of the four secret polynomials, 384 bytes each. -/
def nttStage (o : Ops B T W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (coins : List B) : List B :=
  (List.range 4).flatMap (fun j => encode o 12 (forward o (noise o a k coins j)))

/-- Row `i` of the transposed matrix (four entries, 384 bytes each) and its status. -/
def matrixStage (o : Ops B T W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (i : Nat) (key : List B) :
    List (List B) :=
  let rho := (key.drop 1536).take 32
  let entries := (List.range 4).map (fun j => entry o k (rho ++ [a.const i, a.const j]))
  [entries.flatMap (fun e => encode o 12 e.2), [maskByte o ((entries.map (·.1)).foldl o.and o.one)]]

/-- Compressed `u_i` (352 bytes). -/
def uStage (o : Ops B T W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (i : Nat) (row rhat coins : List B) :
    List B :=
  let u := add o (inverse o (dot o 4 (polyAt o row) (polyAt o rhat))) (noise o a k coins (4+i))
  encode o 11 (u.map (o.compress 11))

/-- Compressed `v` (160 bytes). -/
def vStage (o : Ops B T W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (key rhat coins message : List B) :
    List B :=
  let v := add o (add o (inverse o (dot o 4 (polyAt o key) (polyAt o rhat))) (noise o a k coins 8))
    (messagePoly o message)
  encode o 5 (v.map (o.compress 5))

/-- Status (255 or 0), ciphertext and shared secret; the last two are zero unless every check is 255. -/
def finishStage (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (kyber : Bool)
    (ciphertext kbar : List B) (checks : List B) : List (List B) :=
  let status := ByteAuth.eqMask a (checks.foldl a.and (a.const 255)) (a.const 255)
  let secret := if kyber then Keccak.shake256 k 32 (kbar ++ Keccak.sha3_256 k ciphertext) else kbar
  [[status], ByteAuth.release a status ciphertext, ByteAuth.release a status secret]

/-! ### The stages commute with a homomorphism of the operations -/

section
variable {o : Ops B T W} {o' : Ops B' T' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {k : Keccak.Ops B K} {k' : Keccak.Ops B' K'}
  {fb : B → B'} {ft : T → T'} {fw : W → W'} {gk : K → K'}
  (h : Hom o o' fb ft fw) (ha : ByteAuth.Hom a a' fb) (hk : Keccak.Hom k k' fb gk)

include h in
theorem get_map (poly : Poly W) (i : Nat) : fw (get o poly i) = get o' (poly.map fw) i := by
  simp only [get, List.getElem?_map, Keccak.getD_map fw, h.const]
include h in
theorem forwardLayer_map (level : Nat) (poly : Poly W) :
    (forwardLayer o level poly).map fw = forwardLayer o' level (poly.map fw) := by
  simp only [forwardLayer, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  split <;> simp only [h.addMod, h.subMod, h.mulConst, get_map h]
include h in
theorem inverseLayer_map (level : Nat) (poly : Poly W) :
    (inverseLayer o level poly).map fw = inverseLayer o' level (poly.map fw) := by
  simp only [inverseLayer, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  split <;> simp only [h.addMod, h.subMod, h.mulConst, get_map h]
include h in
theorem forwardLoop_map (levels : List Nat) (poly : Poly W) :
    (levels.foldl (fun state level => forwardLayer o level state) poly).map fw =
      levels.foldl (fun state level => forwardLayer o' level state) (poly.map fw) := by
  induction levels generalizing poly with
  | nil => rfl
  | cons level levels ih => simp only [List.foldl_cons, ih, forwardLayer_map h]
include h in
theorem inverseLoop_map (levels : List Nat) (poly : Poly W) :
    (levels.foldl (fun state level => inverseLayer o level state) poly).map fw =
      levels.foldl (fun state level => inverseLayer o' level state) (poly.map fw) := by
  induction levels generalizing poly with
  | nil => rfl
  | cons level levels ih => simp only [List.foldl_cons, ih, inverseLayer_map h]
include h in
theorem forward_map (poly : Poly W) : (forward o poly).map fw = forward o' (poly.map fw) :=
  forwardLoop_map h _ _
include h in
theorem inverse_map (poly : Poly W) : (inverse o poly).map fw = inverse o' (poly.map fw) := by
  simp only [inverse, List.map_map, Function.comp_def, h.mulConst]
  rw [← inverseLoop_map h]
  simp only [List.map_map, Function.comp_def]
include h in
theorem baseMultiply_map (left right : Poly W) :
    (baseMultiply o left right).map fw = baseMultiply o' (left.map fw) (right.map fw) := by
  simp only [baseMultiply, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  split <;> simp only [h.addMod, h.mulMod, h.mulConst, get_map h]
include h in
theorem add_map (x y : Poly W) : (add o x y).map fw = add o' (x.map fw) (y.map fw) := by
  simp only [add, List.map_zipWith, List.zipWith_map_left, List.zipWith_map_right, h.addMod]
include h in
theorem sumLoop_map (polys : List (Poly W)) (acc : Poly W) :
    (polys.foldl (add o) acc).map fw = (polys.map (List.map fw)).foldl (add o') (acc.map fw) := by
  induction polys generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, add_map h]
include h in
theorem dot_map (rank : Nat) (left right : Nat → Poly W) :
    (dot o rank left right).map fw = dot o' rank (fun i => (left i).map fw) (fun i => (right i).map fw) := by
  simp only [dot, sum, sumLoop_map h, zeroPoly, List.map_replicate, h.const, List.map_map, Function.comp_def,
    baseMultiply_map h]

include h in
theorem bitsOf_map (bytes : List B) : (bitsOf o bytes).map ft = bitsOf o' (bytes.map fb) := by
  simp only [bitsOf, List.map_flatMap, List.flatMap_map, h.byteBits]
theorem chunk_map (f : α → β) (l : List α) (size i : Nat) : (chunk l size i).map f = chunk (l.map f) size i := by
  simp only [chunk, List.map_take, List.map_drop]
include h in
theorem decode12_map (count : Nat) (bytes : List B) :
    (decode12 o count bytes).map fw = decode12 o' count (bytes.map fb) := by
  simp only [decode12, List.map_map, Function.comp_def, h.ofBits, chunk_map, bitsOf_map h]
include h in
theorem encode_map (width : Nat) (poly : Poly W) :
    (encode o width poly).map fb = encode o' width (poly.map fw) := by
  simp only [encode, List.map_map, Function.comp_def, h.bitsByte, chunk_map, List.map_flatMap, List.flatMap_map,
    List.map_take, h.bits, List.length_map]
theorem getD_map' (f : α → β) (l : List α) (i : Nat) (d : α) : f (l.getD i d) = (l.map f).getD i (f d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl
include h in
theorem cbd_map (bytes : List B) : (cbd o bytes).map fw = cbd o' (bytes.map fb) := by
  simp only [cbd, List.map_map, Function.comp_def, h.subMod, h.ofBits, List.map_cons, List.map_nil, h.xor, h.and,
    getD_map' ft, h.zero, bitsOf_map h]
include h in
theorem messagePoly_map (bytes : List B) : (messagePoly o bytes).map fw = messagePoly o' (bytes.map fb) := by
  simp only [messagePoly, ← bitsOf_map h, List.map_map, Function.comp_def, h.ofBits]
  apply List.map_congr_left
  intro b _
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · rfl
  · exact h.zero
include h in
theorem maskByte_map (t : T) : fb (maskByte o t) = maskByte o' (ft t) := by
  simp only [maskByte, h.bitsByte, List.map_replicate]
include h in
theorem andLoop_map (bits : List T) (acc : T) :
    ft (bits.foldl o.and acc) = (bits.map ft).foldl o'.and (ft acc) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, h.and]
include h in
theorem allBelow_map (poly : Poly W) : ft (allBelow o poly) = allBelow o' (poly.map fw) := by
  simp only [allBelow, andLoop_map h, List.map_map, Function.comp_def, h.ltQ, h.one]

include h in
theorem emptyCell_map : (emptyCell o).map ft fw = emptyCell o' := by
  simp only [emptyCell, Cell.map, List.map_replicate, h.zero, h.const]
include h in
theorem increment_map (bits : List T) (carry : T) :
    (increment o bits carry).map ft = increment o' (bits.map ft) (ft carry) := by
  induction bits generalizing carry with
  | nil => rfl
  | cons b rest ih => simp only [increment, List.map_cons, ih, h.xor, h.and]
include h in
theorem cells_map (candidates : List W) (count : List T) :
    (cells o candidates count).map (Cell.map ft fw) = cells o' (candidates.map fw) (count.map ft) := by
  induction candidates generalizing count with
  | nil => rfl
  | cons c rest ih =>
      simp only [cells, List.map_cons, ih, Cell.map, increment_map h, notT, h.xor, h.ltQ, h.one]
include h in
theorem stage_map (s : Nat) (state : List (Cell T W)) :
    (stage o s state).map (Cell.map ft fw) = stage o' s (state.map (Cell.map ft fw)) := by
  have pointwise : ∀ (xs ys : List (Cell T W)),
      (List.zipWith (fun a b =>
        let take := o.and b.valid (b.dist.getD s o.zero)
        let keep := o.and a.valid (notT o (a.dist.getD s o.zero))
        (⟨selT o take b.valid keep, List.zipWith (selT o take) b.dist a.dist, o.select take b.data a.data⟩ : Cell T W))
        xs ys).map (Cell.map ft fw) =
      List.zipWith (fun a b =>
        let take := o'.and b.valid (b.dist.getD s o'.zero)
        let keep := o'.and a.valid (notT o' (a.dist.getD s o'.zero))
        (⟨selT o' take b.valid keep, List.zipWith (selT o' take) b.dist a.dist, o'.select take b.data a.data⟩ : Cell T' W'))
        (xs.map (Cell.map ft fw)) (ys.map (Cell.map ft fw)) := by
    intro xs
    induction xs with
    | nil => intro ys; rfl
    | cons x xs ih =>
        intro ys
        cases ys with
        | nil => rfl
        | cons y ys =>
            simp only [List.zipWith_cons_cons, List.map_cons, ih, Cell.map, selT, notT, h.xor, h.and, h.select,
              getD_map' ft, h.zero, h.one, List.map_zipWith, List.zipWith_map_left, List.zipWith_map_right]
  simp only [stage, pointwise, List.map_append, List.map_drop, List.map_replicate, emptyCell_map h]
include h in
theorem compactLoop_map (stages : List Nat) (state : List (Cell T W)) :
    (stages.foldl (fun state s => stage o s state) state).map (Cell.map ft fw) =
      stages.foldl (fun state s => stage o' s state) (state.map (Cell.map ft fw)) := by
  induction stages generalizing state with
  | nil => rfl
  | cons s rest ih => simp only [List.foldl_cons, ih, stage_map h]
theorem headD_map (f : α → β) (l : List α) (d : α) : f (l.headD d) = (l.map f).headD (f d) := by
  cases l <;> rfl
include h in
theorem sample_map (count : Nat) (candidates : List W) :
    ft (sample o count candidates).1 = (sample o' count (candidates.map fw)).1 ∧
    (sample o count candidates).2.map fw = (sample o' count (candidates.map fw)).2 := by
  have state : (compact o (cells o candidates (List.replicate distBits o.zero))).map (Cell.map ft fw) =
      compact o' (cells o' (candidates.map fw) (List.replicate distBits o'.zero)) := by
    simp only [compact, compactLoop_map h, cells_map h, List.map_replicate, h.zero]
  have ok : ft (sample o count candidates).1 = (sample o' count (candidates.map fw)).1 := by
    simp only [sample, ← state, ← emptyCell_map h, ← List.map_drop, ← headD_map]
    rfl
  refine ⟨ok, ?_⟩
  simp only [sample] at ok ⊢
  simp only [← state, List.map_take, List.map_map, Function.comp_def, h.select, h.const, ok]
  rfl
include h hk in
theorem entry_map (seed : List B) :
    ft (entry o k seed).1 = (entry o' k' (seed.map fb)).1 ∧
    (entry o k seed).2.map fw = (entry o' k' (seed.map fb)).2 := by
  simp only [entry, ← decode12_map h, Keccak.shake128, ← Keccak.hash_map hk]
  exact sample_map h 256 _

include h in
theorem sampleStage_map (stream : List B) :
    (sampleStage o stream).map (List.map fb) = sampleStage o' (stream.map fb) := by
  have e := sample_map h 256 (decode12 o 448 stream)
  rw [decode12_map h] at e
  simp only [sampleStage, List.map_cons, List.map_nil, encode_map h, maskByte_map h, e.1, e.2]
include h ha hk in
theorem noise_map (coins : List B) (nonce : Nat) :
    (noise o a k coins nonce).map fw = noise o' a' k' (coins.map fb) nonce := by
  simp only [noise, cbd_map h, Keccak.shake256, Keccak.hash_map hk, List.map_append, List.map_cons, List.map_nil,
    ha.const]
include h in
theorem polyAt_map (bytes : List B) (j : Nat) : (polyAt o bytes j).map fw = polyAt o' (bytes.map fb) j := by
  simp only [polyAt, decode12_map h, List.map_take, List.map_drop]

include h ha hk in
theorem hashStage_map (kyber : Bool) (key entropyA entropyB : List B) :
    (hashStage o a k kyber key entropyA entropyB).map (List.map fb) =
      hashStage o' a' k' kyber (key.map fb) (entropyA.map fb) (entropyB.map fb) := by
  cases kyber <;>
    simp only [hashStage, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.map_take, List.map_drop,
      Keccak.sha3_512, Keccak.sha3_256, Keccak.hash_map hk, List.map_append, List.map_zipWith,
      List.zipWith_map_left, List.zipWith_map_right, ha.xor, maskByte_map h, allBelow_map h, decode12_map h]
include h ha hk in
theorem nttStage_map (coins : List B) :
    (nttStage o a k coins).map fb = nttStage o' a' k' (coins.map fb) := by
  simp only [nttStage, List.map_flatMap, encode_map h, forward_map h, noise_map h ha hk]
include h ha hk in
theorem matrixStage_map (i : Nat) (key : List B) :
    (matrixStage o a k i key).map (List.map fb) = matrixStage o' a' k' i (key.map fb) := by
  have each (j : Nat) := entry_map h hk ((key.drop 1536).take 32 ++ [a.const i, a.const j])
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_take, List.map_drop, ha.const] at each
  simp only [matrixStage, List.map_cons, List.map_nil, List.map_flatMap, encode_map h, maskByte_map h,
    andLoop_map h, h.one, List.map_map, Function.comp_def, (each _).1, (each _).2, List.flatMap_map]
include h ha hk in
theorem uStage_map (i : Nat) (row rhat coins : List B) :
    (uStage o a k i row rhat coins).map fb = uStage o' a' k' i (row.map fb) (rhat.map fb) (coins.map fb) := by
  simp only [uStage, encode_map h, List.map_map, Function.comp_def, h.compress]
  simp only [← Function.comp_def, ← List.map_map]
  simp only [add_map h, inverse_map h, dot_map h, polyAt_map h, noise_map h ha hk]
include h ha hk in
theorem vStage_map (key rhat coins message : List B) :
    (vStage o a k key rhat coins message).map fb =
      vStage o' a' k' (key.map fb) (rhat.map fb) (coins.map fb) (message.map fb) := by
  simp only [vStage, encode_map h, List.map_map, Function.comp_def, h.compress]
  simp only [← Function.comp_def, ← List.map_map]
  simp only [add_map h, inverse_map h, dot_map h, polyAt_map h, noise_map h ha hk, messagePoly_map h]
end

theorem statusLoop_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {fb : B → B'} (ha : ByteAuth.Hom a a' fb)
    (checks : List B) (acc : B) :
    fb (checks.foldl a.and acc) = (checks.map fb).foldl a'.and (fb acc) := by
  induction checks generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, ha.and]

theorem finishStage_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {k : Keccak.Ops B K} {k' : Keccak.Ops B' K'}
    {fb : B → B'} {gk : K → K'} (ha : ByteAuth.Hom a a' fb) (hk : Keccak.Hom k k' fb gk)
    (kyber : Bool) (ciphertext kbar checks : List B) :
    (finishStage a k kyber ciphertext kbar checks).map (List.map fb) =
      finishStage a' k' kyber (ciphertext.map fb) (kbar.map fb) (checks.map fb) := by
  cases kyber <;>
    simp only [finishStage, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, ByteAuth.release_map ha,
      ByteAuth.eqMask_map ha, statusLoop_map ha, ha.const, Keccak.shake256, Keccak.sha3_256, Keccak.hash_map hk, List.map_append]

end TlsMpc.Signal.MlKemFast
