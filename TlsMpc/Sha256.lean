import TlsMpc.BvConstruct

/-!
Executable SHA-256/HMAC specification, following FIPS 180-4 §§4.1.2, 4.2.2,
5.1.1, 5.2.1, 5.3.3, 6.2 and RFC 2104 §2.

The same algorithm is instantiated with ordinary BitVec values and with symbolic
bit-vector expressions. `Hom` expresses preservation of every primitive; the
refinement proofs below lift this relation through the complete hash and HMAC.
All lengths and loops are public. This module has no I/O or reveal operation.
Byte interfaces require messages shorter than 2^61 bytes (the SHA-256 bound);
the command-line exporter imposes a much smaller resource limit.
-/

namespace TlsMpc.Sha256

open Std.Tactic.BVDecide

structure Ops (B W : Type) where
  byteConst : Nat → B
  wordConst : Nat → W
  byteXor : B → B → B
  xor : W → W → W
  and : W → W → W
  not : W → W
  add : W → W → W
  rotr : W → Nat → W
  shr : W → Nat → W
  pack : B → B → B → B → W
  unpack : W → Nat → B
  -- Default fields preserve the original expression tree exactly. Explicit
  -- backend profiles may replace them with proved equivalent nary circuits.
  sum4 : W → W → W → W → W := fun a b c d => add (add (add a b) c) d
  sum5 : W → W → W → W → W → W := fun a b c d e => add (add (add (add a b) c) d) e

def concrete : Ops (BitVec 8) (BitVec 32) where
  byteConst := BitVec.ofNat 8
  wordConst := BitVec.ofNat 32
  byteXor := (· ^^^ ·)
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := (~~~ ·)
  add := (· + ·)
  rotr := BitVec.rotateRight
  shr := (· >>> ·)
  pack a b c d := (a ++ b) ++ (c ++ d)
  unpack word i := word.extractLsb' (8 * (3 - i)) 8

def symbolic : Ops (BVExpr 8) (BVExpr 32) where
  byteConst n := .const (BitVec.ofNat 8 n)
  wordConst n := .const (BitVec.ofNat 32 n)
  byteXor a b := BvConstruct.bin a .xor b
  xor a b := BvConstruct.bin a .xor b
  and a b := BvConstruct.bin a .and b
  not a := BvConstruct.un .not a
  add a b := BvConstruct.bin a .add b
  rotr a n := BvConstruct.un (.rotateRight n) a
  shr a n := BvConstruct.extract n 32 a
  pack a b c d := BvConstruct.append (BvConstruct.append a b) (BvConstruct.append c d)
  unpack word i := BvConstruct.extract (8 * (3 - i)) 8 word

structure Hom (a : Ops B W) (b : Ops B' W') (fb : B → B') (fw : W → W') : Prop where
  byteConst : ∀ n, fb (a.byteConst n) = b.byteConst n
  wordConst : ∀ n, fw (a.wordConst n) = b.wordConst n
  byteXor : ∀ x y, fb (a.byteXor x y) = b.byteXor (fb x) (fb y)
  xor : ∀ x y, fw (a.xor x y) = b.xor (fw x) (fw y)
  and : ∀ x y, fw (a.and x y) = b.and (fw x) (fw y)
  not : ∀ x, fw (a.not x) = b.not (fw x)
  add : ∀ x y, fw (a.add x y) = b.add (fw x) (fw y)
  rotr : ∀ x n, fw (a.rotr x n) = b.rotr (fw x) n
  shr : ∀ x n, fw (a.shr x n) = b.shr (fw x) n
  pack : ∀ x y z t, fw (a.pack x y z t) = b.pack (fb x) (fb y) (fb z) (fb t)
  unpack : ∀ x n, fb (a.unpack x n) = b.unpack (fw x) n
  sum4 : ∀ x y z t, fw (a.sum4 x y z t)=b.sum4 (fw x) (fw y) (fw z) (fw t)
  sum5 : ∀ x y z t u, fw (a.sum5 x y z t u)=b.sum5 (fw x) (fw y) (fw z) (fw t) (fw u)

def evaluationHom (assign : BVExpr.Assignment) :
    Hom symbolic concrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  constructor <;> intros <;> first
    | rfl
    | simp [symbolic, concrete, ← BitVec.setWidth_ushiftRight_eq_extractLsb]

structure State (W : Type) where
  a : W
  b : W
  c : W
  d : W
  e : W
  f : W
  g : W
  h : W
  deriving Repr

def State.map (f : W → W') (s : State W) : State W' :=
  ⟨f s.a, f s.b, f s.c, f s.d, f s.e, f s.f, f s.g, f s.h⟩

def State.words (s : State W) : List W := [s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

def initial (o : Ops B W) : State W :=
  ⟨o.wordConst 0x6a09e667, o.wordConst 0xbb67ae85,
   o.wordConst 0x3c6ef372, o.wordConst 0xa54ff53a,
   o.wordConst 0x510e527f, o.wordConst 0x9b05688c,
   o.wordConst 0x1f83d9ab, o.wordConst 0x5be0cd19⟩

def constants : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def xor3 (o : Ops B W) (x y z : W) : W := o.xor (o.xor x y) z
def big0 (o : Ops B W) (x : W) : W := xor3 o (o.rotr x 2) (o.rotr x 13) (o.rotr x 22)
def big1 (o : Ops B W) (x : W) : W := xor3 o (o.rotr x 6) (o.rotr x 11) (o.rotr x 25)
def small0 (o : Ops B W) (x : W) : W := xor3 o (o.rotr x 7) (o.rotr x 18) (o.shr x 3)
def small1 (o : Ops B W) (x : W) : W := xor3 o (o.rotr x 17) (o.rotr x 19) (o.shr x 10)
def choose (o : Ops B W) (x y z : W) : W := o.xor (o.and x y) (o.and (o.not x) z)
def majority (o : Ops B W) (x y z : W) : W := xor3 o (o.and x y) (o.and x z) (o.and y z)

def scheduleStep (o : Ops B W) (ws : List W) : List W :=
  let backWord := fun back => ws[ws.length - back]?.getD (o.wordConst 0)
  ws ++ [o.sum4 (small1 o (backWord 2)) (backWord 7) (small0 o (backWord 15)) (backWord 16)]

def extendSchedule (o : Ops B W) : Nat → List W → List W
  | 0, ws => ws
  | n + 1, ws => extendSchedule o n (scheduleStep o ws)

def round (o : Ops B W) (k : Nat) (w : W) (s : State W) : State W :=
  let t1 := o.sum5 s.h (big1 o s.e) (choose o s.e s.f s.g) (o.wordConst k) w
  let t2 := o.add (big0 o s.a) (majority o s.a s.b s.c)
  ⟨o.add t1 t2, s.a, s.b, s.c, o.add s.d t1, s.e, s.f, s.g⟩

def rounds (o : Ops B W) : List Nat → List W → State W → State W
  | k :: ks, w :: ws, s => rounds o ks ws (round o k w s)
  | _, _, s => s

def feedForward (o : Ops B W) (s t : State W) : State W :=
  ⟨o.add s.a t.a, o.add s.b t.b, o.add s.c t.c, o.add s.d t.d,
   o.add s.e t.e, o.add s.f t.f, o.add s.g t.g, o.add s.h t.h⟩

/-- `block` contains exactly 16 words in normal SHA-256 use. -/
def compress (o : Ops B W) (s : State W) (block : List W) : State W :=
  feedForward o s (rounds o constants (extendSchedule o 48 block) s)

def padding (o : Ops B W) (length : Nat) : List B :=
  [o.byteConst 128] ++ List.replicate ((64 - (length + 9) % 64) % 64) (o.byteConst 0) ++
    (List.range 8).map (fun i => o.byteConst (length * 8 / 2 ^ (8 * (7 - i))))

def packWords (o : Ops B W) : List B → List W
  | a :: b :: c :: d :: rest => o.pack a b c d :: packWords o rest
  | _ => []

def processBlocks (o : Ops B W) : Nat → List W → State W → State W
  | 0, _, s => s
  | n + 1, ws, s => processBlocks o n (ws.drop 16) (compress o s (ws.take 16))

def digest (o : Ops B W) (s : State W) : List B :=
  s.words.flatMap (fun w => (List.range 4).map (o.unpack w))

def hash (o : Ops B W) (message : List B) : List B :=
  let words := packWords o (message ++ padding o message.length)
  digest o (processBlocks o (words.length / 16) words (initial o))

def hmacCore (o : Ops B W) (key message : List B) : List B :=
  let key := key ++ List.replicate (64 - key.length) (o.byteConst 0)
  let inner := key.map (fun b => o.byteXor b (o.byteConst 0x36))
  let outer := key.map (fun b => o.byteXor b (o.byteConst 0x5c))
  hash o (outer ++ hash o (inner ++ message))

def hmac (o : Ops B W) (key message : List B) : List B :=
  hmacCore o (if key.length > 64 then hash o key else key) message

theorem digest_length (o : Ops B W) (s : State W) : (digest o s).length = 32 := by
  simp [digest, State.words]

theorem hash_length (o : Ops B W) (message : List B) : (hash o message).length = 32 := by
  exact digest_length o _

theorem hmac_length (o : Ops B W) (key message : List B) : (hmac o key message).length = 32 := by
  exact hash_length o _

theorem padded_length (o : Ops B W) (message : List B) :
    (message ++ padding o message.length).length % 64 = 0 := by
  simp [padding]
  omega

theorem extended_length (o : Ops B W) (n : Nat) (words : List W) :
    (extendSchedule o n words).length = words.length + n := by
  induction n generalizing words with
  | zero => simp [extendSchedule]
  | succ n ih => simp [extendSchedule, ih, scheduleStep]; omega

theorem packed_length (o : Ops B W) (bytes : List B) :
    (packWords o bytes).length = bytes.length / 4 := by
  induction bytes using packWords.induct with
  | case1 x y z t rest ih => simp only [packWords, List.length_cons, ih]; omega
  | case2 bytes h1 =>
      match bytes with
      | [] | [_] | [_, _] | [_, _, _] => simp [packWords]
      | x :: y :: z :: t :: rest => exact False.elim (h1 x y z t rest rfl)

theorem hmac_block_key_length (o : Ops B W) (key : List B) :
    let normalized := if key.length > 64 then hash o key else key
    (normalized ++ List.replicate (64 - normalized.length) (o.byteConst 0)).length = 64 := by
  split <;> simp [hash_length] <;> omega

section Refinement

variable {a : Ops B W} {b : Ops B' W'} {fb : B → B'} {fw : W → W'}
variable (h : Hom a b fb fw)
include h

theorem initial_map : (initial a).map fw = initial b := by
  simp [initial, State.map, h.wordConst]

theorem scheduleStep_map (ws : List W) :
    (scheduleStep a ws).map fw = scheduleStep b (ws.map fw) := by
  have get (i : Nat) : fw (ws[i]?.getD (a.wordConst 0)) =
      (ws.map fw)[i]?.getD (b.wordConst 0) := by
    simp only [List.getElem?_map]
    cases ws[i]? <;> simp [h.wordConst]
  simp only [scheduleStep, List.map_append, List.map_cons, List.map_nil,
    List.length_map, h.sum4, small0, small1, xor3, h.xor, h.rotr, h.shr, get]

theorem extendSchedule_map (n : Nat) (ws : List W) :
    (extendSchedule a n ws).map fw = extendSchedule b n (ws.map fw) := by
  induction n generalizing ws with
  | zero => rfl
  | succ n ih => simp only [extendSchedule, ih, scheduleStep_map h]

theorem round_map (k : Nat) (w : W) (s : State W) :
    (round a k w s).map fw = round b k (fw w) (s.map fw) := by
  simp [round, State.map, big0, big1, choose, majority, xor3,
    h.add, h.sum5, h.xor, h.and, h.not, h.rotr, h.wordConst]

theorem rounds_map (ks : List Nat) (ws : List W) (s : State W) :
    (rounds a ks ws s).map fw = rounds b ks (ws.map fw) (s.map fw) := by
  induction ks generalizing ws s with
  | nil => rfl
  | cons k ks ih =>
      cases ws with
      | nil => rfl
      | cons w ws => simp only [rounds, List.map_cons, ih, round_map h]

theorem compress_map (s : State W) (block : List W) :
    (compress a s block).map fw = compress b (s.map fw) (block.map fw) := by
  have feed (s t : State W) : (feedForward a s t).map fw =
      feedForward b (s.map fw) (t.map fw) := by simp [feedForward, State.map, h.add]
  simp only [compress, feed, rounds_map h, extendSchedule_map h]

theorem padding_map (length : Nat) : (padding a length).map fb = padding b length := by
  simp [padding, List.map_map, h.byteConst]

theorem packWords_map (bytes : List B) : (packWords a bytes).map fw = packWords b (bytes.map fb) := by
  induction bytes using packWords.induct with
  | case1 x y z t rest ih => simp only [packWords, List.map_cons, h.pack, ih]
  | case2 bytes h1 =>
      match bytes with
      | [] | [_] | [_, _] | [_, _, _] => rfl
      | x :: y :: z :: t :: rest => exact False.elim (h1 x y z t rest rfl)

theorem processBlocks_map (n : Nat) (ws : List W) (s : State W) :
    (processBlocks a n ws s).map fw = processBlocks b n (ws.map fw) (s.map fw) := by
  induction n generalizing ws s with
  | zero => rfl
  | succ n ih => simp only [processBlocks, ih, List.map_drop, List.map_take, compress_map h]

theorem digest_map (s : State W) : (digest a s).map fb = digest b (s.map fw) := by
  simp [digest, State.words, State.map, List.map_map, Function.comp_def, h.unpack]

theorem hash_map (message : List B) : (hash a message).map fb = hash b (message.map fb) := by
  have wp : packWords b (message.map fb ++ padding b message.length) =
      (packWords a (message ++ padding a message.length)).map fw := by
    rw [packWords_map h, List.map_append, padding_map h]
  simp only [hash, List.length_map, wp, ← digest_map h, ← initial_map h,
    ← processBlocks_map h, List.length_map]

theorem hmacCore_map (key message : List B) :
    (hmacCore a key message).map fb = hmacCore b (key.map fb) (message.map fb) := by
  simp [hmacCore, hash_map h, List.map_map, Function.comp_def, h.byteXor, h.byteConst]

theorem hmac_map (key message : List B) :
    (hmac a key message).map fb = hmac b (key.map fb) (message.map fb) := by
  simp only [hmac, hmacCore_map h, List.length_map]
  split <;> simp [hash_map h]

end Refinement

theorem hash_refines (message : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (hash symbolic message).map (BVExpr.eval assign) =
      hash concrete (message.map (BVExpr.eval assign)) := hash_map (evaluationHom assign) message

theorem hmac_refines (key message : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (hmac symbolic key message).map (BVExpr.eval assign) =
      hmac concrete (key.map (BVExpr.eval assign)) (message.map (BVExpr.eval assign)) :=
  hmac_map (evaluationHom assign) key message

end TlsMpc.Sha256
