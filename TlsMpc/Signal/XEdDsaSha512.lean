import TlsMpc.ByteCircuit

/-! Executable SHA-512 for the shared XEdDSA challenge hash. FIPS180-4
64-bit words, 80 rounds, 128-byte blocks, 128-bit encoded length. All lengths
are public, values shared. Compiler equality is proved; actual RustCrypto
Aeneas refinement and cryptographic security are not claimed. Byte lengths
must be below 2^125; the standalone exporter uses a smaller public bound. -/

namespace TlsMpc.Signal.XEdDsaSha512

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
  pack : B → B → B → B → B → B → B → B → W
  unpack : W → Nat → B

def concrete : Ops (BitVec 8) (BitVec 64) where
  byteConst := BitVec.ofNat 8
  wordConst := BitVec.ofNat 64
  byteXor := (· ^^^ ·)
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := (~~~ ·)
  add := (· + ·)
  rotr := BitVec.rotateRight
  shr := (· >>> ·)
  pack a b c d e f g h := ((a ++ b) ++ (c ++ d)) ++ ((e ++ f) ++ (g ++ h))
  unpack word i := word.extractLsb' (8 * (7 - i)) 8

def symbolic : Ops (BVExpr 8) (BVExpr 64) where
  byteConst n := .const (BitVec.ofNat 8 n)
  wordConst n := .const (BitVec.ofNat 64 n)
  byteXor a b := BvConstruct.bin a .xor b
  xor a b := BvConstruct.bin a .xor b
  and a b := BvConstruct.bin a .and b
  not a := BvConstruct.un .not a
  add a b := BvConstruct.bin a .add b
  rotr a n := BvConstruct.un (.rotateRight n) a
  shr a n := BvConstruct.extract n 64 a
  pack a b c d e f g h := BvConstruct.append (BvConstruct.append (BvConstruct.append a b) (BvConstruct.append c d)) (BvConstruct.append (BvConstruct.append e f) (BvConstruct.append g h))
  unpack word i := BvConstruct.extract (8 * (7 - i)) 8 word

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
  pack : ∀ x y z t u v w q, fw (a.pack x y z t u v w q) = b.pack (fb x) (fb y) (fb z) (fb t) (fb u) (fb v) (fb w) (fb q)
  unpack : ∀ x n, fb (a.unpack x n) = b.unpack (fw x) n

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
  ⟨o.wordConst 0x6a09e667f3bcc908, o.wordConst 0xbb67ae8584caa73b, o.wordConst 0x3c6ef372fe94f82b, o.wordConst 0xa54ff53a5f1d36f1, o.wordConst 0x510e527fade682d1, o.wordConst 0x9b05688c2b3e6c1f, o.wordConst 0x1f83d9abfb41bd6b, o.wordConst 0x5be0cd19137e2179⟩

def constants : List Nat := [
0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

def xor3 (o : Ops B W) (x y z : W) : W := o.xor (o.xor x y) z
def big0 (o : Ops B W) (x : W) : W := xor3 o (o.rotr x 28) (o.rotr x 34) (o.rotr x 39)
def big1 (o : Ops B W) (x : W) : W := xor3 o (o.rotr x 14) (o.rotr x 18) (o.rotr x 41)
def small0 (o : Ops B W) (x : W) : W := xor3 o (o.rotr x 1) (o.rotr x 8) (o.shr x 7)
def small1 (o : Ops B W) (x : W) : W := xor3 o (o.rotr x 19) (o.rotr x 61) (o.shr x 6)
def choose (o : Ops B W) (x y z : W) : W := o.xor (o.and x y) (o.and (o.not x) z)
def majority (o : Ops B W) (x y z : W) : W := xor3 o (o.and x y) (o.and x z) (o.and y z)

def scheduleStep (o : Ops B W) (ws : List W) : List W :=
  let backWord := fun back => ws[ws.length - back]?.getD (o.wordConst 0)
  ws ++ [o.add (o.add (o.add (small1 o (backWord 2)) (backWord 7)) (small0 o (backWord 15))) (backWord 16)]

def extendSchedule (o : Ops B W) : Nat → List W → List W
  | 0, ws => ws
  | n + 1, ws => extendSchedule o n (scheduleStep o ws)

def round (o : Ops B W) (k : Nat) (w : W) (s : State W) : State W :=
  let t1 := o.add (o.add (o.add (o.add s.h (big1 o s.e))
    (choose o s.e s.f s.g)) (o.wordConst k)) w
  let t2 := o.add (big0 o s.a) (majority o s.a s.b s.c)
  ⟨o.add t1 t2, s.a, s.b, s.c, o.add s.d t1, s.e, s.f, s.g⟩

def rounds (o : Ops B W) : List Nat → List W → State W → State W
  | k :: ks, w :: ws, s => rounds o ks ws (round o k w s)
  | _, _, s => s

def feedForward (o : Ops B W) (s t : State W) : State W :=
  ⟨o.add s.a t.a, o.add s.b t.b, o.add s.c t.c, o.add s.d t.d,
   o.add s.e t.e, o.add s.f t.f, o.add s.g t.g, o.add s.h t.h⟩

/-- `block` contains exactly 16 words in normal SHA-512 use. -/
def compress (o : Ops B W) (s : State W) (block : List W) : State W :=
  feedForward o s (rounds o constants (extendSchedule o 64 block) s)

def padding (o : Ops B W) (length : Nat) : List B :=
  [o.byteConst 128] ++ List.replicate ((128 - (length + 17) % 128) % 128) (o.byteConst 0) ++
    (List.range 16).map (fun i => o.byteConst (length * 8 / 2 ^ (8 * (15 - i))))

def packWords (o : Ops B W) : List B → List W
  | a :: b :: c :: d :: e :: f :: g :: h :: rest => o.pack a b c d e f g h :: packWords o rest
  | _ => []

def processBlocks (o : Ops B W) : Nat → List W → State W → State W
  | 0, _, s => s
  | n + 1, ws, s => processBlocks o n (ws.drop 16) (compress o s (ws.take 16))

def digest (o : Ops B W) (s : State W) : List B :=
  s.words.flatMap (fun w => (List.range 8).map (o.unpack w))

def hash (o : Ops B W) (message : List B) : List B :=
  let words := packWords o (message ++ padding o message.length)
  digest o (processBlocks o (words.length / 16) words (initial o))

theorem digest_length (o : Ops B W) (s : State W) : (digest o s).length = 64 := by
  simp [digest, State.words]

theorem hash_length (o : Ops B W) (message : List B) : (hash o message).length = 64 := by
  exact digest_length o _

theorem padded_length (o : Ops B W) (message : List B) :
    (message ++ padding o message.length).length % 128 = 0 := by
  simp [padding]
  omega

theorem extended_length (o : Ops B W) (n : Nat) (words : List W) :
    (extendSchedule o n words).length = words.length + n := by
  induction n generalizing words with
  | zero => simp [extendSchedule]
  | succ n ih => simp [extendSchedule, ih, scheduleStep]; omega

theorem packed_length (o : Ops B W) (bytes : List B) :
    (packWords o bytes).length = bytes.length / 8 := by
  induction bytes using packWords.induct with
  | case1 x y z t u v w q rest ih => simp only [packWords, List.length_cons, ih]; omega
  | case2 bytes h1 =>
      match bytes with
      | [] | [_] | [_, _] | [_, _, _] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp [packWords]
      | x :: y :: z :: t :: u :: v :: w :: q :: rest => exact False.elim (h1 x y z t u v w q rest rfl)

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
    List.length_map, h.add, small0, small1, xor3, h.xor, h.rotr, h.shr, get]

theorem extendSchedule_map (n : Nat) (ws : List W) :
    (extendSchedule a n ws).map fw = extendSchedule b n (ws.map fw) := by
  induction n generalizing ws with
  | zero => rfl
  | succ n ih => simp only [extendSchedule, ih, scheduleStep_map h]

theorem round_map (k : Nat) (w : W) (s : State W) :
    (round a k w s).map fw = round b k (fw w) (s.map fw) := by
  simp [round, State.map, big0, big1, choose, majority, xor3,
    h.add, h.xor, h.and, h.not, h.rotr, h.wordConst]

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
  | case1 x y z t u v w q rest ih => simp only [packWords, List.map_cons, h.pack, ih]
  | case2 bytes h1 =>
      match bytes with
      | [] | [_] | [_, _] | [_, _, _] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => rfl
      | x :: y :: z :: t :: u :: v :: w :: q :: rest => exact False.elim (h1 x y z t u v w q rest rfl)

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

end Refinement

theorem compiled_hash_correct (message : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(hash symbolic message).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (hash symbolic message))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (hash symbolic message))).vec.get index hi)) =
      (ByteCircuit.joinValue (hash concrete (message.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,hash_map (evaluationHom assign)]
end TlsMpc.Signal.XEdDsaSha512
