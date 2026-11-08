import TlsMpc.Signal.Varint64

/-! Private encodings for the relay's actual WebSocket JSON PUT path. No sealed
sender encryption is supplied here: ciphertext inputs must come from that
separate cryptographic envelope producer, never from bare SignalMessage wire. -/
namespace TlsMpc.Signal.RelayEncoding
open Std.Tactic.BVDecide

def literal (a : ByteAuth.Ops B) (s : String) : List B :=
  s.toUTF8.data.toList.map (fun b => a.const b.toNat)

def slice (a : ByteAuth.Ops B) (x : B) (start len shift : Nat) : B :=
  (List.range len).foldl (fun acc j => a.xor acc
    (a.and (a.maskBit x (start+j)) (a.const (2^(j+shift))))) (a.const 0)

def table (a : ByteAuth.Ops B) (alphabet : String) (x : B) : B :=
  (alphabet.toUTF8.data.toList.zipIdx).foldl (fun acc (b,i) =>
    a.xor acc (a.and (ByteAuth.eqMask a x (a.const i)) (a.const b.toNat))) (a.const 0)

def base64 (a : ByteAuth.Ops B) (raw : List B) : List B :=
  let encode := table a "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
  (List.range ((raw.length+2)/3)).flatMap fun i =>
    let x := OpenResult.get a raw (3*i)
    let y := OpenResult.get a raw (3*i+1)
    let z := OpenResult.get a raw (3*i+2)
    [encode (slice a x 2 6 0),
     encode (a.xor (slice a x 0 2 4) (slice a y 4 4 0)),
     if 3*i+1 < raw.length then encode (a.xor (slice a y 0 4 2) (slice a z 6 2 0)) else a.const 61,
     if 3*i+2 < raw.length then encode (slice a z 0 6 0) else a.const 61]

def uuid (a : ByteAuth.Ops B) (raw : List B) : List B :=
  (List.range 16).flatMap fun i =>
    (if i=4 ∨ i=6 ∨ i=8 ∨ i=10 then [a.const 45] else []) ++
    [table a "0123456789abcdef" (slice a (OpenResult.get a raw i) 4 4 0),
     table a "0123456789abcdef" (slice a (OpenResult.get a raw i) 0 4 0)]

structure DecimalOps (B W : Type) where
  digit : W → Nat → B
  quotientByte : W → Nat → Nat → B

def decimalConcrete : DecimalOps (BitVec 8) (BitVec 64) where
  digit w i := ((w / BitVec.ofNat 64 (10^i)) % 10).extractLsb' 0 8 + 48
  quotientByte w power i := (w / BitVec.ofNat 64 (10^power)).extractLsb' (8*i) 8

def decimalSymbolic : DecimalOps (BVExpr 8) (BVExpr 64) where
  digit w i := BvConstruct.bin (BvConstruct.extract 0 8
    (BvConstruct.bin (BvConstruct.bin w .udiv (.const (BitVec.ofNat 64 (10^i)))) .umod (.const 10))) .add (.const 48)
  quotientByte w power i := BvConstruct.extract (8*i) 8 (BvConstruct.bin w .udiv (.const (BitVec.ofNat 64 (10^power))))

structure DecimalHom (o : DecimalOps B W) (o' : DecimalOps B' W') (f : B → B') (fw : W → W') : Prop where
  digit : ∀ w i, f (o.digit w i) = o'.digit (fw w) i
  quotientByte : ∀ w p i, f (o.quotientByte w p i) = o'.quotientByte (fw w) p i

def decimalEvaluationHom (assign : BVExpr.Assignment) :
    DecimalHom decimalSymbolic decimalConcrete (BVExpr.eval assign) (BVExpr.eval assign) := by
  constructor <;> intros <;> simp [decimalSymbolic,decimalConcrete]

def decimal (d : DecimalOps B W) (word : W) (width : Nat) : List B :=
  (List.range width).reverse.map (d.digit word)

def decimalMask (d : DecimalOps B W) (a : ByteAuth.Ops B) (word : W) (width : Nat) : B :=
  a.and (if width=20 then a.const 255 else ByteAuth.equalMask a
      ((List.range 8).map (d.quotientByte word width)) (List.replicate 8 (a.const 0)))
    (if width=1 then a.const 255 else a.not (ByteAuth.eqMask a (d.digit word (width-1)) (a.const 48)))

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha

theorem literal_map (s : String) : (literal a s).map f = literal a' s := by
  simp [literal,List.map_map,ha.const]

theorem slice_loop_map (js : List Nat) (x acc : B) (start shift : Nat) :
    f (js.foldl (fun acc j => a.xor acc (a.and (a.maskBit x (start+j)) (a.const (2^(j+shift))))) acc) =
      js.foldl (fun acc j => a'.xor acc (a'.and (a'.maskBit (f x) (start+j)) (a'.const (2^(j+shift))))) (f acc) := by
  induction js generalizing acc with
  | nil => rfl
  | cons j js ih => simp only [List.foldl_cons,ih,ha.xor,ha.and,ha.maskBit,ha.const]

theorem slice_map (x : B) (start len shift : Nat) :
    f (slice a x start len shift) = slice a' (f x) start len shift := by
  simp only [slice,slice_loop_map ha,ha.const]

theorem table_loop_map (entries : List (UInt8 × Nat)) (x acc : B) :
    f (entries.foldl (fun acc (b,i) => a.xor acc (a.and (ByteAuth.eqMask a x (a.const i)) (a.const b.toNat))) acc) =
    entries.foldl (fun acc (b,i) => a'.xor acc (a'.and (ByteAuth.eqMask a' (f x) (a'.const i)) (a'.const b.toNat))) (f acc) := by
  induction entries generalizing acc with
  | nil => rfl
  | cons pair entries ih => cases pair; simp only [List.foldl_cons,ih,ha.xor,ha.and,ByteAuth.eqMask_map ha,ha.const]

theorem table_map (alphabet : String) (x : B) : f (table a alphabet x) = table a' alphabet (f x) := by
  simp only [table,table_loop_map ha,ha.const]

theorem base64_map (raw : List B) : (base64 a raw).map f = base64 a' (raw.map f) := by
  simp only [base64,List.map_flatMap,List.length_map,List.map_cons,List.map_nil,table_map ha,
    slice_map ha,OpenResult.get_map ha,ha.xor,ha.const]
  congr 1; funext i
  split <;> split <;> simp_all [table_map ha,slice_map ha,ha.xor,ha.const,OpenResult.get_map ha]

theorem uuid_map (raw : List B) : (uuid a raw).map f = uuid a' (raw.map f) := by
  simp only [uuid,List.map_flatMap,List.map_append,List.map_cons,List.map_nil,table_map ha,
    slice_map ha,OpenResult.get_map ha,ha.const]
  congr 1; funext i
  split <;> simp_all [ha.const]

variable {d : DecimalOps B W} {d' : DecimalOps B' W'} {fw : W → W'} (hd : DecimalHom d d' f fw)
include hd

omit ha in
theorem decimal_map (word : W) (width : Nat) :
    (decimal d word width).map f = decimal d' (fw word) width := by
  simp only [decimal,List.map_map,Function.comp_def,hd.digit]

theorem decimalMask_map (word : W) (width : Nat) :
    f (decimalMask d a word width) = decimalMask d' a' (fw word) width := by
  simp only [decimalMask,ha.and]
  split <;> split <;> simp_all [ha.const,ha.not,ByteAuth.eqMask_map ha,ByteAuth.equalMask_map ha,
    List.map_map,Function.comp_def,hd.quotientByte,hd.digit]
end Refinement
end TlsMpc.Signal.RelayEncoding
