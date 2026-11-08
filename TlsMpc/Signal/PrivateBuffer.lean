import TlsMpc.ByteAuth
import TlsMpc.Signal.OpenResult

/-! Total bounded private-length byte buffers. Interface encoding is
validity mask8 || lengthBE16 || capacity bytes. Internally length bits are
LSB-first 0/255 masks. Invalid inputs/overflow produce validity0,length0,data0;
valid empty is validity255,length0. Append preserves order across chunks and
never truncates a valid result. Validity must reach TLS's terminal error gate. -/
namespace TlsMpc.Signal.PrivateBuffer
open Std.Tactic.BVDecide
structure Buffer (B : Type) where
  valid : B
  lengthBits : List B
  data : List B

def Buffer.map (f : B → B') (b : Buffer B) : Buffer B' :=
  ⟨f b.valid,b.lengthBits.map f,b.data.map f⟩

def decodeLength (a : ByteAuth.Ops B) (bytes : List B) : List B :=
  (List.range 16).map (fun i => a.maskBit (OpenResult.get a bytes (1-i/8)) (i%8))

def publicLength (a : ByteAuth.Ops B) (n : Nat) : List B :=
  decodeLength a [a.const (n/256),a.const n]

def encodeByte (a : ByteAuth.Ops B) (bits : List B) (byte : Nat) : B :=
  (List.range 8).foldl (fun acc bit => a.xor acc
    (a.and (OpenResult.get a bits (8*(1-byte)+bit)) (a.const (2^bit)))) (a.const 0)

def encodeLength (a : ByteAuth.Ops B) (bits : List B) : List B :=
  [encodeByte a bits 0,encodeByte a bits 1]

def choose (a : ByteAuth.Ops B) (mask yes no : B) : B := a.xor no (a.and mask (a.xor yes no))

def addLoop (a : ByteAuth.Ops B) (left right : List B) : List Nat → B → List B × B
  | [],carry => ([],carry)
  | i::is,carry =>
    let x := OpenResult.get a left i
    let y := OpenResult.get a right i
    let either := a.xor x y
    let rest := addLoop a left right is (a.xor (a.and x y) (a.and either carry))
    (a.xor either carry :: rest.1,rest.2)

def borrowLoop (a : ByteAuth.Ops B) (left right : List B) : List Nat → B → B
  | [],borrow => borrow
  | i::is,borrow =>
    let x := OpenResult.get a left i
    let y := OpenResult.get a right i
    borrowLoop a left right is
      (a.xor (a.and (a.not x) y) (a.and (a.not (a.xor x y)) borrow))

def less (a : ByteAuth.Ops B) (left right : List B) : B :=
  borrowLoop a left right (List.range 16) (a.const 0)

def canonicalBits (a : ByteAuth.Ops B) (bits : List B) : B :=
  bits.foldl (fun acc bit => a.and acc
    (a.xor (ByteAuth.eqMask a bit (a.const 0)) (ByteAuth.eqMask a bit (a.const 255)))) (a.const 255)

def zero (a : ByteAuth.Ops B) (capacity : Nat) : Buffer B :=
  ⟨a.const 0,publicLength a 0,List.replicate capacity (a.const 0)⟩

def finish (a : ByteAuth.Ops B) (valid : B) (bits data : List B) : Buffer B :=
  ⟨valid,ByteAuth.release a valid bits,ByteAuth.release a valid data⟩

def make (a : ByteAuth.Ops B) (capacity : Nat) (bits raw : List B) : Buffer B :=
  if capacity < 65536 ∧ bits.length=16 ∧ raw.length=capacity then
    let valid := a.and (canonicalBits a bits) (a.not (less a (publicLength a capacity) bits))
    let data := (List.range capacity).map (fun i => a.and
      (less a (publicLength a i) bits) (OpenResult.get a raw i))
    finish a valid bits data
  else zero a capacity

def fromPrivate (a : ByteAuth.Ops B) (capacity : Nat) (lengthBE data : List B) : Buffer B :=
  if lengthBE.length=2 then make a capacity (decodeLength a lengthBE) data else zero a capacity

def fromPublic (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B) : Buffer B :=
  if raw.length≤capacity then
    make a capacity (publicLength a raw.length) (raw ++ List.replicate (capacity-raw.length) (a.const 0))
  else zero a capacity

def resize (a : ByteAuth.Ops B) (capacity : Nat) (input : Buffer B) : Buffer B :=
  let normalized := make a capacity input.lengthBits
    ((List.range capacity).map (OpenResult.get a input.data))
  finish a (a.and normalized.valid (ByteAuth.eqMask a input.valid (a.const 255)))
    normalized.lengthBits normalized.data

def shifted (a : ByteAuth.Ops B) (amount : Nat) (data : List B) : List B :=
  (List.range data.length).map (fun i => if i<amount then a.const 0 else OpenResult.get a data (i-amount))

def shiftLoop (a : ByteAuth.Ops B) (bits : List B) : List Nat → List B → List B
  | [],data => data
  | bit::rest,data =>
    let candidate := shifted a (2^bit) data
    let next := (List.range data.length).map (fun i => choose a (OpenResult.get a bits bit)
      (OpenResult.get a candidate i) (OpenResult.get a data i))
    shiftLoop a bits rest next

def append (a : ByteAuth.Ops B) (capacity : Nat) (left right : Buffer B) : Buffer B :=
  let l := resize a capacity left
  let r := resize a capacity right
  let sum := addLoop a l.lengthBits r.lengthBits (List.range 16) (a.const 0)
  let valid := a.and l.valid (a.and r.valid
    (a.and (a.not sum.2) (a.not (less a (publicLength a capacity) sum.1))))
  let moved := shiftLoop a l.lengthBits (List.range 16) r.data
  let data := (List.range capacity).map (fun i => a.xor (OpenResult.get a l.data i) (OpenResult.get a moved i))
  finish a valid sum.1 data

def output (a : ByteAuth.Ops B) (buffer : Buffer B) : List B :=
  buffer.valid :: (encodeLength a buffer.lengthBits ++ buffer.data)

def fromWire (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B) : Buffer B :=
  if raw.length=capacity+3 then
    let input := fromPrivate a capacity ((raw.drop 1).take 2) ((raw.drop 3).take capacity)
    finish a (a.and input.valid (ByteAuth.eqMask a (OpenResult.get a raw 0) (a.const 255))) input.lengthBits input.data
  else zero a capacity

def appendWire (a : ByteAuth.Ops B) (capacity : Nat) (left right : List B) : List B :=
  output a (append a capacity (fromWire a capacity left) (fromWire a capacity right))

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a a' f)
include h

theorem decodeLength_map (bytes : List B) : (decodeLength a bytes).map f = decodeLength a' (bytes.map f) := by
  simp [decodeLength,List.map_map,Function.comp_def,h.maskBit,OpenResult.get_map h]
theorem publicLength_map (n : Nat) : (publicLength a n).map f = publicLength a' n := by
  simp only [publicLength,decodeLength_map h,List.map_cons,List.map_nil,h.const]

theorem encodeLoop_map (is : List Nat) (bits : List B) (byte : Nat) (acc : B) :
    f (is.foldl (fun acc bit => a.xor acc (a.and (OpenResult.get a bits (8*(1-byte)+bit)) (a.const (2^bit)))) acc) =
    is.foldl (fun acc bit => a'.xor acc (a'.and (OpenResult.get a' (bits.map f) (8*(1-byte)+bit)) (a'.const (2^bit)))) (f acc) := by
  induction is generalizing acc with
  | nil => rfl
  | cons i is ih => simp only [List.foldl_cons,ih,h.xor,h.and,OpenResult.get_map h,h.const]
theorem encodeLength_map (bits : List B) : (encodeLength a bits).map f = encodeLength a' (bits.map f) := by
  simp only [encodeLength,List.map_cons,List.map_nil,encodeByte,encodeLoop_map h,h.const]
theorem choose_map (mask yes no : B) : f (choose a mask yes no) = choose a' (f mask) (f yes) (f no) := by
  simp only [choose,h.xor,h.and]
theorem addLoop_map (left right : List B) (is : List Nat) (carry : B) :
    ((addLoop a left right is carry).1.map f,f (addLoop a left right is carry).2) =
      addLoop a' (left.map f) (right.map f) is (f carry) := by
  induction is generalizing carry with
  | nil => rfl
  | cons i is ih =>
    simp only [addLoop]
    have mapped := ih (a.xor (a.and (OpenResult.get a left i) (OpenResult.get a right i))
      (a.and (a.xor (OpenResult.get a left i) (OpenResult.get a right i)) carry))
    simp only [h.xor,h.and,OpenResult.get_map h] at mapped
    simpa only [List.map_cons,h.xor,OpenResult.get_map h] using congrArg
      (fun p => (a'.xor (a'.xor (OpenResult.get a' (left.map f) i) (OpenResult.get a' (right.map f) i)) (f carry)::p.1,p.2)) mapped

theorem borrowLoop_map (left right : List B) (is : List Nat) (borrow : B) :
    f (borrowLoop a left right is borrow) = borrowLoop a' (left.map f) (right.map f) is (f borrow) := by
  induction is generalizing borrow with
  | nil => rfl
  | cons i is ih => simp only [borrowLoop,ih,h.xor,h.and,h.not,OpenResult.get_map h]
theorem less_map (left right : List B) : f (less a left right) = less a' (left.map f) (right.map f) := by
  simp only [less,borrowLoop_map h,h.const]
theorem canonicalLoop_map (bits : List B) (acc : B) :
    f (bits.foldl (fun acc bit => a.and acc (a.xor (ByteAuth.eqMask a bit (a.const 0)) (ByteAuth.eqMask a bit (a.const 255)))) acc) =
    (bits.map f).foldl (fun acc bit => a'.and acc (a'.xor (ByteAuth.eqMask a' bit (a'.const 0)) (ByteAuth.eqMask a' bit (a'.const 255)))) (f acc) := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => simp only [List.foldl_cons,List.map_cons,ih,h.and,h.xor,ByteAuth.eqMask_map h,h.const]
theorem canonicalBits_map (bits : List B) : f (canonicalBits a bits) = canonicalBits a' (bits.map f) := by
  simp only [canonicalBits,canonicalLoop_map h,h.const]
theorem zero_map (capacity : Nat) : (zero a capacity).map f = zero a' capacity := by
  simp only [zero,Buffer.map,h.const,publicLength_map h,List.map_replicate]
theorem finish_map (valid : B) (bits data : List B) :
    (finish a valid bits data).map f = finish a' (f valid) (bits.map f) (data.map f) := by
  simp only [finish,Buffer.map,ByteAuth.release_map h]
theorem make_map (capacity : Nat) (bits raw : List B) :
    (make a capacity bits raw).map f = make a' capacity (bits.map f) (raw.map f) := by
  simp only [make,List.length_map]
  split
  · simp only [finish_map h,h.and,canonicalBits_map h,h.not,less_map h,publicLength_map h,
      List.map_map,Function.comp_def,OpenResult.get_map h]
  · exact zero_map h capacity

theorem fromPrivate_map (capacity : Nat) (lengthBE data : List B) :
    (fromPrivate a capacity lengthBE data).map f = fromPrivate a' capacity (lengthBE.map f) (data.map f) := by
  simp only [fromPrivate,List.length_map]
  split <;> simp only [make_map h,decodeLength_map h,zero_map h]
theorem fromPublic_map (capacity : Nat) (raw : List B) :
    (fromPublic a capacity raw).map f = fromPublic a' capacity (raw.map f) := by
  simp only [fromPublic,List.length_map]
  split <;> simp only [make_map h,publicLength_map h,List.map_append,List.map_replicate,h.const,zero_map h]
theorem resize_map (capacity : Nat) (input : Buffer B) :
    (resize a capacity input).map f = resize a' capacity (input.map f) := by
  have norm := make_map h capacity input.lengthBits ((List.range capacity).map (OpenResult.get a input.data))
  simp only [List.map_map,Function.comp_def,OpenResult.get_map h] at norm
  have nv := congrArg Buffer.valid norm
  have nl := congrArg Buffer.lengthBits norm
  have nd := congrArg Buffer.data norm
  simp only [Buffer.map] at nv nl nd
  simp only [resize]
  rw [finish_map h]
  simp only [h.and,ByteAuth.eqMask_map h,h.const]
  rw [nv,nl,nd]
  rfl

theorem shifted_map (amount : Nat) (data : List B) :
    (shifted a amount data).map f = shifted a' amount (data.map f) := by
  simp only [shifted,List.length_map,List.map_map,Function.comp_def]
  congr 1;funext i;split <;> simp_all only [h.const,OpenResult.get_map h]
theorem shiftLoop_map (bits : List B) (is : List Nat) (data : List B) :
    (shiftLoop a bits is data).map f = shiftLoop a' (bits.map f) is (data.map f) := by
  induction is generalizing data with
  | nil => rfl
  | cons i is ih =>
    simp only [shiftLoop,ih,List.length_map,List.map_map,Function.comp_def,choose_map h,OpenResult.get_map h]
    rw [shifted_map h]

theorem append_map (capacity : Nat) (left right : Buffer B) :
    (append a capacity left right).map f = append a' capacity (left.map f) (right.map f) := by
  have ad := addLoop_map h (resize a capacity left).lengthBits (resize a capacity right).lengthBits (List.range 16) (a.const 0)
  simp only [h.const] at ad
  have leftEq := resize_map h capacity left
  have rightEq := resize_map h capacity right
  have lens : ((resize a capacity left).lengthBits.map f) = (resize a' capacity (left.map f)).lengthBits := congrArg Buffer.lengthBits leftEq
  have rens : ((resize a capacity right).lengthBits.map f) = (resize a' capacity (right.map f)).lengthBits := congrArg Buffer.lengthBits rightEq
  rw [lens,rens] at ad
  have sumBits := congrArg Prod.fst ad
  have sumCarry := congrArg Prod.snd ad
  simp only [Prod.fst,Prod.snd] at sumBits sumCarry
  simp only [append,finish_map h,h.and,h.xor,h.not,less_map h,publicLength_map h,sumBits,sumCarry,
    List.map_map,Function.comp_def,OpenResult.get_map h]
  have lv := congrArg Buffer.valid leftEq
  have rv := congrArg Buffer.valid rightEq
  simp only [Buffer.map] at lv rv
  rw [lv,rv]
  rw [shiftLoop_map h,lens]
  rw [show (resize a capacity right).data.map f = (resize a' capacity (right.map f)).data from congrArg Buffer.data rightEq]
  rw [show (resize a capacity left).data.map f = (resize a' capacity (left.map f)).data from congrArg Buffer.data leftEq]
  rfl

theorem output_map (input : Buffer B) : (output a input).map f = output a' (input.map f) := by
  simp only [output,Buffer.map,List.map_cons,List.map_append,encodeLength_map h]
theorem fromWire_map (capacity : Nat) (raw : List B) :
    (fromWire a capacity raw).map f = fromWire a' capacity (raw.map f) := by
  simp only [fromWire,List.length_map]
  split
  · rw [finish_map h]
    have inner := fromPrivate_map h capacity ((raw.drop 1).take 2) ((raw.drop 3).take capacity)
    simp only [List.map_take,List.map_drop] at inner
    have iv := congrArg Buffer.valid inner
    have il := congrArg Buffer.lengthBits inner
    have id := congrArg Buffer.data inner
    simp only [Buffer.map] at iv il id
    simp only [h.and,ByteAuth.eqMask_map h,OpenResult.get_map h,h.const]
    rw [iv,il,id]
  · exact zero_map h capacity

theorem appendWire_map (capacity : Nat) (left right : List B) :
    (appendWire a capacity left right).map f = appendWire a' capacity (left.map f) (right.map f) := by
  simp only [appendWire,output_map h,append_map h,fromWire_map h]

end Refinement
theorem public_length_value (n : Nat) (hn : n<65536) :
    ((BitVec.ofNat 8 (n/256)) ++ BitVec.ofNat 8 n).toNat = n := by
  have hq : n/256<256 := by omega
  simp only [BitVec.toNat_append,BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt hq]
  rw [←Nat.shiftLeft_add_eq_or_of_lt (i:=8) (by omega) (n/256),Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  omega

theorem compiled_append_correct (capacity : Nat) (left right : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(appendWire ByteAuth.symbolic capacity left right).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (appendWire ByteAuth.symbolic capacity left right))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (appendWire ByteAuth.symbolic capacity left right))).vec.get index hi)) =
    (ByteCircuit.joinValue (appendWire ByteAuth.concrete capacity
      (left.map (BVExpr.eval assign)) (right.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,appendWire_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateBuffer
