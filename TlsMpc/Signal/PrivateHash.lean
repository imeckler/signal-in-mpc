import TlsMpc.Signal.PrivateBuffer
import TlsMpc.HmacPrepared

/-! Bounded private-length SHA256/HMAC. Public work is proportional to the
maximum block count, independent of the actual length. The byte model places
padding and selects the final digest obliviously. Its integer/SHA semantic
refinement is pending; compiler homomorphisms do not discharge that boundary. -/
namespace TlsMpc.Signal.PrivateHash
open Std.Tactic.BVDecide

def finalMask (a : ByteAuth.Ops B) (bits : List B) (blockIndex : Nat) : B :=
  a.and (PrivateBuffer.less a bits (PrivateBuffer.publicLength a (64*blockIndex+56)))
    (if blockIndex=0 then a.const 255 else
      a.not (PrivateBuffer.less a bits (PrivateBuffer.publicLength a (64*blockIndex-8))))

def lengthBytes (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (priorBytes : Nat) (bits : List B) : List B :=
  let be := PrivateBuffer.encodeLength a bits
  let n := s.add (s.pack (s.byteConst 0) (s.byteConst 0)
    (OpenResult.get a be 0) (OpenResult.get a be 1)) (s.wordConst priorBytes)
  let twice := s.add n n
  let four := s.add twice twice
  let eight := s.add four four
  List.replicate 4 (s.byteConst 0) ++ (List.range 4).map (s.unpack eight)

def paddedBlock (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (priorBytes blockIndex : Nat)
    (input : PrivateBuffer.Buffer B) : List B :=
  let final := finalMask a input.lengthBits blockIndex
  let size := lengthBytes s a priorBytes input.lengthBits
  (List.range 64).map (fun j =>
    let i := blockIndex*64+j
    let marker := a.and (ByteAuth.equalMask a input.lengthBits (PrivateBuffer.publicLength a i)) (a.const 128)
    let suffix := if 56≤j then a.and final (OpenResult.get a size (j-56)) else a.const 0
    a.xor (OpenResult.get a input.data i) (a.xor marker suffix))

def blocks (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (priorBytes : Nat)
    (input : PrivateBuffer.Buffer B) : Nat → Nat → Sha256.State W → List B
  | 0,_,_ => List.replicate 32 (a.const 0)
  | n+1,index,state =>
    let next := Sha256.compress s state (Sha256.packWords s (paddedBlock s a priorBytes index input))
    (ByteAuth.release a (finalMask a input.lengthBits index) (Sha256.digest s next)).zipWith a.xor
      (blocks s a priorBytes input n (index+1) next)

def hashAfter (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (priorBytes : Nat)
    (state : Sha256.State W) (capacity : Nat) (input : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let b := PrivateBuffer.resize a capacity input
  if capacity≤16384 then
    let bytes := blocks s a priorBytes b ((capacity+9+63)/64) 0 state
    PrivateBuffer.finish a b.valid (PrivateBuffer.publicLength a 32) bytes
  else PrivateBuffer.zero a 32

def hash (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (capacity : Nat)
    (input : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  hashAfter s a 0 (Sha256.initial s) capacity input

def hmac (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (key : List B) (capacity : Nat)
    (input : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let innerState := Sha256.compress s (Sha256.initial s) (Sha256.packWords s (HmacPrepared.padBlock s key 0x36))
  let inner := hashAfter s a 64 innerState capacity input
  let outer := Sha256.hash s (HmacPrepared.padBlock s key 0x5c ++ inner.data)
  PrivateBuffer.finish a inner.valid (PrivateBuffer.publicLength a 32) outer

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem finalMask_map (bits : List B) (index : Nat) :
    f (finalMask a bits index) = finalMask a' (bits.map f) index := by
  simp only [finalMask,ha.and,PrivateBuffer.less_map ha,PrivateBuffer.publicLength_map ha]
  split <;> simp_all only [ha.const,ha.not,PrivateBuffer.less_map ha,PrivateBuffer.publicLength_map ha]
include hs

theorem lengthBytes_map (prior : Nat) (bits : List B) :
    (lengthBytes s a prior bits).map f = lengthBytes s' a' prior (bits.map f) := by
  simp only [lengthBytes,List.map_append,List.map_replicate,hs.byteConst,List.map_map,Function.comp_def,
    hs.unpack,hs.add,hs.pack,hs.wordConst,OpenResult.get_map ha,PrivateBuffer.encodeLength_map ha]

theorem paddedBlock_map (prior index : Nat) (input : PrivateBuffer.Buffer B) :
    (paddedBlock s a prior index input).map f = paddedBlock s' a' prior index (input.map f) := by
  simp only [paddedBlock,List.map_map,Function.comp_def,PrivateBuffer.Buffer.map,ha.xor,ha.and,
    finalMask_map ha,ByteAuth.equalMask_map ha,PrivateBuffer.publicLength_map ha,ha.const,
    OpenResult.get_map ha,lengthBytes_map hs ha]
  congr 1;funext j
  split <;> simp_all only [ha.and,ha.const,OpenResult.get_map ha,lengthBytes_map hs ha,finalMask_map ha]

theorem blocks_map (prior : Nat) (input : PrivateBuffer.Buffer B) (n index : Nat) (state : Sha256.State W) :
    (blocks s a prior input n index state).map f =
      blocks s' a' prior (input.map f) n index (state.map fw) := by
  induction n generalizing index state with
  | zero => simp only [blocks,List.map_replicate,ha.const]
  | succ n ih =>
    simp only [blocks]
    have next := Sha256.compress_map hs state (Sha256.packWords s (paddedBlock s a prior index input))
    rw [Sha256.packWords_map hs,paddedBlock_map hs ha] at next
    have lm := ByteAuth.release_map ha (finalMask a input.lengthBits index)
      (Sha256.digest s (Sha256.compress s state (Sha256.packWords s (paddedBlock s a prior index input))))
    rw [finalMask_map ha,Sha256.digest_map hs,next] at lm
    have rm := ih (index+1) (Sha256.compress s state (Sha256.packWords s (paddedBlock s a prior index input)))
    rw [next] at rm
    simp only [PrivateBuffer.Buffer.map] at lm rm ⊢
    rw [←lm,←rm,List.zipWith_map,List.map_zipWith]
    simp only [ha.xor]

theorem hashAfter_map (prior capacity : Nat) (state : Sha256.State W) (input : PrivateBuffer.Buffer B) :
    (hashAfter s a prior state capacity input).map f =
      hashAfter s' a' prior (state.map fw) capacity (input.map f) := by
  simp only [hashAfter]
  split
  · rw [PrivateBuffer.finish_map ha]
    rw [blocks_map hs ha,PrivateBuffer.resize_map ha,PrivateBuffer.publicLength_map ha]
    have hv := congrArg PrivateBuffer.Buffer.valid (PrivateBuffer.resize_map ha capacity input)
    change f (PrivateBuffer.resize a capacity input).valid = _ at hv
    rw [hv]
  · exact PrivateBuffer.zero_map ha 32

theorem hash_map (capacity : Nat) (input : PrivateBuffer.Buffer B) :
    (hash s a capacity input).map f = hash s' a' capacity (input.map f) := by
  simp only [hash,hashAfter_map hs ha,Sha256.initial_map hs]

omit ha in
theorem padBlock_map (key : List B) (pad : Nat) :
    (HmacPrepared.padBlock s key pad).map f = HmacPrepared.padBlock s' (key.map f) pad := by
  have kb : (HmacPrepared.keyBlock s key).map f = HmacPrepared.keyBlock s' (key.map f) := by
    simp only [HmacPrepared.keyBlock,List.length_map]
    split <;> simp only [List.map_append,List.map_replicate,hs.byteConst,Sha256.hash_map hs,List.length_map,Sha256.hash_length]
  simp only [HmacPrepared.padBlock,List.map_map,Function.comp_def,hs.byteXor,hs.byteConst]
  rw [←kb,List.map_map]
  rfl

theorem hmac_map (key : List B) (capacity : Nat) (input : PrivateBuffer.Buffer B) :
    (hmac s a key capacity input).map f = hmac s' a' (key.map f) capacity (input.map f) := by
  have innerState := Sha256.compress_map hs (Sha256.initial s)
    (Sha256.packWords s (HmacPrepared.padBlock s key 0x36))
  rw [Sha256.initial_map hs,Sha256.packWords_map hs,padBlock_map hs] at innerState
  have inner := hashAfter_map hs ha 64 capacity
    (Sha256.compress s (Sha256.initial s) (Sha256.packWords s (HmacPrepared.padBlock s key 0x36))) input
  rw [innerState] at inner
  simp only [hmac,PrivateBuffer.finish_map ha,PrivateBuffer.publicLength_map ha,Sha256.hash_map hs,
    List.map_append,padBlock_map hs]
  have vi := congrArg PrivateBuffer.Buffer.valid inner
  have di := congrArg PrivateBuffer.Buffer.data inner
  change f _ = _ at vi
  change List.map f _ = _ at di
  rw [vi,di]

end Refinement
theorem compiled_hmac_correct (key raw : List (BVExpr 8)) (capacity : Nat)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(PrivateBuffer.output ByteAuth.symbolic (hmac Sha256.symbolic ByteAuth.symbolic key capacity
      (PrivateBuffer.fromWire ByteAuth.symbolic capacity raw))).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (PrivateBuffer.output ByteAuth.symbolic (hmac Sha256.symbolic ByteAuth.symbolic key capacity
        (PrivateBuffer.fromWire ByteAuth.symbolic capacity raw))))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (PrivateBuffer.output ByteAuth.symbolic (hmac Sha256.symbolic ByteAuth.symbolic key capacity
          (PrivateBuffer.fromWire ByteAuth.symbolic capacity raw))))).vec.get index hi)) =
    (ByteCircuit.joinValue (PrivateBuffer.output ByteAuth.concrete
      (hmac Sha256.concrete ByteAuth.concrete (key.map (BVExpr.eval assign)) capacity
        (PrivateBuffer.fromWire ByteAuth.concrete capacity (raw.map (BVExpr.eval assign)))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,PrivateBuffer.output_map (ByteAuth.evaluationHom assign),
    hmac_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign),
    PrivateBuffer.fromWire_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateHash
