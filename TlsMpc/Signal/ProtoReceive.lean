import TlsMpc.Signal.ProtoParseProofs
import TlsMpc.Signal.SliceAt

/-! Authenticated receive with secret protobuf layout. The exact original
serialized bytes are authenticated. Field offsets, length, duplicate choice,
addresses presence, padding and acceptance remain shared. Message keys must be
selected/derived inside MPC by the session layer. No public layout assertion
is accepted by this entry point. -/
namespace TlsMpc.Signal.ProtoReceive
open Std.Tactic.BVDecide

def capacity (wire : List B) : Nat := (ProtoParse.body wire).length / 16 * 16

def addressMask (o : Word64.Ops B V) (a : ByteAuth.Ops B) (wire expected : List B)
    (state : ProtoParse.State B V) : B :=
  let field := ProtoParse.getField o a state 5
  let read := ReadAt.readCore a 36 (ProtoParse.body wire) (Word64.bytes o field.offset)
  Word64.bor a (a.not field.present)
    (a.and (Word64.eq o a field.length (o.const 36))
      (a.and (OpenResult.get a read 0)
        (a.and (Receive.expectedAddressMask a expected) (ByteAuth.equalMask a (read.drop 9) expected))))

def authenticatedMask (o : Word64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (wire macKey sender receiver expected : List B) (state : ProtoParse.State B V) : B :=
  a.and (ProtoParse.acceptedMask o a wire state)
    (a.and (MessageMac.verifyMask s a macKey sender receiver wire) (addressMask o a wire expected state))

def finishAt (a : ByteAuth.Ops B) (width : Nat) (authenticated : B) (plaintext : List B) (blocks : Nat) : List B :=
  (OpenResult.finish a authenticated (plaintext.take (16 * blocks)) ++ List.replicate (9 + width) (a.const 0)).take (9 + width)

def chooseLength (o : Word64.Ops B V) (a : ByteAuth.Ops B) (width : Nat) (length : V)
    (authenticated : B) (plaintext : List B) : List B :=
  (List.range (width / 16)).foldl (fun acc i =>
    Unpad.choose a (Word64.eq o a length (o.const (16 * (i + 1))))
      (finishAt a width authenticated plaintext (i + 1)) acc)
    (List.replicate (9 + width) (a.const 0))

def openCore (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (cipherKey iv macKey sender receiver wire expected : List B) : List B :=
  let state := ProtoParse.parseBody d o a (ProtoParse.body wire)
  let field := ProtoParse.getField o a state 3
  let ciphertext := SliceAt.readCore o a (capacity wire) (ProtoParse.body wire) field.offset field.length
  let plaintext := CbcOpen.decryptCore aes cipherKey iv ciphertext
  chooseLength o a (capacity wire) field.length
    (authenticatedMask o s a wire macKey sender receiver expected state) plaintext

def openChecked (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (cipherKey iv macKey sender receiver wire expected : List B) : Option (List B) :=
  if cipherKey.length = 32 ∧ iv.length = 16 ∧ macKey.length = 32 ∧ sender.length = 32 ∧ receiver.length = 32 ∧
      expected.length = 36 ∧ wire.length ≤ 512 then
    some (openCore d o aes s a cipherKey iv macKey sender receiver wire expected)
  else none

section Refinement
variable {d : VarintDecode.Spqr.Ops B V} {d' : VarintDecode.Spqr.Ops B' V'}
  {o : Word64.Ops B V} {o' : Word64.Ops B' V'}
  {aes : AesInverse.Ops B} {aes' : AesInverse.Ops B'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fv : V → V'} {fw : W → W'}
  (hd : VarintDecode.Spqr.Hom d d' f fv) (ho : Word64.Hom o o' f fv)
  (he : AesInverse.Hom aes aes' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

theorem capacity_map (wire : List B) : capacity (wire.map f) = capacity wire := by
  simp [capacity, ProtoParse.body, MessageMac.content]

include ho ha in
theorem addressMask_map (wire expected : List B) (state : ProtoParse.State B V) :
    f (addressMask o a wire expected state) = addressMask o' a' (wire.map f) (expected.map f) (state.map f fv) := by
  have hp := congrArg ProtoParse.Field.present (ProtoParse.getField_map ho ha state 5)
  have hl := congrArg ProtoParse.Field.length (ProtoParse.getField_map ho ha state 5)
  have hf := congrArg ProtoParse.Field.offset (ProtoParse.getField_map ho ha state 5)
  simp only [ProtoParse.Field.map] at hp hl hf
  simp only [addressMask, Word64.bor_map ha, ha.not, hp, ha.and, Word64.eq_map ho ha, hl, ho.const,
    OpenResult.get_map ha, ReadAt.readCore_map ha, ProtoParse.body_map, Word64.bytes_map ho, hf,
    Receive.expectedAddressMask_map ha, ByteAuth.equalMask_map ha, List.map_drop]

include ho hs ha in
theorem authenticatedMask_map (wire macKey sender receiver expected : List B) (state : ProtoParse.State B V) :
    f (authenticatedMask o s a wire macKey sender receiver expected state) =
      authenticatedMask o' s' a' (wire.map f) (macKey.map f) (sender.map f) (receiver.map f) (expected.map f) (state.map f fv) := by
  simp only [authenticatedMask, ha.and, ProtoParse.acceptedMask_map ho ha,
    MessageMac.verifyMask_map hs ha, addressMask_map ho ha]

include ha in
theorem finishAt_map (width : Nat) (authenticated : B) (plaintext : List B) (blocks : Nat) :
    (finishAt a width authenticated plaintext blocks).map f = finishAt a' width (f authenticated) (plaintext.map f) blocks := by
  simp only [finishAt, List.map_take, List.map_append, List.map_replicate, ha.const, OpenResult.finish_map ha]

include ho ha in
theorem chooseLength_map (width : Nat) (length : V) (authenticated : B) (plaintext : List B) :
    (chooseLength o a width length authenticated plaintext).map f =
      chooseLength o' a' width (fv length) (f authenticated) (plaintext.map f) := by
  have hf (indices : List Nat) (acc : List B) :
      (indices.foldl (fun acc i => Unpad.choose a (Word64.eq o a length (o.const (16 * (i+1))))
        (finishAt a width authenticated plaintext (i+1)) acc) acc).map f =
      indices.foldl (fun acc i => Unpad.choose a' (Word64.eq o' a' (fv length) (o'.const (16 * (i+1))))
        (finishAt a' width (f authenticated) (plaintext.map f) (i+1)) acc) (acc.map f) := by
    induction indices generalizing acc with
    | nil => rfl
    | cons i rest ih => simp only [List.foldl_cons, ih, Unpad.choose_map ha, Word64.eq_map ho ha, ho.const, finishAt_map ha]
  simpa only [chooseLength, List.map_replicate, ha.const] using hf (List.range (width / 16)) (List.replicate (9+width) (a.const 0))

include hd ho he hs ha in
theorem openCore_map (cipherKey iv macKey sender receiver wire expected : List B) :
    (openCore d o aes s a cipherKey iv macKey sender receiver wire expected).map f =
      openCore d' o' aes' s' a' (cipherKey.map f) (iv.map f) (macKey.map f) (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  have hl (state : ProtoParse.State B V) := congrArg ProtoParse.Field.length (ProtoParse.getField_map ho ha state 3)
  have hf (state : ProtoParse.State B V) := congrArg ProtoParse.Field.offset (ProtoParse.getField_map ho ha state 3)
  simp only [ProtoParse.Field.map] at hl hf
  simp only [openCore, chooseLength_map ho ha, capacity_map, hl, hf,
    CbcOpen.decryptCore_map he, SliceAt.readCore_map ho ha, authenticatedMask_map ho hs ha,
    ProtoParse.parseBody_map hd ho ha, ProtoParse.body_map]

include hd ho he hs ha in
theorem openChecked_map (cipherKey iv macKey sender receiver wire expected : List B) :
    (openChecked d o aes s a cipherKey iv macKey sender receiver wire expected).map (List.map f) =
      openChecked d' o' aes' s' a' (cipherKey.map f) (iv.map f) (macKey.map f) (sender.map f) (receiver.map f) (wire.map f) (expected.map f) := by
  simp only [openChecked, List.length_map]
  split <;> simp [openCore_map hd ho he hs ha]
end Refinement

theorem compiled_openCore_correct (cipherKey iv macKey sender receiver wire expected : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      cipherKey iv macKey sender receiver wire expected).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
      cipherKey iv macKey sender receiver wire expected))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore VarintDecode.Spqr.symbolic Word64.symbolic AesInverse.symbolic Sha256.symbolic ByteAuth.symbolic
        cipherKey iv macKey sender receiver wire expected))).vec.get index hi)) =
      (ByteCircuit.joinValue (openCore VarintDecode.Spqr.concrete Word64.concrete AesInverse.concrete Sha256.concrete ByteAuth.concrete
        (cipherKey.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign)) (macKey.map (BVExpr.eval assign))
        (sender.map (BVExpr.eval assign)) (receiver.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))
        (expected.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, openCore_map (VarintDecode.Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (AesInverse.evaluationHom assign) (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.ProtoReceive
