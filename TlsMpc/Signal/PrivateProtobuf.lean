import TlsMpc.Signal.PrivateSend

namespace TlsMpc.Signal.PrivateProtobuf

open Std.Tactic.BVDecide

/-- Numeric compiler agreement, abstracted to avoid elaborating cryptographic
expressions while typechecking the dependent vector index. -/
def CircuitAgreement (symbolic : List (BVExpr 8)) (concrete : List (BitVec 8))
    (assign : BVExpr.Assignment) : Prop :=
  ∀ index (hi : index<8*symbolic.length),
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr symbolic)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr symbolic)).vec.get index hi)) =
    (ByteCircuit.joinValue concrete).getLsbD index

def bytesField (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (tag : Nat)
    (data : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let cap := data.data.length+4
  let be := PrivateBuffer.encodeLength a data.lengthBits
  let size := s.pack (s.byteConst 0) (s.byteConst 0) (OpenResult.get a be 0) (OpenResult.get a be 1)
  PrivateSend.join a cap [PrivateSend.literal a cap [a.const tag],PrivateVarint.uint32 s a size,data]

def gate (a : ByteAuth.Ops B) (status : B) (b : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  PrivateBuffer.finish a (a.and b.valid (ByteAuth.eqMask a status (a.const 255))) b.lengthBits b.data

def replaceData (a : ByteAuth.Ops B) (b : PrivateBuffer.Buffer B) (raw : List B) : PrivateBuffer.Buffer B :=
  gate a b.valid (PrivateBuffer.make a b.data.length b.lengthBits raw)

def first (a : ByteAuth.Ops B) (n : Nat) (b : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  PrivateBuffer.finish a b.valid (PrivateBuffer.publicLength a n) (b.data.take n)

theorem append_data_length (a : ByteAuth.Ops B) (capacity : Nat) (left right : PrivateBuffer.Buffer B) :
    (PrivateBuffer.append a capacity left right).data.length = capacity := by
  simp [PrivateBuffer.append,PrivateBuffer.finish,ByteAuth.release]

theorem join_data_length (a : ByteAuth.Ops B) (capacity : Nat) (chunks : List (PrivateBuffer.Buffer B)) :
    (PrivateSend.join a capacity chunks).data.length = capacity := by
  have aux (chunks : List (PrivateBuffer.Buffer B)) (initial : PrivateBuffer.Buffer B)
      (hi : initial.data.length=capacity) :
      (chunks.foldl (PrivateBuffer.append a capacity) initial).data.length=capacity := by
    induction chunks generalizing initial with
    | nil => exact hi
    | cons x xs ih => exact ih _ (append_data_length a capacity initial x)
  apply aux
  simp only [PrivateBuffer.fromPublic,PrivateSend.literal,List.length_nil,Nat.zero_le,if_pos,List.nil_append,Nat.sub_zero]
  unfold PrivateBuffer.make
  split <;> simp [PrivateBuffer.finish,PrivateBuffer.zero,ByteAuth.release]

theorem bytesField_data_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (tag : Nat) (data : PrivateBuffer.Buffer B) :
    (bytesField s a tag data).data.length = data.data.length+4 := join_data_length a _ _

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem gate_map (status : B) (b : PrivateBuffer.Buffer B) :
    (gate a status b).map f = gate a' (f status) (b.map f) := by
  unfold gate
  rw [PrivateBuffer.finish_map ha,ha.and,ByteAuth.eqMask_map ha,ha.const]
  rfl

theorem first_map (n : Nat) (b : PrivateBuffer.Buffer B) :
    (first a n b).map f = first a' n (b.map f) := by
  unfold first
  rw [PrivateBuffer.finish_map ha,PrivateBuffer.publicLength_map ha]
  simp only [PrivateBuffer.Buffer.map,List.map_take]
theorem replaceData_map (b : PrivateBuffer.Buffer B) (raw : List B) :
    (replaceData a b raw).map f = replaceData a' (b.map f) (raw.map f) := by
  unfold replaceData
  rw [gate_map ha,PrivateBuffer.make_map ha]
  simp only [PrivateBuffer.Buffer.map,List.length_map]

include hs

theorem bytesField_map (tag : Nat) (data : PrivateBuffer.Buffer B) :
    (bytesField s a tag data).map f = bytesField s' a' tag (data.map f) := by
  unfold bytesField
  rw [PrivateSend.join_map ha]
  simp only [List.map_cons,List.map_nil,PrivateSend.literal_map ha,PrivateVarint.uint32_map hs ha,
    List.map_cons,List.map_nil,ha.const,hs.pack,hs.byteConst,OpenResult.get_map ha,PrivateBuffer.encodeLength_map ha,
    List.length_map]
  simp only [PrivateBuffer.Buffer.map,List.length_map]

end Refinement
end TlsMpc.Signal.PrivateProtobuf
