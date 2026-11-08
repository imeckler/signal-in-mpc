import TlsMpc.Signal.PrivateRecordEncodingV1
namespace TlsMpc.Signal.PrivateRecordEncodingV1
open Std.Tactic.BVDecide

def Node.map (f : B → B') : Node B → Node B'
 | .bytes t p e b => .bytes t (f p) e (b.map f)
 | .scalar t p e b => .scalar t (f p) e (b.map f)
 | .message t p b => .message t (f p) (b.map (Node.map f))

section
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
 {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'} {fv : V → V'}
 (hs : Sha256.Hom s s' f fw) (hv : Varint64.Hom v v' f fv) (ha : ByteAuth.Hom a a' f)
include ha
 theorem selectBuffer_map (mask : B) (yes no : PrivateBuffer.Buffer B) :
  (selectBuffer a mask yes no).map f = selectBuffer a' (f mask) (yes.map f) (no.map f) := by
  simp [selectBuffer,PrivateBuffer.Buffer.map,List.map_zipWith,PrivateBuffer.choose_map ha]
 theorem optional_map (capacity : Nat) (presence enabled : B) (encoded : PrivateBuffer.Buffer B) :
  (optional a capacity presence enabled encoded).map f = optional a' capacity (f presence) (f enabled) (encoded.map f) := by
  simp only [optional,PrivateProtobuf.gate_map ha,selectBuffer_map ha,ha.and,PrivateBuffer.resize_map ha,PrivateSend.literal_map ha,List.map_nil]
  simp [canonicalMask,ha.xor,ByteAuth.eqMask_map ha,ha.const]
 include hs
 theorem field_map (capacity tag wireType : Nat) (value : PrivateBuffer.Buffer B) :
  (field s a capacity tag wireType value).map f = field s' a' capacity tag wireType (value.map f) := by
  unfold field
  split
  · split
    · simp only [PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateSend.literal_map ha,List.map_map,Function.comp_def,ha.const,
       PrivateVarint.uint32_map hs ha,hs.pack,hs.byteConst,OpenResult.get_map ha,PrivateBuffer.encodeLength_map ha]
      rfl
    · simp only [PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateSend.literal_map ha,List.map_map,Function.comp_def,ha.const]
  · exact PrivateBuffer.zero_map ha _
 include hv
 theorem encode_map (capacity fuel : Nat) (nodes : List (Node B)) :
  (encode s v a capacity fuel nodes).map f = encode s' v' a' capacity fuel (nodes.map (Node.map f)) := by
  induction fuel generalizing nodes with
  | zero => exact PrivateBuffer.zero_map ha _
  | succ fuel ih =>
   simp only [encode,PrivateSend.join_map ha,List.map_map,Function.comp_def]
   congr 1
   apply List.map_congr_left
   intro node _
   cases node with
   | bytes tag present emitEmpty value =>
    simp only [Node.map,optional_map ha,field_map hs ha]
    congr 1
    split <;> simp [PrivateBuffer.Buffer.map,ha.const,ha.not,ByteAuth.equalMask_map ha,PrivateBuffer.publicLength_map ha]
   | scalar tag present emitDefault be =>
    simp only [Node.map,List.length_map]
    split
    · simp only [optional_map ha,field_map hs ha,PrivateVarint.uint64_map hv ha,Varint64.pack_map hv ha,
       List.map_append,List.map_replicate,ha.const]
      congr 1
      split <;> simp [ha.const,ha.not,ByteAuth.equalMask_map ha,List.map_append,List.map_replicate]
    · exact PrivateBuffer.zero_map ha _
   | message tag present children =>
    simp only [Node.map,optional_map ha,ha.const,field_map hs ha,ih]
end
theorem compiled_encode_correct (capacity fuel : Nat) (nodes : List (Node (BVExpr 8)))
 (assign : BVExpr.Assignment) :
 PrivateProtobuf.CircuitAgreement
  (PrivateBuffer.output ByteAuth.symbolic (encode Sha256.symbolic Varint64.symbolic ByteAuth.symbolic capacity fuel nodes))
  (PrivateBuffer.output ByteAuth.concrete (encode Sha256.concrete Varint64.concrete ByteAuth.concrete capacity fuel
    (nodes.map (Node.map (BVExpr.eval assign))))) assign := by
 intro index hi
 rw [ByteCircuit.compile_bytes_correct,PrivateBuffer.output_map (ByteAuth.evaluationHom assign),
  encode_map (Sha256.evaluationHom assign) (Varint64.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PrivateRecordEncodingV1
