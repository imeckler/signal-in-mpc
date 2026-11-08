import TlsMpc.Signal.PrivateProtobuf
import TlsMpc.Signal.Varint64
import TlsMpc.TlsWebSocketFrame

/-! Bounded valid-UTF8 text notification. Private input: validity8, BE16 text
length, 48 text bytes, timestampBE8. Output: validity8, kind0, 80-byte ISO7816
application plaintext, identical timestampBE8. Public bucket80 matches the
relay notification profile. Invalid UTF8/bounds/status gives canonical zeros.
This is the text-only Content/DataMessage subset, not the full app schema. -/
namespace TlsMpc.Signal.PrivateTextNotification
open Std.Tactic.BVDecide

def utfLoop (a : ByteAuth.Ops B) (data lengthBits : List B) :
    List Nat → List B → List B
  | [],state => state
  | i::rest,state =>
    let active := PrivateBuffer.less a (PrivateBuffer.publicLength a i) lengthBits
    utfLoop a data lengthBits rest (TlsWebSocketUpgrade.choose a active
      (TlsWebSocketFrame.utfStep a state (OpenResult.get a data i)) state)

def build (s : Sha256.Ops B W) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (input : List B) : List B :=
  if input.length != 59 then List.replicate 90 (a.const 0) else
  let body := PrivateBuffer.fromWire a 48 (input.take 51)
  let timestamp := (input.drop 51).take 8
  let utf := utfLoop a body.data body.lengthBits (List.range 48) (TlsWebSocketUpgrade.initial a 7)
  let bodyField := PrivateProtobuf.bytesField s a 10 body
  let timeField := PrivateSend.join a 11 [PrivateSend.literal a 11 [a.const 56],
    PrivateVarint.uint64 v a (Varint64.pack v a timestamp)]
  let dm := PrivateSend.join a 63 [bodyField,timeField]
  let content := PrivateProtobuf.bytesField s a 10 dm
  let padded := PrivateSend.join a 80 [content,PrivateSend.literal a 80 [a.const 128]]
  let valid := a.and padded.valid (ByteAuth.eqMask a (OpenResult.get a utf 0) (a.const 255))
  valid :: ByteAuth.release a valid (a.const 0 :: padded.data ++ timestamp)

theorem build_length (s : Sha256.Ops B W) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (input : List B) : (build s v a input).length = 90 := by
  unfold build
  split
  · simp only [List.length_replicate]
  · rename_i h
    have hi : input.length = 59 := by simpa using h
    simp only [List.length_cons,ByteAuth.release,List.length_map,List.length_append,
      PrivateProtobuf.join_data_length,List.length_take,List.length_drop,hi]
    decide

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'} {fv : V → V'}
  (hs : Sha256.Hom s s' f fw) (hv : Varint64.Hom v v' f fv) (ha : ByteAuth.Hom a a' f)
include ha

theorem utfLoop_map (data lengthBits : List B) (indices : List Nat) (state : List B) :
    (utfLoop a data lengthBits indices state).map f =
    utfLoop a' (data.map f) (lengthBits.map f) indices (state.map f) := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [utfLoop,ih,TlsWebSocketUpgrade.choose_map ha,TlsWebSocketFrame.utfStep_map ha,
      PrivateBuffer.less_map ha,PrivateBuffer.publicLength_map ha,OpenResult.get_map ha]

theorem fromWire_data_map (cap : Nat) (input : List B) :
    (PrivateBuffer.fromWire a cap input).data.map f =
    (PrivateBuffer.fromWire a' cap (input.map f)).data :=
  congrArg PrivateBuffer.Buffer.data (PrivateBuffer.fromWire_map ha cap input)
theorem fromWire_bits_map (cap : Nat) (input : List B) :
    (PrivateBuffer.fromWire a cap input).lengthBits.map f =
    (PrivateBuffer.fromWire a' cap (input.map f)).lengthBits :=
  congrArg PrivateBuffer.Buffer.lengthBits (PrivateBuffer.fromWire_map ha cap input)
theorem join_valid_map (cap : Nat) (chunks : List (PrivateBuffer.Buffer B)) :
    f (PrivateSend.join a cap chunks).valid =
    (PrivateSend.join a' cap (chunks.map (PrivateBuffer.Buffer.map f))).valid :=
  congrArg PrivateBuffer.Buffer.valid (PrivateSend.join_map ha cap chunks)
theorem join_data_map (cap : Nat) (chunks : List (PrivateBuffer.Buffer B)) :
    (PrivateSend.join a cap chunks).data.map f =
    (PrivateSend.join a' cap (chunks.map (PrivateBuffer.Buffer.map f))).data :=
  congrArg PrivateBuffer.Buffer.data (PrivateSend.join_map ha cap chunks)

include hs hv

theorem build_map (input : List B) :
    (build s v a input).map f = build s' v' a' (input.map f) := by
  simp only [build,List.length_map]
  split
  · simp only [List.map_replicate,ha.const]
  · simp only [List.map_cons,List.map_append,ByteAuth.release_map ha,ha.and,ha.const,
      ByteAuth.eqMask_map ha,OpenResult.get_map ha,utfLoop_map ha,TlsWebSocketUpgrade.initial_map ha,
      PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateSend.literal_map ha,
      PrivateProtobuf.bytesField_map hs ha,PrivateVarint.uint64_map hv ha,Varint64.pack_map hv ha,
      PrivateBuffer.fromWire_map ha,List.map_take,List.map_drop,fromWire_data_map ha,fromWire_bits_map ha,join_valid_map ha,join_data_map ha]
end Refinement

theorem compiled_build_correct (input : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement (build Sha256.symbolic Varint64.symbolic ByteAuth.symbolic input)
      (build Sha256.concrete Varint64.concrete ByteAuth.concrete (input.map (BVExpr.eval assign))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,build_map (Sha256.evaluationHom assign)
    (Varint64.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.PrivateTextNotification
