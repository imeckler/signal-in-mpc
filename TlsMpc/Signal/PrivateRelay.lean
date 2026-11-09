import TlsMpc.Signal.PrivateBase64CountV2
import TlsMpc.Signal.PrivateDecimal
import TlsMpc.Signal.RelayRequest

/-! One-device actual relay PUT with private ciphertext and numeric widths.
All capacities are public bounds; canonical JSON/protobuf/WebSocket lengths
are shared. Invalid inputs/overflow preserve rejection through TLS. -/
namespace TlsMpc.Signal.PrivateRelay
open RelayEncoding

def body (d : DecimalOps B W) (v : Varint64.Ops B W) (a : ByteAuth.Ops B)
    (metadata : List B) (sealed : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let content := PrivateBase64CountV2.encode a sealed
  let cap := content.data.length+256
  PrivateSend.join a cap [
    PrivateSend.literal a cap (literal a "{\"messages\":[{\"content\":\""),content,
    PrivateSend.literal a cap (literal a "\",\"destinationDeviceId\":"),
    PrivateDecimal.encode d a (RelayRequest.word v a metadata 48 1),
    PrivateSend.literal a cap (literal a ",\"destinationRegistrationId\":"),
    PrivateDecimal.encode d a (RelayRequest.word v a metadata 49 4),
    PrivateSend.literal a cap (literal a ",\"type\":6}],\"online\":false,\"timestamp\":"),
    PrivateDecimal.encode d a (RelayRequest.word v a metadata 32 8),
    PrivateSend.literal a cap (literal a ",\"urgent\":true}")]

def protobuf (s : Sha256.Ops B W32) (d : DecimalOps B W) (v : Varint64.Ops B W) (a : ByteAuth.Ops B)
    (metadata : List B) (sealed : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let json := body d v a metadata sealed
  let cap := json.data.length+256
  let request := PrivateSend.join a cap [
    PrivateSend.literal a cap (Serialization.bytesField a 10 (literal a "PUT")),
    PrivateSend.literal a cap (Serialization.bytesField a 18 (RelayRequest.path a metadata)),
    PrivateProtobuf.bytesField s a 26 json,
    PrivateSend.literal a cap [a.const 32],
    PrivateVarint.uint64 v a (RelayRequest.word v a metadata 40 8),
    PrivateSend.literal a cap (Serialization.bytesField a 42 (literal a "content-type: application/json")),
    PrivateSend.literal a cap (Serialization.bytesField a 42
      (literal a "unidentified-access-key: " ++ RelayEncoding.base64 a ((metadata.drop 16).take 16)))]
  let field := PrivateProtobuf.bytesField s a 18 request
  PrivateSend.join a (field.data.length+2)
    [PrivateSend.literal a (field.data.length+2) [a.const 8,a.const 1],field]

def frame (a : ByteAuth.Ops B) (mask : List B) (payload : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let small := PrivateBuffer.less a payload.lengthBits (PrivateBuffer.publicLength a 126)
  let be := PrivateBuffer.encodeLength a payload.lengthBits
  let lo := OpenResult.get a be 1
  let hi := OpenResult.get a be 0
  let bits := (List.range 16).map (fun i => PrivateBuffer.choose a small
    (OpenResult.get a (PrivateBuffer.publicLength a 2) i) (OpenResult.get a (PrivateBuffer.publicLength a 4) i))
  let rawHeader := [a.const 130,PrivateBuffer.choose a small (a.xor lo (a.const 128)) (a.const 254),hi,lo]
  let header := PrivateBuffer.make a 4 bits rawHeader
  let masked := PrivateProtobuf.replaceData a payload ((List.range payload.data.length).map
    (fun i => a.xor (OpenResult.get a payload.data i) (OpenResult.get a mask (i%4))))
  PrivateSend.join a (payload.data.length+8) [header,PrivateSend.literal a (payload.data.length+8) mask,masked]

def encode (s : Sha256.Ops B W32) (d : DecimalOps B W) (v : Varint64.Ops B W) (a : ByteAuth.Ops B)
    (metadata : List B) (sealed : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  frame a ((metadata.drop 53).take 4) (protobuf s d v a metadata sealed)

section Refinement
variable {s : Sha256.Ops B W32} {s' : Sha256.Ops B' W32'}
  {d : DecimalOps B W} {d' : DecimalOps B' W'} {v : Varint64.Ops B W} {v' : Varint64.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'} {fw32 : W32 → W32'}
  (hs : Sha256.Hom s s' f fw32) (hd : DecimalHom d d' f fw)
  (hv : Varint64.Hom v v' f fw) (ha : ByteAuth.Hom a a' f)
include hd hv ha

theorem body_map (metadata : List B) (sealed : PrivateBuffer.Buffer B) :
    (body d v a metadata sealed).map f = body d' v' a' (metadata.map f) (sealed.map f) := by
  have clen := congrArg (fun b => b.data.length) (PrivateBase64CountV2.encode_map ha sealed)
  change (List.map f _).length=_ at clen
  simp only [List.length_map] at clen
  simp only [body,PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateSend.literal_map ha,
    PrivateDecimal.encode_map hd ha,RelayRequest.word_map hv ha,PrivateBase64CountV2.encode_map ha,literal_map ha,clen]
include hs

theorem protobuf_map (metadata : List B) (sealed : PrivateBuffer.Buffer B) :
    (protobuf s d v a metadata sealed).map f = protobuf s' d' v' a' (metadata.map f) (sealed.map f) := by
  have clen := congrArg (fun b => b.data.length) (body_map hd hv ha metadata sealed)
  change (List.map f _).length=_ at clen
  simp only [List.length_map] at clen
  simp only [protobuf,PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateSend.literal_map ha,
    PrivateProtobuf.bytesField_map hs ha,Serialization.bytesField_map ha,literal_map ha,
    RelayRequest.path_map ha,PrivateVarint.uint64_map hv ha,RelayRequest.word_map hv ha,
    body_map hd hv ha,RelayEncoding.base64_map ha,List.map_append,List.map_take,List.map_drop,ha.const]
  simp only [PrivateProtobuf.bytesField_data_length,PrivateProtobuf.join_data_length,clen]

omit hs hd hv in
theorem frame_map (mask : List B) (payload : PrivateBuffer.Buffer B) :
    (frame a mask payload).map f = frame a' (mask.map f) (payload.map f) := by
  simp only [frame,PrivateSend.join_map ha,List.map_cons,List.map_nil,PrivateBuffer.make_map ha,
    PrivateSend.literal_map ha,PrivateProtobuf.replaceData_map ha,List.map_map,Function.comp_def,
    PrivateBuffer.choose_map ha,PrivateBuffer.less_map ha,PrivateBuffer.publicLength_map ha,
    PrivateBuffer.encodeLength_map ha,OpenResult.get_map ha,ha.xor,ha.const]
  simp only [PrivateBuffer.Buffer.map,List.length_map]

theorem encode_map (metadata : List B) (sealed : PrivateBuffer.Buffer B) :
    (encode s d v a metadata sealed).map f = encode s' d' v' a' (metadata.map f) (sealed.map f) := by
  simp only [encode,frame_map ha,List.map_take,List.map_drop,protobuf_map hs hd hv ha]

end Refinement
open Std.Tactic.BVDecide

theorem compiled_encode_correct (metadata : List (BVExpr 8)) (sealed : PrivateBuffer.Buffer (BVExpr 8))
    (assign : BVExpr.Assignment) :
    PrivateProtobuf.CircuitAgreement
      (PrivateBuffer.output ByteAuth.symbolic (encode Sha256.symbolic decimalSymbolic Varint64.symbolic ByteAuth.symbolic metadata sealed))
      (PrivateBuffer.output ByteAuth.concrete (encode Sha256.concrete decimalConcrete Varint64.concrete ByteAuth.concrete
        (metadata.map (BVExpr.eval assign)) (sealed.map (BVExpr.eval assign)))) assign := by
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,PrivateBuffer.output_map (ByteAuth.evaluationHom assign),
    encode_map (Sha256.evaluationHom assign) (decimalEvaluationHom assign) (Varint64.evaluationHom assign)
      (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.PrivateRelay
