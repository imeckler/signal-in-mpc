import TlsMpc.Signal.RelayEncoding
import TlsMpc.Signal.Serialization

/-! One-device relay WebSocket request, with secret UUID/UAK/numbers/sealed
ciphertext. The route matches relay notify, not gRPC. Sealed Sender and the
HTTP101 upgrade/response stream are separate dependencies. Encoded widths are
public profile; rejection status and masked frame remain secret. -/
namespace TlsMpc.Signal.RelayRequest
open Std.Tactic.BVDecide RelayEncoding
structure Shape where
  sealedBytes : Nat
  deviceDigits : Nat
  registrationDigits : Nat
  timestampDigits : Nat
  requestIdWidth : Nat
  deriving DecidableEq

def Shape.valid (p : Shape) : Prop :=
  0<p.sealedBytes ∧ p.sealedBytes≤8192 ∧ 1≤p.deviceDigits ∧ p.deviceDigits≤3 ∧
    1≤p.registrationDigits ∧ p.registrationDigits≤10 ∧ 1≤p.timestampDigits ∧ p.timestampDigits≤20 ∧
    1≤p.requestIdWidth ∧ p.requestIdWidth≤10
instance (p : Shape) : Decidable p.valid := inferInstanceAs (Decidable (_ ∧ _))
-- raw: UUID16,UAK16,timestampBE8,idBE8,device1,registrationBE4,sealed,WSmask4.
def inputBytes (p : Shape) : Nat := 57+p.sealedBytes

def word (v : Varint64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) (offset count : Nat) : W :=
  Varint64.pack v a (List.replicate (8-count) (a.const 0) ++ (raw.drop offset).take count)

def path (a : ByteAuth.Ops B) (raw : List B) : List B :=
  literal a "/v1/messages/" ++ uuid a (raw.take 16) ++ literal a "?story=false"

def body (d : DecimalOps B W) (v : Varint64.Ops B W) (a : ByteAuth.Ops B) (p : Shape) (raw : List B) : List B :=
  literal a "{\"messages\":[{\"content\":\"" ++ base64 a ((raw.drop 53).take p.sealedBytes) ++
  literal a "\",\"destinationDeviceId\":" ++ decimal d (word v a raw 48 1) p.deviceDigits ++
  literal a ",\"destinationRegistrationId\":" ++ decimal d (word v a raw 49 4) p.registrationDigits ++
  literal a ",\"type\":6}],\"online\":false,\"timestamp\":" ++ decimal d (word v a raw 32 8) p.timestampDigits ++
  literal a ",\"urgent\":true}"

def accepted (d : DecimalOps B W) (v : Varint64.Ops B W) (a : ByteAuth.Ops B) (p : Shape) (raw : List B) : B :=
  a.and (decimalMask d a (word v a raw 48 1) p.deviceDigits)
    (a.and (decimalMask d a (word v a raw 49 4) p.registrationDigits)
      (a.and (decimalMask d a (word v a raw 32 8) p.timestampDigits)
        (Varint64.accepts v a (word v a raw 40 8) p.requestIdWidth)))

def protobuf (d : DecimalOps B W) (v : Varint64.Ops B W) (a : ByteAuth.Ops B) (p : Shape) (raw : List B) : List B :=
  let request := Serialization.bytesField a 10 (literal a "PUT") ++
    Serialization.bytesField a 18 (path a raw) ++ Serialization.bytesField a 26 (body d v a p raw) ++
    [a.const 32] ++ Varint64.encode v a (word v a raw 40 8) p.requestIdWidth ++
    Serialization.bytesField a 42 (literal a "content-type: application/json") ++
    Serialization.bytesField a 42 (literal a "unidentified-access-key: " ++ base64 a ((raw.drop 16).take 16))
  [a.const 8,a.const 1] ++ Serialization.bytesField a 18 request

def frame (a : ByteAuth.Ops B) (mask payload : List B) : List B :=
  let header := [a.const 130] ++ (if payload.length<126 then [a.const (128+payload.length)] else
    [a.const 254,a.const (payload.length/256),a.const payload.length])
  header ++ mask ++ (List.range payload.length).map (fun i =>
    a.xor (OpenResult.get a payload i) (OpenResult.get a mask (i%4)))

def encodeCore (d : DecimalOps B W) (v : Varint64.Ops B W) (a : ByteAuth.Ops B) (p : Shape) (raw : List B) : List B :=
  let status := accepted d v a p raw
  status :: ByteAuth.release a status (frame a ((raw.drop (53+p.sealedBytes)).take 4) (protobuf d v a p raw))

section Refinement
variable {d : DecimalOps B W} {d' : DecimalOps B' W'} {v : Varint64.Ops B W} {v' : Varint64.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (hd : DecimalHom d d' f fw) (hv : Varint64.Hom v v' f fw) (ha : ByteAuth.Hom a a' f)
include hv ha

theorem word_map (raw : List B) (offset count : Nat) :
    fw (word v a raw offset count) = word v' a' (raw.map f) offset count := by
  simp only [word,Varint64.pack_map hv ha,List.map_append,List.map_replicate,ha.const,List.map_take,List.map_drop]

omit hv in
theorem path_map (raw : List B) : (path a raw).map f = path a' (raw.map f) := by
  simp [path,literal_map ha,uuid_map ha]
include hd

theorem body_map (p : Shape) (raw : List B) : (body d v a p raw).map f = body d' v' a' p (raw.map f) := by
  simp only [body,List.map_append,literal_map ha,base64_map ha,List.map_take,List.map_drop,decimal_map hd,word_map hv ha]

theorem accepted_map (p : Shape) (raw : List B) :
    f (accepted d v a p raw) = accepted d' v' a' p (raw.map f) := by
  simp only [accepted,ha.and,decimalMask_map ha hd,word_map hv ha,Varint64.accepts_map hv ha]

theorem protobuf_map (p : Shape) (raw : List B) :
    (protobuf d v a p raw).map f = protobuf d' v' a' p (raw.map f) := by
  simp only [protobuf,List.map_append,List.map_cons,List.map_nil,ha.const,Serialization.bytesField_map ha,
    literal_map ha,path_map ha,body_map hd hv ha,Varint64.encode_map hv ha,word_map hv ha,
    base64_map ha,List.map_take,List.map_drop]

omit hd hv in
theorem frame_map (mask payload : List B) :
    (frame a mask payload).map f = frame a' (mask.map f) (payload.map f) := by
  simp only [frame,List.map_append,List.map_cons,List.map_nil,List.length_map,List.map_map,Function.comp_def,
    ha.xor,OpenResult.get_map ha]
  split <;> simp_all [ha.const]

theorem encodeCore_map (p : Shape) (raw : List B) :
    (encodeCore d v a p raw).map f = encodeCore d' v' a' p (raw.map f) := by
  simp only [encodeCore,List.map_cons,accepted_map hd hv ha,ByteAuth.release_map ha,frame_map ha,
    List.map_take,List.map_drop,protobuf_map hd hv ha]
end Refinement

theorem compiled_encode_correct (p : Shape) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8*(encodeCore decimalSymbolic Varint64.symbolic ByteAuth.symbolic p raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (encodeCore decimalSymbolic Varint64.symbolic ByteAuth.symbolic p raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (encodeCore decimalSymbolic Varint64.symbolic ByteAuth.symbolic p raw))).vec.get index hi)) =
    (ByteCircuit.joinValue (encodeCore decimalConcrete Varint64.concrete ByteAuth.concrete p
      (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,encodeCore_map (decimalEvaluationHom assign)
    (Varint64.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.RelayRequest
