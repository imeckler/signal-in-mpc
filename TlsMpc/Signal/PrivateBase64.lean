import TlsMpc.Signal.PrivateProtobuf
import TlsMpc.Signal.RelayEncoding

/-! Standard padded base64 with private prefix length. Public capacity fixes
work, not actual bytes or '=' placement. Unused output suffix is zero. -/
namespace TlsMpc.Signal.PrivateBase64

def group (a : ByteAuth.Ops B) (input : PrivateBuffer.Buffer B) (index : Nat) : List B :=
  let bytes := (List.range 3).map (fun j => OpenResult.get a input.data (3*index+j))
  let encoded := RelayEncoding.base64 a bytes
  let one := ByteAuth.equalMask a input.lengthBits (PrivateBuffer.publicLength a (3*index+1))
  let two := ByteAuth.equalMask a input.lengthBits (PrivateBuffer.publicLength a (3*index+2))
  [OpenResult.get a encoded 0,OpenResult.get a encoded 1,
    PrivateBuffer.choose a one (a.const 61) (OpenResult.get a encoded 2),
    PrivateBuffer.choose a (a.not (a.and (a.not one) (a.not two))) (a.const 61) (OpenResult.get a encoded 3)]

def count (a : ByteAuth.Ops B) (bits : List B) : List Nat → List B → List B
  | [],total => total
  | i::is,total =>
    let active := PrivateBuffer.less a (PrivateBuffer.publicLength a (3*i)) bits
    let increment := ByteAuth.release a active (PrivateBuffer.publicLength a 4)
    count a bits is (PrivateBuffer.addLoop a total increment (List.range 16) (a.const 0)).1

def encode (a : ByteAuth.Ops B) (input : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
  let b := PrivateBuffer.resize a input.data.length input
  let groups := (input.data.length+2)/3
  let bits := count a b.lengthBits (List.range groups) (PrivateBuffer.publicLength a 0)
  let raw := (List.range groups).flatMap (group a b)
  PrivateProtobuf.gate a b.valid (PrivateBuffer.make a (4*groups) bits raw)

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha

theorem group_map (input : PrivateBuffer.Buffer B) (index : Nat) :
    (group a input index).map f = group a' (input.map f) index := by
  simp only [group,List.map_cons,List.map_nil,PrivateBuffer.choose_map ha,ha.const,ha.not,ha.and,
    ByteAuth.equalMask_map ha,PrivateBuffer.publicLength_map ha,OpenResult.get_map ha,RelayEncoding.base64_map ha,
    List.map_map,Function.comp_def,PrivateBuffer.Buffer.map]

theorem count_map (bits : List B) (is : List Nat) (total : List B) :
    (count a bits is total).map f = count a' (bits.map f) is (total.map f) := by
  induction is generalizing total with
  | nil => rfl
  | cons i is ih =>
    simp only [count,ih]
    have mapped := congrArg Prod.fst (PrivateBuffer.addLoop_map ha total
      (ByteAuth.release a (PrivateBuffer.less a (PrivateBuffer.publicLength a (3*i)) bits)
        (PrivateBuffer.publicLength a 4)) (List.range 16) (a.const 0))
    simp only [ByteAuth.release_map ha,PrivateBuffer.less_map ha,PrivateBuffer.publicLength_map ha,ha.const] at mapped
    rw [mapped]

theorem encode_map (input : PrivateBuffer.Buffer B) :
    (encode a input).map f = encode a' (input.map f) := by
  have normalized := PrivateBuffer.resize_map ha input.data.length input
  have data := congrArg PrivateBuffer.Buffer.data normalized
  have bits := congrArg PrivateBuffer.Buffer.lengthBits normalized
  have valid := congrArg PrivateBuffer.Buffer.valid normalized
  change List.map f _ = _ at data
  change List.map f _ = _ at bits
  change f _ = _ at valid
  unfold encode
  rw [PrivateProtobuf.gate_map ha,PrivateBuffer.make_map ha,count_map ha]
  simp only [PrivateBuffer.publicLength_map ha,List.map_flatMap,group_map ha,normalized]
  rw [bits,valid]
  simp only [PrivateBuffer.Buffer.map,List.length_map]

end Refinement
end TlsMpc.Signal.PrivateBase64
