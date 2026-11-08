import TlsMpc.Signal.PrivateProtobuf

/-! Bounded canonical protobuf record trees. The public tree is a CAPACITY
schema; every field/repeated slot has a private presence mask. It must not be
constructed by inspecting live secret protobuf bytes. Bootstrap parsing and the
full SessionRecord projection/update relation remain separate obligations. -/
namespace TlsMpc.Signal.PrivateRecordEncodingV1
inductive Node (B : Type) where
 | bytes (tag : Nat) (present : B) (emitEmpty : Bool) (value : PrivateBuffer.Buffer B)
 | scalar (tag : Nat) (present : B) (emitDefault : Bool) (be : List B)
 | message (tag : Nat) (present : B) (children : List (Node B))

def publicVarint (n : Nat) : List Nat :=
 if n<128 then [n] else [n%128+128] ++ publicVarint (n/128)
termination_by n

def canonicalMask (a : ByteAuth.Ops B) (present : B) : B :=
 a.xor (ByteAuth.eqMask a present (a.const 0)) (ByteAuth.eqMask a present (a.const 255))

def selectBuffer (a : ByteAuth.Ops B) (mask : B)
    (yes no : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
 ⟨PrivateBuffer.choose a mask yes.valid no.valid,
   List.zipWith (PrivateBuffer.choose a mask) yes.lengthBits no.lengthBits,
   List.zipWith (PrivateBuffer.choose a mask) yes.data no.data⟩

def optional (a : ByteAuth.Ops B) (capacity : Nat) (presence enabled : B)
    (encoded : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
 let chosen := selectBuffer a (a.and presence enabled)
   (PrivateBuffer.resize a capacity encoded) (PrivateSend.literal a capacity [])
 PrivateProtobuf.gate a (canonicalMask a presence) chosen

def field (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (capacity tag : Nat)
    (wireType : Nat) (value : PrivateBuffer.Buffer B) : PrivateBuffer.Buffer B :=
 let key := PrivateSend.literal a capacity ((publicVarint (tag*8+wireType)).map a.const)
 if 0<tag ∧ tag<536870912 then
  if wireType=2 then
   let be := PrivateBuffer.encodeLength a value.lengthBits
   let size := s.pack (s.byteConst 0) (s.byteConst 0) (OpenResult.get a be 0) (OpenResult.get a be 1)
   PrivateSend.join a capacity [key,PrivateVarint.uint32 s a size,value]
  else PrivateSend.join a capacity [key,value]
 else PrivateBuffer.zero a capacity

def encode (s : Sha256.Ops B W) (v : Varint64.Ops B V) (a : ByteAuth.Ops B)
    (capacity : Nat) : Nat → List (Node B) → PrivateBuffer.Buffer B
 | 0,_ => PrivateBuffer.zero a capacity
 | fuel+1,nodes =>
  PrivateSend.join a capacity (nodes.map fun node => match node with
   | .bytes tag present emitEmpty value =>
     let enabled := if emitEmpty then a.const 255 else a.not
       (ByteAuth.equalMask a value.lengthBits (PrivateBuffer.publicLength a 0))
     optional a capacity present enabled (field s a capacity tag 2 value)
   | .scalar tag present emitDefault be =>
     if be.length=4 ∨ be.length=8 then
      let raw := List.replicate (8-be.length) (a.const 0) ++ be
      let enabled := if emitDefault then a.const 255 else a.not
        (ByteAuth.equalMask a raw (List.replicate 8 (a.const 0)))
      optional a capacity present enabled
       (field s a capacity tag 0 (PrivateVarint.uint64 v a (Varint64.pack v a raw)))
     else PrivateBuffer.zero a capacity
   | .message tag present children => optional a capacity present (a.const 255)
      (field s a capacity tag 2 (encode s v a capacity fuel children)))
end TlsMpc.Signal.PrivateRecordEncodingV1
