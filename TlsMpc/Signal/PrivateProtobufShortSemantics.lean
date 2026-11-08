import TlsMpc.Signal.PrivateProtobuf
import TlsMpc.Signal.PrivateBufferRecordSemantics

/-! Canonical private varint prefix for the bounded text Content/DataMessage
length domain. Finite kernel computation, never native reflection. -/
namespace TlsMpc.Signal.PrivateProtobuf
open PrivateBuffer
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem uint32_single_byte (n : Fin 128) :
    PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete (BitVec.ofNat 32 n.val) =
      ofContents 5 [BitVec.ofNat 8 n.val] := by
  have all : ∀ n : Fin 128,
    let x := PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete (BitVec.ofNat 32 n.val)
    let y := ofContents 5 [BitVec.ofNat 8 n.val]
    (x.valid,x.lengthBits,x.data)=(y.valid,y.lengthBits,y.data) := by decide +kernel
  have h := all n
  generalize PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete (BitVec.ofNat 32 n.val)=x at h ⊢
  generalize ofContents 5 [BitVec.ofNat 8 n.val]=y at h ⊢
  cases x;cases y
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h1,h2,h3⟩
  subst_vars
  rfl

theorem short_length_word (n : Fin 128) :
    let be := encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete n.val)
    Sha256.concrete.pack 0 0 (OpenResult.get ByteAuth.concrete be 0)
      (OpenResult.get ByteAuth.concrete be 1) = BitVec.ofNat 32 n.val := by
  have all : ∀ n : Fin 128,
    let be := encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete n.val)
    Sha256.concrete.pack 0 0 (OpenResult.get ByteAuth.concrete be 0)
      (OpenResult.get ByteAuth.concrete be 1) = BitVec.ofNat 32 n.val := by decide +kernel
  exact all n

theorem join_three_contents (capacity c1 c2 c3 : Nat) (hc : capacity<65536)
    (x y z : List (BitVec 8)) (fit : x.length+y.length+z.length≤capacity) :
    PrivateSend.join ByteAuth.concrete capacity [ofContents c1 x,ofContents c2 y,ofContents c3 z]=
      ofContents capacity (x++y++z) := by
  unfold PrivateSend.join
  simp only [List.foldl_cons,List.foldl_nil]
  rw [fromPublic_contents capacity hc [] (by simp)]
  rw [append_contents capacity capacity c1 hc [] x (by simp;omega)]
  simp only [List.nil_append]
  rw [append_contents capacity capacity c2 hc x y (by omega)]
  exact append_contents capacity capacity c3 hc (x++y) z (by simpa using fit)

theorem bytesField_short_contents (sourceCapacity tag : Nat)
    (hc : sourceCapacity+4<65536) (raw : List (BitVec 8))
    (fits : raw.length≤sourceCapacity) (short : raw.length<128) :
    bytesField Sha256.concrete ByteAuth.concrete tag (ofContents sourceCapacity raw)=
      ofContents (sourceCapacity+4) ([BitVec.ofNat 8 tag,BitVec.ofNat 8 raw.length]++raw) := by
  have length : (ofContents sourceCapacity raw).data.length=sourceCapacity := by
    simp only [ofContents,List.length_append,List.length_replicate];omega
  unfold bytesField
  rw [length]
  change PrivateSend.join ByteAuth.concrete (sourceCapacity+4)
    [PrivateSend.literal ByteAuth.concrete (sourceCapacity+4) [BitVec.ofNat 8 tag],
      PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete
        (Sha256.concrete.pack 0 0
          (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete raw.length)) 0)
          (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete raw.length)) 1)),
      ofContents sourceCapacity raw]=_
  rw [short_length_word ⟨raw.length,short⟩,uint32_single_byte ⟨raw.length,short⟩]
  unfold PrivateSend.literal
  rw [fromPublic_contents (sourceCapacity+4) hc [BitVec.ofNat 8 tag] (by simp)]
  exact join_three_contents (sourceCapacity+4) (sourceCapacity+4) 5 sourceCapacity hc
    [BitVec.ofNat 8 tag] [BitVec.ofNat 8 raw.length] raw (by simp;omega)
end TlsMpc.Signal.PrivateProtobuf

