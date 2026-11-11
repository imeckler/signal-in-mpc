import TlsMpc.Signal.PrivateTextNotificationContentSemantics

/-! The padding and Content semantics of `PrivateTextNotification.build`
(PrivateTextNotificationSemantics, PrivateTextNotificationContentSemantics,
PrivateProtobufShortSemantics) generalised to the size classes of
`buildSized`: any block count, any text capacity, and length prefixes of one or
two bytes (lengths below 320: finite kernel computation, never native
reflection). The 48-byte, one-block statements are the instances shown at the
end of each part. As there, UTF-8 validation and the wire decoding of the text
input are outside these statements. -/

namespace TlsMpc.Signal.PrivateProtobuf
open PrivateBuffer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- One kernel computation at a time: several at once multiply the memory needed.
set_option Elab.async false

/-- The canonical protobuf varint of a length below 16384. -/
def lengthPrefix (n : Nat) : List (BitVec 8) :=
  if n < 128 then [BitVec.ofNat 8 n] else [BitVec.ofNat 8 (n % 128 + 128), BitVec.ofNat 8 (n / 128)]

theorem lengthPrefix_length (n : Nat) : (lengthPrefix n).length ≤ 2 := by
  unfold lengthPrefix
  split <;> simp

theorem lengthPrefix_short (n : Nat) (short : n < 128) : lengthPrefix n = [BitVec.ofNat 8 n] := by
  simp [lengthPrefix, short]

theorem buffer_eq (x y : Buffer (BitVec 8))
    (h : (x.valid,x.lengthBits,x.data)=(y.valid,y.lengthBits,y.data)) : x=y := by
  cases x;cases y
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h1,h2,h3⟩
  subst_vars
  rfl

/-! Two-byte lengths, 64 at a time (each a separate kernel computation, to bound its memory). -/

theorem uint32_length_128 : ∀ n : Fin 64,
    let x := PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete (BitVec.ofNat 32 (128+n.val))
    let y := ofContents 5 (lengthPrefix (128+n.val))
    (x.valid,x.lengthBits,x.data)=(y.valid,y.lengthBits,y.data) := by decide +kernel
theorem uint32_length_192 : ∀ n : Fin 64,
    let x := PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete (BitVec.ofNat 32 (192+n.val))
    let y := ofContents 5 (lengthPrefix (192+n.val))
    (x.valid,x.lengthBits,x.data)=(y.valid,y.lengthBits,y.data) := by decide +kernel
theorem uint32_length_256 : ∀ n : Fin 64,
    let x := PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete (BitVec.ofNat 32 (256+n.val))
    let y := ofContents 5 (lengthPrefix (256+n.val))
    (x.valid,x.lengthBits,x.data)=(y.valid,y.lengthBits,y.data) := by decide +kernel

theorem uint32_length (n : Nat) (bounded : n<320) :
    PrivateVarint.uint32 Sha256.concrete ByteAuth.concrete (BitVec.ofNat 32 n) =
      ofContents 5 (lengthPrefix n) := by
  by_cases h1 : n<128
  · rw [lengthPrefix_short n h1]
    exact uint32_single_byte ⟨n,h1⟩
  · by_cases h2 : n<192
    · rw [show n=128+(n-128) by omega]
      exact buffer_eq _ _ (uint32_length_128 ⟨n-128,by omega⟩)
    · by_cases h3 : n<256
      · rw [show n=192+(n-192) by omega]
        exact buffer_eq _ _ (uint32_length_192 ⟨n-192,by omega⟩)
      · rw [show n=256+(n-256) by omega]
        exact buffer_eq _ _ (uint32_length_256 ⟨n-256,by omega⟩)

theorem length_word_128 : ∀ n : Fin 64,
    Sha256.concrete.pack 0 0
      (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete (128+n.val))) 0)
      (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete (128+n.val))) 1) =
      BitVec.ofNat 32 (128+n.val) := by decide +kernel
theorem length_word_192 : ∀ n : Fin 64,
    Sha256.concrete.pack 0 0
      (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete (192+n.val))) 0)
      (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete (192+n.val))) 1) =
      BitVec.ofNat 32 (192+n.val) := by decide +kernel
theorem length_word_256 : ∀ n : Fin 64,
    Sha256.concrete.pack 0 0
      (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete (256+n.val))) 0)
      (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete (256+n.val))) 1) =
      BitVec.ofNat 32 (256+n.val) := by decide +kernel

theorem length_word (n : Nat) (bounded : n<320) :
    Sha256.concrete.pack 0 0
      (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete n)) 0)
      (OpenResult.get ByteAuth.concrete (encodeLength ByteAuth.concrete (publicLength ByteAuth.concrete n)) 1) =
      BitVec.ofNat 32 n := by
  by_cases h1 : n<128
  · exact short_length_word ⟨n,h1⟩
  · by_cases h2 : n<192
    · rw [show n=128+(n-128) by omega]
      exact length_word_128 ⟨n-128,by omega⟩
    · by_cases h3 : n<256
      · rw [show n=192+(n-192) by omega]
        exact length_word_192 ⟨n-192,by omega⟩
      · rw [show n=256+(n-256) by omega]
        exact length_word_256 ⟨n-256,by omega⟩

/-- `bytesField_short_contents` without the one-byte bound on the length prefix. -/
theorem bytesField_contents (sourceCapacity tag : Nat)
    (hc : sourceCapacity+4<65536) (raw : List (BitVec 8))
    (fits : raw.length≤sourceCapacity) (bounded : raw.length<320) :
    bytesField Sha256.concrete ByteAuth.concrete tag (ofContents sourceCapacity raw)=
      ofContents (sourceCapacity+4) ([BitVec.ofNat 8 tag]++lengthPrefix raw.length++raw) := by
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
  rw [length_word raw.length bounded,uint32_length raw.length bounded]
  unfold PrivateSend.literal
  rw [fromPublic_contents (sourceCapacity+4) hc [BitVec.ofNat 8 tag] (by simp)]
  exact join_three_contents (sourceCapacity+4) (sourceCapacity+4) 5 sourceCapacity hc
    [BitVec.ofNat 8 tag] (lengthPrefix raw.length) raw
    (by have := lengthPrefix_length raw.length; simp only [List.length_cons,List.length_nil]; omega)

end TlsMpc.Signal.PrivateProtobuf

namespace TlsMpc.Signal.PrivateTextNotification
open PrivateBuffer PrivateProtobuf

/-! ### Padding to any block count -/

theorem iso7816_sized_contents (size sourceCapacity : Nat) (hc : size<65536) (content : List (BitVec 8))
    (fit : content.length<size) :
    PrivateSend.join ByteAuth.concrete size [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete size [128]] = ofContents size (content++[128]) := by
  unfold PrivateSend.join PrivateSend.literal
  simp only [List.foldl_cons,List.foldl_nil]
  rw [fromPublic_contents size hc [] (by simp),
    fromPublic_contents size hc [128] (by simp only [List.length_cons,List.length_nil]; omega)]
  rw [append_contents size size sourceCapacity hc [] content (by simp only [List.length_nil]; omega)]
  simp only [List.nil_append]
  exact append_contents size size size hc content [128] (by simp only [List.length_cons,List.length_nil]; omega)

/-- The padded data: the content, the 0x80 terminator, zeros to the block boundary. -/
theorem iso7816_sized_data (size sourceCapacity : Nat) (hc : size<65536) (content : List (BitVec 8))
    (fit : content.length<size) :
    (PrivateSend.join ByteAuth.concrete size [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete size [128]]).data =
      content ++ 128 :: List.replicate (size-1-content.length) 0 := by
  rw [iso7816_sized_contents size sourceCapacity hc content fit]
  have total : (content++[128]).length=content.length+1 := by simp
  have count : size-(content++[128]).length=size-1-content.length := by omega
  simp only [ofContents,count,List.append_assoc,List.singleton_append]

theorem iso7816_sized_status (size sourceCapacity : Nat) (hc : size<65536) (content : List (BitVec 8))
    (fit : content.length<size) :
    (PrivateSend.join ByteAuth.concrete size [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete size [128]]).valid=255 := by
  rw [iso7816_sized_contents size sourceCapacity hc content fit];rfl

/-- The one-block statement is the instance `size = 80`. -/
theorem iso7816_contents_of_sized (sourceCapacity : Nat) (content : List (BitVec 8)) (fit : content.length<80) :
    PrivateSend.join ByteAuth.concrete 80 [ofContents sourceCapacity content,
      PrivateSend.literal ByteAuth.concrete 80 [128]] = ofContents 80 (content++[128]) :=
  iso7816_sized_contents 80 sourceCapacity (by decide) content fit

/-! ### Content for any text capacity -/

def dataMessageBytesSized (body : List (BitVec 8)) (word : BitVec 64) (width : Nat) : List (BitVec 8) :=
  [BitVec.ofNat 8 10] ++ lengthPrefix body.length ++ body ++
    56 :: Varint64.encode Varint64.concrete ByteAuth.concrete word width

/-- The serialized Content: one DataMessage field. -/
def contentBytesSized (body : List (BitVec 8)) (word : BitVec 64) (width : Nat) : List (BitVec 8) :=
  [BitVec.ofNat 8 10] ++ lengthPrefix (dataMessageBytesSized body word width).length ++
    dataMessageBytesSized body word width

/-- The DataMessage buffer exactly as `buildSized capacity _` forms it. -/
def encodedDataMessageSized (capacity : Nat) (body : Buffer (BitVec 8)) (word : BitVec 64) : Buffer (BitVec 8) :=
  PrivateSend.join ByteAuth.concrete (capacity+15) [PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10 body,
    PrivateSend.join ByteAuth.concrete 11 [PrivateSend.literal ByteAuth.concrete 11 [56],
      PrivateVarint.uint64 Varint64.concrete ByteAuth.concrete word]]

theorem encodedDataMessageSized_base (body : Buffer (BitVec 8)) (word : BitVec 64) :
    encodedDataMessageSized 48 body word = encodedDataMessage body word := rfl

theorem dataMessageBytesSized_length (body : List (BitVec 8)) (word : BitVec 64) (width : Nat) :
    (dataMessageBytesSized body word width).length =
      1 + (lengthPrefix body.length).length + body.length + (1 + width) := by
  simp only [dataMessageBytesSized,List.length_append,List.length_cons,List.length_nil,Varint64.encode_length]
  omega

theorem dataMessageSized_contents (capacity : Nat) (hc : capacity+19<65536) (body : List (BitVec 8))
    (fits : body.length≤capacity) (bounded : body.length<320)
    (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    encodedDataMessageSized capacity (ofContents capacity body) word =
      ofContents (capacity+15) (dataMessageBytesSized body word width) := by
  have prefixLength := lengthPrefix_length body.length
  unfold encodedDataMessageSized
  rw [PrivateProtobuf.bytesField_contents capacity 10 (by omega) body fits bounded,
    timestampField_contents word width hw hl canonical]
  unfold PrivateSend.join
  simp only [List.foldl_cons,List.foldl_nil]
  rw [fromPublic_contents (capacity+15) (by omega) [] (by simp)]
  rw [append_contents (capacity+15) (capacity+15) (capacity+4) (by omega) []
    ([BitVec.ofNat 8 10]++lengthPrefix body.length++body)
    (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)]
  simp only [List.nil_append]
  exact append_contents (capacity+15) (capacity+15) 11 (by omega) _ _
    (by simp only [List.length_append,List.length_cons,List.length_nil,Varint64.encode_length]; omega)

theorem contentSized_contents (capacity : Nat) (hc : capacity+19<65536) (body : List (BitVec 8))
    (fits : body.length≤capacity) (bounded : body.length≤300)
    (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10
      (encodedDataMessageSized capacity (ofContents capacity body) word) =
    ofContents (capacity+15+4) (contentBytesSized body word width) := by
  have prefixLength := lengthPrefix_length body.length
  have total := dataMessageBytesSized_length body word width
  rw [dataMessageSized_contents capacity hc body fits (by omega) word width hw hl canonical]
  exact PrivateProtobuf.bytesField_contents (capacity+15) 10 (by omega) _ (by omega) (by omega)

/-- What `buildSized capacity classes` pads, for a body that fits: the padded
buffer is valid and holds the serialized Content, 0x80, then zeros up to
`paddedBytes classes`. `room` is the size-class condition: Content and its
terminator fit the class. -/
theorem paddedSized_contents (capacity classes : Nat) (hc : capacity+19<65536) (hp : paddedBytes classes<65536)
    (body : List (BitVec 8)) (fits : body.length≤capacity) (bounded : body.length≤300)
    (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width)
    (room : (contentBytesSized body word width).length<paddedBytes classes) :
    PrivateSend.join ByteAuth.concrete (paddedBytes classes)
      [PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10
        (encodedDataMessageSized capacity (ofContents capacity body) word),
       PrivateSend.literal ByteAuth.concrete (paddedBytes classes) [128]] =
      ofContents (paddedBytes classes) (contentBytesSized body word width++[128]) := by
  rw [contentSized_contents capacity hc body fits bounded word width hw hl canonical]
  exact iso7816_sized_contents (paddedBytes classes) (capacity+15+4) hp _ room

theorem paddedSized_data (capacity classes : Nat) (hc : capacity+19<65536) (hp : paddedBytes classes<65536)
    (body : List (BitVec 8)) (fits : body.length≤capacity) (bounded : body.length≤300)
    (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width)
    (room : (contentBytesSized body word width).length<paddedBytes classes) :
    (PrivateSend.join ByteAuth.concrete (paddedBytes classes)
      [PrivateProtobuf.bytesField Sha256.concrete ByteAuth.concrete 10
        (encodedDataMessageSized capacity (ofContents capacity body) word),
       PrivateSend.literal ByteAuth.concrete (paddedBytes classes) [128]]).data =
      contentBytesSized body word width ++
        128 :: List.replicate (paddedBytes classes-1-(contentBytesSized body word width).length) 0 := by
  rw [contentSized_contents capacity hc body fits bounded word width hw hl canonical]
  exact iso7816_sized_data (paddedBytes classes) (capacity+15+4) hp _ room

/-- For a body shorter than 128 bytes the sized DataMessage bytes are the ones
stated for the 48-byte path. -/
theorem dataMessageBytesSized_short (body : List (BitVec 8)) (short : body.length<128)
    (word : BitVec 64) (width : Nat) :
    dataMessageBytesSized body word width = dataMessageBytes body word width := by
  simp [dataMessageBytesSized,dataMessageBytes,lengthPrefix_short body.length short]

end TlsMpc.Signal.PrivateTextNotification
