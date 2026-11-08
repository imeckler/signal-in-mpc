import TlsMpc.Signal.PrivateNewDhReceiveProofs

/-! Parse once: exact private summary joins the point/DH stage and the crypto
transaction without duplicating the large Signal parser or any cryptography.
Native code must produce this summary from the actual original wire. -/
namespace TlsMpc.Signal.PrivateNewDhReceiveSplit
open Std.Tactic.BVDecide PrivateNewDhReceive

structure Summary (B V : Type) where
  valid : B
  remote : List B
  counter : V
  cipherOffset : V
  cipherLength : V
  pqOffset : V
  pqLength : V
  pqPresent : B
  addressPresent : B

def Summary.map (f : B → B') (fv : V → V') (x : Summary B V) : Summary B' V' :=
  ⟨f x.valid,x.remote.map f,fv x.counter,fv x.cipherOffset,fv x.cipherLength,
   fv x.pqOffset,fv x.pqLength,f x.pqPresent,f x.addressPresent⟩

def fromParsed (o : Word64.Ops B V) (a : ByteAuth.Ops B) (p : PrivateProtoParseV1.Parsed B V) : Summary B V :=
  ⟨p.valid,p.metadata.take 32,(ProtoParse.getField o a p.state 1).scalar,
   (ProtoParse.getField o a p.state 3).offset,(ProtoParse.getField o a p.state 3).length,
   (ProtoParse.getField o a p.state 4).offset,(ProtoParse.getField o a p.state 4).length,
   (ProtoParse.getField o a p.state 4).present,(ProtoParse.getField o a p.state 5).present⟩

def encode (o : Word64.Ops B V) (x : Summary B V) : List B :=
  x.valid :: (x.remote ++ Word64.bytes o x.counter ++ Word64.bytes o x.cipherOffset ++
    Word64.bytes o x.cipherLength ++ Word64.bytes o x.pqOffset ++ Word64.bytes o x.pqLength ++
    [x.pqPresent,x.addressPresent])

def decode (o : Word64.Ops B V) (a : ByteAuth.Ops B) (raw : List B) : Summary B V :=
  let word := fun start => o.pack ((raw.drop start).take 8)
  ⟨OpenResult.get a raw 0,(raw.drop 1).take 32,word 33,word 41,word 49,word 57,word 65,
    OpenResult.get a raw 73,OpenResult.get a raw 74⟩

def parseSummary (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (a : ByteAuth.Ops B)
    (encodedWire : List B) : Summary B V :=
  fromParsed o a (PrivateProtoParseV1.parse d o a (encodedWire.drop 3)
    (OpenResult.get a encodedWire 1) (OpenResult.get a encodedWire 2) (OpenResult.get a encodedWire 0))

def parseSummaryBytes (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (a : ByteAuth.Ops B)
    (encodedWire : List B) : List B := encode o (parseSummary d o a encodedWire)

def pqWireSummary (o : Word64.Ops B V) (a : ByteAuth.Ops B) (wire : List B) (x : Summary B V) : List B :=
  let valid := a.and x.valid (a.and x.pqPresent (o.ule x.pqLength (o.const 32)))
  valid :: ((Word64.bytes o x.pqLength).drop 6 ++ SliceAt.readCore o a 32 (wire.drop 1) x.pqOffset x.pqLength)

def receiveSummary (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (old : RatchetStep.State B)
    (receivers : List (ReceiverStore.Entry B 0)) (oldPq sender receiver : List B)
    (newPrivate newPublic receiveAgreement sendAgreement encodedWire : List B) (summary : Summary B V) : List B :=
  let wire := encodedWire.drop 3
  let remote := summary.remote
  let pq := ActiveSpqrReceive.prepare d s a (oldPq.take 8) ((oldPq.drop 8).take 32)
    ((oldPq.drop 40).take 4) (pqWireSummary o a wire summary)
  let derived := RatchetStep.derive s old.root receiveAgreement sendAgreement
  let material := Symmetric.deriveFast s derived.2.1 (pq.drop 45)
  let ciphertext := SliceAt.readCore o a 96 (wire.drop 1) summary.cipherOffset summary.cipherLength
  let opened := CbcOpen.openCore aes a material.material.cipherKey material.material.iv ciphertext
  let known := ReceiverStore.lookup a (listBytes a remote) receivers
  let shape := if receivers.length=5 ∧ oldPq.length=44 ∧ encodedWire.length=259 ∧
      old.root.length=32 ∧ old.privateKey.length=32 ∧ old.publicKey.length=32 ∧ old.chain.length=32 ∧
      old.index.length=4 ∧ old.previous.length=4 ∧ sender.length=32 ∧ receiver.length=32 ∧
      newPrivate.length=32 ∧ newPublic.length=32 ∧ receiveAgreement.length=32 ∧ sendAgreement.length=32
    then a.const 255 else a.const 0
  let accepted := conjunction a [shape,summary.valid,OpenResult.get a pq 0,
    PrivateMessageMac.verify o s a wire.length material.material.macKey sender receiver encodedWire,
    OpenResult.get a opened 0,
    Word64.eq o a (o.band summary.counter (o.const 4294967295)) (o.const 0),
    Word64.eq o a summary.cipherLength (o.const 96),
    a.not summary.addressPresent,
    ByteAuth.equalMask a ((opened.drop 1).take 8) (OpenResult.encodeLength a 80),
    a.not (ByteAuth.eqMask a known.valid (a.const 255)),
    ByteAuth.eqMask a (OpenResult.get a wire 0) (a.const 68),
    DhRatchet.agreementMask a receiveAgreement,DhRatchet.agreementMask a sendAgreement]
  let next : RatchetStep.State B := ⟨derived.1,newPrivate,newPublic,derived.2.2,
    List.replicate 4 (a.const 0),RatchetStep.previousCounter s a old.index⟩
  selectResult a accepted old receivers oldPq next remote material.nextChainKey (pq.drop 1) (opened.drop 9)

theorem split_agreement (d : VarintDecode.Spqr.Ops B V) (o : Word64.Ops B V) (aes : AesInverse.Ops B)
    (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (old : RatchetStep.State B)
    (receivers : List (ReceiverStore.Entry B 0)) (oldPq sender receiver : List B)
    (newPrivate newPublic receiveAgreement sendAgreement encodedWire : List B) :
    let p := PrivateProtoParseV1.parse d o a (encodedWire.drop 3) (OpenResult.get a encodedWire 1)
      (OpenResult.get a encodedWire 2) (OpenResult.get a encodedWire 0)
    receiveSummary d o aes s a old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement encodedWire
      (fromParsed o a p)=
    PrivateNewDhReceive.receive d o aes s a old receivers oldPq sender receiver newPrivate newPublic receiveAgreement sendAgreement encodedWire := by
  simp only [receiveSummary,fromParsed,pqWireSummary,PrivateNewDhReceive.receive,PrivateNewDhReceive.pqWire]
end TlsMpc.Signal.PrivateNewDhReceiveSplit
