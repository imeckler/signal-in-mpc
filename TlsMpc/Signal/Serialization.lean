import TlsMpc.Signal.Varint
import TlsMpc.Signal.ReceiveSpec

/-! Bounded send serialization matching the fields set by the pinned
SignalMessage::new. Field presence and encoded counter widths are public.
The counters, version, ratchet key, ciphertext, PQ bytes and typed address
bytes are secret. A secret validity mask rejects noncanonical counter widths
and invalid typed address encodings. This is not a protobuf parser. -/

namespace TlsMpc.Signal.Serialization
open Std.Tactic.BVDecide

structure Shape where
  counterWidth : Nat
  previousWidth : Nat
  withAddresses : Bool
  deriving DecidableEq

def Shape.valid (shape : Shape) : Prop :=
  1 ≤ shape.counterWidth ∧ shape.counterWidth ≤ 5 ∧
  1 ≤ shape.previousWidth ∧ shape.previousWidth ≤ 5

instance (shape : Shape) : Decidable shape.valid := inferInstanceAs (Decidable (_ ∧ _))

/-- Exactly `((message_version & 0xF) << 4) | CURRENT_VERSION` with the
pinned CURRENT_VERSION = 4. The Rust constructor does not reject other
version inputs; its parser has a separate version policy. -/
def versionByte (a : ByteAuth.Ops B) (version : B) : B :=
  a.xor (a.const 4) (a.xor
    (a.and (a.maskBit version 0) (a.const 16)) (a.xor
    (a.and (a.maskBit version 1) (a.const 32)) (a.xor
    (a.and (a.maskBit version 2) (a.const 64))
    (a.and (a.maskBit version 3) (a.const 128)))))

/-- The tag is an already encoded one-byte protobuf key (10, 34, 42, 50). -/
def bytesField (a : ByteAuth.Ops B) (tag : Nat) (bytes : List B) : List B :=
  a.const tag :: (Varint.publicNat a bytes.length ++ bytes)

def addressField (a : ByteAuth.Ops B) (shape : Shape) (addresses : List B) : List B :=
  if shape.withAddresses then bytesField a 50 addresses else []

def pqField (a : ByteAuth.Ops B) (pq : List B) : List B :=
  if pq.length = 0 then [] else bytesField a 42 pq

/-- `Some(0)` scalar counters are emitted, as in the actual optional proto2
fields. PQ is absent exactly when empty; address presence is a public profile
for the already parsed typed ProtocolAddresses supplied to the constructor. -/
def content (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (shape : Shape)
    (version : B) (counter previous ratchet ciphertext pq addresses : List B) : List B :=
  [versionByte a version] ++ bytesField a 10 (a.const 5 :: ratchet) ++
    (a.const 16 :: Varint.encode s a (Varint.pack s a counter) shape.counterWidth) ++
    (a.const 24 :: Varint.encode s a (Varint.pack s a previous) shape.previousWidth) ++
    bytesField a 34 ciphertext ++ pqField a pq ++ addressField a shape addresses

def acceptedMask (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (shape : Shape)
    (counter previous addresses : List B) : B :=
  a.and (Varint.accepts s a (Varint.pack s a counter) shape.counterWidth)
    (a.and (Varint.accepts s a (Varint.pack s a previous) shape.previousWidth)
      (if shape.withAddresses then Receive.expectedAddressMask a addresses else a.const 255))

/-- Secret status followed by the fixed-profile serialized content. Every
byte is zero on a failed secret width/address check. -/
def encodeCore (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (shape : Shape)
    (version : B) (counter previous ratchet ciphertext pq addresses : List B) : List B :=
  let accepted := acceptedMask s a shape counter previous addresses
  accepted :: ByteAuth.release a accepted (content s a shape version counter previous ratchet ciphertext pq addresses)

def inputShape (shape : Shape) (counter previous ratchet ciphertext pq addresses : List B) : Prop :=
  shape.valid ∧ counter.length = 4 ∧ previous.length = 4 ∧ ratchet.length = 32 ∧
  addresses.length = (if shape.withAddresses then 36 else 0) ∧
  ciphertext.length < 2 ^ 61 ∧ pq.length < 2 ^ 61

instance (shape : Shape) (counter previous ratchet ciphertext pq addresses : List B) :
    Decidable (inputShape shape counter previous ratchet ciphertext pq addresses) :=
  inferInstanceAs (Decidable (_ ∧ _))

def encodeChecked (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (shape : Shape)
    (version : B) (counter previous ratchet ciphertext pq addresses : List B) : Option (List B) :=
  if inputShape shape counter previous ratchet ciphertext pq addresses then
    some (encodeCore s a shape version counter previous ratchet ciphertext pq addresses)
  else none

section Refinement
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
  (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem versionByte_map (version : B) : f (versionByte a version) = versionByte a' (f version) := by
  simp only [versionByte, ha.xor, ha.const, ha.and, ha.maskBit]

theorem bytesField_map (tag : Nat) (bytes : List B) :
    (bytesField a tag bytes).map f = bytesField a' tag (bytes.map f) := by
  simp only [bytesField, List.map_cons, List.map_append, ha.const,
    Varint.publicNat_map ha, List.length_map]

theorem addressField_map (shape : Shape) (addresses : List B) :
    (addressField a shape addresses).map f = addressField a' shape (addresses.map f) := by
  simp only [addressField]
  split <;> simp_all only [bytesField_map ha, List.map_nil]

theorem pqField_map (pq : List B) : (pqField a pq).map f = pqField a' (pq.map f) := by
  simp only [pqField, List.length_map]
  split <;> simp_all only [bytesField_map ha, List.map_nil]

include hs

theorem content_map (shape : Shape) (version : B)
    (counter previous ratchet ciphertext pq addresses : List B) :
    (content s a shape version counter previous ratchet ciphertext pq addresses).map f =
      content s' a' shape (f version) (counter.map f) (previous.map f) (ratchet.map f)
        (ciphertext.map f) (pq.map f) (addresses.map f) := by
  simp only [content, List.map_append, List.map_cons, List.map_nil, versionByte_map ha,
    bytesField_map ha, ha.const, Varint.encode_map hs ha, Varint.pack_map hs ha,
    pqField_map ha, addressField_map ha]

theorem acceptedMask_map (shape : Shape) (counter previous addresses : List B) :
    f (acceptedMask s a shape counter previous addresses) =
      acceptedMask s' a' shape (counter.map f) (previous.map f) (addresses.map f) := by
  simp only [acceptedMask, ha.and, Varint.accepts_map hs ha, Varint.pack_map hs ha]
  split <;> simp_all only [Receive.expectedAddressMask_map ha, ha.const]

theorem encodeCore_map (shape : Shape) (version : B)
    (counter previous ratchet ciphertext pq addresses : List B) :
    (encodeCore s a shape version counter previous ratchet ciphertext pq addresses).map f =
      encodeCore s' a' shape (f version) (counter.map f) (previous.map f) (ratchet.map f)
        (ciphertext.map f) (pq.map f) (addresses.map f) := by
  simp only [encodeCore, List.map_cons, ByteAuth.release_map ha,
    acceptedMask_map hs ha, content_map hs ha]

theorem encodeChecked_map (shape : Shape) (version : B)
    (counter previous ratchet ciphertext pq addresses : List B) :
    (encodeChecked s a shape version counter previous ratchet ciphertext pq addresses).map (List.map f) =
      encodeChecked s' a' shape (f version) (counter.map f) (previous.map f) (ratchet.map f)
        (ciphertext.map f) (pq.map f) (addresses.map f) := by
  simp only [encodeChecked, inputShape, List.length_map]
  split <;> simp [encodeCore_map hs ha]

end Refinement

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem versionByte_value (version : BitVec 8) :
    versionByte ByteAuth.concrete version = ((version &&& 15) <<< 4) ||| 4 := by
  have h : ∀ version : BitVec 8,
      versionByte ByteAuth.concrete version = ((version &&& 15) <<< 4) ||| 4 := by decide +kernel
  exact h version

def accepted (shape : Shape) (counter previous addresses : List (BitVec 8)) : Prop :=
  Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete
    (Varint.pack Sha256.concrete ByteAuth.concrete counter)) shape.counterWidth ∧
  Varint.canonicalGroups (Varint.groups Sha256.concrete ByteAuth.concrete
    (Varint.pack Sha256.concrete ByteAuth.concrete previous)) shape.previousWidth ∧
  (shape.withAddresses = true → Receive.validExpectedAddresses addresses)

instance (shape : Shape) (counter previous addresses : List (BitVec 8)) :
    Decidable (accepted shape counter previous addresses) := inferInstanceAs (Decidable (_ ∧ _))

theorem acceptedMask_value (shape : Shape) (counter previous addresses : List (BitVec 8)) :
    acceptedMask Sha256.concrete ByteAuth.concrete shape counter previous addresses =
      if accepted shape counter previous addresses then 255 else 0 := by
  have hconst : ByteAuth.concrete.const 255 = (255 : BitVec 8) := rfl
  have hand (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  cases hb : shape.withAddresses
  · simp only [acceptedMask, Varint.accepts, Varint.widthMask_value, hb,
      Bool.false_eq_true, if_false, hconst, hand, Receive.mask_and,
      accepted, false_implies, and_true]
  · simp only [acceptedMask, Varint.accepts, Varint.widthMask_value, hb,
      if_true, Receive.expectedAddressMask_value, Receive.mask_and,
      accepted, true_implies]

theorem encodeCore_concrete_correct (shape : Shape) (version : BitVec 8)
    (counter previous ratchet ciphertext pq addresses : List (BitVec 8)) :
    encodeCore Sha256.concrete ByteAuth.concrete shape version counter previous ratchet ciphertext pq addresses =
      if accepted shape counter previous addresses then
        255 :: content Sha256.concrete ByteAuth.concrete shape version counter previous ratchet ciphertext pq addresses
      else List.replicate (1 + (content Sha256.concrete ByteAuth.concrete shape version
        counter previous ratchet ciphertext pq addresses).length) 0 := by
  simp only [encodeCore, acceptedMask_value]
  split
  · rw [ByteAuth.release_accept]
  · rw [ByteAuth.release_reject]
    rw [Nat.add_comm 1, List.replicate_succ]

theorem compiled_encodeCore_correct (shape : Shape) (version : BVExpr 8)
    (counter previous ratchet ciphertext pq addresses : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (encodeCore Sha256.symbolic ByteAuth.symbolic shape version
      counter previous ratchet ciphertext pq addresses).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (encodeCore Sha256.symbolic ByteAuth.symbolic shape version
          counter previous ratchet ciphertext pq addresses))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (encodeCore Sha256.symbolic ByteAuth.symbolic shape version
          counter previous ratchet ciphertext pq addresses))).vec.get index hi)) =
      (ByteCircuit.joinValue (encodeCore Sha256.concrete ByteAuth.concrete shape (version.eval assign)
        (counter.map (BVExpr.eval assign)) (previous.map (BVExpr.eval assign)) (ratchet.map (BVExpr.eval assign))
        (ciphertext.map (BVExpr.eval assign)) (pq.map (BVExpr.eval assign)) (addresses.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, encodeCore_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.Serialization
