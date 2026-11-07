import TlsMpc.Signal.DhRatchet
import TlsMpc.Signal.SkippedKeys

/-! Both halves of a newly selected DH ratchet. Inputs include the two canonical
shared X25519 agreements and a fresh private/public key pair; their provenance
is an explicit composition boundary. The old sender state is replaced only when
auth=255 and both agreements are nonzero. The new receiving chain is released as
a candidate for the bounded authenticated receive transaction. Receiver-chain
selection/retention and fresh joint entropy are outside this module. -/
namespace TlsMpc.Signal.RatchetStep
open Std.Tactic.BVDecide

/-- root32, sender private32, sender public32, sender chain32, sender index4,
previous counter4. Public layout, entirely shared contents. -/
structure State (B : Type) where
  root : List B
  privateKey : List B
  publicKey : List B
  chain : List B
  index : List B
  previous : List B

def State.map (f : B → B') (x : State B) : State B' :=
  ⟨x.root.map f, x.privateKey.map f, x.publicKey.map f, x.chain.map f, x.index.map f, x.previous.map f⟩

def State.bytes (x : State B) : List B :=
  x.root ++ x.privateKey ++ x.publicKey ++ x.chain ++ x.index ++ x.previous

/-- Rust current_index.saturating_sub(1), encoded big endian. -/
def previousCounter (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (index : List B) : List B :=
  let nonzero := a.not (ByteAuth.equalMask a index (List.replicate 4 (a.const 0)))
  ByteAuth.release a nonzero ((List.range 4).map (s.unpack (s.add (Varint.pack s a index) (s.wordConst 0xffffffff))))

/-- The receiver half feeds its new root into the sender half. -/
def derive (s : Sha256.Ops B W) (root receiveAgreement sendAgreement : List B) : List B × List B × List B :=
  let receive := DhRatchet.materialFast s root receiveAgreement
  let send := DhRatchet.materialFast s (receive.take 32) sendAgreement
  (send.take 32, receive.drop 32, send.drop 32)

def acceptedMask (a : ByteAuth.Ops B) (auth : B) (receiveAgreement sendAgreement : List B) : B :=
  a.and (ByteAuth.eqMask a auth (a.const 255))
    (a.and (DhRatchet.agreementMask a receiveAgreement) (DhRatchet.agreementMask a sendAgreement))

/-- Old state survives rejection byte-for-byte; receiver chain/counter are zero.
Caller must supply a fresh already-clamped private key and its actual public key. -/
def step (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (auth : B) (old : State B)
    (newPrivate newPublic receiveAgreement sendAgreement : List B) : List B :=
  let accepted := acceptedMask a auth receiveAgreement sendAgreement
  let (root,receiver,sender) := derive s old.root receiveAgreement sendAgreement
  let next : State B := ⟨root,newPrivate,newPublic,sender,List.replicate 4 (a.const 0),previousCounter s a old.index⟩
  accepted :: (ChainSend.selectState a accepted next.bytes old.bytes ++
    ByteAuth.release a accepted receiver ++ List.replicate 4 (a.const 0))

section
variable {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

theorem bytes_map (x : State B) : x.bytes.map f = (x.map f).bytes := by
  simp only [State.bytes, State.map, List.map_append]
include hs ha in
theorem previousCounter_map (index : List B) : (previousCounter s a index).map f = previousCounter s' a' (index.map f) := by
  simp only [previousCounter, ByteAuth.release_map ha, ha.not, ByteAuth.equalMask_map ha,
    List.map_replicate, ha.const, List.map_map, Function.comp_def, hs.unpack, hs.add, Varint.pack_map hs ha, hs.wordConst]
include hs in
theorem derive_map (root receiveAgreement sendAgreement : List B) :
    let r := derive s root receiveAgreement sendAgreement
    (r.1.map f,r.2.1.map f,r.2.2.map f) = derive s' (root.map f) (receiveAgreement.map f) (sendAgreement.map f) := by
  simp only [derive, DhRatchet.materialFast_map hs, List.map_take, List.map_drop]
include ha in
theorem acceptedMask_map (auth : B) (receiveAgreement sendAgreement : List B) :
    f (acceptedMask a auth receiveAgreement sendAgreement) = acceptedMask a' (f auth) (receiveAgreement.map f) (sendAgreement.map f) := by
  simp only [acceptedMask, ha.and, ByteAuth.eqMask_map ha, ha.const, DhRatchet.agreementMask_map ha]
include hs ha in
theorem step_map (auth : B) (old : State B) (newPrivate newPublic receiveAgreement sendAgreement : List B) :
    (step s a auth old newPrivate newPublic receiveAgreement sendAgreement).map f =
      step s' a' (f auth) (old.map f) (newPrivate.map f) (newPublic.map f) (receiveAgreement.map f) (sendAgreement.map f) := by
  simp only [step, derive, List.map_cons, List.map_append, ChainSend.selectState_map ha,
    acceptedMask_map ha, ByteAuth.release_map ha, DhRatchet.materialFast_map hs,
    List.map_drop, List.map_take, List.map_replicate, ha.const, State.bytes, State.map,
    List.map_append, previousCounter_map hs ha]
end

theorem step_reject (auth : BitVec 8) (old : State (BitVec 8)) (newPrivate newPublic receiveAgreement sendAgreement : List (BitVec 8))
    (h : auth ≠ 255) :
    step Sha256.concrete ByteAuth.concrete auth old newPrivate newPublic receiveAgreement sendAgreement =
      0 :: (old.bytes ++ List.replicate 36 0) := by
  have hmask : acceptedMask ByteAuth.concrete auth receiveAgreement sendAgreement = 0 := by
    simp only [acceptedMask, ByteAuth.eqMask_value]
    change (if auth = 255 then 255 else 0) &&& _ = _
    rw [if_neg h]
    exact BitVec.zero_and
  simp only [step, hmask, ChainSend.selectState_reject, ByteAuth.release_reject, derive,
    DhRatchet.materialFast_correct, List.length_drop, DhRatchet.material_length]
  change 0 :: ((old.bytes ++ List.replicate 32 0) ++ List.replicate 4 0) = _
  rw [List.append_assoc, List.replicate_append_replicate]

theorem step_zero_agreement (auth : BitVec 8) (old : State (BitVec 8))
    (newPrivate newPublic receiveAgreement sendAgreement : List (BitVec 8))
    (h : receiveAgreement = List.replicate 32 0 ∨ sendAgreement = List.replicate 32 0) :
    step Sha256.concrete ByteAuth.concrete auth old newPrivate newPublic receiveAgreement sendAgreement =
      0 :: (old.bytes ++ List.replicate 36 0) := by
  have hmask : acceptedMask ByteAuth.concrete auth receiveAgreement sendAgreement = 0 := by
    rcases h with h | h
    · simp only [acceptedMask, h, DhRatchet.agreementMask_value, ne_eq, not_true_eq_false, if_false]
      exact (congrArg (fun x : BitVec 8 => ByteAuth.eqMask ByteAuth.concrete auth 255 &&& x) BitVec.zero_and).trans BitVec.and_zero
    · simp only [acceptedMask, h, DhRatchet.agreementMask_value, ne_eq, not_true_eq_false, if_false]
      exact (congrArg (fun x : BitVec 8 => ByteAuth.eqMask ByteAuth.concrete auth 255 &&& x) BitVec.and_zero).trans BitVec.and_zero
  simp only [step, hmask, ChainSend.selectState_reject, ByteAuth.release_reject, derive,
    DhRatchet.materialFast_correct, List.length_drop, DhRatchet.material_length]
  change 0 :: ((old.bytes ++ List.replicate 32 0) ++ List.replicate 4 0) = _
  rw [List.append_assoc, List.replicate_append_replicate]

theorem step_length (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (auth : B) (old : State B)
    (newPrivate newPublic receiveAgreement sendAgreement : List B) :
    (step s a auth old newPrivate newPublic receiveAgreement sendAgreement).length = 1 + old.bytes.length + 36 := by
  simp [step, ChainSend.selectState, ByteAuth.release, derive, DhRatchet.materialFast_correct, DhRatchet.material_length]
  omega

theorem compiled_step_correct (auth : BVExpr 8) (old : State (BVExpr 8))
    (newPrivate newPublic receiveAgreement sendAgreement : List (BVExpr 8)) (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (step Sha256.symbolic ByteAuth.symbolic auth old newPrivate newPublic receiveAgreement sendAgreement).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (step Sha256.symbolic ByteAuth.symbolic auth old newPrivate newPublic receiveAgreement sendAgreement))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (step Sha256.symbolic ByteAuth.symbolic auth old newPrivate newPublic receiveAgreement sendAgreement))).vec.get bit hi)) =
      (ByteCircuit.joinValue (step Sha256.concrete ByteAuth.concrete (BVExpr.eval assign auth) (old.map (BVExpr.eval assign))
        (newPrivate.map (BVExpr.eval assign)) (newPublic.map (BVExpr.eval assign))
        (receiveAgreement.map (BVExpr.eval assign)) (sendAgreement.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct, step_map (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.RatchetStep
