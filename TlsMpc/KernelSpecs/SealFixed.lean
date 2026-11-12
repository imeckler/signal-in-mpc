import TlsMpc.HybridKernels

/-!
Kernel-level specification of `signal-seal-official` and `signal-seal-built`
(`HybridKernel.signalSealFixed … true classes official`): the sealed-sender envelope the
Signal server receives, the gated status, the timestamp and the next conversation record.

New file; it changes no definition and no emitter imports it.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `sealFixedWith`: the kernel's body written once over the operation records (`Aes`,
  `Varint64`, `Sha256`, `ByteAuth`), composing exactly what the kernel composes:
  `SpqrSend.acceptedMask`, `SpqrSend.prepare`, `SealedSenderV1.boundSeal`,
  `TlsProviderGate.gate` (twice) and `ChainSend.selectState`.
* `sealFixed_symbolic`: the kernel's output terms are `sealFixedWith` on the symbolic
  operations, with `Sha256Ripple.ops` (the one-AND-per-bit adder) as the SHA-256 backend.
* `sealFixedWith_map`: `sealFixedWith` commutes with any homomorphism of the four operation
  records (from the existing `_map` lemmas of the parts).
* `signalSealBuilt_spec`: on every input assignment, the kernel's four outputs (`status`,
  `conversation`, `timestamp`, `envelope`) are `sealFixedWith` on the CONCRETE operations
  (`Aes.concrete`, `Varint64.concrete`, `Sha256.concrete`, `ByteAuth.concrete`), applied to the
  values of the kernel's input fields. This covers both deployed names (`official` true:
  `signal-seal-official`; false: `signal-seal-built`).
* `signalSealBuilt_rejects`: when the opened status is 0, the opened envelope is all zero.

What this is NOT: the reference function is the kernel's own composition on concrete values, as
for the `receive-*` kernels. No value theorem for `boundSeal` (that it is libsignal's sealed
sender v1 encryption) and no theorem that `prepare` is the Signal/SPQR message encryption are
proved here (SECURITY_MAP C.2, T7(b)); `SpqrSend.prepare_concrete_correct`,
`acceptedMask_value` and `ChainSend.selectState_accept/_reject` are function-level facts about
the same parts and now compose with this theorem.
-/
namespace TlsMpc.KernelSpecs.SealFixed
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape lookup)

theorem getD_map' (f : B → B') (l : List B) (i : Nat) (d : B) : (l.map f).getD i (f d) = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD]

/-- The staged session block: session bytes with the built text's kind and first 80 content
bytes in their slots. -/
def stagedOf (session text : List B) : List B :=
  (session.drop 0).take 117 ++ (text.drop 1).take 1 ++ (session.drop 118).take 64 ++ (text.drop 2).take 80

/-- The send input the kernel builds from the staged block and the text. -/
def inputOf (zero : B) (staged text : List B) (content : Nat) : SpqrSend.Input B :=
  { version := staged.getD 0 zero, counter := (staged.drop 1).take 4, previous := (staged.drop 5).take 4,
    ratchet := (staged.drop 9).take 32, chainKey := (staged.drop 41).take 32, pqChainKey := (staged.drop 73).take 32,
    pqCounter := (staged.drop 105).take 4, epoch := (staged.drop 109).take 8, kind := staged.getD 117 zero,
    chunkIndex := [], chunkData := [], sender := (staged.drop 118).take 32, receiver := (staged.drop 150).take 32,
    plaintext := (text.drop 2).take content, addresses := [] }

/-- The body of `signalSealFixed` for built text, over any operations. Outputs: status, next
conversation record, timestamp, envelope (released under the status). -/
def sealFixedWith (o : Aes.Ops B) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (zero : B)
    (cert counterWidth previousWidth epochWidth indexWidth content : Nat)
    (record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement : List B) : List (List B) :=
  let shape : Serialization.Shape := ⟨counterWidth, previousWidth, false⟩
  let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 1, false⟩
  let certificate := (record.drop 0).take cert
  let session := (record.drop cert).take (182 + 80)
  let metadata := (record.drop (cert + 182 + 80)).take 57
  let staged := stagedOf session text
  let i := inputOf zero staged text content
  let accepted := SpqrSend.acceptedMask v s a shape pqShape i
  let p := SpqrSend.prepare o v s a shape pqShape i
  let sealed := SealedSenderV1.boundSeal o s a i.receiver ephemeralPublic senderPublic ephemeralAgreement
    staticAgreement certificate p.wire i.sender
  let status := TlsProviderGate.gate a (TlsProviderGate.gate a accepted (sealed.getD 0 zero)) (text.getD 0 zero)
  let next := (staged.drop 0).take 1 ++ ChainSend.selectState a status p.nextCounter i.counter ++
    (staged.drop 5).take 36 ++ ChainSend.selectState a status p.nextChainKey i.chainKey ++
    ChainSend.selectState a status p.nextPqChainKey i.pqChainKey ++
    ChainSend.selectState a status p.nextPqCounter i.pqCounter ++ staged.drop 109
  [[status], certificate ++ next ++ metadata, (text.drop (2 + content)).take 8,
    ByteAuth.release a status (sealed.drop 1)]

/-- Padded content bytes of a built text of `classes` size classes. -/
def contentBytes (classes : Nat) (official : Bool) : Nat :=
  if official then PrivateTextNotification.officialPaddedBytes classes else PrivateTextNotification.paddedBytes classes

def sealInputs (cert classes : Nat) (official : Bool) : List (String × Shape) :=
  [("conversation", Shape.bytes (HybridKernel.conversationBytes cert 80)),
    ("text", .bytes (if official then PrivateTextNotification.officialBuiltBytes classes
      else PrivateTextNotification.builtBytes classes)),
    ("ephemeralPublic", .word), ("senderPublic", .word), ("ephemeralAgreement", .word), ("staticAgreement", .word)]

theorem sealFixed_symbolic (cert counterWidth previousWidth epochWidth indexWidth classes : Nat) (official : Bool) :
    let get := lookup (sealInputs cert classes official)
    (HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes official).outputs.map
        (·.value) =
      sealFixedWith Aes.symbolic Varint64.symbolic Sha256Ripple.ops ByteAuth.symbolic (.const 0)
        cert counterWidth previousWidth epochWidth indexWidth (contentBytes classes official)
        (get "conversation") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
        (get "staticAgreement") := by
  rfl

section Refinement
variable {V W V' W' : Type} {o : Aes.Ops B} {o' : Aes.Ops B'} {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} {fv : V → V'}
  (ho : Aes.Hom o o' f) (hv : Varint64.Hom v v' f fv) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)

theorem stagedOf_map (session text : List B) :
    (stagedOf session text).map f = stagedOf (session.map f) (text.map f) := by
  simp only [stagedOf, List.map_append, List.map_take, List.map_drop]

theorem inputOf_map (zero : B) (staged text : List B) (content : Nat) :
    (inputOf zero staged text content).map f = inputOf (f zero) (staged.map f) (text.map f) content := by
  simp only [inputOf, SpqrSend.Input.map, List.map_take, List.map_drop, getD_map', List.map_nil]

include ho hv hs ha

theorem sealFixedWith_map (zero : B) (cert counterWidth previousWidth epochWidth indexWidth content : Nat)
    (record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement : List B) :
    (sealFixedWith o v s a zero cert counterWidth previousWidth epochWidth indexWidth content
        record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement).map (List.map f) =
      sealFixedWith o' v' s' a' (f zero) cert counterWidth previousWidth epochWidth indexWidth content
        (record.map f) (text.map f) (ephemeralPublic.map f) (senderPublic.map f) (ephemeralAgreement.map f)
        (staticAgreement.map f) := by
  have fGetD : ∀ (l : List B) (k : Nat) (d : B), f (l.getD k d) = (l.map f).getD k (f d) :=
    fun l k d => (getD_map' f l k d).symm
  have counterEq : ∀ i : SpqrSend.Input B, i.counter.map f = (i.map f).counter := fun _ => rfl
  have chainEq : ∀ i : SpqrSend.Input B, i.chainKey.map f = (i.map f).chainKey := fun _ => rfl
  have pqChainEq : ∀ i : SpqrSend.Input B, i.pqChainKey.map f = (i.map f).pqChainKey := fun _ => rfl
  have pqCounterEq : ∀ i : SpqrSend.Input B, i.pqCounter.map f = (i.map f).pqCounter := fun _ => rfl
  have receiverEq : ∀ i : SpqrSend.Input B, i.receiver.map f = (i.map f).receiver := fun _ => rfl
  have senderEq : ∀ i : SpqrSend.Input B, i.sender.map f = (i.map f).sender := fun _ => rfl
  have prepareEq := fun sh pq i => SpqrSend.prepare_map ho hv hs ha sh pq i
  have wireEq : ∀ sh pq (i : SpqrSend.Input B), (SpqrSend.prepare o v s a sh pq i).wire.map f =
      (SpqrSend.prepare o' v' s' a' sh pq (i.map f)).wire := fun sh pq i => congrArg SpqrSend.Prepared.wire (prepareEq sh pq i)
  have nextChainEq : ∀ sh pq (i : SpqrSend.Input B), (SpqrSend.prepare o v s a sh pq i).nextChainKey.map f =
      (SpqrSend.prepare o' v' s' a' sh pq (i.map f)).nextChainKey :=
    fun sh pq i => congrArg SpqrSend.Prepared.nextChainKey (prepareEq sh pq i)
  have nextCounterEq : ∀ sh pq (i : SpqrSend.Input B), (SpqrSend.prepare o v s a sh pq i).nextCounter.map f =
      (SpqrSend.prepare o' v' s' a' sh pq (i.map f)).nextCounter :=
    fun sh pq i => congrArg SpqrSend.Prepared.nextCounter (prepareEq sh pq i)
  have nextPqChainEq : ∀ sh pq (i : SpqrSend.Input B), (SpqrSend.prepare o v s a sh pq i).nextPqChainKey.map f =
      (SpqrSend.prepare o' v' s' a' sh pq (i.map f)).nextPqChainKey :=
    fun sh pq i => congrArg SpqrSend.Prepared.nextPqChainKey (prepareEq sh pq i)
  have nextPqCounterEq : ∀ sh pq (i : SpqrSend.Input B), (SpqrSend.prepare o v s a sh pq i).nextPqCounter.map f =
      (SpqrSend.prepare o' v' s' a' sh pq (i.map f)).nextPqCounter :=
    fun sh pq i => congrArg SpqrSend.Prepared.nextPqCounter (prepareEq sh pq i)
  simp only [sealFixedWith, List.map_cons, List.map_nil, List.map_append, List.map_take, List.map_drop,
    ByteAuth.release_map ha, TlsProviderGate.gate_map ha, ChainSend.selectState_map ha, fGetD,
    SpqrSend.acceptedMask_map hv hs ha, SealedSenderV1.boundSeal_map ho hs ha, counterEq, chainEq, pqChainEq,
    pqCounterEq, receiverEq, senderEq, wireEq, nextChainEq, nextCounterEq, nextPqChainEq, nextPqCounterEq,
    inputOf_map, stagedOf_map]

end Refinement

/-- **`signal-seal-official` / `signal-seal-built`** on values: the kernel's four outputs are the
kernel's composition on concrete operations, applied to the values of its input fields. -/
theorem signalSealBuilt_spec (cert counterWidth previousWidth epochWidth indexWidth classes : Nat) (official : Bool)
    (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (sealInputs cert classes official) name).map (BVExpr.eval assign)
    (HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes official).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealFixedWith Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete 0
        cert counterWidth previousWidth epochWidth indexWidth (contentBytes classes official)
        (get "conversation") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
        (get "staticAgreement") := by
  intro get
  have h := sealFixedWith_map (Aes.evaluationHom assign) (Varint64.evaluationHom assign)
    (Sha256Ripple.evaluationHom assign) (ByteAuth.evaluationHom assign) (.const 0)
    cert counterWidth previousWidth epochWidth indexWidth (contentBytes classes official)
    (lookup (sealInputs cert classes official) "conversation") (lookup (sealInputs cert classes official) "text")
    (lookup (sealInputs cert classes official) "ephemeralPublic") (lookup (sealInputs cert classes official) "senderPublic")
    (lookup (sealInputs cert classes official) "ephemeralAgreement")
    (lookup (sealInputs cert classes official) "staticAgreement")
  rw [← sealFixed_symbolic, List.map_map] at h
  exact h

/-- A refused send (opened status 0) opens an all-zero envelope. -/
theorem sealFixedWith_rejects (cert counterWidth previousWidth epochWidth indexWidth content : Nat)
    (record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement : List (BitVec 8))
    (refused : (sealFixedWith Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete 0 cert counterWidth
      previousWidth epochWidth indexWidth content record text ephemeralPublic senderPublic ephemeralAgreement
      staticAgreement).getD 0 [] = [0]) :
    ∀ byte ∈ (sealFixedWith Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete 0 cert counterWidth
      previousWidth epochWidth indexWidth content record text ephemeralPublic senderPublic ephemeralAgreement
      staticAgreement).getD 3 [], byte = 0 := by
  simp only [sealFixedWith, List.getD_cons_zero, List.cons.injEq, and_true] at refused
  simp only [sealFixedWith, List.getD_cons_succ, List.getD_cons_zero]
  rw [refused, ByteAuth.release_reject]
  intro byte member
  exact List.eq_of_mem_replicate member

theorem signalSealBuilt_rejects (cert counterWidth previousWidth epochWidth indexWidth classes : Nat) (official : Bool)
    (assign : BVExpr.Assignment)
    (refused : ((HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes
      official).outputs.map (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes
      official).outputs.map (fun field => field.value.map (BVExpr.eval assign))).getD 3 [], byte = 0 := by
  rw [signalSealBuilt_spec] at refused ⊢
  exact sealFixedWith_rejects _ _ _ _ _ _ _ _ _ _ _ _ refused

#print axioms sealFixed_symbolic
#print axioms sealFixedWith_map
#print axioms signalSealBuilt_spec
#print axioms sealFixedWith_rejects
#print axioms signalSealBuilt_rejects

end TlsMpc.KernelSpecs.SealFixed
