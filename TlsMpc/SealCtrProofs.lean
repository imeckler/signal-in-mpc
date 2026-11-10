import TlsMpc.ContactKernelsProofs
import TlsMpc.GhashShares

/-!
The split seal (`tlsSealCtr` then `gcmTag`, TlsMpc/HybridKernels.lean) against
the full record seal `TlsRecord.sealCore`.

* `sealCore_decompose`: the full seal is header ‖ CTR ciphertext ‖
  (GHASH ⊕ pad), with GHASH the repository's `Ghash.hash` under
  `H = AES_K(0)` of GCM's authenticated blocks for that header and ciphertext
  (`ghashOf`), and the pad `AES_K(nonce ‖ 1)` (`padOf`).
* `tlsSealCtr_spec`, `gcmTag_spec`, `gcmCheck_spec`: the kernels' outputs on
  values.
* `sealCtr_with_tag_is_seal`: header ‖ ciphertext from `tlsSealCtr`, followed by
  the tag `gcmTag` computes from that kernel's pad and two halves, is exactly
  `TlsRecord.sealCore` of the same key, IV, sequence, content, kind and padding,
  WHENEVER the two halves XOR to `ghashOf` of that header and ciphertext.
* `shared_halves_are_ghash`: that hypothesis holds when the halves are the two
  parties' local tags (`GhashShares.localTag`) over GCM's authenticated blocks
  with honest shares of the descending key powers. This inherits the hypothesis
  of `GhashShares.halves_are_ghash`: commutativity and associativity of the
  repository's GF(2^128) multiplication (`GhashShares.Laws`). That hypothesis is
  discharged in `TlsMpc/GcmShareKernelsProofs.lean`
  (`shared_halves_are_ghash_proved`, `scheduled_halves_are_ghash`).

Not covered: that the engines' halves are computed as `localTag` in this byte
order from honestly produced shares (that code is outside Lean).
-/
namespace TlsMpc.HybridKernel
open Std.Tactic.BVDecide
open Signal

/-- The GHASH key `H = AES_K(0)` as a field element. -/
def hashKeyOf (traffic : List (BitVec 8)) : BitVec 128 :=
  Gcm.concrete.pack (Aes.encryptExpanded Gcm.concrete.aes 10 (expandedOf traffic) (Gcm.zeros Gcm.concrete 16))

/-- The GHASH value GCM's tag computation uses for this associated data and
ciphertext, as 16 bytes. -/
def ghashOf (traffic aad ciphertext : List (BitVec 8)) : List (BitVec 8) :=
  Gcm.concrete.unpack (Ghash.hash Gcm.concrete.field (hashKeyOf traffic) (Gcm.authInput Gcm.concrete aad ciphertext))

/-- The full record seal is header ‖ ciphertext ‖ (GHASH ⊕ pad). -/
theorem sealCore_decompose (traffic sequence content : List (BitVec 8)) (kind padding : Nat) :
    TlsRecord.sealCore Gcm.concrete ((traffic.drop 32).take 16) ((traffic.drop 48).take 12) sequence content
        kind padding =
      TlsRecord.header Gcm.concrete ((TlsRecord.inner Gcm.concrete content kind padding).length + 16) ++
      ctrOf traffic sequence (TlsRecord.inner Gcm.concrete content kind padding) ++
      Aes.addRoundKey Gcm.concrete.aes
        (ghashOf traffic (TlsRecord.header Gcm.concrete ((TlsRecord.inner Gcm.concrete content kind padding).length + 16))
          (ctrOf traffic sequence (TlsRecord.inner Gcm.concrete content kind padding)))
        (padOf traffic sequence) := by
  simp only [TlsRecord.sealCore, Gcm.sealCore, Gcm.sealPrepared, Gcm.Sealed.bytes, Gcm.tag, Gcm.prepare,
    Ghash.foldPrepared_correct, List.append_assoc]
  rfl

/-! ### The kernels on values -/

theorem tlsSealCtr_spec (kind size padding : Nat) (assign : BVExpr.Assignment) :
    (tlsSealCtr kind size padding).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [TlsRecord.header Gcm.concrete ((TlsRecord.inner Gcm.concrete (inputValue assign 68 size) kind padding).length + 16),
        ctrOf (inputValue assign 0 60) (inputValue assign 60 8)
          (TlsRecord.inner Gcm.concrete (inputValue assign 68 size) kind padding),
        padOf (inputValue assign 0 60) (inputValue assign 60 8)] := by
  have hB : lookup [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes size)]
      "clientApplication" = ByteCircuit.inputBytes 0 60 := by simp [lookup, lookupFrom]
  have hS : lookup [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes size)]
      "sequence" = ByteCircuit.inputBytes 60 8 := by simp [lookup, lookupFrom, Shape.variables]
  have hC : lookup [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), ("content", .bytes size)]
      "content" = ByteCircuit.inputBytes 68 size := by simp [lookup, lookupFrom, Shape.variables]
  have innerLength : (TlsRecord.inner Gcm.symbolic (ByteCircuit.inputBytes 68 size) kind padding).length =
      (TlsRecord.inner Gcm.concrete ((ByteCircuit.inputBytes 68 size).map (BVExpr.eval assign)) kind padding).length := by
    rw [← TlsRecord.inner_map (Gcm.evaluationHom assign), List.length_map]
  simp only [tlsSealCtr, priv, pub, List.map_cons, List.map_nil, hB, hS, hC,
    TlsRecord.header_map (Gcm.evaluationHom assign), ctr_eval, gcmPad_eval,
    TlsRecord.inner_map (Gcm.evaluationHom assign), innerLength]

theorem xorBytes_eval (assign : BVExpr.Assignment) (x y : List (BVExpr 8)) :
    (xorBytes x y).map (BVExpr.eval assign) =
      Aes.addRoundKey Gcm.concrete.aes (x.map (BVExpr.eval assign)) (y.map (BVExpr.eval assign)) :=
  Aes.addRoundKey_map (Gcm.evaluationHom assign).aes x y

theorem gcmTag_spec (assign : BVExpr.Assignment) :
    gcmTag.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [Aes.addRoundKey Gcm.concrete.aes
        (Aes.addRoundKey Gcm.concrete.aes (inputValue assign 0 16) (inputValue assign 16 16))
        (inputValue assign 32 16)] := by
  have hP : lookup [("pad", Shape.bytes 16), ("halfA", .bytes 16), ("halfB", .bytes 16)] "pad" =
      ByteCircuit.inputBytes 0 16 := by simp [lookup, lookupFrom]
  have hA : lookup [("pad", Shape.bytes 16), ("halfA", .bytes 16), ("halfB", .bytes 16)] "halfA" =
      ByteCircuit.inputBytes 16 16 := by simp [lookup, lookupFrom, Shape.variables]
  have hB : lookup [("pad", Shape.bytes 16), ("halfA", .bytes 16), ("halfB", .bytes 16)] "halfB" =
      ByteCircuit.inputBytes 32 16 := by simp [lookup, lookupFrom, Shape.variables]
  simp only [gcmTag, pub, List.map_cons, List.map_nil, hP, hA, hB, xorBytes_eval]

/-- The receive-side mask: 255 exactly when pad ⊕ halfA ⊕ halfB is the received tag. -/
theorem gcmCheck_spec (assign : BVExpr.Assignment) :
    gcmCheck.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[if Aes.addRoundKey Gcm.concrete.aes
            (Aes.addRoundKey Gcm.concrete.aes (padOf (inputValue assign 0 60) (inputValue assign 60 8))
              (inputValue assign 68 16))
            (inputValue assign 84 16) = inputValue assign 100 16 then 255 else 0]] := by
  have hT : lookup [("traffic", Shape.bytes 60), ("sequence", .bytes 8), ("halfA", .bytes 16), ("halfB", .bytes 16),
      ("tag", .bytes 16)] "traffic" = ByteCircuit.inputBytes 0 60 := by simp [lookup, lookupFrom]
  have hS : lookup [("traffic", Shape.bytes 60), ("sequence", .bytes 8), ("halfA", .bytes 16), ("halfB", .bytes 16),
      ("tag", .bytes 16)] "sequence" = ByteCircuit.inputBytes 60 8 := by simp [lookup, lookupFrom, Shape.variables]
  have hA : lookup [("traffic", Shape.bytes 60), ("sequence", .bytes 8), ("halfA", .bytes 16), ("halfB", .bytes 16),
      ("tag", .bytes 16)] "halfA" = ByteCircuit.inputBytes 68 16 := by simp [lookup, lookupFrom, Shape.variables]
  have hB : lookup [("traffic", Shape.bytes 60), ("sequence", .bytes 8), ("halfA", .bytes 16), ("halfB", .bytes 16),
      ("tag", .bytes 16)] "halfB" = ByteCircuit.inputBytes 84 16 := by simp [lookup, lookupFrom, Shape.variables]
  have hG : lookup [("traffic", Shape.bytes 60), ("sequence", .bytes 8), ("halfA", .bytes 16), ("halfB", .bytes 16),
      ("tag", .bytes 16)] "tag" = ByteCircuit.inputBytes 100 16 := by simp [lookup, lookupFrom, Shape.variables]
  simp only [gcmCheck, priv, List.map_cons, List.map_nil, hT, hS, hA, hB, hG,
    ByteAuth.equalMask_map (ByteAuth.evaluationHom assign), xorBytes_eval, gcmPad_eval, ByteAuth.equalMask_value]

/-! ### Split seal equals full seal -/

theorem xor_rotate : ∀ (pad first second : List (BitVec 8)),
    Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes pad first) second =
      Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes first second) pad
  | [], _, _ => by simp [Aes.addRoundKey]
  | _ :: _, [], _ => by simp [Aes.addRoundKey]
  | _ :: _, _ :: _, [] => by simp [Aes.addRoundKey]
  | x :: pad, y :: first, z :: second => by
      have ih := xor_rotate pad first second
      have head : x ^^^ y ^^^ z = y ^^^ z ^^^ x := by
        ext i
        simp only [BitVec.getElem_xor]
        cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl
      show (x ^^^ y ^^^ z) ::
          Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes pad first) second =
        (y ^^^ z ^^^ x) ::
          Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes first second) pad
      rw [ih, head]

/-- The record header and ciphertext opened by `tlsSealCtr`, followed by the tag
`gcmTag` computes from that kernel's pad and the two halves, is the full record
seal, provided the two halves XOR to GCM's GHASH value for that header and
ciphertext. -/
theorem sealCtr_with_tag_is_seal (kind size padding : Nat) (sealing tagging : BVExpr.Assignment)
    (header ciphertext pad tag : List (BitVec 8))
    (sealed : (tlsSealCtr kind size padding).outputs.map (fun field => field.value.map (BVExpr.eval sealing)) =
      [header, ciphertext, pad])
    (padInput : inputValue tagging 0 16 = pad)
    (tagged : gcmTag.outputs.map (fun field => field.value.map (BVExpr.eval tagging)) = [tag])
    (halves : Aes.addRoundKey Gcm.concrete.aes (inputValue tagging 16 16) (inputValue tagging 32 16) =
      ghashOf (inputValue sealing 0 60) header ciphertext) :
    header ++ ciphertext ++ tag =
      TlsRecord.sealCore Gcm.concrete (((inputValue sealing 0 60).drop 32).take 16)
        (((inputValue sealing 0 60).drop 48).take 12) (inputValue sealing 60 8) (inputValue sealing 68 size)
        kind padding := by
  rw [tlsSealCtr_spec] at sealed
  simp only [List.cons.injEq, and_true] at sealed
  obtain ⟨rfl, rfl, rfl⟩ := sealed
  rw [gcmTag_spec] at tagged
  simp only [List.cons.injEq, and_true] at tagged
  subst tagged
  rw [sealCore_decompose, padInput, xor_rotate, halves]

/-! ### The hypothesis on the halves, from shared key powers -/

theorem zipWith_map_same (f : β → β → γ) (g h : α → β) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map (fun x => f (g x) (h x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

theorem unpack_xor (x y : BitVec 128) :
    Aes.addRoundKey Gcm.concrete.aes (Ghash.unpackValue x) (Ghash.unpackValue y) = Ghash.unpackValue (x ^^^ y) := by
  show List.zipWith (· ^^^ ·) ((List.range 16).map (fun i => x.extractLsb' (8 * (15 - i)) 8))
      ((List.range 16).map (fun i => y.extractLsb' (8 * (15 - i)) 8)) =
    (List.range 16).map (fun i => (x ^^^ y).extractLsb' (8 * (15 - i)) 8)
  rw [zipWith_map_same]
  apply List.map_congr_left
  intro i _
  ext j hj
  simp

/-- With honest shares of the descending key powers, the bytes of the two
parties' local tags XOR to GCM's GHASH value. Takes the field laws for the
repository's multiplication as a hypothesis, as `GhashShares.halves_are_ghash`
does; `GcmShareKernelsProofs.shared_halves_are_ghash_proved` removes it. -/
theorem shared_halves_are_ghash (laws : GhashShares.Laws (Ghash.multiply Ghash.concrete))
    (traffic aad ciphertext : List (BitVec 8)) (first second : List (BitVec 128))
    (same : first.length = second.length)
    (shares : List.zipWith (· ^^^ ·) first second =
      GhashShares.descending (Ghash.multiply Ghash.concrete) (hashKeyOf traffic)
        (Gcm.authInput Gcm.concrete aad ciphertext).length) :
    Aes.addRoundKey Gcm.concrete.aes
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext) first))
        (Ghash.unpackValue (GhashShares.localTag (Ghash.multiply Ghash.concrete)
          (Gcm.authInput Gcm.concrete aad ciphertext) second)) =
      ghashOf traffic aad ciphertext := by
  rw [unpack_xor, GhashShares.halves_are_ghash _ laws GhashShares.multiply_key_additive _ _ _ _ same shares,
    GhashShares.horner_eq_hash]
  rfl

#print axioms sealCore_decompose
#print axioms tlsSealCtr_spec
#print axioms gcmTag_spec
#print axioms gcmCheck_spec
#print axioms sealCtr_with_tag_is_seal
#print axioms shared_halves_are_ghash

end TlsMpc.HybridKernel
