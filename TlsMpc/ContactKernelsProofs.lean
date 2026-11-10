import TlsMpc.HybridKernelsProofs
import TlsMpc.ModAddProofs

/-!
Theorems about the per-contact state kernels (`contactKey`, `contactSeal`,
`contactOpen` in TlsMpc/HybridKernels.lean), for every assignment of the
kernels' input variables.

* `contactKey_spec`: the `traffic` output is 32 zero bytes followed by the first
  28 bytes of SHA-256("CONTACT_STATE_KEY_V1" ‖ le32((A + B) mod (2^255 − 19))),
  for shares `A`, `B` below the modulus.
* `contactSeal_spec`, `contactOpen_spec`: the kernels' outputs as the
  repository's concrete AES-CTR keystream (`ctrOf`) and pad block (`checkOf`).
* `contactOpen_accepted_iff`: `accepted` is 255 exactly when the check input is
  the pad block for the reserved version under the traffic block's key.
* `contactOpen_rejected`: the content is all zero unless `accepted` is 255.
* `contact_round_trip`: opening what `contactSeal` produced, under the same
  traffic block and version, accepts and returns the sealed content.

Nothing here says the pad block identifies the key (that is a property of AES),
or anything about integrity of the ciphertext: `contactOpen` checks the key
only, as its definition states.
-/
namespace TlsMpc.HybridKernel
open Std.Tactic.BVDecide
open Signal

/-- The evaluated input bytes at variables `start … start + count − 1`. -/
abbrev inputValue (assign : BVExpr.Assignment) (start count : Nat) : List (BitVec 8) :=
  (ByteCircuit.inputBytes start count).map (BVExpr.eval assign)

theorem inputValue_length (assign : BVExpr.Assignment) (start count : Nat) :
    (inputValue assign start count).length = count := by
  simp [inputValue, ByteCircuit.inputBytes]

/-! ### What the AES parts compute, on values

A traffic block is secret (32), key (16), IV (12). -/

/-- The AES-128 key schedule of the block's key. -/
def expandedOf (traffic : List (BitVec 8)) : List (BitVec 8) :=
  Aes.expandKey Gcm.concrete.aes 4 10 ((traffic.drop 32).take 16)

/-- The per-record pad `AES_K(nonce ‖ 1)`. -/
def padOf (traffic sequence : List (BitVec 8)) : List (BitVec 8) :=
  Aes.encryptExpanded Gcm.concrete.aes 10 (expandedOf traffic)
    (TlsRecord.nonce Gcm.concrete ((traffic.drop 48).take 12) sequence ++ Gcm.encodeNat Gcm.concrete 4 1)

/-- GCM's counter-mode transformation (counter starting at 2) of `content`. -/
def ctrOf (traffic sequence content : List (BitVec 8)) : List (BitVec 8) :=
  Gcm.ctr Gcm.concrete (expandedOf traffic) (TlsRecord.nonce Gcm.concrete ((traffic.drop 48).take 12) sequence) content

/-- The key check value: the pad for the reserved version `2^64 − 1`. -/
def checkOf (traffic : List (BitVec 8)) : List (BitVec 8) := padOf traffic (List.replicate 8 255)

theorem gcmExpanded_eval (assign : BVExpr.Assignment) (traffic : List (BVExpr 8)) :
    (gcmExpanded traffic).map (BVExpr.eval assign) = expandedOf (traffic.map (BVExpr.eval assign)) := by
  show (Aes.expandKey Gcm.symbolic.aes 4 10 ((traffic.drop 32).take 16)).map (BVExpr.eval assign) =
    Aes.expandKey Gcm.concrete.aes 4 10 (((traffic.map (BVExpr.eval assign)).drop 32).take 16)
  rw [Aes.expandKey_map (Gcm.evaluationHom assign).aes, List.map_take, List.map_drop]

theorem gcmPad_eval (assign : BVExpr.Assignment) (traffic sequence : List (BVExpr 8)) :
    (gcmPad traffic sequence).map (BVExpr.eval assign) =
      padOf (traffic.map (BVExpr.eval assign)) (sequence.map (BVExpr.eval assign)) := by
  show (Aes.encryptExpanded Gcm.symbolic.aes 10 (gcmExpanded traffic)
      (TlsRecord.nonce Gcm.symbolic ((traffic.drop 48).take 12) sequence ++ Gcm.encodeNat Gcm.symbolic 4 1)).map
        (BVExpr.eval assign) =
    Aes.encryptExpanded Gcm.concrete.aes 10 (expandedOf (traffic.map (BVExpr.eval assign)))
      (TlsRecord.nonce Gcm.concrete (((traffic.map (BVExpr.eval assign)).drop 48).take 12)
        (sequence.map (BVExpr.eval assign)) ++ Gcm.encodeNat Gcm.concrete 4 1)
  rw [Aes.encryptExpanded_map (Gcm.evaluationHom assign).aes, gcmExpanded_eval, List.map_append,
    TlsRecord.nonce_map (Gcm.evaluationHom assign), Gcm.encodeNat_map (Gcm.evaluationHom assign),
    List.map_take, List.map_drop]

theorem ctr_eval (assign : BVExpr.Assignment) (traffic sequence content : List (BVExpr 8)) :
    (Gcm.ctr Gcm.symbolic (gcmExpanded traffic) (TlsRecord.nonce Gcm.symbolic (blockIv traffic) sequence) content).map
        (BVExpr.eval assign) =
      ctrOf (traffic.map (BVExpr.eval assign)) (sequence.map (BVExpr.eval assign))
        (content.map (BVExpr.eval assign)) := by
  show (Gcm.ctr Gcm.symbolic (gcmExpanded traffic)
      (TlsRecord.nonce Gcm.symbolic ((traffic.drop 48).take 12) sequence) content).map (BVExpr.eval assign) =
    Gcm.ctr Gcm.concrete (expandedOf (traffic.map (BVExpr.eval assign)))
      (TlsRecord.nonce Gcm.concrete (((traffic.map (BVExpr.eval assign)).drop 48).take 12)
        (sequence.map (BVExpr.eval assign))) (content.map (BVExpr.eval assign))
  rw [Gcm.ctr_map (Gcm.evaluationHom assign), gcmExpanded_eval, TlsRecord.nonce_map (Gcm.evaluationHom assign),
    List.map_take, List.map_drop]

theorem contactCheck_eval (assign : BVExpr.Assignment) (traffic : List (BVExpr 8)) :
    (contactCheck traffic).map (BVExpr.eval assign) = checkOf (traffic.map (BVExpr.eval assign)) := by
  show (gcmPad traffic (List.replicate 8 (const 255))).map (BVExpr.eval assign) = _
  rw [gcmPad_eval]
  rfl

/-! ### Counter mode is its own inverse -/

theorem expandedOf_length (traffic : List (BitVec 8)) (len : traffic.length = 60) :
    (expandedOf traffic).length = 176 :=
  Aes.expandKey_length Gcm.concrete.aes 4 10 _ (by simp only [List.length_take, List.length_drop]; omega) (by decide)

theorem addRoundKey_cancel : ∀ (content stream : List (BitVec 8)), content.length ≤ stream.length →
    Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes content stream) stream = content
  | [], _, _ => by simp [Aes.addRoundKey]
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      have ih := addRoundKey_cancel xs ys (by simpa using h)
      show ((x ^^^ y) ^^^ y) ::
        Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes xs ys) ys = x :: xs
      rw [ih, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem ctrLoop_nil (expanded nonce : List (BitVec 8)) (n counter : Nat) :
    Gcm.ctrLoop Gcm.concrete expanded nonce n counter [] = [] := by
  induction n generalizing counter with
  | zero => rfl
  | succ n ih => simp [Gcm.ctrLoop, Aes.addRoundKey, ih]

theorem ctrLoop_involutive (expanded nonce : List (BitVec 8)) (he : expanded.length = 176) (n : Nat) :
    ∀ (counter : Nat) (content : List (BitVec 8)), content.length ≤ 16 * n →
      Gcm.ctrLoop Gcm.concrete expanded nonce n counter
        (Gcm.ctrLoop Gcm.concrete expanded nonce n counter content) = content := by
  induction n with
  | zero =>
      intro counter content hc
      have empty : content = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst empty
      rfl
  | succ n ih =>
      intro counter content hc
      have streamLength : (Aes.encryptExpanded Gcm.concrete.aes 10 expanded
          (nonce ++ Gcm.encodeNat Gcm.concrete 4 counter)).length = 16 :=
        Aes.encryptExpanded_length Gcm.concrete.aes 10 _ _ he
      have unfoldStep : ∀ data : List (BitVec 8),
          Gcm.ctrLoop Gcm.concrete expanded nonce (n + 1) counter data =
            Aes.addRoundKey Gcm.concrete.aes (data.take 16)
              (Aes.encryptExpanded Gcm.concrete.aes 10 expanded (nonce ++ Gcm.encodeNat Gcm.concrete 4 counter)) ++
            Gcm.ctrLoop Gcm.concrete expanded nonce n (counter + 1) (data.drop 16) := fun _ => rfl
      generalize Aes.encryptExpanded Gcm.concrete.aes 10 expanded
        (nonce ++ Gcm.encodeNat Gcm.concrete 4 counter) = stream at streamLength unfoldStep
      have headLength : (Aes.addRoundKey Gcm.concrete.aes (content.take 16) stream).length =
          min 16 content.length := by
        simp only [Aes.addRoundKey, List.length_zipWith, List.length_take, streamLength]
        omega
      have parts :
          (Aes.addRoundKey Gcm.concrete.aes (content.take 16) stream ++
              Gcm.ctrLoop Gcm.concrete expanded nonce n (counter + 1) (content.drop 16)).take 16 =
            Aes.addRoundKey Gcm.concrete.aes (content.take 16) stream ∧
          (Aes.addRoundKey Gcm.concrete.aes (content.take 16) stream ++
              Gcm.ctrLoop Gcm.concrete expanded nonce n (counter + 1) (content.drop 16)).drop 16 =
            Gcm.ctrLoop Gcm.concrete expanded nonce n (counter + 1) (content.drop 16) := by
        by_cases full : 16 ≤ content.length
        · have exact : (Aes.addRoundKey Gcm.concrete.aes (content.take 16) stream).length = 16 := by
            rw [headLength]
            omega
          exact ⟨List.take_left' exact, List.drop_left' exact⟩
        · have short : content.drop 16 = [] := List.drop_eq_nil_of_le (by omega)
          rw [short, ctrLoop_nil, List.append_nil]
          exact ⟨List.take_of_length_le (by rw [headLength]; omega),
            List.drop_eq_nil_of_le (by rw [headLength]; omega)⟩
      rw [unfoldStep content, unfoldStep, parts.1, parts.2,
        addRoundKey_cancel _ _ (by rw [List.length_take, streamLength]; omega),
        ih (counter + 1) (content.drop 16) (by rw [List.length_drop]; omega), List.take_append_drop]

theorem ctr_involutive (expanded nonce content : List (BitVec 8)) (he : expanded.length = 176) :
    Gcm.ctr Gcm.concrete expanded nonce (Gcm.ctr Gcm.concrete expanded nonce content) = content := by
  have len := Gcm.ctr_length Gcm.concrete expanded nonce content he
  unfold Gcm.ctr at len ⊢
  rw [len]
  exact ctrLoop_involutive expanded nonce he _ 2 content (by omega)

theorem ctrOf_length (traffic sequence content : List (BitVec 8)) (len : traffic.length = 60) :
    (ctrOf traffic sequence content).length = content.length :=
  Gcm.ctr_length Gcm.concrete _ _ content (expandedOf_length traffic len)

/-- Decrypting a ciphertext under the same block and version returns the content. -/
theorem ctrOf_involutive (traffic sequence content : List (BitVec 8)) (len : traffic.length = 60) :
    ctrOf traffic sequence (ctrOf traffic sequence content) = content :=
  ctr_involutive _ _ content (expandedOf_length traffic len)

/-! ### contactKey -/

/-- The domain-separation label, as bytes. -/
def contactLabel : List (BitVec 8) :=
  "CONTACT_STATE_KEY_V1".toUTF8.toList.map (fun byte => BitVec.ofNat 8 byte.toNat)

theorem shareModulus_fits : shareModulus ≤ 2 ^ (8 * 32) := by decide

/-- For shares below the modulus, the record key block is 32 zero bytes (no
traffic secret), then the first 28 bytes (key, IV) of
SHA-256(label ‖ le32((A + B) mod (2^255 − 19))). -/
theorem contactKey_spec (assign : BVExpr.Assignment)
    (aBound : ModAdd.leValue (inputValue assign 0 32) < shareModulus)
    (bBound : ModAdd.leValue (inputValue assign 32 32) < shareModulus) :
    contactKey.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [List.replicate 32 0 ++
        (Sha256.hash Sha256.concrete (contactLabel ++ ModAdd.leBytes 32
          ((ModAdd.leValue (inputValue assign 0 32) + ModAdd.leValue (inputValue assign 32 32)) % shareModulus))).take 28] := by
  have hA : lookup [("shareA", Shape.bytes 32), ("shareB", .bytes 32)] "shareA" = ByteCircuit.inputBytes 0 32 := by
    simp [lookup, lookupFrom]
  have hB : lookup [("shareA", Shape.bytes 32), ("shareB", .bytes 32)] "shareB" = ByteCircuit.inputBytes 32 32 := by
    simp [lookup, lookupFrom, Shape.variables]
  have len : (ByteCircuit.inputBytes 0 32).length = 32 := by simp [ByteCircuit.inputBytes]
  have scalar := ModAdd.modAddBytes_eval assign shareModulus (ByteCircuit.inputBytes 0 32)
    (ByteCircuit.inputBytes 32 32) (by simp [ByteCircuit.inputBytes]) (by rw [len]; exact shareModulus_fits)
    aBound bBound
  rw [len] at scalar
  have label : ("CONTACT_STATE_KEY_V1".toUTF8.toList.map (fun byte => const byte.toNat)).map (BVExpr.eval assign) =
      contactLabel := by
    rw [List.map_map]
    rfl
  have zero : (zeros 32).map (BVExpr.eval assign) = List.replicate 32 0 := by
    rw [zeros, List.map_replicate]
    rfl
  simp only [contactKey, priv, List.map_cons, List.map_nil, hA, hB, List.map_append, sl, List.map_take, List.drop_zero,
    Sha256.hash_map (Sha256Ripple.evaluationHom assign), scalar, label, zero]

/-! ### contactSeal and contactOpen -/

theorem contactSeal_spec (size : Nat) (assign : BVExpr.Assignment) :
    (contactSeal size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [ctrOf (inputValue assign 0 60) (inputValue assign 60 8) (inputValue assign 68 size),
        checkOf (inputValue assign 0 60)] := by
  have hT : lookup [("traffic", Shape.bytes 60), ("version", .bytes 8), ("content", .bytes size)] "traffic" =
      ByteCircuit.inputBytes 0 60 := by simp [lookup, lookupFrom]
  have hV : lookup [("traffic", Shape.bytes 60), ("version", .bytes 8), ("content", .bytes size)] "version" =
      ByteCircuit.inputBytes 60 8 := by simp [lookup, lookupFrom, Shape.variables]
  have hC : lookup [("traffic", Shape.bytes 60), ("version", .bytes 8), ("content", .bytes size)] "content" =
      ByteCircuit.inputBytes 68 size := by simp [lookup, lookupFrom, Shape.variables]
  simp only [contactSeal, pub, List.map_cons, List.map_nil, hT, hV, hC, ctr_eval, contactCheck_eval]

/-- The acceptance mask `contactOpen` computes: 255 when the supplied check value
is the block's key check value, 0 otherwise. -/
def contactMask (traffic check : List (BitVec 8)) : BitVec 8 := if checkOf traffic = check then 255 else 0

theorem contactMask_accept_iff (traffic check : List (BitVec 8)) :
    contactMask traffic check = 255 ↔ check = checkOf traffic := by
  unfold contactMask
  constructor
  · intro h
    by_cases same : checkOf traffic = check
    · exact same.symm
    · rw [if_neg same] at h
      exact absurd h (by decide)
  · intro h
    rw [if_pos h.symm]

theorem contactMask_reject (traffic check : List (BitVec 8)) (h : contactMask traffic check ≠ 255) :
    contactMask traffic check = 0 := by
  unfold contactMask at h ⊢
  by_cases same : checkOf traffic = check
  · rw [if_pos same] at h
    exact absurd rfl h
  · rw [if_neg same]

theorem contactOpen_spec (size : Nat) (assign : BVExpr.Assignment) :
    (contactOpen size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[contactMask (inputValue assign 0 60) (inputValue assign (68 + size) 16)],
        ByteAuth.release ByteAuth.concrete (contactMask (inputValue assign 0 60) (inputValue assign (68 + size) 16))
          (ctrOf (inputValue assign 0 60) (inputValue assign 60 8) (inputValue assign 68 size))] := by
  have hT : lookup [("traffic", Shape.bytes 60), ("version", .bytes 8), ("ciphertext", .bytes size),
      ("check", .bytes 16)] "traffic" = ByteCircuit.inputBytes 0 60 := by simp [lookup, lookupFrom]
  have hV : lookup [("traffic", Shape.bytes 60), ("version", .bytes 8), ("ciphertext", .bytes size),
      ("check", .bytes 16)] "version" = ByteCircuit.inputBytes 60 8 := by simp [lookup, lookupFrom, Shape.variables]
  have hC : lookup [("traffic", Shape.bytes 60), ("version", .bytes 8), ("ciphertext", .bytes size),
      ("check", .bytes 16)] "ciphertext" = ByteCircuit.inputBytes 68 size := by
    simp [lookup, lookupFrom, Shape.variables]
  have hK : lookup [("traffic", Shape.bytes 60), ("version", .bytes 8), ("ciphertext", .bytes size),
      ("check", .bytes 16)] "check" = ByteCircuit.inputBytes (68 + size) 16 := by
    simp [lookup, lookupFrom, Shape.variables]
  simp only [contactOpen, priv, pub, List.map_cons, List.map_nil, hT, hV, hC, hK,
    ByteAuth.release_map (ByteAuth.evaluationHom assign), ByteAuth.equalMask_map (ByteAuth.evaluationHom assign),
    ctr_eval, contactCheck_eval, ByteAuth.equalMask_value]
  rfl

/-- `accepted` is 255 exactly when the check input is the key check value of
the traffic block. -/
theorem contactOpen_accepted_iff (size : Nat) (assign : BVExpr.Assignment) (accepted : BitVec 8)
    (content : List (BitVec 8))
    (out : (contactOpen size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[accepted], content]) :
    accepted = 255 ↔ inputValue assign (68 + size) 16 = checkOf (inputValue assign 0 60) := by
  rw [contactOpen_spec] at out
  simp only [List.cons.injEq, and_true] at out
  rw [← out.1]
  exact contactMask_accept_iff _ _

/-- The content is all zero unless `accepted` is 255. -/
theorem contactOpen_rejected (size : Nat) (assign : BVExpr.Assignment) (accepted : BitVec 8)
    (content : List (BitVec 8))
    (out : (contactOpen size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [[accepted], content])
    (reject : accepted ≠ 255) : content = List.replicate size 0 := by
  rw [contactOpen_spec] at out
  simp only [List.cons.injEq, and_true] at out
  obtain ⟨mask, opened⟩ := out
  rw [← mask] at reject
  rw [← opened, contactMask_reject _ _ reject, ByteAuth.release_reject,
    ctrOf_length _ _ _ (inputValue_length assign 0 60), inputValue_length]

/-- Opening the ciphertext and check value that `contactSeal` produced, under
the same traffic block and version, accepts and returns the sealed content. -/
theorem contact_round_trip (size : Nat) (sealing opening : BVExpr.Assignment)
    (traffic : inputValue opening 0 60 = inputValue sealing 0 60)
    (version : inputValue opening 60 8 = inputValue sealing 60 8)
    (stored : (contactSeal size).outputs.map (fun field => field.value.map (BVExpr.eval sealing)) =
      [inputValue opening 68 size, inputValue opening (68 + size) 16]) :
    (contactOpen size).outputs.map (fun field => field.value.map (BVExpr.eval opening)) =
      [[255], inputValue sealing 68 size] := by
  rw [contactSeal_spec] at stored
  simp only [List.cons.injEq, and_true] at stored
  obtain ⟨ciphertext, check⟩ := stored
  have accept : contactMask (inputValue sealing 0 60) (checkOf (inputValue sealing 0 60)) = 255 :=
    (contactMask_accept_iff _ _).mpr rfl
  rw [contactOpen_spec, traffic, version, ← ciphertext, ← check, accept, ByteAuth.release_accept,
    ctrOf_involutive _ _ _ (inputValue_length sealing 0 60)]

#print axioms contactKey_spec
#print axioms contactSeal_spec
#print axioms contactOpen_spec
#print axioms contactOpen_accepted_iff
#print axioms contactOpen_rejected
#print axioms contact_round_trip

end TlsMpc.HybridKernel
