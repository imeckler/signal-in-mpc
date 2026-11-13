import TlsMpc.Node.Flows.Ceremony
import TlsMpc.Node.Flows.Contacts
import TlsMpc.CeremonyProofs
import TlsMpc.KernelSpecs.RequestFrame

/-!
# T4-CEREMONY: the ceremony scripts on two honest parties, and the kernels on their bundles

* `secretsOut_value`: `ceremony-secrets` on the bundle op 80 concatenates (seedA ‖ seedB ‖ maskA ‖
  maskB ‖ recoveryA ‖ recoveryB) is `Ceremony.secrets` on those bytes (`ceremonySecrets_spec`), the
  three fields 22, 32 and 22 bytes long (`secrets_lengths`).
* `secrets_honest`: two honest parties, each with its own seed, mask and recovery half in its store:
  both return the password and recovery handles `n + 8`, `n + 9` and the opened masked password,
  which is the reference's third field (password ⊕ maskA ⊕ maskB); the two handles hold the
  reference's password and recovery password; every handle below `n` is untouched. With
  `shares_xor` (Ceremony.lean) the replies the controllers compute (`shareOf`) XOR to the password ‖
  the recovery password.
* `register_honest`: op 81's engine part on two honest parties makes the secrets handle hold
  tail ‖ password ‖ recovery.
* `ceremonyRegisterCtr_spec` (on every assignment, as `KernelSpecs.signalRequestCtr_spec`): the
  four outputs of `ceremony-register-ctr` are `[255]`, the record header, the AES-CTR encryption of
  the inner plaintext and the GCM pad, the plaintext being `Ceremony.fill` (the frame with base64 of
  tail ‖ password at the credential slot and base64 of the recovery password at the JSON slot, under
  the WebSocket mask: `registerPlaintext_spec`). `registerCtr_value`: the same on the bundle the
  record seal concatenates (`Send.requestCtrScript`: traffic ‖ sequence ‖ secrets ‖ frame ‖ mask), and
  `registerSlots_value`: the two slots are base64(tail ‖ password) and base64(recovery).
* `ceremony_honest`: the headline: op 80 then op 81 on two honest parties; the request's secrets
  handle holds tail ‖ password ‖ recovery of the reference, and the CTR kernel's output on the record
  seal's bundle is `sealedRequest` of the frame filled with base64(tail ‖ password) and
  base64(recovery).

What is NOT here (S16_NOTES.md K-gaps): the record seal's runs (`Send.requestCtrScript`, S12's tag)
are S13's / S12's run theorems on a generic conversation handle, not restated for this name; the
`Ceremony.basicConsistent` / base64 RFC facts are as in `CeremonyProofs.lean`.
-/

namespace TlsMpc.Node.Flows.Ceremony

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide
open TlsMpc.Signal

/-! ## `ceremony-secrets` on the script's bundle -/

/-- The input bundle op 80 concatenates (as `List.flatten` nests it). -/
def secretsIn (sA sB mA mB rA rB : B8) : B8 := sA ++ (sB ++ (mA ++ (mB ++ (rA ++ rB))))

/-- The reference (`Ceremony.secrets` on concrete bytes): password, recovery password, masked. -/
def reference (sA sB mA mB rA rB : B8) : List B8 :=
  TlsMpc.Ceremony.secrets ByteAuth.concrete sA sB mA mB rA rB

theorem iv (l : B8) (s c : Nat) (h : s + c ≤ l.length) :
    (ByteCircuit.inputBytes s c).map (BVExpr.eval (assignOf l)) = (l.drop s).take c :=
  inputValue_assignOf l s c h

theorem lookup_secrets :
    HybridKernel.lookup CeremonyKernel.secretsInputs "seedA" = ByteCircuit.inputBytes 0 18 ∧
    HybridKernel.lookup CeremonyKernel.secretsInputs "seedB" = ByteCircuit.inputBytes 18 18 ∧
    HybridKernel.lookup CeremonyKernel.secretsInputs "maskA" = ByteCircuit.inputBytes 36 22 ∧
    HybridKernel.lookup CeremonyKernel.secretsInputs "maskB" = ByteCircuit.inputBytes 58 22 ∧
    HybridKernel.lookup CeremonyKernel.secretsInputs "recoveryA" = ByteCircuit.inputBytes 80 32 ∧
    HybridKernel.lookup CeremonyKernel.secretsInputs "recoveryB" = ByteCircuit.inputBytes 112 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [HybridKernel.lookup, HybridKernel.lookupFrom, CeremonyKernel.secretsInputs, HybridKernel.Shape.variables,
      TlsMpc.Ceremony.seedBytes, TlsMpc.Ceremony.passwordBytes, TlsMpc.Ceremony.recoveryBytes]

/-- **`ceremony-secrets` on the bundle the script concatenates** is the reference, flattened. -/
theorem secretsOut_value (sA sB mA mB rA rB : B8) (hsA : sA.length = 18) (hsB : sB.length = 18)
    (hmA : mA.length = 22) (hmB : mB.length = 22) (hrA : rA.length = 32) (hrB : rB.length = 32) :
    kernelOut (CeremonyKernel.ceremonySecrets ()) (secretsIn sA sB mA mB rA rB) =
      (reference sA sB mA mB rA rB).flatten := by
  have h := CeremonyKernel.ceremonySecrets_spec (assignOf (secretsIn sA sB mA mB rA rB))
  simp only at h
  have hl : (secretsIn sA sB mA mB rA rB).length = 144 := by simp [secretsIn, hsA, hsB, hmA, hmB, hrA, hrB]
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lookup_secrets
  rw [l1, l2, l3, l4, l5, l6, iv _ _ _ (by omega), iv _ _ _ (by omega), iv _ _ _ (by omega), iv _ _ _ (by omega),
    iv _ _ _ (by omega), iv _ _ _ (by omega)] at h
  have e1 : ((secretsIn sA sB mA mB rA rB).drop 0).take 18 = sA := by
    simp only [secretsIn, List.drop_zero]; exact List.take_left' hsA
  have e2 : ((secretsIn sA sB mA mB rA rB).drop 18).take 18 = sB := by
    simp only [secretsIn]; rw [List.drop_left' hsA, List.take_left' hsB]
  have e3 : ((secretsIn sA sB mA mB rA rB).drop 36).take 22 = mA := by
    have : secretsIn sA sB mA mB rA rB = (sA ++ sB) ++ (mA ++ (mB ++ (rA ++ rB))) := by simp [secretsIn]
    rw [this, List.drop_left' (by simp [hsA, hsB]), List.take_left' hmA]
  have e4 : ((secretsIn sA sB mA mB rA rB).drop 58).take 22 = mB := by
    have : secretsIn sA sB mA mB rA rB = (sA ++ sB ++ mA) ++ (mB ++ (rA ++ rB)) := by simp [secretsIn]
    rw [this, List.drop_left' (by simp [hsA, hsB, hmA]), List.take_left' hmB]
  have e5 : ((secretsIn sA sB mA mB rA rB).drop 80).take 32 = rA := by
    have : secretsIn sA sB mA mB rA rB = (sA ++ sB ++ mA ++ mB) ++ (rA ++ rB) := by simp [secretsIn]
    rw [this, List.drop_left' (by simp [hsA, hsB, hmA, hmB]), List.take_left' hrA]
  have e6 : ((secretsIn sA sB mA mB rA rB).drop 112).take 32 = rB := by
    have : secretsIn sA sB mA mB rA rB = (sA ++ sB ++ mA ++ mB ++ rA) ++ rB := by simp [secretsIn]
    rw [this, List.drop_left' (by simp [hsA, hsB, hmA, hmB, hrA]), List.take_of_length_le (by omega)]
  rw [e1, e2, e3, e4, e5, e6] at h
  unfold kernelOut
  exact congrArg List.flatten h

/-- The reference's three fields and their lengths. -/
theorem secrets_lengths (sA sB mA mB rA rB : B8) (hsA : sA.length = 18) (hsB : sB.length = 18)
    (hmA : mA.length = 22) (hmB : mB.length = 22) (hrA : rA.length = 32) (hrB : rB.length = 32) :
    ∃ pw rc mk : B8, reference sA sB mA mB rA rB = [pw, rc, mk] ∧ pw.length = 22 ∧ rc.length = 32 ∧
      mk.length = 22 ∧ mk = List.zipWith (· ^^^ ·) pw (List.zipWith (· ^^^ ·) mA mB) ∧
      rc = List.zipWith (· ^^^ ·) rA rB := by
  refine ⟨TlsMpc.Ceremony.password ByteAuth.concrete sA sB, List.zipWith (· ^^^ ·) rA rB,
    List.zipWith (· ^^^ ·) (TlsMpc.Ceremony.password ByteAuth.concrete sA sB) (List.zipWith (· ^^^ ·) mA mB),
    rfl, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [TlsMpc.Ceremony.password, List.length_take, TlsMpc.KernelSpecs.RequestFrame.base64_length,
      List.length_zipWith, hsA, hsB, TlsMpc.Ceremony.passwordBytes]
    decide
  · simp [hrA, hrB]
  · simp only [List.length_zipWith, TlsMpc.Ceremony.password, List.length_take,
      TlsMpc.KernelSpecs.RequestFrame.base64_length, hsA, hsB, hmA, hmB, TlsMpc.Ceremony.passwordBytes]
    decide

/-! ## Op 80 on two honest parties -/

/-- The environment's circuit named `ceremony-secrets` computes the Lean kernel (the T2 trust for
this kernel, as `Contacts.Loaded` for the contact kernels). -/
def SecretsLoaded (E : Env) : Prop :=
  E.circuits secretsName = some (kernelCircuit (CeremonyKernel.ceremonySecrets ()) inputBytes secretsMarks)

/-- Op 80 after its three inputs. -/
def secretsRest (n : Nat) : Script Made :=
  seqs (kernelBlock n) (openThen ⟨n + 10⟩ Label.maskedPassword (afterMasked n))

theorem secretsScript_eq (n seedSlot maskSlot recoverySlot : Nat) :
    secretsScript n seedSlot maskSlot recoverySlot =
      seq (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ (8 * seedBytes) false false seedSlot)
        (seq (.boolInputBoth ⟨n + 2⟩ ⟨n + 3⟩ (8 * passwordBytes) false false maskSlot)
          (seq (.boolInputBoth ⟨n + 4⟩ ⟨n + 5⟩ (8 * recoveryBytes) false false recoverySlot) (secretsRest n))) := rfl

/-- The slices of the output bundle. -/
theorem out_slices (pw rc mk : B8) (hp : pw.length = 22) (hr : rc.length = 32) :
    List.take 176 (bitsOf (pw ++ (rc ++ mk))) = bitsOf pw ∧
    List.take 256 (List.drop 176 (bitsOf (pw ++ (rc ++ mk)))) = bitsOf rc ∧
    List.take 176 (List.drop 432 (bitsOf (pw ++ (rc ++ mk)))) = List.take 176 (bitsOf mk) := by
  simp only [bitsOf_append]
  refine ⟨?_, ?_, ?_⟩
  · exact List.take_left' (by simp [hp])
  · rw [List.drop_left' (by simp [hp]), List.take_left' (by simp [hr])]
  · rw [show (432 : Nat) = (bitsOf pw ++ bitsOf rc).length by simp [hp, hr], ← List.append_assoc, List.drop_left' rfl]

/-- **T4-CEREMONY for op 80.** Two honest parties, A with its seed `sA`, mask `mA` and recovery half
`rA` in its store and B with `sB`, `mB`, `rB`: both return the handles `n + 8`, `n + 9` and the
opened masked password, the reference's third field (password ⊕ maskA ⊕ maskB); the two handles
hold the reference's password and recovery password; every handle below `n` is untouched. -/
theorem secrets_honest (E : Env) (σA σB : Store) (hE : SecretsLoaded E) (I : Ideal)
    (n seedSlot maskSlot recoverySlot : Nat) (sA sB mA mB rA rB : B8)
    (hsA : sA.length = 18) (hsB : sB.length = 18) (hmA : mA.length = 22) (hmB : mB.length = 22)
    (hrA : rA.length = 32) (hrB : rB.length = 32)
    (hσA : σA.bits seedSlot = bitsOf sA ∧ σA.bits maskSlot = bitsOf mA ∧ σA.bits recoverySlot = bitsOf rA)
    (hσB : σB.bits seedSlot = bitsOf sB ∧ σB.bits maskSlot = bitsOf mB ∧ σB.bits recoverySlot = bitsOf rB) :
    (jointRun E (secretsScript n seedSlot maskSlot recoverySlot) (secretsScript n seedSlot maskSlot recoverySlot)
        σA σB I).result =
      some (⟨⟨n + 8⟩, ⟨n + 9⟩, (reference sA sB mA mB rA rB).getD 2 []⟩,
        ⟨⟨n + 8⟩, ⟨n + 9⟩, (reference sA sB mA mB rA rB).getD 2 []⟩) ∧
    (jointRun E (secretsScript n seedSlot maskSlot recoverySlot) (secretsScript n seedSlot maskSlot recoverySlot)
        σA σB I).ideal.bools (n + 8) = some (bitsOf ((reference sA sB mA mB rA rB).getD 0 [])) ∧
    (jointRun E (secretsScript n seedSlot maskSlot recoverySlot) (secretsScript n seedSlot maskSlot recoverySlot)
        σA σB I).ideal.bools (n + 9) = some (bitsOf ((reference sA sB mA mB rA rB).getD 1 [])) ∧
    ∀ j, j < n → (jointRun E (secretsScript n seedSlot maskSlot recoverySlot)
        (secretsScript n seedSlot maskSlot recoverySlot) σA σB I).ideal.bools j = I.bools j := by
  obtain ⟨pw, rc, mk, href, hpw, hrc, hmk, -, -⟩ := secrets_lengths sA sB mA mB rA rB hsA hsB hmA hmB hrA hrB
  have hk : kernelOut (CeremonyKernel.ceremonySecrets ()) (sA ++ (sB ++ (mA ++ (mB ++ (rA ++ rB))))) =
      pw ++ (rc ++ mk) := by
    have h := secretsOut_value sA sB mA mB rA rB hsA hsB hmA hmB hrA hrB
    rw [href] at h
    simpa [secretsIn] using h
  obtain ⟨s1, s2, s3⟩ := out_slices pw rc mk hpw hrc
  have s3' : List.take 176 (List.drop 432 (bitsOf (pw ++ (rc ++ mk)))) = bitsOf mk := by
    rw [s3, List.take_of_length_le (by simp [hmk])]
  rw [href]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  -- the three inputs
  obtain ⟨a1, a2, a3⟩ := hσA
  obtain ⟨b1, b2, b3⟩ := hσB
  let I1 := (I.setBool ⟨n⟩ (bitsOf sA)).setBool ⟨n + 1⟩ (bitsOf sB)
  let I2 := (I1.setBool ⟨n + 2⟩ (bitsOf mA)).setBool ⟨n + 3⟩ (bitsOf mB)
  let I3 := (I2.setBool ⟨n + 4⟩ (bitsOf rA)).setBool ⟨n + 5⟩ (bitsOf rB)
  obtain ⟨r1, d1⟩ := jointRun_seq E (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ (8 * seedBytes) false false seedSlot)
    (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ (8 * seedBytes) false false seedSlot) _ _ σA σB I I1
    (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ (8 * seedBytes) false false (bitsOf sA))
    (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ (8 * seedBytes) false false (bitsOf sB)) rfl
    (by simp [fill, a1, hsA, seedBytes]) (by simp [fill, b1, hsB, seedBytes])
    (by simp [idealStep, Wire.part, hsA, hsB, seedBytes, I1])
  obtain ⟨r2, d2⟩ := jointRun_seq E (.boolInputBoth ⟨n + 2⟩ ⟨n + 3⟩ (8 * passwordBytes) false false maskSlot)
    (.boolInputBoth ⟨n + 2⟩ ⟨n + 3⟩ (8 * passwordBytes) false false maskSlot) _ _ σA σB I1 I2
    (.boolInputBoth ⟨n + 2⟩ ⟨n + 3⟩ (8 * passwordBytes) false false (bitsOf mA))
    (.boolInputBoth ⟨n + 2⟩ ⟨n + 3⟩ (8 * passwordBytes) false false (bitsOf mB)) rfl
    (by simp [fill, a2, hmA, passwordBytes]) (by simp [fill, b2, hmB, passwordBytes])
    (by simp [idealStep, Wire.part, hmA, hmB, passwordBytes, I2])
  obtain ⟨r3, d3⟩ := jointRun_seq E (.boolInputBoth ⟨n + 4⟩ ⟨n + 5⟩ (8 * recoveryBytes) false false recoverySlot)
    (.boolInputBoth ⟨n + 4⟩ ⟨n + 5⟩ (8 * recoveryBytes) false false recoverySlot) (secretsRest n) (secretsRest n)
    σA σB I2 I3 (.boolInputBoth ⟨n + 4⟩ ⟨n + 5⟩ (8 * recoveryBytes) false false (bitsOf rA))
    (.boolInputBoth ⟨n + 4⟩ ⟨n + 5⟩ (8 * recoveryBytes) false false (bitsOf rB)) rfl
    (by simp [fill, a3, hrA, recoveryBytes]) (by simp [fill, b3, hrB, recoveryBytes])
    (by simp [idealStep, Wire.part, hrA, hrB, recoveryBytes, I3])
  rw [secretsScript_eq, r1, d1, r2, d2, r3, d3]
  unfold secretsRest
  have hE' : E.circuits secretsName =
      some (kernelCircuit (CeremonyKernel.ceremonySecrets ()) inputBytes secretsMarks) := hE
  have hin : (bitsOf sA ++ (bitsOf sB ++ (bitsOf mA ++ (bitsOf mB ++ (bitsOf rA ++ bitsOf rB))))).length =
      8 * inputBytes := by
    simp [hsA, hsB, hmA, hmB, hrA, hrB, inputBytes, seedBytes, passwordBytes, recoveryBytes]
  have hb : bytesOf (bitsOf sA ++ (bitsOf sB ++ (bitsOf mA ++ (bitsOf mB ++ (bitsOf rA ++ bitsOf rB))))) =
      sA ++ (sB ++ (mA ++ (mB ++ (rA ++ rB)))) := by
    rw [bytesOf_bitsOf_append, bytesOf_bitsOf_append, bytesOf_bitsOf_append, bytesOf_bitsOf_append,
      bytesOf_bitsOf_append, bytesOf_bitsOf]
  have hrun : ∃ I4, runPlain E (kernelBlock n) I3 = some I4 ∧ I4.bools (n + 8) = some (bitsOf pw) ∧
      I4.bools (n + 9) = some (bitsOf rc) ∧ I4.bools (n + 10) = some (bitsOf mk) ∧
      ∀ j, j < n → I4.bools j = I.bools j := by
    simp [runPlain, kernelBlock, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool, hE',
      kernelCircuit, I3, I2, I1, -bitsOf_append, hsA, hsB, hmA, hmB, hrA, hrB, inputBytes, seedBytes,
      passwordBytes, recoveryBytes, outputBytes, runCopies_one, hb, hk, s1, s2, s3', hpw, hrc, hmk]
    intro j hj
    have e0 : j ≠ n := by omega
    have e1 : j ≠ n + 1 := by omega
    have e2 : j ≠ n + 2 := by omega
    have e3 : j ≠ n + 3 := by omega
    have e4 : j ≠ n + 4 := by omega
    have e5 : j ≠ n + 5 := by omega
    have e6 : j ≠ n + 6 := by omega
    have e7 : j ≠ n + 7 := by omega
    have e8 : j ≠ n + 8 := by omega
    have e9 : j ≠ n + 9 := by omega
    have e10 : j ≠ n + 10 := by omega
    simp [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  obtain ⟨I4, hI, h8, h9, h10, hlow⟩ := hrun
  obtain ⟨r4, d4⟩ := jointRun_seqs E _ _ σA σB (kernelBlock n) (kernelBlock_plain n) I3 I4 hI
  rw [r4, d4]
  obtain ⟨r5, d5⟩ := jointRun_openThen E ⟨n + 10⟩ Label.maskedPassword (afterMasked n) (afterMasked n) σA σB I4
    (bitsOf mk) h10
  rw [r5, d5]
  unfold afterMasked
  obtain ⟨r6, d6⟩ := jointRun_seqs E
    (if (bytesOf (bitsOf mk)).length = passwordBytes then Script.done (⟨⟨n + 8⟩, ⟨n + 9⟩, bytesOf (bitsOf mk)⟩ : Made)
     else .abort "ceremony secrets shape")
    (if (bytesOf (bitsOf mk)).length = passwordBytes then Script.done (⟨⟨n + 8⟩, ⟨n + 9⟩, bytesOf (bitsOf mk)⟩ : Made)
     else .abort "ceremony secrets shape")
    σA σB [.freeBool ⟨n + 10⟩] (by simp [plain]) I4 _ (runPlain_free E _ I4)
  rw [r6, d6]
  have hlen : mk.length = passwordBytes := by simp [hmk, passwordBytes]
  simp only [bytesOf_bitsOf, hlen, if_true]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [jointRun, Ideal.dropBool, h8]
  · simp [jointRun, Ideal.dropBool, h9]
  · intro j hj
    have e10 : j ≠ n + 10 := by omega
    simp [jointRun, Ideal.dropBool, e10, hlow j hj]

/-! ## Op 81's engine part on two honest parties -/

/-- **Op 81's engine part, two honest parties**: with the password and recovery handles holding
`pw`, `rc`, both return the secrets handle `n + 1`, which holds tail ‖ pw ‖ rc. -/
theorem register_honest (E : Env) (σA σB : Store) (I : Ideal) (n : Nat) (password recovery : BoolH) (tail pw rc : B8)
    (htl : tail.length ≤ 2) (hpn : password.id < n) (hrn : recovery.id < n)
    (hp : I.bools password.id = some (bitsOf pw)) (hr : I.bools recovery.id = some (bitsOf rc)) :
    (jointRun E (registerScript n password recovery tail) (registerScript n password recovery tail) σA σB I).result =
      some (⟨n + 1⟩, ⟨n + 1⟩) ∧
    (jointRun E (registerScript n password recovery tail) (registerScript n password recovery tail) σA σB I).ideal.bools
      (n + 1) = some (bitsOf (tail ++ (pw ++ rc))) := by
  unfold registerScript
  rw [if_pos htl]
  have p1 : password.id ≠ n + 1 := by omega
  have r1 : recovery.id ≠ n + 1 := by omega
  have p0 : password.id ≠ n := by omega
  have r0 : recovery.id ≠ n := by omega
  have hrun : ∃ I', runPlain E (registerBlock n password recovery tail) I = some I' ∧
      I'.bools (n + 1) = some (bitsOf (tail ++ (pw ++ rc))) := by
    unfold registerBlock
    split
    · next h0 =>
      subst h0
      simp [runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool, hp, hr,
        Ne.symm p1, Ne.symm r1]
    · simp [runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, Ideal.dropBool, hp, hr, p0,
        r0, Ne.symm p1, Ne.symm r1]
  obtain ⟨I', hI, hv⟩ := hrun
  obtain ⟨r, d⟩ := jointRun_seqs E (.done (⟨n + 1⟩ : BoolH)) (.done (⟨n + 1⟩ : BoolH)) σA σB _
    (registerBlock_plain n password recovery tail) I I' hI
  rw [r, d]
  exact ⟨rfl, hv⟩

/-! ## `ceremony-register-ctr` on values -/

/-- **`ceremony-register-ctr` on every assignment** (as `KernelSpecs.signalRequestCtr_spec`): the
four outputs are `[255]`, the record header, the AES-CTR encryption of the inner plaintext, and the
GCM pad; the plaintext is `Ceremony.fill` of the frame with the two slots (`registerPlaintext_spec`). -/
theorem ceremonyRegisterCtr_spec (size payloadAt authAt tail recoveryAt : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (HybridKernel.lookup (CeremonyKernel.registerInputs size tail) name).map (BVExpr.eval assign)
    (CeremonyKernel.ceremonyRegisterCtr size payloadAt authAt tail recoveryAt).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      KernelSpecs.sealedRequest (get "clientApplication") (get "sequence")
        (TlsMpc.Ceremony.fill ByteAuth.concrete (get "frame") (get "mask") payloadAt
          (TlsMpc.Ceremony.registerSlots ByteAuth.concrete (get "secrets") tail authAt recoveryAt)) 255 := by
  intro get
  have ha := ByteAuth.evaluationHom assign
  have hp := CeremonyKernel.registerPlaintext_spec size payloadAt authAt tail recoveryAt assign
  simp only at hp
  have hinner : (TlsRecord.inner Gcm.symbolic (CeremonyKernel.registerPlaintext size payloadAt authAt tail recoveryAt)
      23 0).map (BVExpr.eval assign) = TlsRecord.inner Gcm.concrete
        (TlsMpc.Ceremony.fill ByteAuth.concrete (get "frame") (get "mask") payloadAt
          (TlsMpc.Ceremony.registerSlots ByteAuth.concrete (get "secrets") tail authAt recoveryAt)) 23 0 := by
    rw [TlsRecord.inner_map (Gcm.evaluationHom assign), hp]
  have innerLength : (TlsRecord.inner Gcm.symbolic
      (CeremonyKernel.registerPlaintext size payloadAt authAt tail recoveryAt) 23 0).length =
      ((TlsRecord.inner Gcm.symbolic (CeremonyKernel.registerPlaintext size payloadAt authAt tail recoveryAt)
        23 0).map (BVExpr.eval assign)).length := (List.length_map _).symm
  unfold CeremonyKernel.ceremonyRegisterCtr
  simp only [HybridKernel.pub, HybridKernel.priv, List.map_cons, List.map_nil,
    TlsRecord.header_map (Gcm.evaluationHom assign), ByteAuth.release_map ha, HybridKernel.ctr_eval,
    HybridKernel.gcmPad_eval, ha.const]
  rw [innerLength, hinner]
  rfl

/-- The bundle the record seal concatenates (`Send.requestCtrScript`): traffic ‖ sequence ‖ secrets
‖ frame ‖ mask. -/
def registerIn (K seqB secrets frame mask : B8) : B8 := K ++ (seqB ++ (secrets ++ (frame ++ mask)))

/-- **The register kernel's view of the record seal's bundle**: its five inputs are the traffic
block, the sequence, the secrets, the frame and the mask. -/
theorem register_get (t : Nat) (K seqB secrets frame mask : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hc : secrets.length = t + 54) (hm : mask.length = 4) :
    let get := fun name => (HybridKernel.lookup (CeremonyKernel.registerInputs frame.length t) name).map
      (BVExpr.eval (assignOf (registerIn K seqB secrets frame mask)))
    get "clientApplication" = K ∧ get "sequence" = seqB ∧ get "secrets" = secrets ∧ get "frame" = frame ∧
      get "mask" = mask := by
  intro get
  have hlen : (registerIn K seqB secrets frame mask).length = 60 + 8 + (t + 54) + frame.length + 4 := by
    simp [registerIn, hK, hs, hc, hm]; omega
  have g1 : HybridKernel.lookup (CeremonyKernel.registerInputs frame.length t) "clientApplication" =
      ByteCircuit.inputBytes 0 60 := by
    simp [HybridKernel.lookup, HybridKernel.lookupFrom, CeremonyKernel.registerInputs, BundleKernel.requestInputs]
  have g2 : HybridKernel.lookup (CeremonyKernel.registerInputs frame.length t) "sequence" =
      ByteCircuit.inputBytes 60 8 := by
    simp [HybridKernel.lookup, HybridKernel.lookupFrom, CeremonyKernel.registerInputs, BundleKernel.requestInputs,
      HybridKernel.Shape.variables]
  have g3 : HybridKernel.lookup (CeremonyKernel.registerInputs frame.length t) "secrets" =
      ByteCircuit.inputBytes 68 (t + 54) := by
    simp [HybridKernel.lookup, HybridKernel.lookupFrom, CeremonyKernel.registerInputs, BundleKernel.requestInputs,
      HybridKernel.Shape.variables, TlsMpc.Ceremony.passwordBytes, TlsMpc.Ceremony.recoveryBytes]
  have g4 : HybridKernel.lookup (CeremonyKernel.registerInputs frame.length t) "frame" =
      ByteCircuit.inputBytes (68 + (t + 54)) frame.length := by
    simp [HybridKernel.lookup, HybridKernel.lookupFrom, CeremonyKernel.registerInputs, BundleKernel.requestInputs,
      HybridKernel.Shape.variables, TlsMpc.Ceremony.passwordBytes, TlsMpc.Ceremony.recoveryBytes]
  have g5 : HybridKernel.lookup (CeremonyKernel.registerInputs frame.length t) "mask" =
      ByteCircuit.inputBytes (68 + (t + 54) + frame.length) 4 := by
    simp [HybridKernel.lookup, HybridKernel.lookupFrom, CeremonyKernel.registerInputs, BundleKernel.requestInputs,
      HybridKernel.Shape.variables, TlsMpc.Ceremony.passwordBytes, TlsMpc.Ceremony.recoveryBytes]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (HybridKernel.lookup _ "clientApplication").map _ = _
    rw [g1, iv _ _ _ (by omega), List.drop_zero, registerIn, List.take_left' hK]
  · show (HybridKernel.lookup _ "sequence").map _ = _
    rw [g2, iv _ _ _ (by omega), registerIn, List.drop_left' hK, List.take_left' hs]
  · show (HybridKernel.lookup _ "secrets").map _ = _
    rw [g3, iv _ _ _ (by omega), registerIn, show (68 : Nat) = (K ++ seqB).length by simp [hK, hs],
      ← List.append_assoc, List.drop_left' rfl, List.take_left' hc]
  · show (HybridKernel.lookup _ "frame").map _ = _
    rw [g4, iv _ _ _ (by omega), registerIn,
      show 68 + (t + 54) = (K ++ seqB ++ secrets).length by simp [hK, hs, hc]; omega,
      show K ++ (seqB ++ (secrets ++ (frame ++ mask))) = (K ++ seqB ++ secrets) ++ (frame ++ mask) by simp,
      List.drop_left' rfl, List.take_left' rfl]
  · show (HybridKernel.lookup _ "mask").map _ = _
    rw [g5, iv _ _ _ (by omega), registerIn,
      show 68 + (t + 54) + frame.length = (K ++ seqB ++ secrets ++ frame).length by simp [hK, hs, hc]; omega,
      show K ++ (seqB ++ (secrets ++ (frame ++ mask))) = (K ++ seqB ++ secrets ++ frame) ++ mask by simp,
      List.drop_left' rfl, List.take_of_length_le (by omega)]

/-- **The two slots of the registration request** for secrets tail ‖ password ‖ recovery: the end of
the Basic credential is base64(tail ‖ password), the JSON field base64(recovery). -/
theorem registerSlots_value (tail pw rc : B8) (authAt recoveryAt : Nat) (hp : pw.length = 22) (hr : rc.length = 32) :
    TlsMpc.Ceremony.registerSlots ByteAuth.concrete (tail ++ (pw ++ rc)) tail.length authAt recoveryAt =
      [(authAt, RelayEncoding.base64 ByteAuth.concrete (tail ++ pw)),
       (recoveryAt, RelayEncoding.base64 ByteAuth.concrete rc)] := by
  simp only [TlsMpc.Ceremony.registerSlots, TlsMpc.Ceremony.passwordBytes, TlsMpc.Ceremony.recoveryBytes]
  have e1 : (tail ++ (pw ++ rc)).take (tail.length + 22) = tail ++ pw := by
    rw [← List.append_assoc, List.take_left' (by simp [hp])]
  have e2 : ((tail ++ (pw ++ rc)).drop (tail.length + 22)).take 32 = rc := by
    rw [← List.append_assoc, List.drop_left' (by simp [hp]), List.take_of_length_le (by omega)]
  rw [e1, e2]

/-- **The register kernel on the record seal's bundle** (function level): for a request whose
secrets are tail ‖ password ‖ recovery, the kernel's outputs are `sealedRequest` of the frame filled
with base64(tail ‖ password) at the credential slot and base64(recovery) at the JSON slot, under the
WebSocket mask, accepted (255). -/
theorem registerCtr_value (payloadAt authAt recoveryAt : Nat) (K seqB tail pw rc frame mask : B8)
    (hK : K.length = 60) (hs : seqB.length = 8) (hp : pw.length = 22) (hr : rc.length = 32) (hm : mask.length = 4) :
    (CeremonyKernel.ceremonyRegisterCtr frame.length payloadAt authAt tail.length recoveryAt).outputs.map
        (fun field => field.value.map (BVExpr.eval (assignOf (registerIn K seqB (tail ++ (pw ++ rc)) frame mask)))) =
      KernelSpecs.sealedRequest K seqB
        (TlsMpc.Ceremony.fill ByteAuth.concrete frame mask payloadAt
          [(authAt, RelayEncoding.base64 ByteAuth.concrete (tail ++ pw)),
           (recoveryAt, RelayEncoding.base64 ByteAuth.concrete rc)]) 255 := by
  have h := ceremonyRegisterCtr_spec frame.length payloadAt authAt tail.length recoveryAt
    (assignOf (registerIn K seqB (tail ++ (pw ++ rc)) frame mask))
  obtain ⟨g1, g2, g3, g4, g5⟩ := register_get tail.length K seqB (tail ++ (pw ++ rc)) frame mask hK hs
    (by simp [hp, hr]) hm
  simp only at h g1 g2 g3 g4 g5
  rw [h, g1, g2, g3, g4, g5, registerSlots_value tail pw rc authAt recoveryAt hp hr]

/-! ## The headline: op 80 then op 81 -/

/-- **T4-CEREMONY (the headline).** Two honest parties run op 80 (ids from `n`) and then op 81 on the
handles it returned (ids from `m ≥ n + 11`), with tail `tail`: both return the request's secrets
handle `m + 1`, which holds tail ‖ password ‖ recovery password of the reference
(`Ceremony.secrets` on the parties' seeds, masks and recovery halves); and on the record seal's
bundle with those secrets the register kernel outputs `sealedRequest` of the frame filled with
base64(tail ‖ password) and base64(recovery password) (function level, `registerCtr_value`). With
`shares_xor` the controllers' replies of op 80 XOR to password ‖ recovery password. -/
theorem ceremony_honest (E : Env) (σA σB : Store) (hE : SecretsLoaded E) (I : Ideal)
    (n m seedSlot maskSlot recoverySlot : Nat) (hm : n + 11 ≤ m) (sA sB mA mB rA rB tail : B8)
    (hsA : sA.length = 18) (hsB : sB.length = 18) (hmA : mA.length = 22) (hmB : mB.length = 22)
    (hrA : rA.length = 32) (hrB : rB.length = 32) (htl : tail.length ≤ 2)
    (hσA : σA.bits seedSlot = bitsOf sA ∧ σA.bits maskSlot = bitsOf mA ∧ σA.bits recoverySlot = bitsOf rA)
    (hσB : σB.bits seedSlot = bitsOf sB ∧ σB.bits maskSlot = bitsOf mB ∧ σB.bits recoverySlot = bitsOf rB) :
    let s := (secretsScript n seedSlot maskSlot recoverySlot).bind fun r => registerScript m r.password r.recovery tail
    let ref := reference sA sB mA mB rA rB
    (jointRun E s s σA σB I).result = some (⟨m + 1⟩, ⟨m + 1⟩) ∧
    (jointRun E s s σA σB I).ideal.bools (m + 1) = some (bitsOf (tail ++ (ref.getD 0 [] ++ ref.getD 1 []))) ∧
    ∀ (payloadAt authAt recoveryAt : Nat) (K seqB frame mask : B8), K.length = 60 → seqB.length = 8 →
      mask.length = 4 →
      (CeremonyKernel.ceremonyRegisterCtr frame.length payloadAt authAt tail.length recoveryAt).outputs.map
          (fun field => field.value.map (BVExpr.eval (assignOf
            (registerIn K seqB (tail ++ (ref.getD 0 [] ++ ref.getD 1 [])) frame mask)))) =
        KernelSpecs.sealedRequest K seqB
          (TlsMpc.Ceremony.fill ByteAuth.concrete frame mask payloadAt
            [(authAt, RelayEncoding.base64 ByteAuth.concrete (tail ++ ref.getD 0 [])),
             (recoveryAt, RelayEncoding.base64 ByteAuth.concrete (ref.getD 1 []))]) 255 := by
  intro s ref
  obtain ⟨pw, rc, mk, href, hpw, hrc, -, -, -⟩ := secrets_lengths sA sB mA mB rA rB hsA hsB hmA hmB hrA hrB
  obtain ⟨h1, h2, h3, -⟩ := secrets_honest E σA σB hE I n seedSlot maskSlot recoverySlot sA sB mA mB rA rB
    hsA hsB hmA hmB hrA hrB hσA hσB
  simp only [ref, href, List.getD_cons_zero, List.getD_cons_succ] at h1 h2 h3 ⊢
  have hb := jointRun_bind E _ _ (fun r : Made => registerScript m r.password r.recovery tail)
    (fun r : Made => registerScript m r.password r.recovery tail) σA σB I _ _ h1
  obtain ⟨r1, r2⟩ := register_honest E _ _ _ m ⟨n + 8⟩ ⟨n + 9⟩ tail pw rc htl (by simp; omega) (by simp; omega) h2 h3
  refine ⟨?_, ?_, fun payloadAt authAt recoveryAt K seqB frame mask hK hs hmk =>
    registerCtr_value payloadAt authAt recoveryAt K seqB tail pw rc frame mask hK hs hpw hrc hmk⟩
  · show (jointRun E (Script.bind _ _) (Script.bind _ _) σA σB I).result = _
    rw [hb]
    simpa [Outcome2.then] using r1
  · show (jointRun E (Script.bind _ _) (Script.bind _ _) σA σB I).ideal.bools (m + 1) = _
    rw [hb]
    simpa [Outcome2.then] using r2

end TlsMpc.Node.Flows.Ceremony
