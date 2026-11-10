import XEdDsaReferenceWork.FieldDecodeProof
import TlsMpc.Signal.XEdDsaField

/-! Actual pinned dalek byte normalization at the input to the frozen shared
recovery circuit. The circuit's recovery formulas are not here claimed equal
to dalek's full to_edwards implementation. No input canonicality is imposed. -/
namespace XEdDsaReference.RecoveryInput
open Aeneas Aeneas.Std
open backend.serial.u64.field
open TlsMpc

def decodeNat (n : Nat) : FieldDag.F := FieldDag.ofNat (n % 2^255)
def decode (bytes : Array Std.U8 32#usize) : FieldDag.F := decodeNat (bytes.asNat 8)
def represented (limbs : FieldElement51) : FieldDag.F := FieldDag.ofNat limbs.asNat

theorem actual_decode_normalizes (bytes : Array Std.U8 32#usize) :
    ∃ limbs, FieldElement51.from_bytes bytes = .ok limbs ∧
      represented limbs = decode bytes ∧ limbs.LimbsLt 51 := by
  obtain ⟨limbs,hout,hval,hbounds⟩ :=
    WP.spec_imp_exists (FieldElement51.from_bytes_spec bytes)
  exact ⟨limbs,hout,by simp only [represented,decode,decodeNat,hval],hbounds⟩

theorem decode_nat_value (n : Nat) :
    (decodeNat n).val = (n % 2^255) % FieldDag.modulus := rfl

theorem high_bit_ignored (n : Nat) : decodeNat (n + 2^255) = decodeNat n := by
  simp only [decodeNat,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]

/-- All nineteen noncanonical low255-bit encodings p..p+18 are accepted as
field representations. This statement does not imply curve-point validity. -/
theorem noncanonical_reduction (k : Nat) (hk : k < 19) :
    decodeNat (FieldDag.modulus + k) = FieldDag.ofNat k := by
  have hsmall : FieldDag.modulus + k < 2^255 := by
    unfold FieldDag.modulus
    omega
  apply Fin.ext
  change ((FieldDag.modulus+k) % 2^255) % FieldDag.modulus = k % FieldDag.modulus
  rw [Nat.mod_eq_of_lt hsmall, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

/-- Actual decoder output and the shared compiler's normalization input agree.
Only the frozen circuit's own recovery formulas are on the right-hand side. -/
theorem compiled_recovery_input (bytes : Array Std.U8 32#usize) (index : Nat)
    (artifact : FieldDag.Artifact)
    (hc : FieldDag.compile (Signal.XEdDsaField.output true index) = some artifact) :
    ∃ limbs, FieldElement51.from_bytes bytes = .ok limbs ∧
      FieldDag.result (FieldDag.concrete (fun _ => decode bytes)) artifact.nodes artifact.output =
        (Signal.XEdDsaField.recover X25519.concrete (represented limbs))[index]?.getD
          (FieldDag.ofNat 0) := by
  obtain ⟨limbs,hout,hval,_⟩ := actual_decode_normalizes bytes
  refine ⟨limbs,hout,?_⟩
  rw [Signal.XEdDsaField.compiled_output_correct true index (fun _ => decode bytes) artifact hc]
  simp only [Signal.XEdDsaField.run, ↓reduceIte]
  rw [hval]

/-- Field-equivalent byte encodings produce equal represented actual Rust
outputs. The limbs themselves may differ for noncanonical aliases. -/
theorem actual_decode_field_alias (a b : Array Std.U8 32#usize)
    (h : (a.asNat 8 % 2^255) % FieldDag.modulus =
      (b.asNat 8 % 2^255) % FieldDag.modulus) :
    ∃ la lb, FieldElement51.from_bytes a = .ok la ∧
      FieldElement51.from_bytes b = .ok lb ∧ represented la = represented lb ∧
      la.LimbsLt 51 ∧ lb.LimbsLt 51 := by
  obtain ⟨la,ha,hva,hba⟩ := actual_decode_normalizes a
  obtain ⟨lb,hb,hvb,hbb⟩ := actual_decode_normalizes b
  refine ⟨la,lb,ha,hb,?_,hba,hbb⟩
  rw [hva,hvb]
  apply Fin.ext
  exact h

/-- Every compiled recovery output is invariant under the same field aliases
as the actual decoder. This remains a statement about frozen recovery formulas,
not a refinement of dalek's complete point-validity or signature verifier. -/
theorem compiled_recovery_field_alias (a b : Array Std.U8 32#usize)
    (h : (a.asNat 8 % 2^255) % FieldDag.modulus =
      (b.asNat 8 % 2^255) % FieldDag.modulus)
    (index : Nat) (artifact : FieldDag.Artifact)
    (hc : FieldDag.compile (Signal.XEdDsaField.output true index) = some artifact) :
    FieldDag.result (FieldDag.concrete (fun _ => decode a)) artifact.nodes artifact.output =
      FieldDag.result (FieldDag.concrete (fun _ => decode b)) artifact.nodes artifact.output := by
  obtain ⟨la,ha,hva,_⟩ := actual_decode_normalizes a
  obtain ⟨lb,hb,hvb,_⟩ := actual_decode_normalizes b
  obtain ⟨la',lb',ha',hb',heq,_,_⟩ := actual_decode_field_alias a b h
  have hla : la' = la := by simpa [ha] using ha'.symm
  have hlb : lb' = lb := by simpa [hb] using hb'.symm
  subst la'; subst lb'
  have hd : decode a = decode b := hva.symm.trans (heq.trans hvb)
  rw [Signal.XEdDsaField.compiled_output_correct true index (fun _ => decode a) artifact hc,
    Signal.XEdDsaField.compiled_output_correct true index (fun _ => decode b) artifact hc, hd]

end XEdDsaReference.RecoveryInput
