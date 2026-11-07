import LibSignalReference.Generated.AesSubBytes.Funs
import LibSignalReference.Proofs.AesNetwork
import TlsMpc.ByteCircuit

/-!
The selected actual RustCrypto software S-box omits four NOT operations,
which its key schedule accounts for separately. Here we compare the translated
`sub_bytes` followed by the translated `sub_bytes_nots` with the MPC S-box.
This is a leaf equivalence, not a complete AES key-schedule/CBC refinement.
-/

namespace LibSignalReference.Proofs.AesSubBytes

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std
open TlsMpc.AesSbox

def wordOps : Ops U64 := ⟨0#u64, (· ^^^ ·), (· &&& ·), (· ^^^ 18446744073709551615#u64)⟩

def bitvectorOps : Ops (BitVec 64) := ⟨0, (· ^^^ ·), (· &&& ·), (~~~ ·)⟩

def input (a b c d e f g h : U64) : Slice U64 :=
  ⟨[a, b, c, d, e, f, g, h], by simp; scalar_tac⟩

def output (a b c d e f g h : U64) : Slice U64 :=
  ⟨AesNetwork.run wordOps [a, b, c, d, e, f, g, h], by
    simp [AesNetwork.run, AesNetwork.indices]; scalar_tac⟩

def translated (state : Slice U64) : Result (Slice U64) := do
  let state ← RustCryptoAesSubBytes.soft.fixslice.sub_bytes state
  RustCryptoAesSubBytes.soft.fixslice.sub_bytes_nots state

theorem translated_network (a b c d e f g h : U64) :
    translated (input a b c d e f g h) = .ok (output a b c d e f g h) := by
  have hlen (hx : 8 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 8 hx = 8#usize := by scalar_tac
  simp [translated, RustCryptoAesSubBytes.soft.fixslice.sub_bytes,
    RustCryptoAesSubBytes.soft.fixslice.sub_bytes_nots, input, output,
    Slice.len, Slice.index_usize, Slice.update, lift, hlen, massert,
    AesNetwork.run, AesNetwork.program, AesNetwork.rawProgram, AesNetwork.indices,
    TlsMpc.AesSbox.run, gate, wordOps]

theorem wordHom : Hom wordOps bitvectorOps (fun x : U64 => x.bv) := by
  constructor
  · rfl
  · intros; rfl
  · intros; rfl
  · intro x
    change x.bv ^^^ (BitVec.allOnes 64) = ~~~x.bv
    exact BitVec.xor_allOnes

def wordLane (n : Nat) (x : U64) : BitVec 1 := x.bv.extractLsb' n 1

theorem wordLaneHom (n : Nat) (hn : n < 64) : Hom wordOps concrete (wordLane n) := by
  constructor
  · simp [wordLane, wordOps, concrete]
  · intros; simp [wordLane, wordOps, concrete, BitVec.extractLsb'_xor]
  · intros; simp [wordLane, wordOps, concrete, BitVec.extractLsb'_and]
  · intro x
    change (x.bv ^^^ BitVec.allOnes 64).extractLsb' n 1 = ~~~(x.bv.extractLsb' n 1)
    rw [BitVec.xor_allOnes]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 1
    · have he : i = 0 := by omega
      subst i
      simp [hn]
    · simp [BitVec.getLsbD_not, hi]

set_option maxHeartbeats 0 in
theorem bits_of_packed : ∀ a b c d e f g h : BitVec 1,
    (List.range 8).map (fun i => (packValue [a,b,c,d,e,f,g,h]).extractLsb' i 1) =
      [a,b,c,d,e,f,g,h] := by decide +kernel

theorem network_byte (a b c d e f g h : BitVec 1) :
    packValue (AesNetwork.run concrete [a,b,c,d,e,f,g,h]) =
      value (packValue [a,b,c,d,e,f,g,h]) := by
  have result := AesNetwork.byte_correct (packValue [a,b,c,d,e,f,g,h])
  rw [bits_of_packed] at result
  exact result

/-- Every one of the 64 parallel byte lanes matches the existing MPC S-box,
    for all eight input words, after restoring the actual omitted NOTs. -/
theorem translated_lane (a b c d e f g h : U64) (n : Nat) (hn : n < 64) :
    ∃ result, translated (input a b c d e f g h) = .ok result ∧
      packValue (result.val.map (wordLane n)) =
        value (packValue ((input a b c d e f g h).val.map (wordLane n))) := by
  refine ⟨output a b c d e f g h, translated_network a b c d e f g h, ?_⟩
  change packValue ((AesNetwork.run wordOps [a,b,c,d,e,f,g,h]).map (wordLane n)) = _
  rw [AesNetwork.run_map (wordLaneHom n hn)]
  exact network_byte _ _ _ _ _ _ _ _

theorem translated_bad_length (state : Slice U64) (hlen : state.length ≠ 8) :
    translated state = .fail .assertionFailure := by
  have h : Slice.len state ≠ 8#usize := by scalar_tac
  simp [translated, RustCryptoAesSubBytes.soft.fixslice.sub_bytes, h, massert]

theorem sbox_refines_artifact (a b c d e f g h : U64) (n : Nat) (hn : n < 64)
    (secret : _root_.Std.Tactic.BVDecide.BVExpr 8)
    (assign : _root_.Std.Tactic.BVDecide.BVExpr.Assignment)
    (hsecret : secret.eval assign =
      packValue ((input a b c d e f g h).val.map (wordLane n))) :
    ∃ result, translated (input a b c d e f g h) = .ok result ∧
      ∀ (index : Nat) (hi : index < 8 * [TlsMpc.AesSbox.expr secret].length),
        TlsMpc.AigExport.evalRef
          (TlsMpc.AigExport.exportNodes (TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr [TlsMpc.AesSbox.expr secret])).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (TlsMpc.AigExport.exportRef ((TlsMpc.AigExport.compile
            (TlsMpc.ByteCircuit.joinExpr [TlsMpc.AesSbox.expr secret])).vec.get index hi)) =
          (TlsMpc.ByteCircuit.joinValue [packValue (result.val.map (wordLane n))]).getLsbD index := by
  obtain ⟨result, hr, hv⟩ := translated_lane a b c d e f g h n hn
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [TlsMpc.ByteCircuit.compile_bytes_correct]
  simp only [List.map_cons, List.map_nil]
  rw [TlsMpc.AesSbox.expr_refines assign secret, hsecret,
    ← TlsMpc.AesSbox.value_eq_spec, ← hv]

end LibSignalReference.Proofs.AesSubBytes
