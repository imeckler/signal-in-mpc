import TlsMpc.Artifact
import TlsMpc.Protocols

/-!
TLS 1.3 layout specification (RFC 9846 sections 5.2 and 5.3).
This is byte-exact framing and nonce construction, not an AEAD or handshake.
Byte strings are MSB-first Boolean lists. Lengths/padding are public shape.
-/

namespace TlsMpc.Tls13

def byteBits (byte : BitVec 8) : List Bool :=
  List.ofFn (fun (bit : Fin 8) => byte.getLsbD (7 - bit.val))

def byteExpr (byte : BitVec 8) : List (Boolean.Expr inputs) :=
  (byteBits byte).map .literal

theorem byteExpr_correct (byte : BitVec 8) (env : Fin inputs → Bool) :
    (byteExpr byte).map (Boolean.Expr.eval env) = byteBits byte := by
  simp [byteExpr, List.map_map, Boolean.Expr.eval, Function.comp_def]

def inputsExpr (inputs : Nat) : List (Boolean.Expr inputs) := List.ofFn .input

theorem inputsExpr_correct (inputs : Nat) (env : Fin inputs → Bool) :
    (inputsExpr inputs).map (Boolean.Expr.eval env) = List.ofFn env := by
  simp [inputsExpr, List.map_ofFn, Function.comp_def, Boolean.Expr.eval]

def innerSpec (content : List Bool) (kind : BitVec 8) (padding : Nat) : List Bool :=
  content ++ byteBits kind ++ List.replicate (8 * padding) false

def innerCircuit (contentBytes : Nat) (kind : BitVec 8) (padding : Nat) :
    List (Boolean.Expr (8 * contentBytes)) :=
  inputsExpr (8 * contentBytes) ++ byteExpr kind ++ List.replicate (8 * padding) (.literal false)

theorem innerCircuit_correct (contentBytes padding : Nat) (kind : BitVec 8)
    (env : Fin (8 * contentBytes) → Bool) :
    (innerCircuit contentBytes kind padding).map (Boolean.Expr.eval env) =
      innerSpec (List.ofFn env) kind padding := by
  simp [innerCircuit, innerSpec, inputsExpr_correct, byteExpr_correct, Boolean.Expr.eval]

def headerBytes (ciphertextBytes : Nat) : List (BitVec 8) :=
  [23, 3, 3, BitVec.ofNat 8 (ciphertextBytes / 256), BitVec.ofNat 8 ciphertextBytes]

def headerSpec (ciphertextBytes : Nat) : List Bool :=
  (headerBytes ciphertextBytes).flatMap byteBits

def headerCircuit (ciphertextBytes : Nat) : List (Boolean.Expr 0) :=
  (headerBytes ciphertextBytes).flatMap byteExpr

theorem headerCircuit_correct (ciphertextBytes : Nat) (env : Fin 0 → Bool) :
    (headerCircuit ciphertextBytes).map (Boolean.Expr.eval env) = headerSpec ciphertextBytes := by
  simp [headerCircuit, headerSpec, List.map_flatMap, byteExpr_correct]

/-- Output order matches the TLS nonce's network byte order. -/
def nonceCircuit : List (Boolean.Expr 160) :=
  List.ofFn (fun (i : Fin 96) => nonceExpr ⟨95 - i.val, by omega⟩)

theorem nonceCircuit_correct (iv : BitVec 96) (sequence : BitVec 64) :
    nonceCircuit.map (Boolean.Expr.eval (nonceInputs iv sequence)) =
      List.ofFn (fun (i : Fin 96) => (nonce iv sequence).getLsbD (95 - i.val)) := by
  simp only [nonceCircuit, List.map_ofFn, Function.comp_def, nonceExpr_correct]

def nonceEnvironment (iv : BitVec 96) (sequence : BitVec 64) (i : Nat) : Bool :=
  if i < 96 then iv.getLsbD i else sequence.getLsbD (i - 96)

theorem exported_nonce_correct (iv : BitVec 96) (sequence : BitVec 64) :
    Boolean.Artifact.evaluateProgram (nonceEnvironment iv sequence)
      (Boolean.Artifact.exportProgram nonceCircuit) =
      some (List.ofFn (fun (i : Fin 96) => (nonce iv sequence).getLsbD (95 - i.val))) := by
  rw [Boolean.Artifact.exportProgram_correct]
  change some (nonceCircuit.map (Boolean.Expr.eval (nonceInputs iv sequence))) = _
  rw [nonceCircuit_correct]

theorem exported_inner_correct (contentBytes padding : Nat) (kind : BitVec 8)
    (env : Nat → Bool) :
    Boolean.Artifact.evaluateProgram env
      (Boolean.Artifact.exportProgram (innerCircuit contentBytes kind padding)) =
      some (innerSpec (List.ofFn (fun (i : Fin (8 * contentBytes)) => env i.val)) kind padding) := by
  rw [Boolean.Artifact.exportProgram_correct, innerCircuit_correct]

theorem exported_header_correct (ciphertextBytes : Nat) (env : Nat → Bool) :
    Boolean.Artifact.evaluateProgram env
      (Boolean.Artifact.exportProgram (headerCircuit ciphertextBytes)) =
      some (headerSpec ciphertextBytes) := by
  rw [Boolean.Artifact.exportProgram_correct, headerCircuit_correct]

end TlsMpc.Tls13
