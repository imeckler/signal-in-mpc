import TlsMpc.HybridKernels
import TlsMpc.Signal.MlKemFast

/-!
Worker kernels for Kyber-1024 / ML-KEM-1024 ENCAPSULATION to a private key, in
the conventions of `TlsMpc/HybridKernels.lean`. Together they replace
`establish-kem` (`TlsMpc/EstablishKernels.lean`, about 190 million AND gates)
and produce its three outputs under the same names. The bodies are the stage
functions of `TlsMpc/Signal/MlKemFast.lean`; the theorems are in
`TlsMpc/MlKemFastProofs.lean`; the design, the measured gate counts and the
argument for the sampling budget are in
`handshake_backend/EmpHybridWork/ML_KEM_ENCAPSULATION.md`.

NOTHING is opened by any of these kernels. Every output is private and is
passed to a later kernel by name.

`VARIANT` is `kyber` (round-3 Kyber-1024, libsignal's key type 8, what PQXDH
uses: the message is hashed first and the secret is SHAKE256(K ‖ H(c))) or
`mlkem` (FIPS 203 ML-KEM-1024, key type 10).

## Order of operations for one encapsulation

Inputs: `kyberPrekey` (1568 bytes, private), `entropyA`, `entropyB` (32 bytes,
one private input of each party; the randomness is their XOR).

1. `kem-hash VARIANT`: `message`, `kbar`, `coins` (32 each), `keyValid` (255
   exactly when every coefficient of the key is below q: the modulus check of
   FIPS 203 §7.2).
2. `kem-ntt` (input `coins`): `rhat`, the NTT of the four secret polynomials.
3. `kem-matrix ROW` for ROW = 0..3 (input `kyberPrekey`): `rowROW`, four
   entries of the matrix expanded from the key's seed, and `okROW` (255 unless
   an entry found fewer than 256 coefficients in four SHAKE128 blocks).
4. `kem-u ROW` for ROW = 0..3 (inputs `rowROW`, `rhat`, `coins`): `uROW`, the
   compressed polynomial (352 bytes).
5. `kem-v` (inputs `kyberPrekey`, `rhat`, `coins`, `message`): `v` (160 bytes).
6. `kem-finish VARIANT` (inputs `u0`..`u3`, `v`, `kbar`, `ok0`..`ok3`,
   `keyValid`): `kemStatus`, `kemCiphertext` (1568), `kemSecret` (32), the
   inputs of `establish-session`. The ciphertext and the secret are zero
   unless the status is 255.

Steps 2 and 3 are independent of each other; step 4 needs both; step 5 needs
steps 1 and 2.
-/
namespace TlsMpc.MlKemFastKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape Output lookup priv)

def hashInputs : List (String × Shape) :=
  [("kyberPrekey", Shape.bytes 1568), ("entropyA", .bytes 32), ("entropyB", .bytes 32)]

def kemHash (kyber : Bool) : Kernel :=
  let get := lookup hashInputs
  let out := MlKemFast.hashStage MlKemFast.symbolic ByteAuth.symbolic Keccak.symbolic kyber
    (get "kyberPrekey") (get "entropyA") (get "entropyB")
  { name := "kem-hash", inputs := hashInputs, outputs := [
      priv "message" (out.getD 0 []), priv "kbar" (out.getD 1 []), priv "coins" (out.getD 2 []),
      priv "keyValid" (out.getD 3 [])] }

def nttInputs : List (String × Shape) := [("coins", Shape.bytes 32)]

def kemNtt (_ : Unit) : Kernel :=
  { name := "kem-ntt", inputs := nttInputs, outputs := [
      priv "rhat" (MlKemFast.nttStage MlKemFast.symbolic ByteAuth.symbolic Keccak.symbolic
        (lookup nttInputs "coins"))] }

def matrixInputs : List (String × Shape) := [("kyberPrekey", Shape.bytes 1568)]

def kemMatrix (row : Nat) : Kernel :=
  let out := MlKemFast.matrixStage MlKemFast.symbolic ByteAuth.symbolic Keccak.symbolic row
    (lookup matrixInputs "kyberPrekey")
  { name := "kem-matrix", inputs := matrixInputs, outputs := [
      priv s!"row{row}" (out.getD 0 []), priv s!"ok{row}" (out.getD 1 [])] }

def uInputs (row : Nat) : List (String × Shape) :=
  [(s!"row{row}", Shape.bytes 1536), ("rhat", .bytes 1536), ("coins", .bytes 32)]

def kemU (row : Nat) : Kernel :=
  let get := lookup (uInputs row)
  { name := "kem-u", inputs := uInputs row, outputs := [
      priv s!"u{row}" (MlKemFast.uStage MlKemFast.symbolic ByteAuth.symbolic Keccak.symbolic row
        (get s!"row{row}") (get "rhat") (get "coins"))] }

def vInputs : List (String × Shape) :=
  [("kyberPrekey", Shape.bytes 1568), ("rhat", .bytes 1536), ("coins", .bytes 32), ("message", .bytes 32)]

def kemV (_ : Unit) : Kernel :=
  let get := lookup vInputs
  { name := "kem-v", inputs := vInputs, outputs := [
      priv "v" (MlKemFast.vStage MlKemFast.symbolic ByteAuth.symbolic Keccak.symbolic
        (get "kyberPrekey") (get "rhat") (get "coins") (get "message"))] }

def finishInputs : List (String × Shape) :=
  [("u0", Shape.bytes 352), ("u1", .bytes 352), ("u2", .bytes 352), ("u3", .bytes 352), ("v", .bytes 160),
    ("kbar", .bytes 32), ("ok0", .bytes 1), ("ok1", .bytes 1), ("ok2", .bytes 1), ("ok3", .bytes 1),
    ("keyValid", .bytes 1)]

def kemFinish (kyber : Bool) : Kernel :=
  let get := lookup finishInputs
  let out := MlKemFast.finishStage ByteAuth.symbolic Keccak.symbolic kyber
    (get "u0" ++ get "u1" ++ get "u2" ++ get "u3" ++ get "v") (get "kbar")
    (get "ok0" ++ get "ok1" ++ get "ok2" ++ get "ok3" ++ get "keyValid")
  { name := "kem-finish", inputs := finishInputs, outputs := [
      priv "kemStatus" (out.getD 0 []), priv "kemCiphertext" (out.getD 1 []), priv "kemSecret" (out.getD 2 [])] }

def sampleInputs : List (String × Shape) := [("stream", Shape.bytes 672)]

/-- CHECK ONLY: the sampler of `kem-matrix` on a given stream instead of SHAKE128 output, so that
streams with too few accepted candidates can be tried. Not part of the sequence. -/
def kemSample (_ : Unit) : Kernel :=
  let out := MlKemFast.sampleStage MlKemFast.symbolic (lookup sampleInputs "stream")
  { name := "kem-sample", inputs := sampleInputs, outputs := [
      priv "entry" (out.getD 0 []), priv "ok" (out.getD 1 [])] }

def variant : String → Option Bool
  | "kyber" => some true
  | "mlkem" => some false
  | _ => none

def rowOf (text : String) : Option Nat :=
  match text.toNat? with
  | some row => if row < 4 then some row else none
  | none => none

set_option compiler.extract_closed false in   -- or the argument-free kernels would be built at program start
/-- Kernel named on the command line: `kem-hash VARIANT`, `kem-ntt`,
`kem-matrix ROW`, `kem-u ROW`, `kem-v`, `kem-finish VARIANT` (`VARIANT` is
`kyber` or `mlkem`, `ROW` is 0..3), and the check-only `kem-sample`. -/
def find : List String → Option Kernel
  | ["kem-hash", v] => (variant v).map kemHash
  | ["kem-ntt"] => some (kemNtt ())
  | ["kem-matrix", row] => (rowOf row).map kemMatrix
  | ["kem-u", row] => (rowOf row).map kemU
  | ["kem-v"] => some (kemV ())
  | ["kem-finish", v] => (variant v).map kemFinish
  | ["kem-sample"] => some (kemSample ())
  | _ => none

end TlsMpc.MlKemFastKernel
