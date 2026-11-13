import TlsMpc.Node.Flows.Registry
import TlsMpc.Sha256

/-!
# Stand-in tables shared by the test vector files and the runner test (TEST ONLY)

STACK_NOTES J14. The stand-in programs and circuits the stage vector files evaluate the scripts
against (the exported texts come from the re-export; their pins are placeholders in loader.rs until
then), as a module both `node_worker/tests/lean/S10Vectors.lean` and
`node_worker/tests/lean/RunnerTest.lean` import, so the runner test drives the runner on the SAME
tables the vector files' outputs were computed with. Moved verbatim from `S10Vectors.lean` (its
output is byte-identical after the move). Nothing in the library imports this module; no I/O.

  * `sha256`: SHA-256 on bytes (the model's `Env.hash`).
  * S10: `field-bit-check`, `field-bit-xor`, `field-recompose` as V3 rows with the values
    `Conv.ProgsLoaded` states; `field-mask-sub` and `field-quotient` are the Lean programs
    themselves (`Conv.maskSub`, `FieldDagV3.quotient`); the word circuits are S10's model circuits
    (`Conv.modaddC` …, `swapBitsC`).
-/

namespace TlsMpc.Node.TestStandIns

open TlsMpc.Node.Engine
open TlsMpc.FieldDag (F)
open TlsMpc.FieldDag.V3 (Program Row)
open TlsMpc.Node.Flows
open TlsMpc.Node.Flows.Conv

def sha256 (m : Bytes) : Bytes :=
  (TlsMpc.Sha256.hash TlsMpc.Sha256.concrete (m.map fun b => BitVec.ofNat 8 b.toNat)).map
    fun b => UInt8.ofNat b.toNat

/-! ## S10: the conversions' programs and circuits -/

def bitCheckP : Program :=
  { inputs := 1, masks := 0, rows := [.input 0, .const 1, .sub 0 1, .mul 0 2], outputs := [(3, .pub)] }

def bitXorP : Program :=
  { inputs := 2, masks := 0, rows := [.input 0, .input 1, .add 0 1, .mul 0 1, .const 2, .mul 4 3, .sub 2 5],
    outputs := [(6, .never)] }

/-- Horner: acc₂₅₄ = in₂₅₄, accᵢ = inᵢ + 2·accᵢ₊₁, then acc₀ − in₂₅₅. -/
def recomposeRows : List Row × Nat :=
  (List.range 254).foldl (fun (st : List Row × Nat) k =>
    let n := st.1.length
    (st.1 ++ [Row.mul 256 st.2, Row.add (253 - k) n], n + 1))
    ((List.range 256).map Row.input ++ [Row.const 2], 254)

def recomposeP : Program :=
  { inputs := 256, masks := 0, rows := recomposeRows.1 ++ [Row.sub recomposeRows.2 255],
    outputs := [(recomposeRows.1.length, .pub)] }

def s10Programs : List (String × Program) :=
  [("field-bit-check", bitCheckP), ("field-bit-xor", bitXorP), ("field-recompose", recomposeP),
   ("field-mask-sub", maskSub), ("field-quotient", TlsMpc.FieldDag.V3.quotient)]

def s10Circuits : List (String × Circuit) :=
  [("modadd", modaddC), ("modadd-open", modaddOpenC), ("finalize-mask", finalizeMaskC),
   ("finalize-bits", finalizeBitsC), ("into-field-open", intoFieldOpenC), ("xor-bit", xorBitC),
   ("xor-bit-open", xorBitOpenC), ("swap-bits", swapBitsC)]

/-- A table lookup by the circuit / program name's bytes. -/
def lookup {α : Type} (t : List (String × α)) (n : Bytes) : Option α := (t.find? (fun e => ascii e.1 == n)).map (·.2)

def s10Env : Env :=
  { circuits := lookup s10Circuits, hash := sha256, programs := lookup s10Programs }

end TlsMpc.Node.TestStandIns
