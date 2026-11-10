import TlsMpc.WordMask
import TlsMpc.FieldBits
import TlsMpc.X25519SwapBits
import TlsMpc.EdwardsShare
open TlsMpc TlsMpc.WordMask TlsMpc.BoolDag

/-! Export the conversion-mask circuits as flat gate lists.

Inputs are wires 0..509 (word `x` then word `y`, least significant bit first);
every other node becomes the next wire. Output `k` is the `k`-th expression of
the Lean circuit. The node list comes from `BoolDag.compile`, which is covered by
`BoolDag.compile_correct`; this printer (wire numbering, the `N` shorthand for
XOR with constant true, constant wires) is outside the theorems and is checked
against integer arithmetic by `lower_word_circuits.py`. -/

structure Printer where
  lines : Array String := #[]
  wire : Array Nat := #[]          -- node index → wire
  constTrue : Array Bool := #[]    -- node index is the constant true
  inputs : Nat := 510
  next : Nat := 510
  zero : Option Nat := none
  one : Option Nat := none

def Printer.emit (p : Printer) (line : String) : Nat × Printer :=
  (p.next, { p with lines := p.lines.push line, next := p.next + 1 })

def Printer.getZero (p : Printer) : Nat × Printer :=
  match p.zero with
  | some w => (w, p)
  | none => let (w, q) := p.emit "X 0 0"; (w, { q with zero := some w })

def Printer.getOne (p : Printer) : Nat × Printer :=
  match p.one with
  | some w => (w, p)
  | none =>
      let (z, q) := p.getZero
      let (w, r) := q.emit s!"N {z}"
      (w, { r with one := some w })

def Printer.node (p : Printer) : Node → Except String Printer
  | .input i =>
      if i < p.inputs then pure { p with wire := p.wire.push i, constTrue := p.constTrue.push false }
      else throw "input index out of range"
  | .const false =>
      let (w, q) := p.getZero
      pure { q with wire := q.wire.push w, constTrue := q.constTrue.push false }
  | .const true =>
      let (w, q) := p.getOne
      pure { q with wire := q.wire.push w, constTrue := q.constTrue.push true }
  | .bin op a b => do
      let some wa := p.wire[a]? | throw "dangling operand"
      let some wb := p.wire[b]? | throw "dangling operand"
      let ta := p.constTrue[a]?.getD false
      let tb := p.constTrue[b]?.getD false
      let line := match op with
        | .and => s!"A {wa} {wb}"
        | .xor => if tb then s!"N {wa}" else if ta then s!"N {wb}" else s!"X {wa} {wb}"
      let (w, q) := p.emit line
      pure { q with wire := q.wire.push w, constTrue := q.constTrue.push false }

def render (es : List Expr) (inputs : Nat := 510) : Except String String := do
  let some artifact := compile es | throw "circuit failed its translation validator"
  let printer ← artifact.nodes.foldlM Printer.node { inputs, next := inputs }
  let outputs ← artifact.outputs.mapM (fun o => match printer.wire[o]? with
    | some w => pure w | none => throw "dangling output")
  let header := s!"EMP_HYBRID_BOOL_V1\n{inputs} {printer.lines.size} {outputs.length}\n"
  let body := printer.lines.foldl (fun acc line => acc ++ line ++ "\n") ""
  pure (header ++ body ++ "O " ++ " ".intercalate (outputs.map toString) ++ "\n")

/-- Field programs in the flat format the native loader reads. Constants are
restricted to what the loader accepts as machine words. -/
def renderField (inputs : Nat) (e : FieldDag.Expr) : Except String String := do
  let some artifact := FieldDag.compile e | throw "field program failed its translation validator"
  let rows ← artifact.nodes.mapM (fun node => match node with
    | FieldDag.Node.const n => if n < 2 ^ 63 then pure s!"C {n}" else throw "field constant too large"
    | .input i => if i < inputs then pure s!"I {i}" else throw "field input out of range"
    | .bin .add a b => pure s!"A {a} {b}"
    | .bin .sub a b => pure s!"S {a} {b}"
    | .bin .mul a b => pure s!"M {a} {b}")
  let header := s!"EMP_HYBRID_FIELD_DAG_V1\n{inputs} {rows.length} {artifact.output}\n{FieldDag.modulus}\n"
  pure (header ++ rows.foldl (fun acc row => acc ++ row ++ "\n") "")

/-- Multi-output field programs: same rows, then the output node indices. -/
def renderFieldAll (inputs : Nat) (es : List FieldDag.Expr) : Except String String := do
  let some artifact := FieldDag.compileAll es | throw "field program failed its translation validator"
  let rows ← artifact.nodes.mapM (fun node => match node with
    | FieldDag.Node.const n => if n < 2 ^ 63 then pure s!"C {n}" else throw "field constant too large"
    | .input i => if i < inputs then pure s!"I {i}" else throw "field input out of range"
    | .bin .add a b => pure s!"A {a} {b}"
    | .bin .sub a b => pure s!"S {a} {b}"
    | .bin .mul a b => pure s!"M {a} {b}")
  let header := s!"EMP_HYBRID_FIELD_DAG_V2\n{inputs} {rows.length} {artifact.outputs.length}\n{FieldDag.modulus}\n"
  pure (header ++ rows.foldl (fun acc row => acc ++ row ++ "\n") "" ++
    "O " ++ " ".intercalate (artifact.outputs.map toString) ++ "\n")

def main (args : List String) : IO Unit := do
  if let ["equal", size] := args then
    let some n := size.toNat? | throw (IO.userError "equal N")
    unless 0 < n && n ≤ 4096 do throw (IO.userError "equal width 1..4096")
    match render (equalCircuit n) (2 * n) with
    | .ok text => (← IO.getStdout).putStr text; return
    | .error message => throw (IO.userError message)
  let [mode] := args | throw (IO.userError "modadd|finalize-mask|finalize-bits|into-field|status|xor-bit|field-bit-check|field-bit-xor|field-recompose")
  let rendered ← match mode with
    | "modadd" => pure (render modAddCircuit)
    | "finalize-mask" => pure (render finalizeMaskCircuit)
    | "finalize-bits" => pure (render finalizeBitsCircuit)
    | "into-field" => pure (render intoFieldCircuit)
    | "status" => pure (render statusCircuit)
    | "xor-bit" => pure (render xorBitCircuit 2)
    | "field-bit-check" => pure (renderField 1 FieldBits.bitCheck)
    | "field-bit-xor" => pure (renderField 2 FieldBits.bitXor)
    | "field-recompose" => pure (renderField 256 FieldBits.recompose)
    | "field-mask-pair" => pure (renderFieldAll 3 FieldBits.maskPair)
    | "x25519-fast" => pure (renderFieldAll 257 X25519Fast.exprs)
    | "edwards-on-curve" => pure (renderField 2 EdwardsShare.onCurve)
    | "edwards-add-u" => pure (renderFieldAll 4 EdwardsShare.addU)
    | "swap-bits" => pure (render X25519SwapBits.circuit 256)
    | _ => throw (IO.userError "unknown circuit")
  match rendered with
  | .ok text => (← IO.getStdout).putStr text
  | .error message => throw (IO.userError message)
