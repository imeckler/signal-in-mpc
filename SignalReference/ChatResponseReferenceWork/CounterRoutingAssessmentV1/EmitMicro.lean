import Lean
import ChatResponseReferenceWork.ParserCircuitCandidateV1.Stack32Codec
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
open ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
structure CandidateImage where
  format : String := "tls-mpc-aig-v1"
  name : String
  input_bits : Nat
  input_widths : Array Nat
  nodes : Array (List Nat)
  outputs : Array (Nat × Nat)
  deriving Lean.ToJson

def bounded13 (raw : List (BVExpr 8)) : BVExpr 64 :=
  Word64.symbolic.pack (List.replicate 6 (.const 0) ++
    [ByteAuth.symbolic.and (TlsWebSocketUpgrade.get ByteAuth.symbolic raw 0) (.const 31),
     TlsWebSocketUpgrade.get ByteAuth.symbolic raw 1])

def guarded13ULE (left right : BVExpr 64) : BVExpr 8 :=
  let left13 : BVExpr 13 := BvConstruct.extract 0 13 left
  let right13 : BVExpr 13 := BvConstruct.extract 0 13 right
  let borrow := BvConstruct.extract 13 1
    (Word64.subtract (BvConstruct.append (.const 0#1) right13) (BvConstruct.append (.const 0#1) left13))
  let low := BvConstruct.un .not (.replicate 8 borrow rfl)
  ByteAuth.symbolic.and (Word64.eq Word64.symbolic ByteAuth.symbolic
    (Word64.symbolic.shift left 13) (Word64.symbolic.const 0)) low

def main (args : List String) : IO Unit := do
  let [mode] := args | throw (IO.userError "mode")
  let size := if mode=="sub64" then 8 else if mode=="sub13" then 2
    else if mode=="ule64" then 16 else if mode=="utf-step" then 9 else 10
  let raw := ByteCircuit.inputBytes 0 size
  let out := if mode=="sub64" then Word64.bytes Word64.symbolic
      (Word64.symbolic.sub (Word64.symbolic.pack raw) (Word64.symbolic.const 1))
    else if mode=="sub13" then
      let bytes := Word64.bytes Word64.symbolic (Word64.symbolic.sub (bounded13 raw) (Word64.symbolic.const 1))
      [ByteAuth.symbolic.and (TlsWebSocketUpgrade.get ByteAuth.symbolic bytes 6) (.const 31),
       TlsWebSocketUpgrade.get ByteAuth.symbolic bytes 7]
    else if mode=="ule64" then [Word64.symbolic.ule (Word64.symbolic.pack (raw.take 8)) (Word64.symbolic.pack (raw.drop 8))]
    else if mode=="ule64-bound13" then [Word64.symbolic.ule (Word64.symbolic.pack (raw.take 8)) (bounded13 (raw.drop 8))]
    else if mode=="ule-guarded13" then [guarded13ULE (Word64.symbolic.pack (raw.take 8)) (bounded13 (raw.drop 8))]
    else if mode=="utf-step" then TlsWebSocketFrame.utfStep ByteAuth.symbolic (raw.take 8) (TlsWebSocketUpgrade.get ByteAuth.symbolic raw 8)
    else []
  unless out.length>0 do throw (IO.userError "invalid mode")
  let circuit := AigExport.compile (ByteCircuit.joinExpr out)
  let image : CandidateImage := {
    name := "chat-counter-micro-"++mode,input_bits := 8*size,input_widths := Array.replicate size 8,
    nodes := AigExport.exportNodes circuit.aig,
    outputs := Array.ofFn (fun i : Fin (8*out.length) =>
      AigExport.exportRef (circuit.vec.get (8*out.length-1-i.val) (by omega)))}
  (← IO.getStdout).putStrLn (Lean.toJson image).compress
