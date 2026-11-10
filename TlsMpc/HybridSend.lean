import TlsMpc.Signal.ChainSend

/-!
Two consecutive established Signal sends as one circuit.

The first send is `ChainSend.sealCore` on the supplied chain key and counter.
The second send reuses the session fields and takes its chain key and counter
from the first send's private output, so the returned state of one message is
the input state of the next without leaving the circuit. No new cryptography:
this is composition of the existing proved step.

Input bytes: the `signal-chain-send` layout for the first message
(version1, counterBE4, previousBE4, ratchet32, chainKey32, PQpresent1, PQkey32,
sender32, receiver32, plaintext, PQ, addresses0/36), then the second plaintext.
Output: the first step's output followed by the second step's output, each
status1, nextChain32, nextCounter4, Signal wire.
-/
namespace TlsMpc.HybridSend
open Std.Tactic.BVDecide TlsMpc.Signal

/-- One step on explicit state, returning the full step output. -/
def step (shape : Serialization.Shape) (version present : BVExpr 8)
    (counter previous ratchet chain pqKey sender receiver plaintext pq addresses : List (BVExpr 8)) :
    List (BVExpr 8) :=
  ChainSend.sealCore Aes.symbolic Sha256.symbolic ByteAuth.symbolic shape version present
    counter previous ratchet chain pqKey sender receiver plaintext pq addresses

def twoSends (shape : Serialization.Shape) (size pqSize : Nat) : List (BVExpr 8) :=
  let addressSize := if shape.withAddresses then 36 else 0
  let version : BVExpr 8 := .var 0
  let counter := ByteCircuit.inputBytes 1 4
  let previous := ByteCircuit.inputBytes 5 4
  let ratchet := ByteCircuit.inputBytes 9 32
  let chain := ByteCircuit.inputBytes 41 32
  let present : BVExpr 8 := .var 73
  let pqKey := ByteCircuit.inputBytes 74 32
  let sender := ByteCircuit.inputBytes 106 32
  let receiver := ByteCircuit.inputBytes 138 32
  let plaintext1 := ByteCircuit.inputBytes 170 size
  let pq := ByteCircuit.inputBytes (170 + size) pqSize
  let addresses := ByteCircuit.inputBytes (170 + size + pqSize) addressSize
  let plaintext2 := ByteCircuit.inputBytes (170 + size + pqSize + addressSize) size
  let first := step shape version present counter previous ratchet chain pqKey sender receiver plaintext1 pq addresses
  let chain2 := (first.drop 1).take 32
  let counter2 := (first.drop 33).take 4
  let second := step shape version present counter2 previous ratchet chain2 pqKey sender receiver plaintext2 pq addresses
  first ++ second

def inputBytes (shape : Serialization.Shape) (size pqSize : Nat) : Nat :=
  170 + size + pqSize + (if shape.withAddresses then 36 else 0) + size

end TlsMpc.HybridSend
