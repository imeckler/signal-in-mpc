import TlsMpc.TlsWorker

/-! PUBLIC RPC CONTRACT FIXTURE ONLY. No secret values or MPC execution. -/
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.TlsWorker

def requireIO (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def succeeded (action : M α) : IO α := do
  match ← action.run with
  | .ok value => return value
  | .error error => throw (IO.userError error)

def failed (action : M α) : IO Unit := do
  match ← action.run with
  | .ok _ => throw (IO.userError "invalid worker application contract accepted")
  | .error _ => pure ()

def main : IO Unit := do
  let requests ← IO.mkRef ([] : List (Operation × Bytes))
  let reply ← IO.mkRef ([] : Bytes)
  let rpc : Rpc := {
    authenticate := fun _ _ _ _ _ => pure true
    call := fun op input => do
      liftM (requests.modify (· ++ [(op,input)]) : IO Unit)
      liftM (reply.get : IO Bytes) }
  let backend := applicationBackend rpc
  let keys := applicationHandleKeys
  let wire := record 23 (List.replicate 18 0)
  reply.set wire
  let result ← succeeded (backend.sealApplication keys 7 ⟨9⟩ 17 3)
  requireIO (result == wire) "ciphertext reply changed"
  requireIO ((← requests.get) == [(.sealApplication,uint 8 7 ++ uint 8 9 ++ uint 2 17 ++ uint 2 3)])
    "application request must contain only sequence, handle and public dimensions"
  let prior ← requests.get
  for (seq,id,size,padding) in [(2^64,9,17,3),(0,0,17,3),(0,2^64,17,3),(0,9,16384,1)] do
    failed (backend.sealApplication keys seq ⟨id⟩ size padding)
  requireIO ((← requests.get) == prior) "bad application request reached worker"
  for (kind,content) in [(22,[24,0,0,1,0]),(22,[24,0,0,1,1]),(21,[1,0])] do
    let _ ← succeeded (backend.sealControl keys 3 kind content)
    requireIO ((← requests.get).getLast? == some (.sealControl,uint 8 3 ++ [UInt8.ofNat kind] ++ content))
      "control encoding mismatch"
  let prior ← requests.get
  for (kind,content) in [(23,[1,2]),(22,[24,0,0,1,2]),(21,[2,0]),(22,[])] do
    failed (backend.sealControl keys 0 kind content)
  requireIO ((← requests.get) == prior) "nonapproved public control reached worker"
  let mut rejected := 8
  for bad in [[],[0],[1,0],[1,0] ++ uint 8 0,[1,1] ++ uint 8 2,
      [0,1],[2,1],[3,2],[4,1],[5,0],[255,0],[2,0,0],[3,0,0],[4,0,0],
      [1,0] ++ uint 8 2 ++ [0]] do
    reply.set bad
    failed (backend.openRecord keys 0 wire)
    rejected := rejected+1
  for id in [1,9,2^64-1] do
    reply.set ([1,0] ++ uint 8 id)
    match ← succeeded (backend.openRecord keys 11 wire) with
    | .application handle => requireIO (handle.id == id) "opaque handle changed"
    | _ => throw (IO.userError "application event lost")
    requireIO ((← requests.get).getLast? == some (.openApplication,uint 8 11 ++ wire))
      "receive request encoding mismatch"
  for (raw,expected) in [([0,0],0),([2,0],2),([3,0],3),([3,1],5),([4,0],4)] do
    reply.set raw
    let event ← succeeded (backend.openRecord keys 0 wire)
    let observed := match event with
      | .fatal => 0 | .skippedControl => 2 | .keyUpdate false => 3 | .keyUpdate true => 5
      | .closeNotify => 4 | .application _ => 1
    requireIO (observed == expected) "control event mapping mismatch"
  reply.set [0]
  failed (backend.rotateSend keys); failed (backend.rotateReceive keys); failed backend.abort
  reply.set []
  let _ ← succeeded (backend.rotateSend keys)
  let _ ← succeeded (backend.rotateReceive keys)
  succeeded backend.abort
  requireIO (((← requests.get).reverse.take 3).map Prod.fst == [.abort,.rotateReceive,.rotateSend])
    "rotation/abort opcode mismatch"
  IO.println s!"application RPC contract: {rejected+3} rejected cases; opaque handles, controls and rotations passed"
