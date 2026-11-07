import TlsMpc.Artifact

/-!
Secret-wire layout for the fixed-size symmetric Signal key state.

This module implements constructors and projections only. HMAC, HKDF, state
advancement, authentication and the Signal wire format are separate obligations.
The layout is internal to MPC: bytes and counters are MSB-first, and every field
is an input wire. Returning wires here does not authorize opening their values.
-/

namespace TlsMpc.Signal

abbrev Bytes (n : Nat) := { bytes : List (BitVec 8) // bytes.length = n }

structure ChainKey where
  key : Bytes 32
  index : BitVec 32

structure MessageKeys where
  cipherKey : Bytes 32
  macKey : Bytes 32
  iv : Bytes 16
  counter : BitVec 32

structure RootKey where
  key : Bytes 32

def byteBit (bytes : Bytes n) (i : Nat) : Bool :=
  (bytes.val[i / 8]?.getD 0).getLsbD (7 - i % 8)

def bytesBits (bytes : Bytes n) : List Bool :=
  List.ofFn (fun (i : Fin (8 * n)) => byteBit bytes i.val)

def counterBits (counter : BitVec 32) : List Bool :=
  List.ofFn (fun (i : Fin 32) => counter.getLsbD (31 - i.val))

def chainEnvironment (key : ChainKey) (i : Nat) : Bool :=
  if i < 256 then byteBit key.key i
  else key.index.getLsbD (31 - (i - 256))

def messageEnvironment (keys : MessageKeys) (i : Nat) : Bool :=
  if i < 256 then byteBit keys.cipherKey i
  else if i < 512 then byteBit keys.macKey (i - 256)
  else if i < 640 then byteBit keys.iv (i - 512)
  else keys.counter.getLsbD (31 - (i - 640))

def rootEnvironment (key : RootKey) (i : Nat) : Bool := byteBit key.key i

def projection (total offset count : Nat) (h : offset + count ≤ total) :
    List (Boolean.Expr total) :=
  List.ofFn (fun (i : Fin count) => .input ⟨offset + i.val, by omega⟩)

theorem projection_correct (h : offset + count ≤ total) (env : Nat → Bool) :
    (projection total offset count h).map (Boolean.Expr.eval (fun i => env i.val)) =
      List.ofFn (fun (i : Fin count) => env (offset + i.val)) := by
  simp [projection, List.map_ofFn, Function.comp_def, Boolean.Expr.eval]

def chainKeyCircuit := projection 288 0 256 (by decide)
def chainIndexCircuit := projection 288 256 32 (by decide)
def messageCipherCircuit := projection 672 0 256 (by decide)
def messageMacCircuit := projection 672 256 256 (by decide)
def messageIvCircuit := projection 672 512 128 (by decide)
def messageCounterCircuit := projection 672 640 32 (by decide)
def rootKeyCircuit := projection 256 0 256 (by decide)

theorem chainKeyCircuit_correct (key : ChainKey) :
    chainKeyCircuit.map (Boolean.Expr.eval (fun i => chainEnvironment key i.val)) =
      bytesBits key.key := by
  rw [chainKeyCircuit, projection_correct]
  apply congrArg List.ofFn
  funext i
  simp [chainEnvironment, i.isLt]

theorem chainIndexCircuit_correct (key : ChainKey) :
    chainIndexCircuit.map (Boolean.Expr.eval (fun i => chainEnvironment key i.val)) =
      counterBits key.index := by
  rw [chainIndexCircuit, projection_correct]
  apply congrArg List.ofFn
  funext i
  have h : ¬256 + i.val < 256 := by omega
  simp [chainEnvironment, h]

theorem messageCipherCircuit_correct (keys : MessageKeys) :
    messageCipherCircuit.map (Boolean.Expr.eval (fun i => messageEnvironment keys i.val)) =
      bytesBits keys.cipherKey := by
  rw [messageCipherCircuit, projection_correct]
  apply congrArg List.ofFn
  funext i
  simp [messageEnvironment, i.isLt]

theorem messageMacCircuit_correct (keys : MessageKeys) :
    messageMacCircuit.map (Boolean.Expr.eval (fun i => messageEnvironment keys i.val)) =
      bytesBits keys.macKey := by
  rw [messageMacCircuit, projection_correct]
  apply congrArg List.ofFn
  funext i
  have h0 : ¬256 + i.val < 256 := by omega
  have h1 : 256 + i.val < 512 := by omega
  simp [messageEnvironment, h0, h1]

theorem messageIvCircuit_correct (keys : MessageKeys) :
    messageIvCircuit.map (Boolean.Expr.eval (fun i => messageEnvironment keys i.val)) =
      bytesBits keys.iv := by
  rw [messageIvCircuit, projection_correct]
  apply congrArg List.ofFn
  funext i
  have h0 : ¬512 + i.val < 256 := by omega
  have h1 : ¬512 + i.val < 512 := by omega
  have h2 : 512 + i.val < 640 := by omega
  simp [messageEnvironment, h0, h1, h2]

theorem messageCounterCircuit_correct (keys : MessageKeys) :
    messageCounterCircuit.map (Boolean.Expr.eval (fun i => messageEnvironment keys i.val)) =
      counterBits keys.counter := by
  rw [messageCounterCircuit, projection_correct]
  apply congrArg List.ofFn
  funext i
  have h0 : ¬640 + i.val < 256 := by omega
  have h1 : ¬640 + i.val < 512 := by omega
  have h2 : ¬640 + i.val < 640 := by omega
  simp [messageEnvironment, h0, h1, h2]

theorem rootKeyCircuit_correct (key : RootKey) :
    rootKeyCircuit.map (Boolean.Expr.eval (fun i => rootEnvironment key i.val)) =
      bytesBits key.key := by
  rw [rootKeyCircuit, projection_correct]
  apply congrArg List.ofFn
  funext i
  simp [rootEnvironment]

theorem exported_chainKey_correct (key : ChainKey) :
    Boolean.Artifact.evaluateProgram (chainEnvironment key)
      (Boolean.Artifact.exportProgram chainKeyCircuit) = some (bytesBits key.key) := by
  rw [Boolean.Artifact.exportProgram_correct, chainKeyCircuit_correct]

theorem exported_chainIndex_correct (key : ChainKey) :
    Boolean.Artifact.evaluateProgram (chainEnvironment key)
      (Boolean.Artifact.exportProgram chainIndexCircuit) = some (counterBits key.index) := by
  rw [Boolean.Artifact.exportProgram_correct, chainIndexCircuit_correct]

theorem exported_messageCipher_correct (keys : MessageKeys) :
    Boolean.Artifact.evaluateProgram (messageEnvironment keys)
      (Boolean.Artifact.exportProgram messageCipherCircuit) = some (bytesBits keys.cipherKey) := by
  rw [Boolean.Artifact.exportProgram_correct, messageCipherCircuit_correct]

theorem exported_messageMac_correct (keys : MessageKeys) :
    Boolean.Artifact.evaluateProgram (messageEnvironment keys)
      (Boolean.Artifact.exportProgram messageMacCircuit) = some (bytesBits keys.macKey) := by
  rw [Boolean.Artifact.exportProgram_correct, messageMacCircuit_correct]

theorem exported_messageIv_correct (keys : MessageKeys) :
    Boolean.Artifact.evaluateProgram (messageEnvironment keys)
      (Boolean.Artifact.exportProgram messageIvCircuit) = some (bytesBits keys.iv) := by
  rw [Boolean.Artifact.exportProgram_correct, messageIvCircuit_correct]

theorem exported_messageCounter_correct (keys : MessageKeys) :
    Boolean.Artifact.evaluateProgram (messageEnvironment keys)
      (Boolean.Artifact.exportProgram messageCounterCircuit) = some (counterBits keys.counter) := by
  rw [Boolean.Artifact.exportProgram_correct, messageCounterCircuit_correct]

theorem exported_rootKey_correct (key : RootKey) :
    Boolean.Artifact.evaluateProgram (rootEnvironment key)
      (Boolean.Artifact.exportProgram rootKeyCircuit) = some (bytesBits key.key) := by
  rw [Boolean.Artifact.exportProgram_correct, rootKeyCircuit_correct]

end TlsMpc.Signal
