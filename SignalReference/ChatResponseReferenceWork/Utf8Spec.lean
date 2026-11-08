import TlsMpc.TlsChatResponse
open TlsMpc
namespace ChatResponseReference.Utf8

/-- Pending code-unit obligations from the Unicode UTF8 byte grammar. These
bounds reject overlong encodings, UTF16 surrogates and scalars above U+10FFFF. -/
inductive Phase where
  | ready | one | two | three | e0 | ed | f0 | f4 | dead
  deriving DecidableEq, Repr

def between (byte : BitVec 8) (low high : Nat) : Bool := decide (low ≤ byte.toNat ∧ byte.toNat ≤ high)

def next (phase : Phase) (byte : BitVec 8) : Phase :=
  match phase with
  | .dead => .dead
  | .one => if between byte 128 191 then .ready else .dead
  | .two => if between byte 128 191 then .one else .dead
  | .three => if between byte 128 191 then .two else .dead
  | .e0 => if between byte 160 191 then .one else .dead
  | .ed => if between byte 128 159 then .one else .dead
  | .f0 => if between byte 144 191 then .two else .dead
  | .f4 => if between byte 128 143 then .two else .dead
  | .ready =>
    if between byte 0 127 then .ready
    else if between byte 194 223 then .one
    else if between byte 225 236 || between byte 238 239 then .two
    else if between byte 241 243 then .three
    else if byte.toNat = 224 then .e0
    else if byte.toNat = 237 then .ed
    else if byte.toNat = 240 then .f0
    else if byte.toNat = 244 then .f4
    else .dead

def run : Phase → List (BitVec 8) → Phase
  | phase,[] => phase
  | phase,byte::rest => run (next phase byte) rest

def accepts (bytes : List (BitVec 8)) : Bool := decide (run .ready bytes = .ready)

def index : Phase → Option Nat
  | .ready => some 0 | .one => some 1 | .two => some 2 | .three => some 3
  | .e0 => some 4 | .ed => some 5 | .f0 => some 6 | .f4 => some 7 | .dead => none

def encode (phase : Phase) : List (BitVec 8) :=
  (List.range 8).map (fun i => if index phase = some i then 255 else 0)

def circuitRun (bytes : List (BitVec 8)) : List (BitVec 8) :=
  bytes.foldl (TlsWebSocketFrame.utfStep ByteAuth.concrete) (encode .ready)

/-- This is an executable specification boundary. Agreement with the actual
Rust std validator's pointer-optimized implementation is a separate obligation. -/
theorem initial_encoding : encode .ready = TlsWebSocketUpgrade.initial ByteAuth.concrete 7 := rfl
end ChatResponseReference.Utf8
