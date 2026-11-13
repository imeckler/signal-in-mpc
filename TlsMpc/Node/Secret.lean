import TlsMpc.TlsWorker
import TlsMpc.Node.Bytes

/-!
# `Secret`: a value only this party may hold (REORGANIZATION_PLAN.md section 4.1, stage S4)

This party's own share of a key, its XOR share of the account credentials, its own private keys
(OWN), its own randomness: the secret material of section 4.2. A `Secret` cannot be printed,
serialised, logged or sent: it has no `ToString`, `Repr`, `ToJson` or `BEq` instance, its
constructor and its field are `private` to this file, and only the functions below look inside.

Making one is harmless (`hide`, `ofHex`, `map`, `++`): wrapping a value hides it. Taking a value
OUT is what this file controls. The **eliminators** are:
- `inputOwn` (here): own private input to the engines. Until the engine's instruction set exists
  (plan section 5.1, `Engine.inputOwn*`) this is the worker operations that take this party's
  private input, `OwnInput`; the worker keeps the value in the engines.
- `stash` (here, next to `inputOwn`): own private input for the script flows, put in this party's
  script store (`Flows/Runner.lean`), from which only `Engine.fill` reads it into a batch.
- `expose` (here), used ONLY by the eliminators' files of plan 4.1: `Channels.lean`
  (`saveShare`, `loadShare` round trip, `kemDecapsulate`: the key on the tool's stdin), and later
  `Engine.lean`, `Reveal.lean`, `Local/*`. `scripts/lint_node.py` check `secret-val` (on from S4)
  rejects `expose`, `Secret.val` and `Secret.mk` in any other file.
- `length`: the size of a secret. Every secret the controller holds has a size fixed by its
  format (a 32-byte key share, the 38-byte credentials share, a 32-byte KEM secret), so its length
  is public; the controller checks shapes with it.

Lean's `private` is enforced per file by the compiler; it is not a boundary against
metaprogramming. The S0 lint rejects `unsafe`, `implemented_by`, `extern` and `opaque` in
`TlsMpc/Node`, which are the bypasses. No emitter imports this module.
-/

namespace TlsMpc.Node
open TlsMpc.TlsWire

/-- A value only this party may hold: its own share or random contribution, or an OWN key.
It cannot be printed, serialised, logged or sent. Its eliminators are listed at the top of
`TlsMpc/Node/Secret.lean`. -/
structure Secret (α : Type) where
  private mk ::
  private val : α

namespace Secret

/-- Hide a value (any value may be made secret). -/
def hide (a : α) : Secret α := ⟨a⟩

/-- A function of a secret is secret. -/
def map (f : α → β) (s : Secret α) : Secret β := ⟨f s.val⟩

/-- A function of two secrets is secret. -/
def zipWith (f : α → β → γ) (a : Secret α) (b : Secret β) : Secret γ := ⟨f a.val b.val⟩

instance : Append (Secret (List α)) := ⟨zipWith (· ++ ·)⟩

instance [Inhabited α] : Inhabited (Secret α) := ⟨hide default⟩

/-- A secret given as hex (an environment variable, a file, the database client's output). The
error names no digit of it. -/
def ofHex (text : String) : Except String (Secret Bytes) := hide <$> Node.Bytes.fromHex text

/-- The size of a secret: public, as every secret the controller holds has a size fixed by its
format (section 4.2). -/
def length (s : Secret (List α)) : Nat := s.val.length

/-- **Eliminator for the eliminators' files only** (plan 4.1: `Channels.lean`, and later
`Engine.lean`, `Reveal.lean`, `Local/*`): the value itself. `scripts/lint_node.py` (check
`secret-val`) rejects this name in every other file. -/
def expose (s : Secret α) : α := s.val

/-- The worker operations that take this party's own private input (SECURITY_MAP A.1): the value
goes into the engines and stays there. Plan 4.2 rows 1, 2, 3, 5, 6. -/
inductive OwnInput where
  /-- Op 36: a contact's id, then this party's additive share of its key (row 1). -/
  | contactKey
  /-- Op 52: this party's additive share of the account's key (row 2). -/
  | accountKey
  /-- Op 47: this party's XOR share of the account id and password (row 3). -/
  | accountCredentials
  /-- Op 44 (TEST): a contact's id and its record from the export (row 6). -/
  | contactAdmit
  /-- Op 46 (TEST): the account's identity key (OWN) and its certificate (row 5). -/
  | accountAdmit
  /-- Op 51: a new contact's session from our prekey private keys (OWN) and the KEM secret (row 5). -/
  | envelopeSession

def OwnInput.operation : OwnInput → TlsWorker.Operation
  | .contactKey => .contactKey
  | .accountKey => .accountKey
  | .accountCredentials => .accountCredentials
  | .contactAdmit => .contactAdmit
  | .accountAdmit => .accountAdmit
  | .envelopeSession => .envelopeSession

/-- **Eliminator: own private input to the engines** (plan 4.1 `Engine.inputOwn*`; until the
instruction set exists, the worker operation `op`). The reply is the operation's public reply. -/
def inputOwn (rpc : TlsWorker.Rpc) (op : OwnInput) (input : Secret Bytes) : TlsClient.M Bytes :=
  rpc.call op.operation input.val

/-- **Eliminator: own private data into this party's script store** (the script flows' private
input, plan 4.1 `Engine.inputOwn*`; decision D1 of `TlsMpc/Node/Engine.lean`: a script carries no
private data, an input instruction names a store slot, and only `Engine.fill` reads the slot into
the batch this party sends). `put` writes the value under a slot of the store `σ`
(`Flows/Runner.lean`, the only caller); the value is not returned. -/
def stash {σ : Type} (put : α → σ → σ) (s : Secret α) (store : σ) : σ := put s.val store

end Secret
end TlsMpc.Node
