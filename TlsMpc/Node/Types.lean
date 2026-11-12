/-!
# Public and engine values in the types (REORGANIZATION_PLAN.md section 4.1, stage S4)

With `Secret` (`TlsMpc/Node/Secret.lean`), the three kinds of value the controller holds:
- `Secret α`: this party's own; only its eliminators look inside;
- `Opened r α`: a value released from the engines (or from this party's secrets) by the opening
  `r`, one function per opening in `Reveal.lean` (stage S6). Public: `.val` is unrestricted;
- `Handle e`: an engine value, which carries no bytes.

Everything else the controller holds is public by construction: configuration, the application's
request and text, opened values, and what is computed from those.

Stage S4 introduces the types. `RevealKind` has no constructor yet, so no `Opened` value exists:
stage S6 adds one constructor per opening of plan section 4.3, each with its function in
`Reveal.lean`, and moves `Opened`'s private constructor there. Pure; no emitter imports this module.
-/

namespace TlsMpc.Node

/-- The openings (plan 4.3, SECURITY_MAP B). Empty until stage S6 lists them; a value of type
`Opened r α` can only be made by the function of its kind. -/
inductive RevealKind where

/-- A value that left the engines (or this party's secrets) through a function of `Reveal.lean`;
`r` names the opening (SECURITY_MAP B). Public: `.val` is unrestricted. The constructor is
private (to this file until S6 moves it to `Reveal.lean`). -/
structure Opened (r : RevealKind) (α : Type) where
  private mk ::
  val : α

/-- Which engine holds a value: the Boolean engine (wires) or the field engine (shares). -/
inductive EngineKind where
  | boolean
  | field
  deriving BEq, Repr, DecidableEq

/-- An engine value (Boolean wires or field shares); carries no bytes. Allocated by scripts
(plan section 5). -/
structure Handle (e : EngineKind) where
  id : UInt64
  deriving BEq, Repr

/-- A contact's id: the application's public u128 (`notify(ids, message)`). -/
abbrev ContactId := Nat

end TlsMpc.Node
