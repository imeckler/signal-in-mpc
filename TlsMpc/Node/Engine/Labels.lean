import TlsMpc.Node.Engine

/-!
# The release labels: one registry for every flow

REORGANIZATION_PLAN.md 5.4 (the open rule), stage S9. Every release instruction (`openBool`,
`openBoolTo`, `openField`, `exchange`) carries a `Label`, and the label is part of the agreed
skeleton (Engine.lean decision D7). The codes are provisional until `RevealKind` (TlsMpc/Node/
Types.lean, owned elsewhere) lists the reveal kinds; this file is the single place a flow takes a
label from, so that the later mapping `RevealKind → Label` is written once, here.

Rules: a flow never writes a literal `⟨n⟩` label; every constant below is listed in `all`;
`all_distinct` (no two kinds share a code) and `all_nonzero` (code 0 is refused by `check`) are
checked by `decide`. Codes 1-19 are the joint-randomness and upgrade family, 20-39 stored state.

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Engine.Label

/-- `Random.joint` (op 33): this party's commitment. -/
def jointRandomCommitment : Label := ⟨1⟩
/-- `Random.joint` (op 33): the commitment's opening (nonce, value). -/
def jointRandomOpening : Label := ⟨2⟩
/-- `Reveal.blobAccepted`: the `accepted` byte of `contact-open` (ops 37, 55, 63). -/
def blobAccepted : Label := ⟨20⟩
/-- `Reveal.sealedBlob`: ciphertext and check value of `contact-seal` (ops 38, 54, 64). -/
def sealedBlob : Label := ⟨21⟩

/-- Every label a flow uses. -/
def all : List Label := [jointRandomCommitment, jointRandomOpening, blobAccepted, sealedBlob]

/-- **The labels are pairwise distinct**, so a release's label names its kind. -/
theorem all_distinct : (all.map (·.code)).Nodup := by decide

/-- **Every label is a label** (`check` refuses code 0). -/
theorem all_nonzero : ∀ l ∈ all, l.code ≠ 0 := by decide

end TlsMpc.Node.Engine.Label
