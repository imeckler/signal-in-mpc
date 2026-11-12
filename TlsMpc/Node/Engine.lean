import TlsMpc.FieldDag

/-!
THE ENGINE INSTRUCTION SET, SCRIPTS, WELL-FORMEDNESS, AND THE BATCH FORMAT.

REORGANIZATION_PLAN.md sections 5.1 and 5.2, stage S9 (Lean side, advance work in new files).
No emitter imports this module (rule 4); it does no I/O and has no escape hatch (rule 6).

DESIGN NOTE FOR THE RUST INTERPRETER (node_worker/src/interp.rs, handles.rs). Plain text on
purpose: this is the specification the Rust side implements, byte for byte.

  1. Transport. A batch is one pipe request (TlsWorkerPipe framing, unchanged) with a new
     operation code reserved for batches; its payload is encodeBatch of the batch. The reply
     payload is encodeReplies of the reply items. A rejected batch is an ordinary rejected pipe
     reply (status 1, empty), after which the latch is terminal as today.

  2. Numbers. Every number is u64 little-endian (8 bytes). A list is its length as u64, then its
     items. A byte string is a list of bytes. Bits are one byte each, 0 or 1 (any other byte:
     reject). A field element is 32 bytes little-endian and must be below p = 2^255 - 19
     (otherwise reject). A flag is one byte, 0 or 1. A party is one byte: 0 for party A
     (leader, ABI party 0), 1 for party B. A field-input kind is one byte: 0 coins, 1 elements.
     A handle is a u64 chosen by the Lean script; Boolean and field handles are two separate
     name spaces.

  3. Instructions. One opcode byte, then the fields in the order below (encWire is the
     definition). Payload fields are marked with a star; they are this party's private data.
        1  boolInput      out, owner(party), width, once(flag), revealable(flag), *bits
                          (the non-owner sends an empty bit list)
        2  boolInputBoth  outA, outB, width, once, revealable, *bits
        3  boolPublic     out, bits
        4  run            out, circuit name(bytes), copies, input
        5  concat         out, list of handles
        6  slice          out, handle, lo, hi                (bits lo .. hi-1)
        7  pick           out, handle, list of indices       (repeats allowed)
        8  openBool       handle, label(u64)
        9  openBoolTo     handle, recipient(party), label
       10  freeBool       handle
       11  fieldInput     list outsA, list outsB, kind, revealable, *elements
       12  fieldPublic    out, element
       13  fieldAdd       out, a, b
       14  fieldSub       out, a, b
       15  fieldScale     out, a, constant (u64, ABI ea_field_scale)
       16  fieldDivide    out, a, element c (c nonzero; ABI ea_field_divide_public)
       17  fieldMul       list outs, list of pairs (a, b)
       18  fieldCheck
       19  openField      list of handles, label
       20  freeField      handle
       21  exchange       len, label, *bytes (exactly len bytes)
     Mapping to engine_abi.h: 1 ea_bool_input_private (owner, the non-owner passes width
     placeholder bits), 2 ea_bool_input_both, 3 ea_bool_public, 4 ea_bool_run on the circuit the
     manifest loaded under that name, 5-7 ea_bool_concat / ea_bool_slice / ea_bool_pick,
     8 ea_bool_open, 9 ea_bool_open_to, 10 ea_bool_free, 11 ea_field_input_coins (coins: each
     element must be below 2^64, passed as u64) or ea_field_input_elements, 12 ea_field_public
     (or ea_field_constant for values below 2^64; same value), 13-16 ea_field_add / sub /
     scale / divide_public, 17 ea_field_mul, 18 ea_field_check, 19 ea_field_checked_open,
     20 ea_field_free, 21 the control link's exchange (link.rs; both payloads have length len).
     ea_bool_interleave is not used (interleave is concat then pick).

  4. Agreement. Before executing anything of a batch, each worker computes the skeleton bytes:
     the batch decoded, every starred payload replaced by the empty list, re-encoded
     (skeletonBytes; the Lean theorem skeletonBytes_inj says equal skeleton bytes mean equal
     skeletons). The agreed part of the pipe request (agree.rs agreed_part) is these bytes, so
     the hash is SHA-256("tls-worker-v3:" || session || code || sequence || size || skeleton).
     Disagreement rejects the batch before any engine call.

  5. Execution. The handle table and the open rule (handles.rs) are the Lean function check
     over the skeleton, started from the empty context at session start and carried across
     batches. Since check reads only skeletons, the shell runs it over the whole batch right
     after the agreement and before the first engine call; if it refuses any instruction the
     batch is rejected and nothing of it runs (both parties refuse identically). Then the
     instructions run in order. The private payloads are checked against the skeleton too:
     a boolInput owner's bits and a boolInputBoth's bits have exactly width entries, a
     fieldInput's elements number outsA's length (coins below 2^64), an exchange payload has
     exactly len bytes; the non-owner's boolInput payload is empty. In particular, in check: an
     output handle id that was ever defined before is refused (handles are never reused), and so
     is an operand that is not live (never defined, freed, or consumed); a once handle is consumed by its
     first use as an operand (any instruction), after which it is undefined; open marks are kept
     per bit for Boolean handles and per element for field handles; openBool and openField need
     every bit/element marked public or revealable; openBoolTo needs every bit marked for that
     recipient; every release (8, 9, 19, 21) carries a nonzero label; an exchange has
     1 <= len <= 65536. Marks: inputs get revealable or never as declared, public values and
     constants public, run outputs the circuit layout's marks repeated per copy, plumbing moves
     marks with the bits, field results the join of their operands' marks (public with public is
     public; public or revealable with public or revealable is revealable; anything else never).

  6. Replies. One reply item per instruction that releases data to this party, in order:
     openBool: the bits; openBoolTo: the bits, to the recipient only (the other party gets no
     item); openField: the elements; exchange: the peer's bytes. Items are encoded by
     encodeReplies (tag 1 bits, 2 elements, 3 bytes, then the list).

  7. What is not here. Randomness is drawn on the Lean side (rule 5) into this party's private
     store before a script runs; local computations on own secrets (commitments) are evaluated
     by the Lean interpreter into exchange payloads. The server operations (9, 10, 11, 17, 90,
     91, 92) and the legacy operations stay separate pipe operations until their flows move.

DECISIONS (against or beyond the plan's text, with the reason):

  D1. Scripts carry no private data. The plan's Instr carries "mine : Secret Bits". Here an
      input instruction names a slot of this party's private store (Store), and an exchange
      payload is a Payload: plain public bytes, or a declared own-secret reveal of store slots
      (a commitment, or an opening). A script is therefore a public value, its continuations
      receive only Reply values (opened data), and T12 (skeleton determinism) holds by
      construction for every script builder, with no parametricity argument
      (Model.lean: trace_eq_skeletons, T12_skeleton_determinism). openBoolTo writes the
      recipient's bits into a store slot instead of passing them to the script. Randomness is
      not an instruction: it is put in the store (from Channels.random) before the script runs.
  D2. Three instantiations of one inductive InstrP SB SF X D: Instr (script level: slots and
      payload descriptions), Wire (pipe level: the filled private data), Skel (everything
      erased: what is agreed). fill is the only function that reads the store.
  D3. Boolean open marks are per bit, not per handle. The plan's rule "plumb results are
      revealable iff every operand is" would make a slice of a kernel's public output field
      unopenable (run returns one bundle, as the ABI does). Per-bit marks move with the bits and
      are exact. once is linear: a once handle is consumed by its first use as an operand, and
      plumbing results inherit once; so a mask's bits reach at most one run. Field handles have
      no once (single use of field masks is P-CUT (h), by the pool's API).
  D4. run takes one input bundle and gives one output bundle with copies side by side, as the
      ABI does (no field-name binding: layouts are bound by concat/slice in the flow library).
  D5. No program instruction yet. Its semantics depends on the V3 format (D/Z nodes, output
      marks), which is scheduled separately; it is added with V3. No server instruction yet:
      the server operations stay pipe operations until the TLS flows move (S12). Both extend the
      inductive later without changing what is here.
  D6. One field-input instruction with a kind (coins or elements) and one fieldPublic (the
      shell may use ea_field_constant for small values). interleave is dropped (concat+pick).
      "Jointly random" inputs are boolInputBoth / fieldInput: each party inputs its own random
      contribution and the script combines them in the engine; there is no engine-side random
      instruction (the ABI has none).
  D7. The reply type is a plain sum (Reply), not indexed by the instruction; builders check the
      constructor and abort otherwise. Labels are numeric codes (Label), provisional until
      Reveal.lean's RevealKind exists, whose constructor index becomes the code. Labels are part
      of the agreed skeleton, so both parties agree on why a value is released.
  D8. A batch ends at every instruction with a data reply, including openBoolTo (a later input
      may read the slot it fills) and exchange. So P-RAND's commitment and opening are two
      batches, not one: the opening is sent only after the peer's commitment was received, which
      is the property the plan wanted from the single batch.
  D9. Numbers are u64 little-endian; bits one byte each (the ABI's convention).
  D10. Handles, Party and Label are defined here in namespace TlsMpc.Node.Engine; when
      Types.lean (S4) lands, its Handle replaces BoolH/FieldH by a rename.
  D11. Commitment frames are tag || party || nonce || value with the party byte 1 for A and 2
      for B (as split_ecdh.h), and a 32-byte random nonce revealed with the opening; one frame
      function (commitFrame) for every commit-then-open site.
-/

namespace TlsMpc.Node.Engine

open TlsMpc.FieldDag (F modulus)

/-! ## Parties, data, handles, marks, labels -/

/-- Party A is the leader (ABI party 0, emp ALICE); party B dials (ABI party 1, emp BOB). -/
inductive Party where
  | a
  | b
  deriving DecidableEq, Repr, Inhabited

namespace Party
def other : Party → Party
  | a => b
  | b => a
/-- The byte in commitment frames (emp's ALICE = 1, BOB = 2, as `split_ecdh.h`). -/
def emp : Party → UInt8
  | a => 1
  | b => 2
@[simp] theorem other_other (p : Party) : p.other.other = p := by cases p <;> rfl
@[simp] theorem other_ne (p : Party) : p.other ≠ p := by cases p <;> decide
@[simp] theorem ne_other (p : Party) : p ≠ p.other := by cases p <;> decide
theorem emp_ne (p : Party) : p.emp ≠ p.other.emp := by cases p <;> decide
end Party

abbrev Bits := List Bool
abbrev Bytes := List UInt8

/-- The ASCII bytes of a string (for circuit names and commitment tags). -/
def ascii (s : String) : Bytes := s.toList.map (fun c => UInt8.ofNat c.toNat)

/-- A Boolean wire bundle in the Boolean engine. -/
structure BoolH where
  id : Nat
  deriving DecidableEq, Repr

/-- A field element in the field engine. -/
structure FieldH where
  id : Nat
  deriving DecidableEq, Repr

/-- Open marks (5.4), fixed at creation: per bit for Boolean handles, per element for field
handles. `pub`: public by construction; `revealable`: may be opened (cut-and-choose candidates,
masked values); `toA`/`toB`: may be opened to that party only; `never`: may not be opened. -/
inductive Mark where
  | never
  | pub
  | toA
  | toB
  | revealable
  deriving DecidableEq, Repr

namespace Mark
def ofInput (revealable : Bool) : Mark := if revealable then .revealable else .never
def openable : Mark → Bool
  | .pub => true
  | .revealable => true
  | _ => false
def to : Party → Mark
  | .a => .toA
  | .b => .toB
/-- The mark of a field result from its operands' marks. -/
def join : Mark → Mark → Mark
  | .pub, .pub => .pub
  | .pub, .revealable => .revealable
  | .revealable, .pub => .revealable
  | .revealable, .revealable => .revealable
  | _, _ => .never
end Mark

/-- The reveal label every release carries (an opening, or an exchange). Provisional numeric
codes (decision D7); code 0 is not a label. -/
structure Label where
  code : Nat
  deriving DecidableEq, Repr

namespace Label
/-- `Random.joint`: this party's commitment, and the commitment's opening (nonce, value). -/
def jointRandomCommitment : Label := ⟨1⟩
def jointRandomOpening : Label := ⟨2⟩
end Label

inductive FieldIn where
  | coins
  | elements
  deriving DecidableEq, Repr

/-- An exchange payload, as the script describes it. `plain`: public bytes written in the
script. `commitment tag nonce value`: the hash of `commitFrame tag me nonce value`, the slots
read from this party's byte store (an own-secret reveal: `Reveal.commitment`). `opening slots`:
the slots' bytes, concatenated (`Reveal.commitOpening`). -/
inductive Payload where
  | plain (bytes : Bytes)
  | commitment (tag : Bytes) (nonce value : Nat)
  | opening (slots : List Nat)
  deriving DecidableEq, Repr

/-! ## The instruction set (5.1)

`SB`: what a Boolean input carries; `SF`: what a field input carries; `X`: what an exchange
carries; `D`: where `openBoolTo` puts the recipient's bits. -/

inductive InstrP (SB SF X D : Type) where
  /-- `owner`'s private bits (`width` of them), as handle `out`. -/
  | boolInput (out : BoolH) (owner : Party) (width : Nat) (once revealable : Bool) (src : SB)
  /-- Both parties' private bits: A's as `outA`, B's as `outB`. -/
  | boolInputBoth (outA outB : BoolH) (width : Nat) (once revealable : Bool) (src : SB)
  | boolPublic (out : BoolH) (bits : Bits)
  /-- `copies` side-by-side copies of the named circuit on `input`. -/
  | run (out : BoolH) (circuit : Bytes) (copies : Nat) (input : BoolH)
  | concat (out : BoolH) (parts : List BoolH)
  | slice (out : BoolH) (h : BoolH) (lo hi : Nat)
  | pick (out : BoolH) (h : BoolH) (indices : List Nat)
  /-- Opens to both parties. -/
  | openBool (h : BoolH) (label : Label)
  /-- Opens to `recipient` only. -/
  | openBoolTo (h : BoolH) (recipient : Party) (label : Label) (dst : D)
  | freeBool (h : BoolH)
  /-- Both parties' private elements (or coins below 2^64): A's as `outsA`, B's as `outsB`. -/
  | fieldInput (outsA outsB : List FieldH) (kind : FieldIn) (revealable : Bool) (src : SF)
  | fieldPublic (out : FieldH) (v : F)
  | fieldAdd (out a b : FieldH)
  | fieldSub (out a b : FieldH)
  /-- Multiplication by a public constant below 2^64. -/
  | fieldScale (out a : FieldH) (c : Nat)
  /-- Division by a public nonzero element. -/
  | fieldDivide (out a : FieldH) (c : F)
  | fieldMul (outs : List FieldH) (pairs : List (FieldH × FieldH))
  /-- The field engine's MAC check. -/
  | fieldCheck
  /-- Checked opening to both parties. -/
  | openField (hs : List FieldH) (label : Label)
  | freeField (h : FieldH)
  /-- Each party sends `len` bytes on the control link and receives the other's `len` bytes. -/
  | exchange (len : Nat) (label : Label) (payload : X)
  deriving DecidableEq, Repr

namespace InstrP

variable {SB SF X D SB' SF' X' D' : Type}

def map (fb : SB → SB') (ff : SF → SF') (fx : X → X') (fd : D → D') :
    InstrP SB SF X D → InstrP SB' SF' X' D'
  | boolInput out owner w once rev s => boolInput out owner w once rev (fb s)
  | boolInputBoth oa ob w once rev s => boolInputBoth oa ob w once rev (fb s)
  | boolPublic out bits => boolPublic out bits
  | run out c n i => run out c n i
  | concat out ps => concat out ps
  | slice out h lo hi => slice out h lo hi
  | pick out h is => pick out h is
  | openBool h l => openBool h l
  | openBoolTo h r l d => openBoolTo h r l (fd d)
  | freeBool h => freeBool h
  | fieldInput oa ob k rev s => fieldInput oa ob k rev (ff s)
  | fieldPublic out v => fieldPublic out v
  | fieldAdd out a b => fieldAdd out a b
  | fieldSub out a b => fieldSub out a b
  | fieldScale out a c => fieldScale out a c
  | fieldDivide out a c => fieldDivide out a c
  | fieldMul outs ps => fieldMul outs ps
  | fieldCheck => fieldCheck
  | openField hs l => openField hs l
  | freeField h => freeField h
  | exchange n l x => exchange n l (fx x)

/-- The instruction with every private part erased: what both parties agree on. -/
def skel (i : InstrP SB SF X D) : InstrP Unit Unit Unit Unit :=
  i.map (fun _ => ()) (fun _ => ()) (fun _ => ()) (fun _ => ())

/-- The label of a release instruction (an opening or an exchange); `none` for the others. -/
def label? : InstrP SB SF X D → Option Label
  | openBool _ l => some l
  | openBoolTo _ _ l _ => some l
  | openField _ l => some l
  | exchange _ l _ => some l
  | _ => none

/-- Whether the instruction releases data to party `me` (the reply items of the design note). -/
def releasesTo (me : Party) : InstrP SB SF X D → Bool
  | openBool .. => true
  | openBoolTo _ r _ _ => r == me
  | openField .. => true
  | exchange .. => true
  | _ => false

/-- Whether a batch ends after this instruction (decision D8). -/
def endsBatch : InstrP SB SF X D → Bool
  | openBool .. => true
  | openBoolTo .. => true
  | openField .. => true
  | exchange .. => true
  | _ => false

@[simp] theorem skel_skel (i : InstrP SB SF X D) : i.skel.skel = i.skel := by
  cases i <;> rfl

theorem label?_skel (i : InstrP SB SF X D) : i.skel.label? = i.label? := by
  cases i <;> rfl

theorem releasesTo_skel (me : Party) (i : InstrP SB SF X D) : i.skel.releasesTo me = i.releasesTo me := by
  cases i <;> rfl

end InstrP

/-- Script level: inputs name a slot of this party's store, exchanges carry a `Payload`, and
`openBoolTo` names the slot that receives the recipient's bits. -/
abbrev Instr := InstrP Nat Nat Payload Nat
/-- Pipe level: the private data filled in (the non-owner of a `boolInput` sends `[]`). -/
abbrev Wire := InstrP Bits (List F) Bytes Unit
/-- What is agreed. -/
abbrev Skel := InstrP Unit Unit Unit Unit

/-- A skeleton as a wire instruction with empty payloads (what the agreement hash covers). -/
def InstrP.blank (s : Skel) : Wire := s.map (fun _ => []) (fun _ => []) (fun _ => []) id

@[simp] theorem InstrP.blank_skel (s : Skel) : s.blank.skel = s := by
  cases s <;> rfl

/-! ## Replies and scripts (5.2) -/

/-- What a script's continuation receives: opened data only (decision D1). -/
inductive Reply where
  | unit
  | bits (b : Bits)
  | elems (v : List F)
  /-- An exchange: what this party sent (now public) and what it received. -/
  | exchanged (sent received : Bytes)

/-- The reply an instruction is expected to produce. -/
inductive Shape where
  | unit
  | bits (n : Nat)
  | elems (n : Nat)
  | bytes (n : Nat)

def Shape.Fits : Shape → Reply → Prop
  | .unit, .unit => True
  | .bits n, .bits b => b.length = n
  | .elems n, .elems v => v.length = n
  | .bytes n, .exchanged s r => s.length = n ∧ r.length = n
  | _, _ => False

/-- A script: a tree of instructions whose branches depend only on replies. -/
inductive Script (α : Type) where
  | done (a : α)
  | abort (reason : String)
  | step (i : Instr) (k : Reply → Script α)

namespace Script

def bind {α β : Type} : Script α → (α → Script β) → Script β
  | done a, f => f a
  | abort r, _ => abort r
  | step i k, f => step i (fun r => (k r).bind f)

instance : Monad Script where
  pure := done
  bind := bind

@[simp] theorem bind_done {α β : Type} (a : α) (f : α → Script β) : (done a).bind f = f a := rfl
@[simp] theorem bind_abort {α β : Type} (r : String) (f : α → Script β) : (abort r : Script α).bind f = abort r := rfl
@[simp] theorem bind_step {α β : Type} (i : Instr) (k : Reply → Script α) (f : α → Script β) :
    (step i k).bind f = step i (fun r => (k r).bind f) := rfl
@[simp] theorem bind_eq {α β : Type} (s : Script α) (f : α → Script β) : s >>= f = s.bind f := rfl
@[simp] theorem pure_eq {α : Type} (a : α) : (pure a : Script α) = done a := rfl

/-- The skeletons a script reaches when its steps are given the replies `rs`, in order. The
last one is included even when no reply follows (the run stopped there). -/
def skeletons {α : Type} : Script α → List Reply → List Skel
  | done _, _ => []
  | abort _, _ => []
  | step i _, [] => [i.skel]
  | step i k, r :: rs => i.skel :: (k r).skeletons rs

/-- One instruction whose reply is `unit`. -/
def instr (i : Instr) : Script Unit :=
  step i fun
    | .unit => done ()
    | _ => abort "reply shape"

def openBool (h : BoolH) (l : Label) : Script Bits :=
  step (.openBool h l) fun
    | .bits b => done b
    | _ => abort "reply shape"

def openField (hs : List FieldH) (l : Label) : Script (List F) :=
  step (.openField hs l) fun
    | .elems v => done v
    | _ => abort "reply shape"

/-- An exchange; returns (sent, received). -/
def exchange (len : Nat) (l : Label) (p : Payload) : Script (Bytes × Bytes) :=
  step (.exchange len l p) fun
    | .exchanged s r => done (s, r)
    | _ => abort "reply shape"

def ensure (c : Bool) (reason : String) : Script Unit :=
  if c then done () else abort reason

end Script

/-! ## Well-formedness (the handle table and the open rule of 5.4)

`check` is the judgement for one agreed instruction, over a context of live handles. Rust's
handles.rs implements exactly this function. -/

structure BoolInfo where
  marks : List Mark
  once : Bool
  deriving DecidableEq, Repr

/-- A circuit's signature: input width of one copy, and the output marks of one copy (its
layout: 0/1/2/3 never/public/toA/toB, `kernel.h:25`). -/
structure Sig where
  inWidth : Nat
  outMarks : List Mark

structure Ctx where
  bools : List (Nat × BoolInfo) := []
  fields : List (Nat × Mark) := []
  /-- Every Boolean handle id ever defined (ids are never reused). -/
  seenB : List Nat := []
  seenF : List Nat := []

/-- The largest exchange payload (`link.rs` MAX_EXCHANGE). -/
def maxExchange : Nat := 65536
/-- The bound of a u64. -/
def B64 : Nat := 2 ^ 64

namespace Ctx

def bool? (c : Ctx) (h : BoolH) : Option BoolInfo := c.bools.lookup h.id
def field? (c : Ctx) (h : FieldH) : Option Mark := c.fields.lookup h.id

def defBool (c : Ctx) (h : BoolH) (i : BoolInfo) : Option Ctx :=
  if h.id ∈ c.seenB then none
  else some { c with bools := (h.id, i) :: c.bools, seenB := h.id :: c.seenB }

def defField (c : Ctx) (h : FieldH) (m : Mark) : Option Ctx :=
  if h.id ∈ c.seenF then none
  else some { c with fields := (h.id, m) :: c.fields, seenF := h.id :: c.seenF }

def dropBool (c : Ctx) (id : Nat) : Ctx := { c with bools := c.bools.filter (fun e => e.1 != id) }
def dropField (c : Ctx) (id : Nat) : Ctx := { c with fields := c.fields.filter (fun e => e.1 != id) }

/-- Read a Boolean handle as an operand; a `once` handle is consumed. -/
def useBool (c : Ctx) (h : BoolH) : Option (BoolInfo × Ctx) :=
  match c.bool? h with
  | none => none
  | some i => some (i, if i.once then c.dropBool h.id else c)

def useBools (c : Ctx) : List BoolH → Option (List BoolInfo × Ctx)
  | [] => some ([], c)
  | h :: hs => do
    let (i, c) ← c.useBool h
    let (is, c) ← useBools c hs
    pure (i :: is, c)

def defFields (c : Ctx) : List FieldH → List Mark → Option Ctx
  | [], [] => some c
  | h :: hs, m :: ms => do
    let c ← c.defField h m
    defFields c hs ms
  | _, _ => none

end Ctx

/-- The judgement for one agreed instruction: the context after it and the shape of its reply,
or `none` if the instruction is refused. -/
def check (sigs : Bytes → Option Sig) (c : Ctx) : Skel → Option (Ctx × Shape)
  | .boolInput out _ w once rev _ => do
    let c ← c.defBool out ⟨List.replicate w (Mark.ofInput rev), once⟩
    pure (c, .unit)
  | .boolInputBoth outA outB w once rev _ => do
    let c ← c.defBool outA ⟨List.replicate w (Mark.ofInput rev), once⟩
    let c ← c.defBool outB ⟨List.replicate w (Mark.ofInput rev), once⟩
    pure (c, .unit)
  | .boolPublic out bits => do
    let c ← c.defBool out ⟨List.replicate bits.length .pub, false⟩
    pure (c, .unit)
  | .run out name copies input => do
    let s ← sigs name
    guard (0 < copies)
    let (i, c) ← c.useBool input
    guard (i.marks.length = copies * s.inWidth)
    let c ← c.defBool out ⟨(List.replicate copies s.outMarks).flatten, false⟩
    pure (c, .unit)
  | .concat out parts => do
    let (is, c) ← c.useBools parts
    let c ← c.defBool out ⟨(is.map (·.marks)).flatten, is.any (·.once)⟩
    pure (c, .unit)
  | .slice out h lo hi => do
    let (i, c) ← c.useBool h
    guard (lo ≤ hi ∧ hi ≤ i.marks.length)
    let c ← c.defBool out ⟨(i.marks.drop lo).take (hi - lo), i.once⟩
    pure (c, .unit)
  | .pick out h idx => do
    let (i, c) ← c.useBool h
    guard (idx.all (· < i.marks.length))
    let c ← c.defBool out ⟨idx.map (fun j => i.marks.getD j .never), i.once⟩
    pure (c, .unit)
  | .openBool h l => do
    guard (l.code ≠ 0)
    let (i, c) ← c.useBool h
    guard (i.marks.all Mark.openable)
    pure (c, .bits i.marks.length)
  | .openBoolTo h r l _ => do
    guard (l.code ≠ 0)
    let (i, c) ← c.useBool h
    guard (i.marks.all (· == Mark.to r))
    pure (c, .unit)
  | .freeBool h => do
    let _ ← c.bool? h
    pure (c.dropBool h.id, .unit)
  | .fieldInput outsA outsB _ rev _ => do
    guard (outsA.length = outsB.length)
    let c ← c.defFields (outsA ++ outsB) (List.replicate (outsA.length + outsB.length) (Mark.ofInput rev))
    pure (c, .unit)
  | .fieldPublic out _ => do
    let c ← c.defField out .pub
    pure (c, .unit)
  | .fieldAdd out a b => do
    let ma ← c.field? a
    let mb ← c.field? b
    let c ← c.defField out (ma.join mb)
    pure (c, .unit)
  | .fieldSub out a b => do
    let ma ← c.field? a
    let mb ← c.field? b
    let c ← c.defField out (ma.join mb)
    pure (c, .unit)
  | .fieldScale out a k => do
    guard (k < B64)
    let m ← c.field? a
    let c ← c.defField out (m.join .pub)
    pure (c, .unit)
  | .fieldDivide out a k => do
    guard (k ≠ 0)
    let m ← c.field? a
    let c ← c.defField out (m.join .pub)
    pure (c, .unit)
  | .fieldMul outs pairs => do
    guard (outs.length = pairs.length)
    let ms ← pairs.mapM (fun p => do
      let x ← c.field? p.1
      let y ← c.field? p.2
      pure (x.join y))
    let c ← c.defFields outs ms
    pure (c, .unit)
  | .fieldCheck => some (c, .unit)
  | .openField hs l => do
    guard (l.code ≠ 0)
    let ms ← hs.mapM c.field?
    guard (ms.all Mark.openable)
    pure (c, .elems hs.length)
  | .freeField h => do
    let _ ← c.field? h
    pure (c.dropField h.id, .unit)
  | .exchange len l _ => do
    guard (l.code ≠ 0 ∧ 0 < len ∧ len ≤ maxExchange)
    pure (c, .bytes len)

/-- A well-formed script: along every branch (every reply of the expected shape), every
instruction passes `check` in the context the branch has built. -/
inductive WF (sigs : Bytes → Option Sig) {α : Type} : Ctx → Script α → Prop
  | done (c : Ctx) (a : α) : WF sigs c (.done a)
  | abort (c : Ctx) (r : String) : WF sigs c (.abort r)
  | step (c c' : Ctx) (sh : Shape) (i : Instr) (k : Reply → Script α) :
      check sigs c i.skel = some (c', sh) → (∀ r, sh.Fits r → WF sigs c' (k r)) → WF sigs c (.step i k)

/-- Every release a context accepts carries a label (code nonzero). -/
theorem check_label (sigs : Bytes → Option Sig) (c c' : Ctx) (sh : Shape) (s : Skel) (l : Label)
    (h : check sigs c s = some (c', sh)) (hl : s.label? = some l) : l.code ≠ 0 := by
  cases s <;> simp only [InstrP.label?, Option.some.injEq, reduceCtorEq] at hl <;> subst hl <;>
    simp only [check, Option.bind_eq_bind, Option.bind_eq_some_iff, guard, Option.pure_def] at h <;>
    (try (obtain ⟨_, h1, _⟩ := h; split at h1 <;> simp_all)) <;>
    (try (split at h <;> simp_all))

/-! ## The private store and filling (what the Lean interpreter does before sending a batch) -/

/-- This party's private data: Boolean inputs and received `openBoolTo` bits, field inputs, and
bytes (randomness, nonces, own values to commit to). Slots are public names; their contents are
this party's secrets (in S4 terms each slot is a `Secret`, placed here by an eliminator). -/
structure Store where
  bits : Nat → Bits := fun _ => []
  elems : Nat → List F := fun _ => []
  bytes : Nat → Bytes := fun _ => []

namespace Store
def setBits (σ : Store) (slot : Nat) (v : Bits) : Store :=
  { σ with bits := fun j => if j = slot then v else σ.bits j }
def setElems (σ : Store) (slot : Nat) (v : List F) : Store :=
  { σ with elems := fun j => if j = slot then v else σ.elems j }
def setBytes (σ : Store) (slot : Nat) (v : Bytes) : Store :=
  { σ with bytes := fun j => if j = slot then v else σ.bytes j }
end Store

/-- The commitment frame `tag ‖ party ‖ nonce ‖ value` (plan 7.1, P-RAND default and
"Commit-then-open sites, unified"; the party byte as in `split_ecdh.h`). -/
def commitFrame (tag : Bytes) (who : Party) (nonce value : Bytes) : Bytes :=
  tag ++ who.emp :: (nonce ++ value)

/-- The bytes a payload stands for, for party `me` with store `σ`. `hash` is SHA-256 in the
node; the model keeps it a parameter. -/
def Payload.eval (hash : Bytes → Bytes) (me : Party) (σ : Store) : Payload → Bytes
  | .plain b => b
  | .commitment tag n v => hash (commitFrame tag me (σ.bytes n) (σ.bytes v))
  | .opening slots => (slots.map σ.bytes).flatten

/-- Fill an instruction's private parts from the store; `none` when a slot's content does not
have the declared shape (the party then aborts locally, before sending the batch). -/
def fill (hash : Bytes → Bytes) (me : Party) (σ : Store) : Instr → Option Wire
  | .boolInput out owner w once rev slot =>
    if owner = me then
      if (σ.bits slot).length = w then some (.boolInput out owner w once rev (σ.bits slot)) else none
    else some (.boolInput out owner w once rev [])
  | .boolInputBoth oa ob w once rev slot =>
    if (σ.bits slot).length = w then some (.boolInputBoth oa ob w once rev (σ.bits slot)) else none
  | .fieldInput oa ob k rev slot =>
    if (σ.elems slot).length = oa.length then some (.fieldInput oa ob k rev (σ.elems slot)) else none
  | .exchange len l p =>
    if (p.eval hash me σ).length = len then some (.exchange len l (p.eval hash me σ)) else none
  | i => some (i.map (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => ()))

theorem fill_skel (hash : Bytes → Bytes) (me : Party) (σ : Store) (i : Instr) (w : Wire)
    (h : fill hash me σ i = some w) : w.skel = i.skel := by
  cases i <;> simp only [fill] at h <;> (try split at h) <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-! ## Batching (5.2)

The Lean interpreter sends instructions in batches: every instruction up to and including the
first one that ends a batch (decision D8). A batch that would end in an abort is not sent. -/

inductive Pending (α : Type) where
  | finished (a : α)
  | aborted (reason : String)
  /-- The batch's last instruction; its reply (from the worker, through `absorb` in the model)
  resumes the script. -/
  | waiting (i : Instr) (k : Reply → Script α)

structure Batch (α : Type) where
  wires : List Wire
  rest : Pending α

def nextBatch {α : Type} (hash : Bytes → Bytes) (me : Party) (σ : Store) : Script α → Batch α
  | .done a => ⟨[], .finished a⟩
  | .abort r => ⟨[], .aborted r⟩
  | .step i k =>
    match fill hash me σ i with
    | none => ⟨[], .aborted "private input shape"⟩
    | some w =>
      if i.endsBatch then ⟨[w], .waiting i k⟩
      else
        match nextBatch hash me σ (k .unit) with
        | ⟨_, .aborted r⟩ => ⟨[], .aborted r⟩
        | ⟨ws, rest⟩ => ⟨w :: ws, rest⟩

/-- A batch's skeletons are the script's own skeletons along unit replies (so the batch agreed
is the one the script describes). -/
theorem nextBatch_skel {α : Type} (hash : Bytes → Bytes) (me : Party) (σ : Store) (s : Script α) :
    ∃ rs, (nextBatch hash me σ s).wires.map InstrP.skel <+: s.skeletons rs := by
  induction s with
  | done a => exact ⟨[], by simp [nextBatch]⟩
  | abort r => exact ⟨[], by simp [nextBatch]⟩
  | step i k ih =>
    simp only [nextBatch]
    split
    · exact ⟨[], by simp⟩
    · next w hw =>
      split
      · exact ⟨[], by simp [Script.skeletons, fill_skel hash me σ i w hw]⟩
      · obtain ⟨rs, hrs⟩ := ih .unit
        rcases hnb : nextBatch hash me σ (k .unit) with ⟨ws, rest⟩
        rw [hnb] at hrs
        have hs : w.skel = i.skel := fill_skel hash me σ i w hw
        cases rest with
        | aborted r => exact ⟨[], by simp⟩
        | finished a =>
          exact ⟨.unit :: rs, by simpa [Script.skeletons, hs] using hrs⟩
        | waiting i' k' =>
          exact ⟨.unit :: rs, by simpa [Script.skeletons, hs] using hrs⟩

/-! ## The pipe encoding of batches and replies, and their decoders -/

/-- `k` little-endian bytes of `n` (mod 256^k). -/
def le : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: le k (n / 256)

def fromLE : Bytes → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * fromLE l

namespace Enc
def u64 (n : Nat) : Bytes := le 8 n
def flag (b : Bool) : Bytes := [if b then 1 else 0]
def party : Party → Bytes
  | .a => [0]
  | .b => [1]
def kind : FieldIn → Bytes
  | .coins => [0]
  | .elements => [1]
def felt (v : F) : Bytes := le 32 v.val
def list {α : Type} (e : α → Bytes) (l : List α) : Bytes := u64 l.length ++ (l.map e).flatten
def bytes (b : Bytes) : Bytes := list (fun x => [x]) b
def bits (b : Bits) : Bytes := list flag b
def felts (v : List F) : Bytes := list felt v
def boolH (h : BoolH) : Bytes := u64 h.id
def fieldH (h : FieldH) : Bytes := u64 h.id
def label (l : Label) : Bytes := u64 l.code
def pair (p : FieldH × FieldH) : Bytes := fieldH p.1 ++ fieldH p.2
end Enc

/-- One wire instruction (the table of the design note). -/
def encWire : Wire → Bytes
  | .boolInput out owner w once rev v =>
    1 :: (Enc.boolH out ++ Enc.party owner ++ Enc.u64 w ++ Enc.flag once ++ Enc.flag rev ++ Enc.bits v)
  | .boolInputBoth oa ob w once rev v =>
    2 :: (Enc.boolH oa ++ Enc.boolH ob ++ Enc.u64 w ++ Enc.flag once ++ Enc.flag rev ++ Enc.bits v)
  | .boolPublic out v => 3 :: (Enc.boolH out ++ Enc.bits v)
  | .run out name n input => 4 :: (Enc.boolH out ++ Enc.bytes name ++ Enc.u64 n ++ Enc.boolH input)
  | .concat out ps => 5 :: (Enc.boolH out ++ Enc.list Enc.boolH ps)
  | .slice out h lo hi => 6 :: (Enc.boolH out ++ Enc.boolH h ++ Enc.u64 lo ++ Enc.u64 hi)
  | .pick out h is => 7 :: (Enc.boolH out ++ Enc.boolH h ++ Enc.list Enc.u64 is)
  | .openBool h l => 8 :: (Enc.boolH h ++ Enc.label l)
  | .openBoolTo h r l _ => 9 :: (Enc.boolH h ++ Enc.party r ++ Enc.label l)
  | .freeBool h => 10 :: Enc.boolH h
  | .fieldInput oa ob k rev v =>
    11 :: (Enc.list Enc.fieldH oa ++ Enc.list Enc.fieldH ob ++ Enc.kind k ++ Enc.flag rev ++ Enc.felts v)
  | .fieldPublic out v => 12 :: (Enc.fieldH out ++ Enc.felt v)
  | .fieldAdd out a b => 13 :: (Enc.fieldH out ++ Enc.fieldH a ++ Enc.fieldH b)
  | .fieldSub out a b => 14 :: (Enc.fieldH out ++ Enc.fieldH a ++ Enc.fieldH b)
  | .fieldScale out a k => 15 :: (Enc.fieldH out ++ Enc.fieldH a ++ Enc.u64 k)
  | .fieldDivide out a k => 16 :: (Enc.fieldH out ++ Enc.fieldH a ++ Enc.felt k)
  | .fieldMul outs ps => 17 :: (Enc.list Enc.fieldH outs ++ Enc.list Enc.pair ps)
  | .fieldCheck => [18]
  | .openField hs l => 19 :: (Enc.list Enc.fieldH hs ++ Enc.label l)
  | .freeField h => 20 :: Enc.fieldH h
  | .exchange len l p => 21 :: (Enc.u64 len ++ Enc.label l ++ Enc.bytes p)

/-- A batch: the number of instructions, then each. -/
def encodeBatch (b : List Wire) : Bytes := Enc.list encWire b

/-- The bytes the agreement hash covers (design note, item 4): the batch with every private
payload emptied. A function of the skeletons only, by definition. -/
def skeletonBytes (b : List Wire) : Bytes := encodeBatch (b.map fun w => w.skel.blank)

/-- A reply item. -/
inductive Datum where
  | bits (b : Bits)
  | elems (v : List F)
  | bytes (b : Bytes)
  deriving DecidableEq, Repr

def encDatum : Datum → Bytes
  | .bits b => 1 :: Enc.bits b
  | .elems v => 2 :: Enc.felts v
  | .bytes b => 3 :: Enc.bytes b

def encodeReplies (r : List Datum) : Bytes := Enc.list encDatum r

/-- A decoder: the value and the rest of the input, or `none`. -/
def Dec (α : Type) : Type := Bytes → Option (α × Bytes)

namespace Dec

def pure {α : Type} (a : α) : Dec α := fun s => some (a, s)
def bind {α β : Type} (d : Dec α) (f : α → Dec β) : Dec β := fun s =>
  match d s with
  | some (a, s') => f a s'
  | none => none

instance : Monad Dec where
  pure := Dec.pure
  bind := Dec.bind

@[simp] theorem bind_apply {α β : Type} (d : Dec α) (f : α → Dec β) (s : Bytes) :
    (d >>= f) s = (match d s with
      | some (a, s') => f a s'
      | none => none) := rfl
@[simp] theorem pure_apply {α : Type} (a : α) (s : Bytes) : (Pure.pure a : Dec α) s = some (a, s) := rfl

def fail {α : Type} : Dec α := fun _ => none
def byte : Dec UInt8 := fun s =>
  match s with
  | b :: s => some (b, s)
  | [] => none
def take (n : Nat) : Dec Bytes := fun s => if n ≤ s.length then some (s.take n, s.drop n) else none
def u64 : Dec Nat := fun s =>
  match take 8 s with
  | some (b, s) => some (fromLE b, s)
  | none => none
def flag : Dec Bool := fun s =>
  match s with
  | b :: s => if b = 0 then some (false, s) else if b = 1 then some (true, s) else none
  | [] => none
def party : Dec Party := fun s =>
  match s with
  | b :: s => if b = 0 then some (.a, s) else if b = 1 then some (.b, s) else none
  | [] => none
def kind : Dec FieldIn := fun s =>
  match s with
  | b :: s => if b = 0 then some (.coins, s) else if b = 1 then some (.elements, s) else none
  | [] => none
def felt : Dec F := fun s =>
  match take 32 s with
  | some (b, s) => if h : fromLE b < modulus then some (⟨fromLE b, h⟩, s) else none
  | none => none
def count {α : Type} (d : Dec α) : Nat → Dec (List α)
  | 0 => fun s => some ([], s)
  | n + 1 => fun s =>
    match d s with
    | some (x, s) =>
      match count d n s with
      | some (xs, s) => some (x :: xs, s)
      | none => none
    | none => none
def list {α : Type} (d : Dec α) : Dec (List α) := fun s =>
  match u64 s with
  | some (n, s) => count d n s
  | none => none
def bytes : Dec Bytes := list byte
def bits : Dec Bits := list flag
def felts : Dec (List F) := list felt
def boolH : Dec BoolH := fun s =>
  match u64 s with
  | some (n, s) => some (⟨n⟩, s)
  | none => none
def fieldH : Dec FieldH := fun s =>
  match u64 s with
  | some (n, s) => some (⟨n⟩, s)
  | none => none
def label : Dec Label := fun s =>
  match u64 s with
  | some (n, s) => some (⟨n⟩, s)
  | none => none
def pair : Dec (FieldH × FieldH) := do
  let x ← fieldH
  let y ← fieldH
  Pure.pure (x, y)

end Dec

def decWire : Dec Wire := do
  let op ← Dec.byte
  match op.toNat with
  | 1 => do
    let out ← Dec.boolH; let owner ← Dec.party; let w ← Dec.u64
    let once ← Dec.flag; let rev ← Dec.flag; let v ← Dec.bits
    Pure.pure (.boolInput out owner w once rev v)
  | 2 => do
    let oa ← Dec.boolH; let ob ← Dec.boolH; let w ← Dec.u64
    let once ← Dec.flag; let rev ← Dec.flag; let v ← Dec.bits
    Pure.pure (.boolInputBoth oa ob w once rev v)
  | 3 => do
    let out ← Dec.boolH; let v ← Dec.bits
    Pure.pure (.boolPublic out v)
  | 4 => do
    let out ← Dec.boolH; let name ← Dec.bytes; let n ← Dec.u64; let input ← Dec.boolH
    Pure.pure (.run out name n input)
  | 5 => do
    let out ← Dec.boolH; let ps ← Dec.list Dec.boolH
    Pure.pure (.concat out ps)
  | 6 => do
    let out ← Dec.boolH; let h ← Dec.boolH; let lo ← Dec.u64; let hi ← Dec.u64
    Pure.pure (.slice out h lo hi)
  | 7 => do
    let out ← Dec.boolH; let h ← Dec.boolH; let is ← Dec.list Dec.u64
    Pure.pure (.pick out h is)
  | 8 => do
    let h ← Dec.boolH; let l ← Dec.label
    Pure.pure (.openBool h l)
  | 9 => do
    let h ← Dec.boolH; let r ← Dec.party; let l ← Dec.label
    Pure.pure (.openBoolTo h r l ())
  | 10 => do
    let h ← Dec.boolH
    Pure.pure (.freeBool h)
  | 11 => do
    let oa ← Dec.list Dec.fieldH; let ob ← Dec.list Dec.fieldH; let k ← Dec.kind
    let rev ← Dec.flag; let v ← Dec.felts
    Pure.pure (.fieldInput oa ob k rev v)
  | 12 => do
    let out ← Dec.fieldH; let v ← Dec.felt
    Pure.pure (.fieldPublic out v)
  | 13 => do
    let out ← Dec.fieldH; let a ← Dec.fieldH; let b ← Dec.fieldH
    Pure.pure (.fieldAdd out a b)
  | 14 => do
    let out ← Dec.fieldH; let a ← Dec.fieldH; let b ← Dec.fieldH
    Pure.pure (.fieldSub out a b)
  | 15 => do
    let out ← Dec.fieldH; let a ← Dec.fieldH; let k ← Dec.u64
    Pure.pure (.fieldScale out a k)
  | 16 => do
    let out ← Dec.fieldH; let a ← Dec.fieldH; let k ← Dec.felt
    Pure.pure (.fieldDivide out a k)
  | 17 => do
    let outs ← Dec.list Dec.fieldH; let ps ← Dec.list Dec.pair
    Pure.pure (.fieldMul outs ps)
  | 18 => Pure.pure .fieldCheck
  | 19 => do
    let hs ← Dec.list Dec.fieldH; let l ← Dec.label
    Pure.pure (.openField hs l)
  | 20 => do
    let h ← Dec.fieldH
    Pure.pure (.freeField h)
  | 21 => do
    let len ← Dec.u64; let l ← Dec.label; let p ← Dec.bytes
    Pure.pure (.exchange len l p)
  | _ => Dec.fail

def decodeBatch (s : Bytes) : Option (List Wire) :=
  match Dec.list decWire s with
  | some (b, []) => some b
  | _ => none

def decDatum : Dec Datum := do
  let t ← Dec.byte
  match t.toNat with
  | 1 => do let b ← Dec.bits; Pure.pure (.bits b)
  | 2 => do let v ← Dec.felts; Pure.pure (.elems v)
  | 3 => do let b ← Dec.bytes; Pure.pure (.bytes b)
  | _ => Dec.fail

def decodeReplies (s : Bytes) : Option (List Datum) :=
  match Dec.list decDatum s with
  | some (r, []) => some r
  | _ => none

/-- Every number written by `encWire` fits in a u64. -/
def Wire.Bounded : Wire → Prop
  | .boolInput out _ w _ _ v => out.id < B64 ∧ w < B64 ∧ v.length < B64
  | .boolInputBoth oa ob w _ _ v => oa.id < B64 ∧ ob.id < B64 ∧ w < B64 ∧ v.length < B64
  | .boolPublic out v => out.id < B64 ∧ v.length < B64
  | .run out name n input => out.id < B64 ∧ name.length < B64 ∧ n < B64 ∧ input.id < B64
  | .concat out ps => out.id < B64 ∧ ps.length < B64 ∧ ∀ p ∈ ps, p.id < B64
  | .slice out h lo hi => out.id < B64 ∧ h.id < B64 ∧ lo < B64 ∧ hi < B64
  | .pick out h is => out.id < B64 ∧ h.id < B64 ∧ is.length < B64 ∧ ∀ j ∈ is, j < B64
  | .openBool h l => h.id < B64 ∧ l.code < B64
  | .openBoolTo h _ l _ => h.id < B64 ∧ l.code < B64
  | .freeBool h => h.id < B64
  | .fieldInput oa ob _ _ v =>
    oa.length < B64 ∧ (∀ x ∈ oa, x.id < B64) ∧ ob.length < B64 ∧ (∀ x ∈ ob, x.id < B64) ∧ v.length < B64
  | .fieldPublic out _ => out.id < B64
  | .fieldAdd out a b => out.id < B64 ∧ a.id < B64 ∧ b.id < B64
  | .fieldSub out a b => out.id < B64 ∧ a.id < B64 ∧ b.id < B64
  | .fieldScale out a k => out.id < B64 ∧ a.id < B64 ∧ k < B64
  | .fieldDivide out a _ => out.id < B64 ∧ a.id < B64
  | .fieldMul outs ps =>
    outs.length < B64 ∧ (∀ x ∈ outs, x.id < B64) ∧ ps.length < B64 ∧ ∀ p ∈ ps, p.1.id < B64 ∧ p.2.id < B64
  | .fieldCheck => True
  | .openField hs l => hs.length < B64 ∧ (∀ x ∈ hs, x.id < B64) ∧ l.code < B64
  | .freeField h => h.id < B64
  | .exchange len l p => len < B64 ∧ l.code < B64 ∧ p.length < B64

def Datum.Bounded : Datum → Prop
  | .bits b => b.length < B64
  | .elems v => v.length < B64
  | .bytes b => b.length < B64

/-! ### Round trip -/

section RoundTrip

theorem length_le (k n : Nat) : (le k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [le, ih]

theorem fromLE_le (k n : Nat) : fromLE (le k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [le, fromLE, Nat.mod_one]
  | succ k ih =>
    rw [le, fromLE, ih, Nat.pow_succ', Nat.mod_mul,
      UInt8.toNat_ofNat_of_lt' (Nat.mod_lt n (by decide))]

theorem take_enc (n : Nat) (b s : Bytes) (h : b.length = n) : Dec.take n (b ++ s) = some (b, s) := by
  simp [Dec.take, h, List.take_left', List.drop_left']

@[simp] theorem u64_enc (n : Nat) (h : n < B64) (s : Bytes) : Dec.u64 (Enc.u64 n ++ s) = some (n, s) := by
  have hb : n % 256 ^ 8 = n := Nat.mod_eq_of_lt (by simpa [B64] using h)
  simp [Dec.u64, Enc.u64, take_enc 8 _ s (length_le 8 n), fromLE_le, hb]

@[simp] theorem flag_enc (b : Bool) (s : Bytes) : Dec.flag (Enc.flag b ++ s) = some (b, s) := by
  cases b <;> simp [Dec.flag, Enc.flag]

@[simp] theorem party_enc (p : Party) (s : Bytes) : Dec.party (Enc.party p ++ s) = some (p, s) := by
  cases p <;> simp [Dec.party, Enc.party]

@[simp] theorem kind_enc (k : FieldIn) (s : Bytes) : Dec.kind (Enc.kind k ++ s) = some (k, s) := by
  cases k <;> simp [Dec.kind, Enc.kind]

theorem modulus_lt : modulus < 256 ^ 32 := by decide

@[simp] theorem felt_enc (v : F) (s : Bytes) : Dec.felt (Enc.felt v ++ s) = some (v, s) := by
  have hv : v.val % 256 ^ 32 = v.val := Nat.mod_eq_of_lt (Nat.lt_trans v.isLt modulus_lt)
  simp [Dec.felt, Enc.felt, take_enc 32 _ s (length_le 32 v.val), fromLE_le, hv]

@[simp] theorem byte_enc (b : UInt8) (s : Bytes) : Dec.byte ([b] ++ s) = some (b, s) := rfl

@[simp] theorem boolH_enc (h : BoolH) (hb : h.id < B64) (s : Bytes) : Dec.boolH (Enc.boolH h ++ s) = some (h, s) := by
  simp [Dec.boolH, Enc.boolH, hb]

@[simp] theorem fieldH_enc (h : FieldH) (hb : h.id < B64) (s : Bytes) : Dec.fieldH (Enc.fieldH h ++ s) = some (h, s) := by
  simp [Dec.fieldH, Enc.fieldH, hb]

@[simp] theorem label_enc (l : Label) (hb : l.code < B64) (s : Bytes) : Dec.label (Enc.label l ++ s) = some (l, s) := by
  simp [Dec.label, Enc.label, hb]

theorem count_enc {α : Type} (d : Dec α) (e : α → Bytes) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s, d (e x ++ s) = some (x, s)) →
      ∀ s, Dec.count d l.length ((l.map e).flatten ++ s) = some (l, s)
  | [], _, s => rfl
  | x :: l, h, s => by
    have hx := h x (by simp) ((l.map e).flatten ++ s)
    have hl := count_enc d e l (fun y hy => h y (by simp [hy])) s
    simp only [List.map_cons, List.flatten_cons, List.length_cons, Dec.count, List.append_assoc, hx, hl]

theorem list_enc {α : Type} (d : Dec α) (e : α → Bytes) (l : List α) (hl : l.length < B64)
    (h : ∀ x ∈ l, ∀ s, d (e x ++ s) = some (x, s)) (s : Bytes) :
    Dec.list d (Enc.list e l ++ s) = some (l, s) := by
  simp only [Dec.list, Enc.list, List.append_assoc, u64_enc _ hl, count_enc d e l h s]

@[simp] theorem bytes_enc (b : Bytes) (hl : b.length < B64) (s : Bytes) : Dec.bytes (Enc.bytes b ++ s) = some (b, s) :=
  list_enc _ _ b hl (fun x _ s => byte_enc x s) s

@[simp] theorem bits_enc (b : Bits) (hl : b.length < B64) (s : Bytes) : Dec.bits (Enc.bits b ++ s) = some (b, s) :=
  list_enc _ _ b hl (fun x _ s => flag_enc x s) s

@[simp] theorem felts_enc (v : List F) (hl : v.length < B64) (s : Bytes) : Dec.felts (Enc.felts v ++ s) = some (v, s) :=
  list_enc _ _ v hl (fun x _ s => felt_enc x s) s

@[simp] theorem boolHs_enc (l : List BoolH) (hl : l.length < B64) (hb : ∀ x ∈ l, x.id < B64) (s : Bytes) :
    Dec.list Dec.boolH (Enc.list Enc.boolH l ++ s) = some (l, s) :=
  list_enc _ _ l hl (fun x hx s => boolH_enc x (hb x hx) s) s

@[simp] theorem fieldHs_enc (l : List FieldH) (hl : l.length < B64) (hb : ∀ x ∈ l, x.id < B64) (s : Bytes) :
    Dec.list Dec.fieldH (Enc.list Enc.fieldH l ++ s) = some (l, s) :=
  list_enc _ _ l hl (fun x hx s => fieldH_enc x (hb x hx) s) s

@[simp] theorem nats_enc (l : List Nat) (hl : l.length < B64) (hb : ∀ x ∈ l, x < B64) (s : Bytes) :
    Dec.list Dec.u64 (Enc.list Enc.u64 l ++ s) = some (l, s) :=
  list_enc _ _ l hl (fun x hx s => u64_enc x (hb x hx) s) s

@[simp] theorem pairs_enc (l : List (FieldH × FieldH)) (hl : l.length < B64)
    (hb : ∀ p ∈ l, p.1.id < B64 ∧ p.2.id < B64) (s : Bytes) :
    Dec.list Dec.pair (Enc.list Enc.pair l ++ s) = some (l, s) :=
  list_enc _ _ l hl (fun x hx s => by
    obtain ⟨h1, h2⟩ := hb x hx
    simp [Dec.pair, Enc.pair, h1, h2]) s

theorem wire_enc (w : Wire) (hw : w.Bounded) (s : Bytes) : decWire (encWire w ++ s) = some (w, s) := by
  cases w <;> simp only [Wire.Bounded] at hw <;>
    simp +contextual [decWire, encWire, Dec.byte, hw]

/-- **Round trip of the batch encoding.** -/
theorem decodeBatch_encodeBatch (b : List Wire) (hl : b.length < B64) (hb : ∀ w ∈ b, w.Bounded) :
    decodeBatch (encodeBatch b) = some b := by
  have := list_enc decWire encWire b hl (fun w hw s => wire_enc w (hb w hw) s) []
  simp only [List.append_nil] at this
  simp [decodeBatch, encodeBatch, this]

theorem datum_enc (d : Datum) (hd : d.Bounded) (s : Bytes) : decDatum (encDatum d ++ s) = some (d, s) := by
  cases d <;> simp only [Datum.Bounded] at hd <;> simp [decDatum, encDatum, Dec.byte, hd]

/-- **Round trip of the reply encoding.** -/
theorem decodeReplies_encodeReplies (r : List Datum) (hl : r.length < B64) (hr : ∀ d ∈ r, d.Bounded) :
    decodeReplies (encodeReplies r) = some r := by
  have := list_enc decDatum encDatum r hl (fun d hd s => datum_enc d (hr d hd) s) []
  simp only [List.append_nil] at this
  simp [decodeReplies, encodeReplies, this]

theorem blank_bounded (w : Wire) (hw : w.Bounded) : w.skel.blank.Bounded := by
  have h0 : (0 : Nat) < B64 := by decide
  cases w <;> simp_all [Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank] <;> exact hw.2.2.2

/-- **Agreement on skeleton bytes is agreement on skeletons.** Equal skeleton bytes (what the
agreement hash covers) mean the two batches have the same skeletons, instruction by
instruction; so a hash match (absent a SHA-256 collision) is skeleton agreement. -/
theorem skeletonBytes_inj (b₁ b₂ : List Wire) (h₁ : b₁.length < B64) (h₂ : b₂.length < B64)
    (hb₁ : ∀ w ∈ b₁, w.Bounded) (hb₂ : ∀ w ∈ b₂, w.Bounded) (h : skeletonBytes b₁ = skeletonBytes b₂) :
    b₁.map InstrP.skel = b₂.map InstrP.skel := by
  have d₁ := decodeBatch_encodeBatch (b₁.map fun w => w.skel.blank) (by simpa using h₁)
    (by simpa using fun w hw => blank_bounded w (hb₁ w hw))
  have d₂ := decodeBatch_encodeBatch (b₂.map fun w => w.skel.blank) (by simpa using h₂)
    (by simpa using fun w hw => blank_bounded w (hb₂ w hw))
  unfold skeletonBytes at h
  rw [h, d₂] at d₁
  have e := congrArg (fun o => (o.getD []).map InstrP.skel) d₁
  have hc : (InstrP.skel ∘ fun w : Wire => w.skel.blank) = InstrP.skel :=
    funext fun w => InstrP.blank_skel w.skel
  simp only [Option.getD_some, List.map_map, hc] at e
  exact e.symm

end RoundTrip

end TlsMpc.Node.Engine
