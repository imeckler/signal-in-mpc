import TlsMpc.Node.Engine.Model
import TlsMpc.Node.Engine.Labels
import TlsMpc.ContactKernelsProofs

/-!
# Contacts and account flows: shared definitions and generic lemmas

REORGANIZATION_PLAN.md stage S9 (flows `Contacts.*`, `Account.*`). Advance work in a new file;
nothing here edits the engine framework (`Engine.lean`, `Engine/Model.lean`). No I/O; no emitter
imports this module.

WHAT IS HERE.
  * Bytes as wire bits: `bitsOf` / `bytesOf`, each byte least significant bit first, as
    `kernel.h` `byte_bits` / `bits_bytes` (the order every kernel bundle and every `k.constant`
    uses). `bytesOf_bitsOf` is the round trip.
  * `assignOf`: the `BVExpr` assignment whose variable `j` is byte `j` of a list, and
    `inputValue_assignOf`: a kernel's input field read under it is the corresponding slice. This is
    how the kernel theorems of `ContactKernelsProofs.lean` (stated for every assignment) are applied
    to the bits a flow feeds a circuit.
  * `kernelCircuit K inBytes marks`: the model circuit (`Engine.Circuit`) that computes the Lean
    kernel `K` on its input bundle, the bundle being the kernel's input fields concatenated in
    declaration order and the output bundle its output fields concatenated (`kernel.h` `Kernel::run`).
    `Loaded E` is the statement that the environment's circuits under the names `contact-key`,
    `contact-seal N`, `contact-open N` are these. It is exactly the trust in the pinned flat
    circuits computing their Lean definitions (T2, stage P3; the model's own assumption that "a
    circuit computes its Lean definition"). Nothing else about the engines is assumed.
  * Labels `blobAccepted`, `sealedBlob` (plan 4.3, "Stored state"): the registry's
    `Label.blobAccepted`, `Label.sealedBlob` (Engine/Labels.lean, pairwise distinct with every
    other flow's label; provisional codes until RevealKind exists, Engine.lean decision D7).
  * Script combinators `seq` (an instruction whose reply is unit), `seqs` (a block of them) and
    `openThen` (an opening and its continuation), with generic lemmas:
      - `plain` instructions (no private input, no release, independent of the peer: public bits,
        run, concat, slice, pick, free) and `runPlain`, their ideal effect;
      - `viewD_seqs`, `jointRun_seqs`: a block of plain instructions releases nothing and moves the
        ideal state by `runPlain`, against any adversary / for two honest parties;
      - `viewD_openThen`, `jointRun_openThen`: an opening releases the handle's ideal value, with its
        label, to both;
      - `Silent` scripts (no release instruction on any branch) and `silent_view`: their runs
        release nothing to either party, whatever the adversary;
      - `WF_seqs`, `WF_openThen`: well-formedness reduced to the shell's `check`, in a form `simp`
        evaluates on a symbolic context; `Fresh c n`: no handle id from `n` on was ever defined
        (the Boolean half of `Counters.Ahead`, Engine.lean); `WFP_seq`, `WFP_openThen`,
        `frees_wfp`: the same with a postcondition on the context a script leaves (`WFP`).
-/

namespace TlsMpc.Node.Flows.Contacts

open TlsMpc.Node.Engine
open Std.Tactic.BVDecide

abbrev B8 := List (BitVec 8)

/-! ## Bytes as wire bits (`kernel.h` `byte_bits`: least significant bit first) -/

def bitsOfByte (b : BitVec 8) : Bits :=
  [b.getLsbD 0, b.getLsbD 1, b.getLsbD 2, b.getLsbD 3, b.getLsbD 4, b.getLsbD 5, b.getLsbD 6, b.getLsbD 7]

def bitsOf (l : B8) : Bits := l.flatMap bitsOfByte

def byteOfBits (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BitVec 8 :=
  BitVec.ofNat 8 (b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat +
    32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat)

/-- `kernel.h` `bits_bytes` (a trailing partial byte is dropped). -/
def bytesOf : Bits → B8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => byteOfBits b0 b1 b2 b3 b4 b5 b6 b7 :: bytesOf rest
  | _ => []

theorem byteOfBits_bitsOfByte : ∀ b : BitVec 8,
    byteOfBits (b.getLsbD 0) (b.getLsbD 1) (b.getLsbD 2) (b.getLsbD 3) (b.getLsbD 4) (b.getLsbD 5)
      (b.getLsbD 6) (b.getLsbD 7) = b := by
  decide

@[simp] theorem bitsOf_nil : bitsOf [] = [] := rfl

@[simp] theorem bitsOf_cons (b : BitVec 8) (l : B8) : bitsOf (b :: l) = bitsOfByte b ++ bitsOf l := by
  simp [bitsOf]

@[simp] theorem bitsOf_append (l m : B8) : bitsOf (l ++ m) = bitsOf l ++ bitsOf m := by
  simp [bitsOf, List.flatMap_append]

@[simp] theorem length_bitsOfByte (b : BitVec 8) : (bitsOfByte b).length = 8 := rfl

@[simp] theorem length_bitsOf (l : B8) : (bitsOf l).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [bitsOf_cons, List.length_append, ih, length_bitsOfByte, List.length_cons]; omega

theorem bytesOf_byte (b : BitVec 8) (rest : Bits) : bytesOf (bitsOfByte b ++ rest) = b :: bytesOf rest := by
  simp only [bitsOfByte, List.cons_append, List.nil_append, bytesOf, byteOfBits_bitsOfByte]

theorem bytesOf_bitsOf_append (l : B8) (rest : Bits) : bytesOf (bitsOf l ++ rest) = l ++ bytesOf rest := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [bitsOf_cons, List.append_assoc, bytesOf_byte, ih, List.cons_append]

@[simp] theorem bytesOf_bitsOf (l : B8) : bytesOf (bitsOf l) = l := by
  have h := bytesOf_bitsOf_append l []
  rw [List.append_nil] at h
  rw [h]
  simp [bytesOf]

theorem bitsOf_inj (l m : B8) (h : bitsOf l = bitsOf m) : l = m := by
  rw [← bytesOf_bitsOf l, h, bytesOf_bitsOf]

/-! ## The assignment of a kernel's input variables -/

/-- Variable `j` (for `j ≥ i`) is element `j - i` of the list (a zero byte beyond it). -/
def chain : Nat → List BVExpr.PackedBitVec → BVExpr.Assignment
  | _, [] => .leaf ⟨(0 : BitVec 8)⟩
  | i, x :: xs => .branch (i + 1) (.leaf x) (chain (i + 1) xs)

/-- The assignment whose variable `j` is byte `j` of `l`. -/
def assignOf (l : B8) : BVExpr.Assignment := chain 0 (l.map fun b => ⟨b⟩)

theorem get_branch {α : Type} (p : Nat) (l r : Lean.RArray α) (n : Nat) :
    (Lean.RArray.branch p l r).get n = if p ≤ n then r.get n else l.get n := by
  have e : (Lean.RArray.branch p l r).get n = Bool.rec (motive := fun _ => α) (l.get n) (r.get n) (Nat.ble p n) := rfl
  rw [e]
  cases hb : Nat.ble p n
  · rw [if_neg (fun hp => by rw [Nat.ble_eq_true_of_le hp] at hb; cases hb)]
  · rw [if_pos (Nat.le_of_ble_eq_true hb)]

theorem get_chain : ∀ (l : List BVExpr.PackedBitVec) (i n : Nat), i ≤ n →
    BVExpr.Assignment.get (chain i l) n = l.getD (n - i) ⟨(0 : BitVec 8)⟩
  | [], i, n, _ => by simp [chain, BVExpr.Assignment.get]
  | x :: xs, i, n, h => by
    have ih := fun hn => get_chain xs (i + 1) n hn
    unfold BVExpr.Assignment.get at *
    rw [chain, get_branch]
    by_cases hn : i + 1 ≤ n
    · rw [if_pos hn, ih hn]
      have e : n - i = (n - (i + 1)) + 1 := by omega
      rw [e]
      simp
    · rw [if_neg hn]
      have e : n - i = 0 := by omega
      rw [e]
      rfl

theorem eval_assignOf (l : B8) (j : Nat) (hj : j < l.length) :
    BVExpr.eval (assignOf l) (BVExpr.var j : BVExpr 8) = l[j] := by
  rw [BVExpr.eval_var, assignOf, get_chain _ 0 j (Nat.zero_le j), Nat.sub_zero,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  simp

theorem inputValue_assignOf (l : B8) (start count : Nat) (h : start + count ≤ l.length) :
    HybridKernel.inputValue (assignOf l) start count = (l.drop start).take count := by
  apply List.ext_getElem
  · rw [HybridKernel.inputValue_length]
    simp
    omega
  · intro i h1 h2
    rw [HybridKernel.inputValue_length] at h1
    simp only [HybridKernel.inputValue, ByteCircuit.inputBytes, List.getElem_map, List.getElem_range,
      List.getElem_take, List.getElem_drop]
    exact eval_assignOf l (start + i) (by omega)

/-! ## Kernels as model circuits -/

/-- The kernel's output fields, concatenated, on the input bytes `input` (byte `j` = variable `j`). -/
def kernelOut (K : HybridKernel.Kernel) (input : B8) : B8 :=
  (K.outputs.map (fun field => field.value.map (BVExpr.eval (assignOf input)))).flatten

/-- The circuit that computes kernel `K`: input bundle `8 * inBytes` bits, output marks `marks`. -/
def kernelCircuit (K : HybridKernel.Kernel) (inBytes : Nat) (marks : List Mark) : Engine.Circuit where
  inWidth := 8 * inBytes
  outMarks := marks
  eval v := bitsOf (kernelOut K (bytesOf v))

/-- The kernel cache names (`service_kernels.h`: `k.cache.get(...)` arguments). -/
def keyName : Bytes := ascii "contact-key"
def sealName (size : Nat) : Bytes := ascii ("contact-seal " ++ toString size)
def openName (size : Nat) : Bytes := ascii ("contact-open " ++ toString size)

/-- Output marks (`HybridKernels.lean`: `contactKey` traffic private; `contactSeal` ciphertext and
check public; `contactOpen` accepted public, content private). -/
def keyMarks : List Mark := List.replicate 480 .never
def sealMarks (size : Nat) : List Mark := List.replicate (8 * size + 128) .pub
def openMarks (size : Nat) : List Mark := List.replicate 8 .pub ++ List.replicate (8 * size) .never

/-- The environment's circuits under the contact kernels' names compute the Lean kernels (inputs:
traffic 60, version 8, content / ciphertext, check 16 bytes; `HybridKernel.find` accepts sizes 1 to
16384). The trusted correspondence of T2; nothing else is assumed of `E`. -/
structure Loaded (E : Env) : Prop where
  key : E.circuits keyName = some (kernelCircuit HybridKernel.contactKey 64 keyMarks)
  sealing : ∀ size, 0 < size → size ≤ 16384 →
    E.circuits (sealName size) = some (kernelCircuit (HybridKernel.contactSeal size) (68 + size) (sealMarks size))
  opening : ∀ size, 0 < size → size ≤ 16384 →
    E.circuits (openName size) = some (kernelCircuit (HybridKernel.contactOpen size) (84 + size) (openMarks size))

/-! ## Labels (from the registry, Engine/Labels.lean; plan 4.3 "Stored state") -/

/-- `Reveal.blobAccepted`: the `accepted` byte of `contact-open` (ops 37, 55, 63). -/
def blobAccepted : Label := Label.blobAccepted
/-- `Reveal.sealedBlob`: ciphertext and check value of `contact-seal` (ops 38, 54, 64). -/
def sealedBlob : Label := Label.sealedBlob

/-! ## Script combinators -/

/-- One instruction whose reply is unit, then `s`. -/
def seq {α : Type} (i : Instr) (s : Script α) : Script α :=
  .step i fun
    | .unit => s
    | _ => .abort "reply shape"

/-- A block of unit-reply instructions, then `s`. -/
def seqs {α : Type} (is : List Instr) (s : Script α) : Script α := is.foldr seq s

/-- Open `h` to both parties with label `l`, then continue with the opened bits. -/
def openThen {α : Type} (h : BoolH) (l : Label) (k : Bits → Script α) : Script α :=
  .step (.openBool h l) fun
    | .bits b => k b
    | _ => .abort "reply shape"

/-- Free each of the handles, in order. -/
def frees (hs : List BoolH) : List Instr := hs.map .freeBool

@[simp] theorem seqs_nil {α : Type} (s : Script α) : seqs [] s = s := rfl
@[simp] theorem seqs_cons {α : Type} (i : Instr) (is : List Instr) (s : Script α) :
    seqs (i :: is) s = seq i (seqs is s) := rfl

/-! ## Plain instructions in the model -/

/-- No private input, no release, and an ideal effect independent of the parties. -/
def plain : Instr → Bool
  | .boolPublic .. => true
  | .run .. => true
  | .concat .. => true
  | .slice .. => true
  | .pick .. => true
  | .freeBool .. => true
  | _ => false

/-- The wire form of an instruction without private parts. -/
def blankWire (i : Instr) : Wire := i.map (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => ())

theorem fill_plain (hash : Bytes → Bytes) (me : Party) (σ : Store) (i : Instr) (h : plain i = true) :
    fill hash me σ i = some (blankWire i) := by
  cases i <;> simp_all [plain, fill, blankWire]

theorem early_blank (i : Instr) (h : plain i = true) : (blankWire i).early = none := by
  cases i <;> simp_all [plain, blankWire, InstrP.map, Wire.early]

/-- The ideal effect of a plain instruction (`none`: the functionality aborts). -/
def plainStep (E : Env) (i : Instr) (I : Ideal) : Option Ideal :=
  match idealStep E .a (blankWire i) {} I with
  | some (I', _, _) => some I'
  | none => none

theorem idealStep_plain (E : Env) (me : Party) (p : PeerPart) (I : Ideal) (i : Instr) (h : plain i = true) :
    idealStep E me (blankWire i) p I = (plainStep E i I).map fun I' => (I', none, none) := by
  cases i with
  | boolPublic out bits => simp [idealStep, plainStep, blankWire, InstrP.map]
  | run out name copies input =>
    simp only [idealStep, plainStep, blankWire, InstrP.map]
    cases hc : E.circuits name <;> cases hv : I.bools input.id <;> simp
    split <;> simp
  | concat out parts =>
    simp only [idealStep, plainStep, blankWire, InstrP.map]
    cases hm : parts.mapM (fun h => I.bools h.id) <;> simp
  | slice out hh lo hi =>
    simp only [idealStep, plainStep, blankWire, InstrP.map]
    cases hv : I.bools hh.id <;> simp
    split <;> simp
  | pick out hh idx =>
    simp only [idealStep, plainStep, blankWire, InstrP.map]
    cases hv : I.bools hh.id <;> simp
    split <;> simp
  | freeBool hh => simp [idealStep, plainStep, blankWire, InstrP.map]
  | _ => simp [plain] at h

/-- A block of plain instructions, ideally. -/
def runPlain (E : Env) : List Instr → Ideal → Option Ideal
  | [], I => some I
  | i :: is, I =>
    match plainStep E i I with
    | some I' => runPlain E is I'
    | none => none

theorem runPlain_free (E : Env) (h : BoolH) (I : Ideal) : runPlain E [.freeBool h] I = some (I.dropBool h) := by
  simp [runPlain, plainStep, idealStep, blankWire, InstrP.map]

theorem runPlain_free2 (E : Env) (h₁ h₂ : BoolH) (I : Ideal) :
    runPlain E [.freeBool h₁, .freeBool h₂] I = some ((I.dropBool h₁).dropBool h₂) := by
  simp [runPlain, plainStep, idealStep, blankWire, InstrP.map]

theorem absorb_none (hash : Bytes → Bytes) (me : Party) (i : Instr) (σ : Store) :
    absorb hash me i σ none = (.unit, σ) := by
  cases i <;> rfl

/-! ## Runs against an adversary -/

section Adv

variable (E : Env) (me : Party) (adv : Adversary)

/-- **A block of plain instructions releases nothing.** If the rest of the run, from the ideal
state the block produces, releases at most `L` to the adversary, so does the whole run. -/
theorem viewD_seqs {α : Type} (s : Script α) (σ : Store) (L : List Release) :
    ∀ (is : List Instr), (∀ i ∈ is, plain i = true) → ∀ (I : Ideal) (vD : List Release),
    (∀ I', runPlain E is I = some I' → (withAdv E me adv s σ I' vD).viewD <+: L) →
    (withAdv E me adv (seqs is s) σ I vD).viewD <+: L
  | [], _, I, vD, h => h I rfl
  | i :: is, hp, I, vD, h => by
    have hi := hp i (by simp)
    show (withAdv E me adv (seq i (seqs is s)) σ I vD).viewD <+: L
    simp only [seq, withAdv, fill_plain _ _ _ i hi, early_blank i hi, Option.toList_none, List.append_nil]
    split
    · exact List.nil_prefix
    · rw [idealStep_plain E me _ I i hi]
      cases hs : plainStep E i I with
      | none => exact List.nil_prefix
      | some I' =>
        simp only [Option.map_some, absorb_none, Option.toList_none, List.nil_append, List.append_nil]
        exact viewD_seqs s σ L is (fun j hj => hp j (by simp [hj])) I' vD
          (fun I'' h'' => h I'' (by simp [runPlain, hs, h'']))

/-- **An opening releases the handle's value, with its label.** -/
theorem viewD_openThen {α : Type} (h : BoolH) (l : Label) (k : Bits → Script α) (σ : Store) (I : Ideal)
    (vD : List Release) (v : Bits) (L : List Release) (hv : I.bools h.id = some v)
    (hk : (withAdv E me adv (k v) σ I (vD ++ [⟨l, .bits v⟩])).viewD <+: L) :
    (withAdv E me adv (openThen h l k) σ I vD).viewD <+: ⟨l, .bits v⟩ :: L := by
  simp only [openThen, withAdv, fill, InstrP.map, Wire.early, Option.toList_none, List.append_nil]
  split
  · exact List.nil_prefix
  · simp only [idealStep, hv, absorb, Option.toList_some, List.cons_append, List.nil_append]
    exact List.cons_prefix_cons.mpr ⟨rfl, hk⟩

/-- Scripts with no release instruction on any branch. -/
inductive Silent {α : Type} : Script α → Prop
  | done (a : α) : Silent (.done a)
  | abort (r : String) : Silent (.abort r)
  | step (i : Instr) (k : Reply → Script α) : i.label? = none → (∀ r, Silent (k r)) → Silent (.step i k)

theorem Silent.seq {α : Type} {i : Instr} {s : Script α} (hl : i.label? = none) (hs : Silent s) :
    Silent (Contacts.seq i s) :=
  Silent.step i _ hl (fun r => by cases r <;> first | exact hs | exact Silent.abort _)

theorem Silent.seqs {α : Type} {s : Script α} (hs : Silent s) :
    ∀ (is : List Instr), (∀ i ∈ is, i.label? = none) → Silent (Contacts.seqs is s)
  | [], _ => hs
  | i :: is, h => Silent.seq (h i (by simp)) (Silent.seqs hs is (fun j hj => h j (by simp [hj])))

/-- **Silent scripts release nothing**, to the honest party or to the adversary. -/
theorem silent_view {α : Type} (s : Script α) (hs : Silent s) :
    ∀ (σ : Store) (I : Ideal) (vD : List Release),
      (withAdv E me adv s σ I vD).viewD = [] ∧ (withAdv E me adv s σ I vD).viewH = [] := by
  induction hs with
  | done a => intro σ I vD; exact ⟨rfl, rfl⟩
  | abort r => intro σ I vD; exact ⟨rfl, rfl⟩
  | step i k hl _ ih =>
    intro σ I vD
    simp only [withAdv]
    split
    · exact ⟨rfl, rfl⟩
    · next w hw =>
      have hwl : w.label? = none := by
        rw [← InstrP.label?_skel, fill_skel E.hash me σ i w hw, InstrP.label?_skel]
        exact hl
      have he : w.early = none := by
        cases w <;> simp_all [Wire.early, InstrP.label?]
      split
      · simp [he]
      · split
        · simp [he]
        · next I' toH toD hst =>
          have hls := idealStep_labels E me w _ I I' toH toD hst
          have h1 : toH = none := by
            cases toH with
            | none => rfl
            | some r => have := hls.1 r rfl; rw [hwl] at this; cases this
          have h2 : toD = none := by
            cases toD with
            | none => rfl
            | some r => have := hls.2 r rfl; rw [hwl] at this; cases this
          subst h1
          subst h2
          simp only [Option.toList_none, List.nil_append, List.append_nil]
          exact ih _ _ _ _

theorem silent_prefix {α : Type} (s : Script α) (hs : Silent s) (σ : Store) (I : Ideal) (vD L : List Release) :
    (withAdv E me adv s σ I vD).viewD <+: L := by
  rw [(silent_view E me adv s hs σ I vD).1]
  exact List.nil_prefix

theorem viewD_openThen_none {α : Type} (h : BoolH) (l : Label) (k : Bits → Script α) (σ : Store) (I : Ideal)
    (vD : List Release) (hv : I.bools h.id = none) :
    (withAdv E me adv (openThen h l k) σ I vD).viewD = [] := by
  simp only [openThen, withAdv, fill, InstrP.map, Wire.early, Option.toList_none, List.append_nil]
  split
  · rfl
  · simp [idealStep, hv]

/-- The value of handle `h` after the block `is` (the empty list if the block or the handle has
none: then nothing is released). -/
def openedAfter (E : Env) (is : List Instr) (h : BoolH) (I : Ideal) : Bits :=
  match runPlain E is I with
  | some I' => (I'.bools h.id).getD []
  | none => []

/-- **T3 for the shape "plain block, one opening, silent rest".** At most one release: the label
of the opening and the opened handle's value after the block. -/
theorem viewD_block_open {α : Type} (is : List Instr) (hp : ∀ i ∈ is, plain i = true) (h : BoolH) (l : Label)
    (k : Bits → Script α) (hk : ∀ v, Silent (k v)) (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv (seqs is (openThen h l k)) σ I vD).viewD <+: [⟨l, .bits (openedAfter E is h I)⟩] := by
  refine viewD_seqs E me adv _ σ _ is hp I vD (fun I' hI' => ?_)
  cases hv : I'.bools h.id with
  | none => rw [viewD_openThen_none E me adv h l k σ I' vD hv]; exact List.nil_prefix
  | some v =>
    have e : openedAfter E is h I = v := by simp [openedAfter, hI', hv]
    rw [e]
    exact viewD_openThen E me adv h l k σ I' vD v [] hv (silent_prefix E me adv _ (hk v) _ _ _ _)

theorem seqs_append {α : Type} (is js : List Instr) (s : Script α) : seqs is (seqs js s) = seqs (is ++ js) s := by
  simp [seqs, List.foldr_append]

end Adv

/-! ## Properties of every result -/

/-- Every `done` leaf of the script satisfies `Q`. -/
inductive Leaves {α : Type} (Q : α → Prop) : Script α → Prop
  | done (a : α) : Q a → Leaves Q (.done a)
  | abort (r : String) : Leaves Q (.abort r)
  | step (i : Instr) (k : Reply → Script α) : (∀ r, Leaves Q (k r)) → Leaves Q (.step i k)

theorem Leaves.bind {α β : Type} {Q : β → Prop} (f : α → Script β) (hf : ∀ a, Leaves Q (f a)) :
    ∀ (s : Script α), Leaves Q (s.bind f)
  | .done a => hf a
  | .abort r => Leaves.abort r
  | .step i k => Leaves.step i _ (fun r => Leaves.bind f hf (k r))

theorem Leaves.seqs {α : Type} {Q : α → Prop} {s : Script α} (hs : Leaves Q s) :
    ∀ (is : List Instr), Leaves Q (Contacts.seqs is s)
  | [] => hs
  | i :: is => Leaves.step i _ (fun r => by
      cases r <;> first | exact Leaves.seqs hs is | exact Leaves.abort _)

/-- **Results satisfy the leaves' property**, against any adversary. -/
theorem Leaves.result {α : Type} {Q : α → Prop} (E : Env) (me : Party) (adv : Adversary) (s : Script α)
    (hs : Leaves Q s) : ∀ (σ : Store) (I : Ideal) (vD : List Release) (x : α),
      (withAdv E me adv s σ I vD).result = some x → Q x := by
  induction hs with
  | done a ha => intro σ I vD x h; simp only [withAdv, Option.some.injEq] at h; subst h; exact ha
  | abort r => intro σ I vD x h; simp [withAdv] at h
  | step i k _ ih =>
    intro σ I vD x h
    simp only [withAdv] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact ih _ _ _ _ x h

/-! ## Two honest parties -/

section Joint

variable (E : Env)

theorem jointRun_seqs {α β : Type} (sA : Script α) (sB : Script β) (σA σB : Store) :
    ∀ (is : List Instr), (∀ i ∈ is, plain i = true) → ∀ (I I' : Ideal), runPlain E is I = some I' →
    (jointRun E (seqs is sA) (seqs is sB) σA σB I).result = (jointRun E sA sB σA σB I').result ∧
    (jointRun E (seqs is sA) (seqs is sB) σA σB I).ideal = (jointRun E sA sB σA σB I').ideal
  | [], _, I, I', h => by
    simp only [runPlain, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | i :: is, hp, I, I', h => by
    have hi := hp i (by simp)
    simp only [runPlain] at h
    cases hs : plainStep E i I with
    | none => rw [hs] at h; cases h
    | some I1 =>
      rw [hs] at h
      have ih := jointRun_seqs sA sB σA σB is (fun j hj => hp j (by simp [hj])) I1 I' h
      show (jointRun E (seq i (seqs is sA)) (seq i (seqs is sB)) σA σB I).result = _ ∧
        (jointRun E (seq i (seqs is sA)) (seq i (seqs is sB)) σA σB I).ideal = _
      simp only [seq, jointRun, if_true, fill_plain _ _ _ i hi, idealStep_plain E .a _ I i hi, hs,
        Option.map_some, absorb_none]
      exact ih

/-- One unit-reply step of two honest parties whose ideal effect is `I'` (inputs included). -/
theorem jointRun_seq {α β : Type} (iA iB : Instr) (sA : Script α) (sB : Script β) (σA σB : Store) (I I' : Ideal)
    (wA wB : Wire) (hsk : iA.skel = iB.skel) (hA : fill E.hash .a σA iA = some wA)
    (hB : fill E.hash .b σB iB = some wB) (hst : idealStep E .a wA wB.part I = some (I', none, none)) :
    (jointRun E (seq iA sA) (seq iB sB) σA σB I).result = (jointRun E sA sB σA σB I').result ∧
    (jointRun E (seq iA sA) (seq iB sB) σA σB I).ideal = (jointRun E sA sB σA σB I').ideal := by
  simp only [seq, jointRun, if_pos hsk, hA, hB, hst, absorb_none]
  exact ⟨trivial, trivial⟩

theorem jointRun_openThen {α β : Type} (h : BoolH) (l : Label) (kA : Bits → Script α) (kB : Bits → Script β)
    (σA σB : Store) (I : Ideal) (v : Bits) (hv : I.bools h.id = some v) :
    (jointRun E (openThen h l kA) (openThen h l kB) σA σB I).result = (jointRun E (kA v) (kB v) σA σB I).result ∧
    (jointRun E (openThen h l kA) (openThen h l kB) σA σB I).ideal = (jointRun E (kA v) (kB v) σA σB I).ideal := by
  simp [openThen, jointRun, fill, InstrP.map, idealStep, hv, absorb]

theorem jointRun_done {α β : Type} (a : α) (b : β) (σA σB : Store) (I : Ideal) :
    (jointRun E (.done a) (.done b) σA σB I).result = some (a, b) ∧
    (jointRun E (.done a) (.done b) σA σB I).ideal = I := ⟨rfl, rfl⟩

end Joint

/-! ## Well-formedness -/

/-- No Boolean handle id from `n` on was ever defined (the session's counter is above them all). -/
def Fresh (c : Ctx) (n : Nat) : Prop := ∀ j, n ≤ j → j ∉ c.seenB

/-- The context after defining Boolean handle `n` with `i`. -/
def push (c : Ctx) (n : Nat) (i : BoolInfo) : Ctx :=
  { c with bools := (n, i) :: c.bools, seenB := n :: c.seenB }

theorem Fresh.push {c : Ctx} {n : Nat} (hf : Fresh c n) (j : Nat) (hj : n ≤ j) (i : BoolInfo) :
    Fresh (Contacts.push c j i) (j + 1) := by
  intro m hm hmem
  simp only [Contacts.push, List.mem_cons] at hmem
  rcases hmem with h | h
  · omega
  · exact hf m (by omega) h

theorem Fresh.drop {c : Ctx} {n : Nat} (hf : Fresh c n) (id : Nat) : Fresh (c.dropBool id) n := hf

theorem Fresh.mono {c : Ctx} {n m : Nat} (hf : Fresh c n) (h : n ≤ m) : Fresh c m :=
  fun j hj => hf j (by omega)

theorem bool?_push (c : Ctx) (n : Nat) (i : BoolInfo) (h : BoolH) :
    (push c n i).bool? h = if h.id = n then some i else c.bool? h := by
  simp only [push, Ctx.bool?, List.lookup_cons]
  by_cases e : h.id = n
  · simp [e]
  · have hb : (h.id == n) = false := by simpa using e
    simp [e, hb]

theorem bool?_push_self (c : Ctx) (n : Nat) (i : BoolInfo) : (push c n i).bool? ⟨n⟩ = some i := by
  simp [bool?_push]

theorem bool?_push_of_ne (c : Ctx) (n : Nat) (i : BoolInfo) (h : BoolH) (hne : h.id ≠ n) :
    (push c n i).bool? h = c.bool? h := by
  simp [bool?_push, hne]

theorem lookup_filter_ne (l : List (Nat × BoolInfo)) (id x : Nat) :
    (l.filter (fun e => e.1 != id)).lookup x = if x = id then none else l.lookup x := by
  induction l with
  | nil => simp
  | cons e l ih =>
    obtain ⟨k, v⟩ := e
    by_cases hk : k = id
    · subst hk
      by_cases hx : x = k
      · subst hx; simp [ih]
      · have hb : (x == k) = false := by simpa using hx
        simp [List.lookup_cons, ih, hx, hb]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, hk, not_false_eq_true, if_true,
        List.lookup_cons]
      by_cases hx : x = k
      · subst hx; simp [hk]
      · have hb : (x == k) = false := by simpa using hx
        simp [ih, hb]

theorem bool?_drop (c : Ctx) (id : Nat) (h : BoolH) :
    (c.dropBool id).bool? h = if h.id = id then none else c.bool? h := by
  simp only [Ctx.dropBool, Ctx.bool?, lookup_filter_ne]

theorem bool?_drop_of_ne (c : Ctx) (id : Nat) (h : BoolH) (hne : h.id ≠ id) :
    (c.dropBool id).bool? h = c.bool? h := by
  simp [bool?_drop, hne]

theorem useBool_keep {c : Ctx} {h : BoolH} {i : BoolInfo} (hb : c.bool? h = some i) (ho : i.once = false) :
    c.useBool h = some (i, c) := by
  simp [Ctx.useBool, hb, ho]

theorem useBool_once {c : Ctx} {h : BoolH} {i : BoolInfo} (hb : c.bool? h = some i) (ho : i.once = true) :
    c.useBool h = some (i, c.dropBool h.id) := by
  simp [Ctx.useBool, hb, ho]

theorem useBools_cons {c c' c'' : Ctx} {h : BoolH} {hs : List BoolH} {i : BoolInfo} {is : List BoolInfo}
    (h1 : c.useBool h = some (i, c')) (h2 : c'.useBools hs = some (is, c'')) :
    c.useBools (h :: hs) = some (i :: is, c'') := by
  simp [Ctx.useBools, h1, h2]

theorem useBools_nil (c : Ctx) : c.useBools [] = some ([], c) := rfl

theorem check_boolPublic (sigs : Bytes → Option Sig) {c : Ctx} {n : Nat} (hf : Fresh c n) (bits : Bits)
    (hw : bits.length ≤ maxWidth) :
    check sigs c (.boolPublic ⟨n⟩ bits) = some (push c n ⟨List.replicate bits.length .pub, false⟩, .unit) := by
  simp [check, Ctx.defBool, hf n (Nat.le_refl n), push, Nat.not_lt.mpr hw]

theorem check_boolInputBoth (sigs : Bytes → Option Sig) {c : Ctx} {n : Nat} (hf : Fresh c n) (w : Nat)
    (once rev : Bool) (hw : w ≤ maxWidth) :
    check sigs c (.boolInputBoth ⟨n⟩ ⟨n + 1⟩ w once rev ()) =
      some (push (push c n ⟨List.replicate w (Mark.ofInput rev), once⟩) (n + 1) ⟨List.replicate w (Mark.ofInput rev), once⟩,
        .unit) := by
  have h0 := hf n (Nat.le_refl n)
  have h1 := hf (n + 1) (by omega)
  simp [check, guard, Ctx.defBool, h0, h1, push, hw, Nat.not_lt.mpr hw]

theorem check_concat (sigs : Bytes → Option Sig) {c c' : Ctx} {n : Nat} {parts : List BoolH} {is : List BoolInfo}
    (hu : c.useBools parts = some (is, c')) (hf : Fresh c' n) (hw : ((is.map (·.marks)).flatten).length ≤ maxWidth) :
    check sigs c (.concat ⟨n⟩ parts) =
      some (push c' n ⟨(is.map (·.marks)).flatten, is.any (·.once)⟩, .unit) := by
  simp [check, hu, Ctx.defBool, hf n (Nat.le_refl n), push]
  split
  · next h => exact absurd h (by simpa using hw)
  · rfl

theorem check_run (sigs : Bytes → Option Sig) {c c' : Ctx} {n copies : Nat} {name : Bytes} {input : BoolH}
    {i : BoolInfo} {s : Sig} (hs : sigs name = some s) (hc : 0 < copies) (hu : c.useBool input = some (i, c'))
    (hl : i.marks.length = copies * s.inWidth) (hf : Fresh c' n) (hcw : copies ≤ maxWidth)
    (hw : copies * s.outMarks.length ≤ maxWidth) :
    check sigs c (.run ⟨n⟩ name copies input) =
      some (push c' n ⟨(List.replicate copies s.outMarks).flatten, false⟩, .unit) := by
  simp [check, hs, hc, hcw, hu, hl, guard, Ctx.defBool, hf n (Nat.le_refl n), push, hw, Nat.not_lt.mpr hw]

theorem check_slice (sigs : Bytes → Option Sig) {c c' : Ctx} {n lo hi : Nat} {h : BoolH} {i : BoolInfo}
    (hu : c.useBool h = some (i, c')) (hb : lo ≤ hi ∧ hi ≤ i.marks.length) (hf : Fresh c' n)
    (hw : hi - lo ≤ maxWidth) :
    check sigs c (.slice ⟨n⟩ h lo hi) =
      some (push c' n ⟨(i.marks.drop lo).take (hi - lo), i.once⟩, .unit) := by
  simp [check, hu, hb, guard, Ctx.defBool, hf n (Nat.le_refl n), push]
  split
  · next h => exact absurd h (by omega)
  · rfl

theorem check_openBool (sigs : Bytes → Option Sig) {c c' : Ctx} {h : BoolH} {l : Label} {i : BoolInfo}
    (hl : l.code ≠ 0) (hu : c.useBool h = some (i, c')) (ho : i.marks.all Mark.openable = true) :
    check sigs c (.openBool h l) = some (c', .bits i.marks.length) := by
  simp only [List.all_eq_true] at ho
  simp only [check, hl, hu, guard, ne_eq, not_false_eq_true, if_true, Option.bind_eq_bind, Option.bind_some,
    List.all_eq_true, if_pos ho, Option.pure_def]

theorem check_freeBool (sigs : Bytes → Option Sig) {c : Ctx} {h : BoolH} {i : BoolInfo}
    (hb : c.bool? h = some i) : check sigs c (.freeBool h) = some (c.dropBool h.id, .unit) := by
  simp [check, hb]

theorem check_freeBool' (sigs : Bytes → Option Sig) {c : Ctx} {h : BoolH}
    (hb : (c.bool? h).isSome = true) : check sigs c (.freeBool h) = some (c.dropBool h.id, .unit) := by
  cases e : c.bool? h with
  | none => rw [e] at hb; cases hb
  | some i => exact check_freeBool sigs e

/-- A block of unit-reply instructions through the shell's `check`. -/
def checkAll (sigs : Bytes → Option Sig) : Ctx → List Instr → Option Ctx
  | c, [] => some c
  | c, i :: is =>
    match check sigs c i.skel with
    | some (c', .unit) => checkAll sigs c' is
    | _ => none

theorem WF_seq {α : Type} (sigs : Bytes → Option Sig) (c c' : Ctx) (i : Instr) (s : Script α)
    (h : check sigs c i.skel = some (c', .unit)) (hs : WF sigs c' s) : WF sigs c (seq i s) :=
  WF.step c c' .unit i _ h (fun r hr => by
    cases r with
    | unit => exact hs
    | _ => exact absurd hr (by simp [Shape.Fits]))

theorem WF_seqs {α : Type} (sigs : Bytes → Option Sig) (s : Script α) :
    ∀ (is : List Instr) (c : Ctx),
      (match checkAll sigs c is with
       | some c' => WF sigs c' s
       | none => False) → WF sigs c (seqs is s)
  | [], c, h => h
  | i :: is, c, h => by
    simp only [checkAll] at h
    cases hc : check sigs c i.skel with
    | none => rw [hc] at h; simp at h
    | some p =>
      obtain ⟨c', sh⟩ := p
      cases sh with
      | unit => rw [hc] at h; exact WF_seq sigs c c' i _ hc (WF_seqs sigs s is c' h)
      | _ => rw [hc] at h; simp at h

theorem WF_openThen {α : Type} (sigs : Bytes → Option Sig) (c : Ctx) (h : BoolH) (l : Label) (k : Bits → Script α)
    (hw : match check sigs c (.openBool h l) with
      | some (c', .bits m) => ∀ b : Bits, b.length = m → WF sigs c' (k b)
      | _ => False) : WF sigs c (openThen h l k) := by
  split at hw
  · next c' m hc =>
    refine WF.step c c' (.bits m) _ _ hc (fun r hr => ?_)
    cases r with
    | bits b => exact hw b hr
    | _ => exact absurd hr (by simp [Shape.Fits])
  · exact hw.elim

/-! ### Well-formedness with a postcondition (`WFP`, Engine.lean) -/

theorem Fresh.of_seenB {c c' : Ctx} {n : Nat} (hf : Fresh c n) (h : c'.seenB = c.seenB) : Fresh c' n := by
  intro j hj hm
  rw [h] at hm
  exact hf j hj hm

/-- `Fresh` is the Boolean half of the session counters being ahead of the context. -/
theorem fresh_of_ahead {n : Counters} {c : Ctx} (h : n.Ahead c) : Fresh c n.bool := h.1

theorem WFP_seq {α : Type} (sigs : Bytes → Option Sig) {Q : Ctx → α → Prop} (c c' : Ctx) (i : Instr) (s : Script α)
    (h : check sigs c i.skel = some (c', .unit)) (hs : WFP sigs Q c' s) : WFP sigs Q c (seq i s) :=
  WFP.step c c' .unit i _ h (fun r hr => by
    cases r with
    | unit => exact hs
    | _ => exact absurd hr (by simp [Shape.Fits]))

theorem WFP_openThen {α : Type} (sigs : Bytes → Option Sig) {Q : Ctx → α → Prop} (c c' : Ctx) (h : BoolH)
    (l : Label) (k : Bits → Script α) (m : Nat) (hc : check sigs c (.openBool h l) = some (c', .bits m))
    (hk : ∀ b : Bits, b.length = m → WFP sigs Q c' (k b)) : WFP sigs Q c (openThen h l k) :=
  WFP.step c c' (.bits m) _ _ hc (fun r hr => by
    cases r with
    | bits b => exact hk b hr
    | _ => exact absurd hr (by simp [Shape.Fits]))

/-- **Freeing live, distinct handles**, then `s`: well formed when `s` is, from every context in
which exactly those handles were dropped (and no id was defined). -/
theorem frees_wfp {α : Type} (sigs : Bytes → Option Sig) {Q : Ctx → α → Prop} (s : Script α) :
    ∀ (hs : List BoolH) (c : Ctx), (hs.map (·.id)).Nodup → (∀ h ∈ hs, (c.bool? h).isSome = true) →
      (∀ c' : Ctx, (∀ g : BoolH, c'.bool? g = if g.id ∈ hs.map (·.id) then none else c.bool? g) →
        c'.seenB = c.seenB → WFP sigs Q c' s) →
      WFP sigs Q c (seqs (frees hs) s)
  | [], c, _, _, hk => hk c (fun g => by simp) rfl
  | h :: hs, c, hn, hl, hk => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    refine WFP_seq sigs c _ _ _ (check_freeBool' sigs (hl h (by simp))) ?_
    refine frees_wfp sigs s hs _ hn.2 (fun g hg => ?_) (fun c' h1 h2 => hk c' (fun g => ?_) h2)
    · have hne : g.id ≠ h.id := fun e => hn.1 ⟨g, hg, e⟩
      rw [bool?_drop_of_ne _ _ _ hne]
      exact hl g (by simp [hg])
    · rw [h1 g, bool?_drop]
      by_cases e : g.id = h.id
      · simp [e]
      · by_cases m : g.id ∈ hs.map (·.id)
        · simp [m]
        · simp only [m, if_false, e, List.map_cons, List.mem_cons, false_or]

end TlsMpc.Node.Flows.Contacts
