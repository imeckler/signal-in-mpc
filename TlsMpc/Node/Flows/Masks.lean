import TlsMpc.Node.Flows.Challenge
import TlsMpc.Node.Flows.ConvertBase
import TlsMpc.Node.Flows.RunLemmas

/-!
# `Masks.generate`: conversion masks by cut-and-choose (P-CUT)

REORGANIZATION_PLAN.md 7.1 P-CUT, stage S10. Replaces `dyn_word_mask.h` `generate_masks`
(malicious, lines 47-120) for the Lean conversions; the legacy library keeps its own pool until its
callers move (S11–S16): **masks of the two implementations come from separate pools** (a Lean mask
is a handle in the Rust handle table, made by this script; a legacy mask is a `DynMask` inside
`legacy_dispatch`; neither can name the other's).

THE SCRIPT (both parties run it; `p : Params` public; M = 2·B·N candidates per party, K = B·N cut,
D = 2·N·(B − 1) bucket pairs, W = 255):
  1. `inputs`: each party's M candidates, drawn before the script (canonical random values, as the
     C++ draws them), go into BOTH engines: `boolInputBoth` (M·W bits each, marked revealable: they
     are cut-and-choose candidates, plan 5.4), concatenated A ‖ B; `fieldInput` (M elements each,
     revealable).
  2. `Random.challenge` (P-CHAL) gives π₁, a permutation of [0, M); its first K entries are cut.
  3. `cutPhase`: open the cut candidates in both engines (field first, then Boolean, as the C++);
     continue iff every opened Boolean word is canonical and equals the opened field element
     (`cutCheck`).
  4. `Random.challenge` gives π₂, a permutation of [0, K): bucket j is entries B·j … B·j + B − 1
     of π₂, mapped through the remaining candidates π₁[K ..]; member 0 is the reference.
  5. `bucketPhase`: per owner, bucket and member k ≥ 1, the Boolean `modAdd(ref, k)` (D copies of
     `modadd-open`) and the field sum; open both; continue iff equal (`bucketCheck`).
  6. `finalPhase`: the kept references' pairs (A's, B's): the first `bits` through `finalize-bits`,
     the rest through `finalize-mask`; open the flag of each; continue iff all set.
  7. `maskBlock`: word masks: the 255 bits of each `finalize-mask` copy (a slice) and the field sum
     of the two references.
  8. `bitPhase` (only when `bits > 0`): each party inputs its references' bits as field coins;
     `field-recompose` and `field-bit-check` on them, opened, all zero; `field-bit-xor` of the two
     parties' coins: the bit pairs.
  The pool: the word masks and the bit pairs, all handles of fresh blocks.

PARAMETERS. `profile N bits` gives the deployed bucket size B for N (`word_bucket_for`:
16 → 22, 64 → 17, 256 → 14, 1024 → 12; the S128 receipts of `parameters.py`); the worker uses
N = 16 (`TlsKernels::prepare`, `take_mask`). `testParams` (N = 2, B = 2) is for the test vectors
ONLY (a `Config.test` deviation: far below the statistical target).

PROVED HERE (pure protocol layer; the run-level statements are in the phase sections below):
  see the summary at the end of the file and the S10 entries of `TlsMpc/Security.lean`.
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent every_seq every_seqs every_openThen labelIn_of_none)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)

/-- Bits per word. -/
abbrev W : Nat := 255

/-! ## Parameters -/

structure Params where
  N : Nat
  B : Nat
  /-- How many kept references become bit blocks (255 bit pairs each). -/
  bits : Nat
  deriving DecidableEq, Repr

namespace Params
def K (p : Params) : Nat := p.B * p.N
def M (p : Params) : Nat := 2 * p.K
def D (p : Params) : Nat := 2 * (p.N * (p.B - 1))
def words (p : Params) : Nat := p.N - p.bits
end Params

/-- The deployed bucket sizes (`dyn_word_mask.h` `word_bucket_for`; `parameters.choose(N, 128)`,
`check_parameters_128.py`). -/
def bucketFor : Nat → Option Nat
  | 16 => some 22
  | 64 => some 17
  | 256 => some 14
  | 1024 => some 12
  | _ => none

/-- **The deployed profiles**: N kept references, the deployed bucket size, `bits ≤ N`. -/
def profile (N bits : Nat) : Option Params :=
  match bucketFor N with
  | some B => if bits ≤ N then some ⟨N, B, bits⟩ else none
  | none => none

/-- The worker's profile (`TlsKernels::prepare` / `take_mask`: N = 16, so B = 22). -/
theorem profile_worker : profile 16 0 = some ⟨16, 22, 0⟩ := rfl

/-- TEST ONLY (`Config.test`; the stand-in vectors): N = 2, B = 2. Not a deployed profile. -/
def testParams (bits : Nat) : Params := ⟨2, 2, bits⟩

/-- The challenge domains (fixed per call: plan R18). -/
def domain (p : Params) (phase : String) : Bytes :=
  ascii ("WORDMASK-lean-v1:p25519:n" ++ toString p.N ++ ":bits" ++ toString p.bits ++ ":B" ++
    toString p.B ++ ":C2:S128:" ++ phase)

/-! ## This party's store slots -/

structure Slots where
  /-- The M candidates' bits, M·255 (candidate j at j·255 …). -/
  bits : Nat
  /-- The M candidates as field elements. -/
  elems : Nat
  /-- `coins + j`: candidate j's 255 bits as field coins (0 or 1). -/
  coins : Nat
  cutNonce : Nat
  cutValue : Nat
  bucketNonce : Nat
  bucketValue : Nat

/-! ## The handle layout (Boolean ids from `b`, field ids from `f`) -/

section Layout

variable (p : Params) (f : Nat)

/-- Owner `o`'s (0: A, 1: B) candidate `c`, field side. -/
def fOf (o c : Nat) : FieldH := ⟨f + o * p.M + c⟩
/-- The position of bit `i` of owner `o`'s candidate `c` in the concatenation A ‖ B. -/
def bitAt (o c i : Nat) : Nat := o * (p.M * W) + c * W + i
def wordAt (o c : Nat) : List Nat := (List.range W).map (bitAt p o c)

def owners : List Nat := [0, 1]

/-- The cut (the first K entries of π₁) and the remaining candidates. -/
def cutOf (π₁ : List Nat) : List Nat := π₁.take p.K
def remainOf (π₁ : List Nat) : List Nat := π₁.drop p.K

/-- Member `k` of bucket `j` (a candidate index): `remain[π₂[B·j + k]]`. -/
def member (π₁ π₂ : List Nat) (j k : Nat) : Nat := (remainOf p π₁).getD (π₂.getD (p.B * j + k) 0) 0

/-- The bucket pairs (owner, bucket, member ≥ 1), in the C++ order. -/
def pairs : List (Nat × Nat × Nat) :=
  owners.flatMap fun o => (List.range p.N).flatMap fun j => (List.range (p.B - 1)).map fun k => (o, j, k + 1)

def cutBits (π₁ : List Nat) : List Nat := owners.flatMap fun o => (cutOf p π₁).flatMap (wordAt p o)
def cutFields (π₁ : List Nat) : List FieldH := owners.flatMap fun o => (cutOf p π₁).map (fOf p f o)

def bucketBits (π₁ π₂ : List Nat) : List Nat :=
  (pairs p).flatMap fun e => wordAt p e.1 (member p π₁ π₂ e.2.1 0) ++ wordAt p e.1 (member p π₁ π₂ e.2.1 e.2.2)

/-- The sum handles. -/
def sumH (q : Nat) : FieldH := ⟨f + 2 * p.M + q⟩

def sumAdds (π₁ π₂ : List Nat) : List Instr :=
  ((pairs p).zipIdx).map fun e =>
    .fieldAdd (sumH p f e.2) (fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 0)) (fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2))

def sums : List FieldH := ((pairs p).zipIdx).map fun e => sumH p f e.2

/-- The reference pair of kept reference `j` (A's word, then B's). -/
def refPair (π₁ π₂ : List Nat) (j : Nat) : List Nat :=
  wordAt p 0 (member p π₁ π₂ j 0) ++ wordAt p 1 (member p π₁ π₂ j 0)

/-- The first word-mask field handle. -/
def maskBase : Nat := f + 2 * p.M + p.D
/-- The first bit-block coin handle. -/
def coinBase : Nat := maskBase p f + p.words
def coinH (o j i : Nat) : FieldH := ⟨coinBase p f + o * (p.bits * W) + j * W + i⟩
def recH (o j : Nat) : FieldH := ⟨coinBase p f + 2 * (p.bits * W) + o * p.bits + j⟩
def chkH (q : Nat) : FieldH := ⟨coinBase p f + 2 * (p.bits * W) + 2 * p.bits + q⟩
def xorH (q : Nat) : FieldH := ⟨coinBase p f + 4 * (p.bits * W) + 2 * p.bits + q⟩

/-- How many field ids a generation takes (from `f`). -/
def fieldIds : Nat := 2 * p.M + p.D + p.words + 5 * (p.bits * W) + 2 * p.bits

end Layout

/-- How many Boolean ids a generation takes (from `b`). -/
def boolIds (p : Params) : Nat := 12 + p.words

/-! ## The script -/

section Script

variable (p : Params) (b f : Nat)

/-- Step 1: the candidates into both engines. -/
def inputBlock (s : Slots) : List Instr :=
  [.boolInputBoth ⟨b⟩ ⟨b + 1⟩ (p.M * W) false true s.bits,
   .concat ⟨b + 2⟩ [⟨b⟩, ⟨b + 1⟩],
   .fieldInput ((List.range p.M).map (fOf p f 0)) ((List.range p.M).map (fOf p f 1)) .elements true s.elems]

/-- The words of a flat bit list, `w` at a time (`n` of them). -/
def chunksN (w : Nat) : Nat → Bits → List Bits
  | 0, _ => []
  | n + 1, l => l.take w :: chunksN w n (l.drop w)

def chunks (w : Nat) (l : Bits) : List Bits := chunksN w (l.length / w) l

/-- The cut check on the replies: every opened word canonical and equal to the opened element. -/
def wordsMatch (canon : Bool) (ws : List Bits) (es : List F) : Bool :=
  ws.length == es.length &&
    (ws.zip es).all fun e => (!canon || decide (natOf e.1 < P)) && natOf e.1 == e.2.val

def cutCheck (vb : Bits) (ve : List F) : Bool := wordsMatch true (chunks W vb) ve
def bucketCheck (vb : Bits) (ve : List F) : Bool := wordsMatch false (chunks W vb) ve

/-- Step 3. -/
def cutPhase (π₁ : List Nat) : Script Unit :=
  seq (.pick ⟨b + 3⟩ ⟨b + 2⟩ (cutBits p π₁)) <|
  openFieldThen (cutFields p f π₁) Label.cutCandidates fun ve =>
  openThen ⟨b + 3⟩ Label.cutCandidates fun vb =>
  if cutCheck vb ve then seqs [.freeBool ⟨b + 3⟩] (.done ()) else .abort "cross-domain candidate mismatch"

/-- Step 5's local block. -/
def bucketBlock (π₁ π₂ : List Nat) : List Instr :=
  [.pick ⟨b + 4⟩ ⟨b + 2⟩ (bucketBits p π₁ π₂), .run ⟨b + 5⟩ modaddOpenName p.D ⟨b + 4⟩] ++ sumAdds p f π₁ π₂

/-- Step 5. -/
def bucketPhase (π₁ π₂ : List Nat) : Script Unit :=
  seqs (bucketBlock p b f π₁ π₂) <|
  openFieldThen (sums p f) Label.bucketSums fun ve =>
  openThen ⟨b + 5⟩ Label.bucketSums fun vb =>
  if bucketCheck vb ve then seqs [.freeBool ⟨b + 4⟩, .freeBool ⟨b + 5⟩] (.done ())
  else .abort "cross-domain bucket mismatch"

/-- Step 6's local block: the reference pairs, the finalize circuits, the flags. -/
def finalBlock (π₁ π₂ : List Nat) : List Instr :=
  [.pick ⟨b + 6⟩ ⟨b + 2⟩ ((List.range p.bits).flatMap (refPair p π₁ π₂)),
   .pick ⟨b + 7⟩ ⟨b + 2⟩ ((List.range' p.bits p.words).flatMap (refPair p π₁ π₂))] ++
  (if p.bits = 0 then [] else [.run ⟨b + 8⟩ finalizeBitsName p.bits ⟨b + 6⟩]) ++
  (if p.words = 0 then [] else [.run ⟨b + 9⟩ finalizeMaskName p.words ⟨b + 7⟩]) ++
  [.concat ⟨b + 10⟩ ((if p.bits = 0 then [] else [⟨b + 8⟩]) ++ (if p.words = 0 then [] else [⟨b + 9⟩])),
   .pick ⟨b + 11⟩ ⟨b + 10⟩ ((List.range p.N).map fun j => 256 * j + 255)]

/-- Step 7: the word masks (slices of the finalized bundle, field sums of the references), and the
handles no longer needed freed. -/
def maskBlock (π₁ π₂ : List Nat) : List Instr :=
  ((List.range p.words).map fun j =>
    (.slice ⟨b + 12 + j⟩ ⟨b + 10⟩ (256 * (p.bits + j)) (256 * (p.bits + j) + W) : Instr)) ++
  ((List.range p.words).map fun j =>
    (.fieldAdd ⟨maskBase p f + j⟩ (fOf p f 0 (member p π₁ π₂ (p.bits + j) 0))
      (fOf p f 1 (member p π₁ π₂ (p.bits + j) 0)) : Instr)) ++
  frees ([⟨b⟩, ⟨b + 1⟩, ⟨b + 2⟩, ⟨b + 6⟩, ⟨b + 7⟩, ⟨b + 11⟩] ++
    (if p.bits = 0 then [] else [⟨b + 8⟩]) ++ (if p.words = 0 then [] else [⟨b + 9⟩]))

/-- The word masks the pool gets. -/
def maskList : List WordMask := (List.range p.words).map fun j => ⟨⟨b + 12 + j⟩, ⟨maskBase p f + j⟩⟩

/-- The bit pairs the pool gets: bit i of block j is bit 256·j + i of the finalized bundle. -/
def pairList : List BitPair :=
  (List.range p.bits).flatMap fun j => (List.range W).map fun i => ⟨⟨b + 10⟩, 256 * j + i, xorH p f (j * W + i)⟩

/-- Step 8's inputs: per bit block, each party's reference coins. -/
def coinInputs (s : Slots) (π₁ π₂ : List Nat) : List Instr :=
  (List.range p.bits).map fun j =>
    .fieldInput ((List.range W).map (coinH p f 0 j)) ((List.range W).map (coinH p f 1 j)) .coins false
      (s.coins + member p π₁ π₂ j 0)

/-- `field-recompose` instances: owner o, block j: its coins, then its reference's field value. -/
def recIns (π₁ π₂ : List Nat) : List FieldH :=
  owners.flatMap fun o => (List.range p.bits).flatMap fun j =>
    (List.range W).map (coinH p f o j) ++ [fOf p f o (member p π₁ π₂ j 0)]
def recOuts : List FieldH := owners.flatMap fun o => (List.range p.bits).map (recH p f o)
def allCoins : List FieldH :=
  owners.flatMap fun o => (List.range p.bits).flatMap fun j => (List.range W).map (coinH p f o j)
def chkOuts : List FieldH := (List.range (2 * (p.bits * W))).map (chkH p f)
def xorIns : List FieldH :=
  (List.range p.bits).flatMap fun j => (List.range W).flatMap fun i => [coinH p f 0 j i, coinH p f 1 j i]
def xorOuts : List FieldH := (List.range (p.bits * W)).map (xorH p f)

/-- Step 8 (when there are bit blocks). -/
def bitPhase (s : Slots) (π₁ π₂ : List Nat) : Script Unit :=
  if p.bits = 0 then .done () else
  seqs (coinInputs p f s π₁ π₂) <|
  seq (.program recomposeName (2 * p.bits) (recIns p f π₁ π₂) [] (recOuts p f) Label.bitBlockChecks) <|
  seq (.program bitCheckName (2 * (p.bits * W)) (allCoins p f) [] (chkOuts p f) Label.bitBlockChecks) <|
  openFieldThen (recOuts p f ++ chkOuts p f) Label.bitBlockChecks fun z =>
  if z.all (· == 0) then
    seq (.program bitXorName (p.bits * W) (xorIns p f) [] (xorOuts p f) Label.bitBlockChecks) (.done ())
  else .abort "bit block inconsistent with verified reference"

/-- Steps 6–8. -/
def finishPhase (s : Slots) (π₁ π₂ : List Nat) : Script MaskPool :=
  seqs (finalBlock p b π₁ π₂) <|
  openThen ⟨b + 11⟩ Label.referenceFlags fun fl =>
  if fl.all id then
    seqs (maskBlock p b f π₁ π₂) <|
    (bitPhase p f s π₁ π₂).bind fun _ => .done ⟨maskList p b f, pairList p b f⟩
  else .abort "kept reference out of range"

/-- **`Masks.generate`** (malicious mode): the pool of `p.words` word masks and `255·p.bits` bit
pairs, for party `me` with its candidates and randomness in the slots `s`; Boolean handles from
`b` (`boolIds p` of them), field handles from `f` (`fieldIds p` of them). -/
def generate (hash : Bytes → Bytes) (me : Party) (s : Slots) : Script MaskPool :=
  seqs (inputBlock p b f s) <|
  (Random.challenge hash me s.cutNonce s.cutValue (domain p "cut") p.M).bind fun π₁ =>
  (cutPhase p b f π₁).bind fun _ =>
  (Random.challenge hash me s.bucketNonce s.bucketValue (domain p "bucket") p.K).bind fun π₂ =>
  (bucketPhase p b f π₁ π₂).bind fun _ =>
  finishPhase p b f s π₁ π₂

end Script

/-! ## The reveal list: the kinds `generate` declares -/

/-- The kinds of `generate`: the challenges' commitments and openings, the cut candidates, the
bucket sums, the reference flags, the bit-block checks. -/
def generateKinds : List TlsMpc.Node.RevealKind :=
  [.commitment, .commitOpening, .cutCandidates, .bucketSums, .referenceFlags, .bitBlockChecks]

theorem labelIn_mem {k : TlsMpc.Node.RevealKind} (hk : k ∈ generateKinds) {i : Instr}
    (h : i.label? = some (Label.ofKind k)) : LabelIn generateKinds i := LabelIn.of_mem hk h

theorem local_reveals {α : Type} {s : Script α} (hs : Reveals generateKinds s) (is : List Instr)
    (h : ∀ i ∈ is, isLocal i = true) : Reveals generateKinds (seqs is s) :=
  every_seqs hs is (fun i hi => LabelIn.of_none (label_local i (h i hi)))

theorem mem_ite_nil {α : Type} {c : Prop} [Decidable c] {x : α} {l : List α}
    (h : x ∈ (if c then [] else l)) : x ∈ l := by
  split at h
  · cases h
  · exact h

theorem finalBlock_local (p : Params) (b : Nat) (π₁ π₂ : List Nat) :
    ∀ i ∈ finalBlock p b π₁ π₂, isLocal i = true := by
  intro i hi
  simp only [finalBlock, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((h | h) | h) | h
  · rcases h with rfl | rfl <;> rfl
  · have := mem_ite_nil h
    simp only [List.mem_singleton] at this
    subst this
    rfl
  · have := mem_ite_nil h
    simp only [List.mem_singleton] at this
    subst this
    rfl
  · rcases h with rfl | rfl <;> rfl

theorem maskBlock_local (p : Params) (b f : Nat) (π₁ π₂ : List Nat) :
    ∀ i ∈ maskBlock p b f π₁ π₂, isLocal i = true := by
  intro i hi
  simp only [maskBlock, frees, List.mem_append, List.mem_map] at hi
  rcases hi with (⟨j, -, rfl⟩ | ⟨j, -, rfl⟩) | ⟨g, -, rfl⟩ <;> rfl

theorem bucketBlock_local (p : Params) (b f : Nat) (π₁ π₂ : List Nat) :
    ∀ i ∈ bucketBlock p b f π₁ π₂, isLocal i = true := by
  intro i hi
  simp only [bucketBlock, sumAdds, List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hi
  rcases hi with rfl | rfl | ⟨e, -, rfl⟩ <;> rfl

theorem cutPhase_reveals (p : Params) (b f : Nat) (π₁ : List Nat) : Reveals generateKinds (cutPhase p b f π₁) := by
  unfold cutPhase
  refine every_seq (LabelIn.of_none rfl) (every_openFieldThen (labelIn_mem (by decide) rfl) fun ve =>
    every_openThen (labelIn_mem (by decide) rfl) fun vb => ?_)
  split
  · exact every_seqs (Every.done _) _ (fun i hi => by simp at hi; subst hi; exact LabelIn.of_none rfl)
  · exact Every.abort _

theorem bucketPhase_reveals (p : Params) (b f : Nat) (π₁ π₂ : List Nat) :
    Reveals generateKinds (bucketPhase p b f π₁ π₂) := by
  unfold bucketPhase
  refine local_reveals (every_openFieldThen (labelIn_mem (by decide) rfl) fun ve =>
    every_openThen (labelIn_mem (by decide) rfl) fun vb => ?_) _ (bucketBlock_local p b f π₁ π₂)
  split
  · exact every_seqs (Every.done _) _ (fun i hi => by
      simp at hi; rcases hi with rfl | rfl <;> exact LabelIn.of_none rfl)
  · exact Every.abort _

theorem bitPhase_reveals (p : Params) (f : Nat) (s : Slots) (π₁ π₂ : List Nat) :
    Reveals generateKinds (bitPhase p f s π₁ π₂) := by
  unfold bitPhase
  split
  · exact Every.done _
  · refine every_seqs (every_seq (labelIn_mem (by decide) rfl) (every_seq (labelIn_mem (by decide) rfl)
      (every_openFieldThen (labelIn_mem (by decide) rfl) fun z => ?_))) _ (fun i hi => ?_)
    · split
      · exact every_seq (labelIn_mem (by decide) rfl) (Every.done _)
      · exact Every.abort _
    · simp only [coinInputs, List.mem_map] at hi
      obtain ⟨j, -, rfl⟩ := hi
      exact LabelIn.of_none rfl

theorem finishPhase_reveals (p : Params) (b f : Nat) (s : Slots) (π₁ π₂ : List Nat) :
    Reveals generateKinds (finishPhase p b f s π₁ π₂) := by
  unfold finishPhase
  refine local_reveals (every_openThen (labelIn_mem (by decide) rfl) fun fl => ?_) _ (finalBlock_local p b π₁ π₂)
  split
  · exact local_reveals (Every.bind (bitPhase_reveals p f s π₁ π₂) (fun _ => Every.done _)) _
      (maskBlock_local p b f π₁ π₂)
  · exact Every.abort _

theorem challenge_reveals' (hash : Bytes → Bytes) (me : Party) (nonce value : Nat) (dom : Bytes) (n : Nat) :
    Reveals generateKinds (Random.challenge hash me nonce value dom n) :=
  (Random.challenge_reveals hash me nonce value dom n).mono (by decide)

/-- **`generate` declares `generateKinds`** (on every branch, for every argument). -/
theorem generate_reveals (p : Params) (b f : Nat) (hash : Bytes → Bytes) (me : Party) (s : Slots) :
    Reveals generateKinds (generate p b f hash me s) := by
  unfold generate
  refine every_seqs ?_ _ (fun i hi => ?_)
  · refine Every.bind (challenge_reveals' _ _ _ _ _ _) fun π₁ => Every.bind (cutPhase_reveals p b f π₁) fun _ =>
      Every.bind (challenge_reveals' _ _ _ _ _ _) fun π₂ => Every.bind (bucketPhase_reveals p b f π₁ π₂) fun _ =>
      finishPhase_reveals p b f s π₁ π₂
  · simp only [inputBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact LabelIn.of_none rfl

end TlsMpc.Node.Flows.Masks
