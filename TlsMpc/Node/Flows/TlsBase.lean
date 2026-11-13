import TlsMpc.Node.Flows.ContactsBase
import TlsMpc.Node.Local.Ghash

/-!
# GHASH shares and TLS flows: shared definitions and generic lemmas

REORGANIZATION_PLAN.md stage S12. Advance work in a new file; nothing here edits the engine
framework. No I/O; no emitter imports this module.

  * Kernels as model circuits, generically: `markOf` (an output's open mark: `opened` → public,
    audience 1 → to A, 2 → to B, else never; `kernel.h:25`), `kernelMarks`, `kernelInBytes`,
    `circuitOf K` (the circuit computing the Lean kernel `K` on its byte inputs,
    `ContactsBase.kernelCircuit`). An environment's circuit under a kernel's name being `circuitOf`
    of the kernel is the trusted correspondence of T2 (the pinned flat file computes the Lean
    kernel), as `Contacts.Loaded` states it for the contact kernels.
  * Kernel cache names (`cache.get(...)` arguments of `tls_kernels.h`): `name0`, `name1`, `name3`.
  * Shares as wire bits: `bitsOfW` / `wOfBits` (16 bytes, `Gcm.concrete.unpack` / `pack`, each byte
    least significant bit first as `kernel.h` `byte_bits`).
  * The shell's `check` on the instructions the TLS flows add to those of ContactsBase.lean:
    `check_boolInput`, `check_openBoolTo`, `check_pick`.
  * Releases to one party only: `idealStep_toD` (what the other party receives from one agreed
    instruction is exactly what its `releasesTo` says) and `viewD_nil_of_toMe`: a script none of
    whose instructions releases to the other party (`ToMe`) leaves the adversary's view EMPTY,
    whatever the adversary does (the GHASH resharing for an honest B: everything is opened to B).
-/

namespace TlsMpc.Node.Flows.TlsBase

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts

abbrev W := BitVec 128

/-! ## Kernels as model circuits -/

/-- The open mark of a kernel output (`kernel.h:25`: 0/1/2/3 never/public/toA/toB). -/
def markOf (o : HybridKernel.Output) : Mark :=
  if o.opened then .pub else if o.audience = 1 then .toA else if o.audience = 2 then .toB else .never

/-- The output marks of one copy of a kernel: its output fields' marks, bit by bit, in order. -/
def kernelMarks (K : HybridKernel.Kernel) : List Mark :=
  K.outputs.flatMap fun o => List.replicate o.bits (markOf o)

/-- The input width of a kernel in bytes (every input `.bytes`; a `.word` input counts one). -/
def kernelInBytes (K : HybridKernel.Kernel) : Nat := (K.inputs.map fun p => p.2.variables).sum

/-- **The model circuit of a kernel**: inputs its byte fields concatenated, outputs its output
fields concatenated (`kernel.h` `Kernel::run`), marks from the kernel's declared fields. -/
def circuitOf (K : HybridKernel.Kernel) : Engine.Circuit :=
  kernelCircuit K (kernelInBytes K) (kernelMarks K)

/-- A kernel name without parameters. -/
def name0 (s : String) : Bytes := ascii s
/-- A kernel name with one public shape parameter (`"tls-open-handshake " + size`). -/
def name1 (s : String) (a : Nat) : Bytes := ascii (s ++ " " ++ toString a)
/-- A kernel name with three (`"tls-seal-ctr " + kind + " " + size + " " + padding`). -/
def name3 (s : String) (a b c : Nat) : Bytes :=
  ascii (s ++ " " ++ toString a ++ " " ++ toString b ++ " " ++ toString c)

/-! ## Shares as wire bits -/

/-- A share as the 128 wire bits of its 16 bytes. -/
def bitsOfW (w : W) : Bits := bitsOf (Local.Ghash.toBytes w)

/-- 128 wire bits as a share. -/
def wOfBits (b : Bits) : W := Local.Ghash.ofBytes (bytesOf b)

theorem wOfBits_bitsOfW (w : W) : wOfBits (bitsOfW w) = w := by
  simp [wOfBits, bitsOfW, Local.Ghash.ofBytes_toBytes]

theorem length_bitsOfW (w : W) : (bitsOfW w).length = 128 := by
  simp [bitsOfW, Local.Ghash.toBytes_length]

/-- Several shares, concatenated. -/
def bitsOfWs (ws : List W) : Bits := ws.flatMap bitsOfW

/-- `128 · k` wire bits as `k` shares. -/
def wsOfBits : Nat → Bits → List W
  | 0, _ => []
  | k + 1, b => wOfBits (b.take 128) :: wsOfBits k (b.drop 128)

theorem length_bitsOfWs (ws : List W) : (bitsOfWs ws).length = 128 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [bitsOfWs, List.flatMap_cons, List.length_append, length_bitsOfW, List.length_cons] at ih ⊢
    rw [ih]
    omega

theorem wsOfBits_bitsOfWs (ws : List W) : wsOfBits ws.length (bitsOfWs ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.length_cons, wsOfBits, bitsOfWs, List.flatMap_cons]
    rw [List.take_left' (length_bitsOfW w), List.drop_left' (length_bitsOfW w), wOfBits_bitsOfW]
    exact congrArg _ ih

/-! ## The shell's `check` on the further instructions -/

theorem check_boolInput (sigs : Bytes → Option Sig) {c : Ctx} {n : Nat} (hf : Fresh c n) (owner : Party)
    (w : Nat) (once rev : Bool) (hw : w ≤ maxWidth) :
    check sigs c (.boolInput ⟨n⟩ owner w once rev ()) =
      some (push c n ⟨List.replicate w (Mark.ofInput rev), once⟩, .unit) := by
  simp [check, guard, Ctx.defBool, hf n (Nat.le_refl n), push, hw, Nat.not_lt.mpr hw]

theorem check_openBoolTo (sigs : Bytes → Option Sig) {c c' : Ctx} {h : BoolH} {r : Party} {l : Label}
    {i : BoolInfo} (hl : l.code ≠ 0) (hu : c.useBool h = some (i, c'))
    (ho : i.marks.all (· == Mark.to r) = true) :
    check sigs c (.openBoolTo h r l ()) = some (c', .unit) := by
  simp only [List.all_eq_true] at ho
  simp only [check, hl, hu, guard, ne_eq, not_false_eq_true, if_true, Option.bind_eq_bind, Option.bind_some,
    List.all_eq_true, if_pos ho, Option.pure_def]

theorem check_pick (sigs : Bytes → Option Sig) {c c' : Ctx} {n : Nat} {h : BoolH} {idx : List Nat} {i : BoolInfo}
    (hu : c.useBool h = some (i, c')) (hb : idx.all (· < i.marks.length) = true) (hf : Fresh c' n)
    (hw : idx.length ≤ maxWidth) :
    check sigs c (.pick ⟨n⟩ h idx) =
      some (push c' n ⟨idx.map (fun j => i.marks.getD j .never), i.once⟩, .unit) := by
  simp only [List.all_eq_true] at hb
  simp only [check, hu, guard, Option.bind_eq_bind, Option.bind_some, List.all_eq_true, if_pos hb,
    Ctx.defBool, hf n (Nat.le_refl n), List.length_map, Nat.not_lt.mpr hw, or_self, if_false,
    Option.pure_def, push]

/-! ## Releases to one party only -/

theorem party_b_of_ne_a (r : Party) (h : ¬r = .a) : r = .b := by cases r <;> simp_all
theorem party_a_of_ne_b (r : Party) (h : ¬r = .b) : r = .a := by cases r <;> simp_all

/-- What the other party receives from one agreed instruction: something exactly when the
instruction releases to it. -/
theorem idealStep_toD (E : Env) (me : Party) (w : Wire) (p : PeerPart) (I I' : Ideal)
    (toH toD : Option Release) (h : idealStep E me w p I = some (I', toH, toD)) :
    toD.isSome = w.releasesTo me.other := by
  cases w <;> simp only [idealStep] at h <;>
    (repeat' first
      | (split at h)
      | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h)) <;>
    (try obtain ⟨_, rfl, rfl⟩ := h) <;>
    (try simp_all [InstrP.releasesTo]) <;>
    (cases me <;> simp_all [Party.other, party_b_of_ne_a, party_a_of_ne_b])

/-- No instruction of the script releases to the other party (`openBoolTo` to this party, or no
release at all). -/
def ToMe (me : Party) (i : Instr) : Prop := i.releasesTo me.other = false

theorem early_none_of_toMe (me : Party) (w : Wire) (h : w.releasesTo me.other = false) : w.early = none := by
  cases w <;> simp_all [Wire.early, InstrP.releasesTo]

/-- **A script that releases only to the honest party leaves the adversary's view empty**, against
any adversary, from any store and engine state. -/
theorem viewD_nil_of_toMe (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (hs : Every (ToMe me) s) : ∀ (σ : Store) (I : Ideal) (vD : List Release),
      (withAdv E me adv s σ I vD).viewD = [] := by
  induction hs with
  | done a => intro σ I vD; rfl
  | abort r => intro σ I vD; rfl
  | step i k hi _ ih =>
    intro σ I vD
    simp only [withAdv]
    split
    · rfl
    · next w hw =>
      have hrel : w.releasesTo me.other = false := by
        rw [← InstrP.releasesTo_skel, fill_skel E.hash me σ i w hw, InstrP.releasesTo_skel]
        exact hi
      have he := early_none_of_toMe me w hrel
      split
      · simp [he]
      · split
        · simp [he]
        · next I' toH toD hst =>
          have hd := idealStep_toD E me w _ I I' toH toD hst
          rw [hrel] at hd
          cases toD with
          | some r => cases hd
          | none => simp only [Option.toList_none, List.nil_append]; exact ih _ _ _ _

theorem runCopies_one' (c : Engine.Circuit) (v : Bits) (h : v.length = c.inWidth) : runCopies c 1 v = c.eval v := by
  simp [runCopies, List.take_of_length_le, h]

/-- **An own private input releases nothing**: the honest owner's bits go in, whatever the
adversary does (it may only abort). -/
theorem viewD_seq_boolInput (E : Env) (me : Party) (adv : Adversary) {α : Type} (n w slot : Nat) (once rev : Bool)
    (s : Script α) (σ : Store) (I : Ideal) (vD L : List Release) (hw : (σ.bits slot).length = w)
    (hk : (withAdv E me adv s σ (I.setBool ⟨n⟩ (σ.bits slot)) vD).viewD <+: L) :
    (withAdv E me adv (seq (.boolInput ⟨n⟩ me w once rev slot) s) σ I vD).viewD <+: L := by
  simp only [seq, withAdv, fill, if_true, hw, Wire.early, Option.toList_none, List.append_nil]
  split
  · exact List.nil_prefix
  · simp only [idealStep, if_true, hw, absorb, Option.toList_none, List.nil_append, List.append_nil]
    exact hk

/-- **An opening to the other party releases the handle's value to it, with its label.** -/
theorem viewD_seq_openBoolTo (E : Env) (me : Party) (adv : Adversary) {α : Type} (h : BoolH) (l : Label) (d : Nat)
    (s : Script α) (σ : Store) (I : Ideal) (vD L : List Release) (v : Bits) (hv : I.bools h.id = some v)
    (hk : (withAdv E me adv s σ I (vD ++ [⟨l, .bits v⟩])).viewD <+: L) :
    (withAdv E me adv (seq (.openBoolTo h me.other l d) s) σ I vD).viewD <+: ⟨l, .bits v⟩ :: L := by
  simp only [seq, withAdv, fill, InstrP.map, Wire.early, Option.toList_none, List.append_nil]
  split
  · exact List.nil_prefix
  · simp only [idealStep, hv, Party.other_ne, if_false, absorb, Option.toList_none, Option.toList_some,
      List.nil_append, List.cons_append]
    exact List.cons_prefix_cons.mpr ⟨rfl, hk⟩

theorem every_seq_seqs {α : Type} {P : Instr → Prop} {s : Script α} (hs : Every P s) (is : List Instr)
    (h : ∀ i ∈ is, P i) : Every P (seqs is s) := every_seqs hs is h

end TlsMpc.Node.Flows.TlsBase
