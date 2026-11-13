import TlsMpc.Node.Flows.SendDevices

/-!
# The send scripts through the model's runs (S13, F51, F57, F59)

REORGANIZATION_PLAN.md stage S13. New file; it changes no definition. No I/O; no emitter imports
this module.

PUBLIC SCRIPTS. Every instruction of `sealScript`, `requestScript` and `requestCtrScript` is plain
(public bits, plumbing, runs, frees) or an opening to both parties: no private input, no exchange.
`pubRun` runs such a script in the ideal model (the functionality's state, the releases, the
result), without parties or adversary. Then
  * `jointRun_pub`: two honest parties running it in lockstep (`Engine/Model.lean` `jointRun`) end
    with `pubRun`'s result, both of them (the same value twice), its ideal state, and both see
    exactly `pubRun`'s releases;
  * `withAdv_pub`: against ANY adversary, the adversary's (and the honest party's) view is a prefix
    of `pubRun`'s releases and a result, if any, is `pubRun`'s (the adversary can only stop the run).

OP 41 IN THE MODEL (`sealScript_run`, `afterWidths_run`): from the ideal values of the certificate,
the stored record, the sender key, the agreements, with the widths kernel and the seal kernels
loaded as their model circuits (`shapedCircuit`, T2), `pubRun` of `sealScript` releases exactly the
width flags, the status byte and (only when it is 255) timestamp ‖ envelope; returns the timestamp,
the envelope and the handle `n + 6`, which then holds the kept record; or (status not 255) returns
`none` with the stored state's value untouched.

F51 (`send_joint`): both honest parties run op 41, op 42 and the request's record seal (CTR phase,
then S12's `Tls.tagScript` with each party's half from its own store) and end with the same results:
the same new state (the advanced record, `send_accepted`), the same envelope, and the same record
for the server, which is `TlsRecord.sealCore` of the request frame carrying the reference envelope.
`seal_joint_refused`: on a refused status both return `none`, the stored state's value is kept, and
both saw only the flags and the status.

F57 (`seal_view`): against any adversary, the adversary's view of op 41 is a prefix of
[flags, status] when the status is not 255, of [flags, status, timestamp ‖ envelope] otherwise, with
the values characterised by the kernel theorems (`seal_accepted_value`: the envelope is `sealV1` of
the reference message).

F59 (ORD-1 at script level): `sealScript_state_order` (the only handle the accepted op 41 returns
as the new state is `n + 6`, defined by the seal kernel's run BEFORE any release of the envelope; the
old state is freed after), `request_reads_state` (op 42 reads only the state handle it is given and
the certificate: its value is certificate ‖ the first record of that handle's value), so the request
is built from the state op 41 produced.
-/

namespace TlsMpc.Node.Flows.Send

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.HybridKernel (Kernel lookup lookupFrom)

/-! ## Public scripts and their run -/

/-- An opening to both parties. -/
def openOf : Instr → Option (BoolH × Label)
  | .openBool h l => some (h, l)
  | _ => none

/-- A plain instruction or an opening to both parties. -/
def pubInstr (i : Instr) : Bool := plain i || (openOf i).isSome

theorem openOf_plain (i : Instr) (h : plain i = true) : openOf i = none := by
  cases i <;> simp_all [plain, openOf]

theorem pubInstr_cases (i : Instr) (h : pubInstr i = true) : plain i = true ∨ ∃ hh l, i = .openBool hh l := by
  cases i <;> simp_all [pubInstr, plain, openOf]

theorem pub_of_plain (i : Instr) (h : plain i = true) : pubInstr i = true := by
  simp [pubInstr, h]

/-- A public script in the ideal model: its result, the functionality's state, the releases (to
both parties). -/
def pubRun (E : Env) {α : Type} : Script α → Ideal → Option α × Ideal × List Release
  | .done a, I => (some a, I, [])
  | .abort _, I => (none, I, [])
  | .step i k, I =>
    match openOf i with
    | some (h, l) =>
      match I.bools h.id with
      | some v =>
        let r := pubRun E (k (.bits v)) I
        (r.1, r.2.1, ⟨l, .bits v⟩ :: r.2.2)
      | none => (none, I, [])
    | none =>
      match plainStep E i I with
      | some I' => pubRun E (k .unit) I'
      | none => (none, I, [])

/-- **Two honest parties on a public script** end with `pubRun`'s result (the same for both), its
ideal state, and both see exactly its releases, whatever their stores. -/
theorem jointRun_pub (E : Env) {α : Type} {s : Script α} (hs : Every (fun i => pubInstr i = true) s) :
    ∀ (σA σB : Store) (I : Ideal),
    (jointRun E s s σA σB I).result = (pubRun E s I).1.map (fun a => (a, a)) ∧
    (jointRun E s s σA σB I).ideal = (pubRun E s I).2.1 ∧
    (jointRun E s s σA σB I).viewA = (pubRun E s I).2.2 ∧
    (jointRun E s s σA σB I).viewB = (pubRun E s I).2.2 := by
  induction hs with
  | done a => intro σA σB I; exact ⟨rfl, rfl, rfl, rfl⟩
  | abort r => intro σA σB I; exact ⟨rfl, rfl, rfl, rfl⟩
  | step i k hi _ ih =>
    intro σA σB I
    rcases pubInstr_cases i hi with hp | ⟨h, l, rfl⟩
    · simp only [jointRun, if_true, fill_plain _ _ _ i hp, idealStep_plain E .a _ I i hp, pubRun,
        openOf_plain i hp]
      cases hst : plainStep E i I with
      | none => simp
      | some I' =>
        simp only [Option.map_some, absorb_none]
        exact ih .unit σA σB I'
    · simp only [jointRun, if_true, fill, InstrP.map, idealStep, pubRun, openOf]
      cases hv : I.bools h.id with
      | none => simp
      | some v =>
        simp only [absorb, Option.toList_some, List.cons_append, List.nil_append]
        obtain ⟨e1, e2, e3, e4⟩ := ih (.bits v) σA σB I
        exact ⟨e1, e2, by rw [e3], by rw [e4]⟩

/-- **Against any adversary**, a public script releases a prefix of `pubRun`'s releases (to the
adversary and to the honest party), and a result, if any, is `pubRun`'s. -/
theorem withAdv_pub (E : Env) (me : Party) (adv : Adversary) {α : Type} {s : Script α}
    (hs : Every (fun i => pubInstr i = true) s) :
    ∀ (σ : Store) (I : Ideal) (vD : List Release),
    (withAdv E me adv s σ I vD).viewD <+: (pubRun E s I).2.2 ∧
    (withAdv E me adv s σ I vD).viewH <+: (pubRun E s I).2.2 ∧
    ∀ x, (withAdv E me adv s σ I vD).result = some x → (pubRun E s I).1 = some x := by
  induction hs with
  | done a => intro σ I vD; exact ⟨List.nil_prefix, List.nil_prefix, fun x hx => hx⟩
  | abort r => intro σ I vD; exact ⟨List.nil_prefix, List.nil_prefix, fun x hx => by simp [withAdv] at hx⟩
  | step i k hi _ ih =>
    intro σ I vD
    rcases pubInstr_cases i hi with hp | ⟨h, l, rfl⟩
    · simp only [withAdv, fill_plain _ _ _ i hp, early_blank i hp, Option.toList_none, List.append_nil, pubRun,
        openOf_plain i hp]
      split
      · exact ⟨List.nil_prefix, List.nil_prefix, fun x hx => by simp at hx⟩
      · rw [idealStep_plain E me _ I i hp]
        cases hst : plainStep E i I with
        | none => exact ⟨List.nil_prefix, List.nil_prefix, fun x hx => by simp at hx⟩
        | some I' =>
          simp only [Option.map_some, absorb_none, Option.toList_none, List.nil_append, List.append_nil]
          exact ih .unit σ I' vD
    · simp only [withAdv, fill, InstrP.map, Wire.early, Option.toList_none, List.append_nil, pubRun, openOf]
      split
      · exact ⟨List.nil_prefix, List.nil_prefix, fun x hx => by simp at hx⟩
      · cases hv : I.bools h.id with
        | none => simp [idealStep, hv]
        | some v =>
          simp only [idealStep, hv, absorb, Option.toList_some, List.cons_append, List.nil_append]
          obtain ⟨e1, e2, e3⟩ := ih (.bits v) σ I (vD ++ [⟨l, .bits v⟩])
          exact ⟨List.cons_prefix_cons.mpr ⟨rfl, e1⟩, List.cons_prefix_cons.mpr ⟨rfl, e2⟩, e3⟩

/-! ### `pubRun` through the combinators -/

section Steps

variable (E : Env) {α : Type}

@[simp] theorem setBool_bools (I : Ideal) (h : BoolH) (v : Bits) (j : Nat) :
    (I.setBool h v).bools j = if j = h.id then some v else I.bools j := rfl

@[simp] theorem dropBool_bools (I : Ideal) (h : BoolH) (j : Nat) :
    (I.dropBool h).bools j = if j = h.id then none else I.bools j := rfl

theorem bools_setk_ne (I : Ideal) (k : Nat) (v : Bits) (j : Nat) (hne : j ≠ k) :
    (I.setBool ⟨k⟩ v).bools j = I.bools j := by
  show (if j = k then some v else I.bools j) = I.bools j
  rw [if_neg hne]

theorem bools_setk_eq (I : Ideal) (k : Nat) (v : Bits) (j : Nat) (he : j = k) :
    (I.setBool ⟨k⟩ v).bools j = some v := by
  show (if j = k then some v else I.bools j) = some v
  rw [if_pos he]

theorem bools_dropk_ne (I : Ideal) (k : Nat) (j : Nat) (hne : j ≠ k) : (I.dropBool ⟨k⟩).bools j = I.bools j := by
  show (if j = k then none else I.bools j) = I.bools j
  rw [if_neg hne]

theorem bools_drop_ne (I : Ideal) (h : BoolH) (j : Nat) (hne : j ≠ h.id) : (I.dropBool h).bools j = I.bools j := by
  show (if j = h.id then none else I.bools j) = I.bools j
  rw [if_neg hne]

theorem pubRun_seq_plain (i : Instr) (hi : plain i = true) (s : Script α) (I I1 : Ideal)
    (h : plainStep E i I = some I1) : pubRun E (seq i s) I = pubRun E s I1 := by
  simp only [seq, pubRun, openOf_plain i hi, h]

theorem pubRun_boolPublic (out : BoolH) (v : Bits) (s : Script α) (I : Ideal) :
    pubRun E (seq (.boolPublic out v) s) I = pubRun E s (I.setBool out v) :=
  pubRun_seq_plain E _ rfl s I _ (by simp [plainStep, idealStep, blankWire, InstrP.map])

theorem pubRun_free (h : BoolH) (s : Script α) (I : Ideal) :
    pubRun E (seq (.freeBool h) s) I = pubRun E s (I.dropBool h) :=
  pubRun_seq_plain E _ rfl s I _ (by simp [plainStep, idealStep, blankWire, InstrP.map])

theorem pubRun_concat (out : BoolH) (parts : List BoolH) (s : Script α) (I : Ideal) (vs : List Bits)
    (hv : parts.mapM (fun h => I.bools h.id) = some vs) :
    pubRun E (seq (.concat out parts) s) I = pubRun E s (I.setBool out vs.flatten) :=
  pubRun_seq_plain E _ rfl s I _ (by simp [plainStep, idealStep, blankWire, InstrP.map, hv])

theorem pubRun_run (out : BoolH) (name : Bytes) (copies : Nat) (input : BoolH) (s : Script α) (I : Ideal)
    (c : Circuit) (v : Bits) (hc : E.circuits name = some c) (hv : I.bools input.id = some v)
    (hl : v.length = copies * c.inWidth) :
    pubRun E (seq (.run out name copies input) s) I = pubRun E s (I.setBool out (runCopies c copies v)) :=
  pubRun_seq_plain E _ rfl s I _ (by simp [plainStep, idealStep, blankWire, InstrP.map, hc, hv, hl])

theorem pubRun_slice (out h : BoolH) (lo hi : Nat) (s : Script α) (I : Ideal) (v : Bits)
    (hv : I.bools h.id = some v) (h1 : lo ≤ hi) (h2 : hi ≤ v.length) :
    pubRun E (seq (.slice out h lo hi) s) I = pubRun E s (I.setBool out ((v.drop lo).take (hi - lo))) :=
  pubRun_seq_plain E _ rfl s I _ (by simp [plainStep, idealStep, blankWire, InstrP.map, hv, h1, h2])

theorem pubRun_openThen (h : BoolH) (l : Label) (k : Bits → Script α) (I : Ideal) (v : Bits)
    (hv : I.bools h.id = some v) :
    pubRun E (openThen h l k) I =
      ((pubRun E (k v) I).1, (pubRun E (k v) I).2.1, ⟨l, .bits v⟩ :: (pubRun E (k v) I).2.2) := by
  simp only [openThen, pubRun, openOf, hv]

theorem runCopies_one (c : Circuit) (v : Bits) (h : v.length = c.inWidth) : runCopies c 1 v = c.eval v := by
  simp [runCopies, List.take_of_length_le (Nat.le_of_eq h)]

end Steps

/-! ### The send scripts are public -/

theorem pub_open (h : BoolH) (l : Label) : pubInstr (.openBool h l) = true := rfl

theorem plain_pub {is : List Instr} (h : is.all plain = true) : ∀ i ∈ is, pubInstr i = true :=
  fun i hi => pub_of_plain i (plain_of_all h i hi)

theorem sealScript_pubs (n : Nat) (a : SealArgs) : Every (fun i => pubInstr i = true) (sealScript n a) := by
  unfold sealScript
  split
  · split
    · refine every_seqs (every_openThen (pub_open _ _) (fun flags => every_seqs ?_ _ (plain_pub rfl))) _
        (fun i hi => pub_of_plain i (widthsBlock_plain _ _ _ _ i hi))
      unfold afterWidths
      split
      · split
        · refine every_seqs (every_openThen (pub_open _ _) (fun st => ?_)) _ (fun i hi => pub_of_plain i (sealBlock_plain _ _ _ _ i hi))
          unfold afterStatus
          split
          · exact every_seqs (every_openThen (pub_open _ _) (fun _ => every_seqs (Every.done _) _ (plain_pub rfl))) _ (plain_pub rfl)
          · exact every_seqs (Every.done _) _ (plain_pub rfl)
        · exact Every.abort _
      · exact Every.abort _
    · exact Every.abort _
  · exact Every.abort _

theorem requestScript_pubs (n : Nat) (cert state : BoolH) :
    Every (fun i => pubInstr i = true) (requestScript n cert state) :=
  every_seqs (Every.done _) _ (plain_pub rfl)

theorem requestCtrScript_pubs (n : Nat) (traffic conv : BoolH) (seq frame mask : B8) (name : Bytes) :
    Every (fun i => pubInstr i = true) (requestCtrScript n traffic conv seq frame mask name) := by
  refine every_seqs (every_openThen (pub_open _ _) (fun _ => every_seqs ?_ _ (plain_pub rfl))) _ (plain_pub rfl)
  split
  · exact Every.done _
  · exact Every.abort _

/-! ## Op 41 in the model -/

theorem textClass_pos {t : Nat} {p : Bool × Nat} (h : textClass t = some p) : 1 ≤ p.2 := by
  unfold textClass at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; dsimp only; omega
  · split at h
    · simp only [Option.some.injEq] at h; subst h; dsimp only; omega
    · cases h

theorem sealInputs_bits (cert classes : Nat) (official : Bool) :
    ((KernelSpecs.SealFixed.sealInputs cert classes official).map (·.2.bits)).sum =
      8 * convBytes cert + 8 * textBytes classes official + 4 * 255 := by
  cases official <;>
    simp [KernelSpecs.SealFixed.sealInputs, HybridKernel.Shape.bits, HybridKernel.conversationBytes, convBytes,
      recordBytes, textBytes] <;> omega

theorem sealBound_of (cert cw pw ew iw classes : Nat) (official : Bool) (hc : cert ≤ 1024) (hcl : classes ≤ 4)
    (hw : cw ≤ 10 ∧ pw ≤ 10 ∧ ew ≤ 10 ∧ iw ≤ 10) : SealBound cert cw pw ew iw classes official := by
  unfold SealBound
  cases official <;>
    simp [KernelSpecs.SealFixed.contentBytes, PrivateTextNotification.officialPaddedBytes,
      PrivateTextNotification.paddedBytes] <;> omega

/-- The seal kernel's output on the bundle op 41 builds (the script's concatenation). -/
def sealOutOf (a : SealArgs) (certB record : B8) (db eb tb : Bits) (official : Bool) (classes cw pw ew iw : Nat) : B8 :=
  shapedOut (sealK a.certLen cw pw ew iw classes official)
    (bitsOf (certB ++ record) ++ (bitsOf a.text ++ (wordBits a.ephPublic ++ (db ++ (eb ++ tb)))))

theorem sealOut_length (a : SealArgs) (certB record : B8) (db eb tb : Bits) (official : Bool) (classes cw pw ew iw : Nat)
    (hb : SealBound a.certLen cw pw ew iw classes official) (hcl : 1 ≤ classes) :
    (sealOutOf a certB record db eb tb official classes cw pw ew iw).length =
      1 + convBytes a.certLen + (8 + sealEnvBytes a.certLen classes official cw pw ew iw) := by
  obtain ⟨L0, L1, L2, L3, L4⟩ := sealOut_lengths a.certLen cw pw ew iw classes official
    (shapedAssign (sealK a.certLen cw pw ew iw classes official).inputs
      (bitsOf (certB ++ record) ++ (bitsOf a.text ++ (wordBits a.ephPublic ++ (db ++ (eb ++ tb)))))) hb hcl
  show (List.flatten _).length = _
  rw [flatten4 _ L4]
  simp only [List.length_append, L0, L1, L2, L3]
  omega

theorem slice_bytes (l : B8) (a b lo hi : Nat) (h1 : lo = 8 * a) (h2 : hi = 8 * b) :
    ((bitsOf l).drop lo).take (hi - lo) = bitsOf ((l.drop a).take (b - a)) := by
  subst h1 h2
  exact bitsOf_slice l a b

/-- **Op 41 after the widths, in the model**: the seal kernel's run on the script's bundle, the
three slices, the status opening and the gate. On status 255: the result is the timestamp, the
envelope and the handle `n + 6`, the releases are the status and timestamp ‖ envelope, and `n + 6`
holds the kept record. Otherwise: `none`, only the status released, the stored state's value kept. -/
theorem afterWidths_run (E : Env) (n : Nat) (a : SealArgs) (official : Bool) (classes : Nat) (flags : Bits)
    (certB record : B8) (db eb tb : Bits) (mk : List Mark) (J : Ideal) (cw pw ew iw : Nat)
    (hcB : certB.length = a.certLen) (hr : record.length = recordBytes)
    (hcl : textClass a.text.length = some (official, classes)) (hcert : a.certLen ≤ 1024)
    (hpk : a.ephPublic.length = 32) (hdb : db.length = 255) (heb : eb.length = 255) (htb : tb.length = 255)
    (hw : widthsOf (bytesOf flags) = some (cw, pw, ew, iw))
    (henv : sealEnvBytes a.certLen classes official cw pw ew iw ≤ maxEnvelope)
    (hS : E.circuits (sealName official a.certLen classes cw pw ew iw) =
      some (shapedCircuit (sealK a.certLen cw pw ew iw classes official) mk))
    (hdn : a.sender.id < n) (htn : a.static.id < n) (hen : a.ephAgreement.id < n) (hsn : a.state.id < n)
    (hes : a.ephAgreement.id ≠ a.state.id)
    (h0 : J.bools n = some (bitsOf (certB ++ record))) (hd : J.bools a.sender.id = some db)
    (he : J.bools a.ephAgreement.id = some eb) (ht : J.bools a.static.id = some tb) :
    let out := sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + convBytes a.certLen)).take (8 + sealEnvBytes a.certLen classes official cw pw ew iw)
    let r := pubRun E (afterWidths n a official classes flags) J
    (out.take 1 = [255] →
      r.1 = some (some ⟨te.take 8, [te.drop 8], ⟨n + 6⟩⟩) ∧
      r.2.2 = [⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩, ⟨envelopeLabel, .bits (bitsOf te)⟩] ∧
      r.2.1.bools (n + 6) = some (bitsOf ((out.drop (1 + a.certLen)).take recordBytes)) ∧
      ∀ x, x < n → x ≠ a.ephAgreement.id → x ≠ a.state.id → r.2.1.bools x = J.bools x) ∧
    (out.take 1 ≠ [255] →
      r.1 = some none ∧ r.2.2 = [⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩] ∧
      ∀ x, x < n → x ≠ a.ephAgreement.id → r.2.1.bools x = J.bools x) := by
  dsimp only
  obtain ⟨hT330, hcls4⟩ := textClass_le hcl
  obtain ⟨hT, -⟩ := textClass_some hcl
  have hcl1 : 1 ≤ classes := textClass_pos hcl
  have hw' := widthsOf_le hw
  have hb := sealBound_of a.certLen cw pw ew iw classes official hcert hcls4 hw'
  have hlen := sealOut_length a certB record db eb tb official classes cw pw ew iw hb hcl1
  generalize hO : sealOutOf a certB record db eb tb official classes cw pw ew iw = out at hlen ⊢
  generalize hEv : sealEnvBytes a.certLen classes official cw pw ew iw = env at hlen henv ⊢
  -- id facts (the concatenation's lookups)
  have nk : ∀ i j : Nat, i ≠ j → (n + i = n + j) = False := fun i j h => by simp; omega
  have n0 : ∀ j : Nat, j ≠ 0 → (n = n + j) = False := fun j h => by simp; omega
  have n0' : ∀ j : Nat, j ≠ 0 → (n + j = n) = False := fun j h => by simp; omega
  have xd : ∀ k, (a.sender.id = n + k) = False := fun k => by simp; omega
  have xt : ∀ k, (a.static.id = n + k) = False := fun k => by simp; omega
  have xe : ∀ k, (a.ephAgreement.id = n + k) = False := fun k => by simp; omega
  -- the bundle
  have hV : [bitsOf (certB ++ record), bitsOf a.text ++ wordBits a.ephPublic, db, eb, tb].flatten =
      bitsOf (certB ++ record) ++ (bitsOf a.text ++ (wordBits a.ephPublic ++ (db ++ (eb ++ tb)))) := by
    simp [List.append_assoc]
  have hVl : (bitsOf (certB ++ record) ++ (bitsOf a.text ++ (wordBits a.ephPublic ++ (db ++ (eb ++ tb))))).length =
      1 * (shapedCircuit (sealK a.certLen cw pw ew iw classes official) mk).inWidth := by
    show _ = 1 * ((KernelSpecs.SealFixed.sealInputs a.certLen classes official).map (·.2.bits)).sum
    rw [sealInputs_bits]
    simp [wordBits, hpk, hdb, heb, htb, hcB, hr, hT, convBytes]
    omega
  have hOut : (shapedCircuit (sealK a.certLen cw pw ew iw classes official) mk).eval
      (bitsOf (certB ++ record) ++ (bitsOf a.text ++ (wordBits a.ephPublic ++ (db ++ (eb ++ tb))))) = bitsOf out := by
    rw [← hO]; rfl
  have hBl : (bitsOf out).length = 8 * (1 + convBytes a.certLen + (8 + env)) := by
    rw [length_bitsOf, hlen]
  -- the block, the status opening
  have key : ∃ J5 : Ideal, pubRun E (afterWidths n a official classes flags) J =
      ((pubRun E (afterStatus n a (bitsOf (out.take 1))) J5).1, (pubRun E (afterStatus n a (bitsOf (out.take 1))) J5).2.1,
        ⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩ :: (pubRun E (afterStatus n a (bitsOf (out.take 1))) J5).2.2) ∧
      J5.bools (n + 6) = some (bitsOf ((out.drop (1 + a.certLen)).take recordBytes)) ∧
      J5.bools (n + 7) = some (bitsOf ((out.drop (1 + convBytes a.certLen)).take (8 + env))) ∧
      ∀ x, x < n → x ≠ a.ephAgreement.id → J5.bools x = J.bools x := by
    refine ⟨?J5, ?e, ?f6, ?f7, ?fs⟩
    case e =>
      unfold afterWidths
      rw [hw]
      dsimp only
      rw [hEv, if_pos henv]
      simp only [sealBlock, seqs_cons, seqs_nil]
      rw [pubRun_boolPublic]
      rw [pubRun_concat E _ _ _ _ [bitsOf (certB ++ record), bitsOf a.text ++ wordBits a.ephPublic, db, eb, tb] (by
        simp (config := { decide := true }) only [List.mapM_cons, List.mapM_nil, setBool_bools, n0, n0', xd, xt, xe,
          eq_self_iff_true, if_true, if_false, h0, hd, he, ht]
        rfl)]
      rw [hV, pubRun_run E _ _ _ _ _ _ _ _ hS (by simp) hVl, runCopies_one _ _ (by rw [hVl, Nat.one_mul]), hOut]
      rw [pubRun_slice E _ _ _ _ _ _ (bitsOf out) (by simp) (by simp [statusEnd]) (by rw [hBl]; simp [statusEnd]; omega)]
      rw [pubRun_slice E _ _ _ _ _ _ (bitsOf out)
        (by simp (config := { decide := true }) only [setBool_bools, nk, eq_self_iff_true, if_true, if_false])
        (by simp only [recordFrom, recordEnd, convBytes]; omega) (by rw [hBl]; simp [recordEnd, convBytes]; omega)]
      rw [pubRun_slice E _ _ _ _ _ _ (bitsOf out)
        (by simp (config := { decide := true }) only [setBool_bools, nk, eq_self_iff_true, if_true, if_false])
        (by simp only [envelopeEnd, recordEnd]; omega) (by rw [hBl]; simp [envelopeEnd, recordEnd, convBytes]; omega)]
      rw [pubRun_free, pubRun_free, pubRun_free, pubRun_free, pubRun_free]
      rw [pubRun_openThen E ⟨n + 5⟩ _ _ _ (bitsOf (out.take 1)) ?hl]
      case hl =>
        dsimp only
        rw [bools_dropk_ne _ _ _ (by omega), bools_drop_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega),
          bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega),
          bools_setk_ne _ _ _ _ (by omega), bools_setk_eq _ _ _ _ rfl]
        congr 1
        rw [slice_bytes out 0 1 0 statusEnd rfl rfl, List.drop_zero]
    · rw [bools_dropk_ne _ _ _ (by omega), bools_drop_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega),
        bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega),
        bools_setk_eq _ _ _ _ rfl]
      rw [slice_bytes out (1 + a.certLen) (1 + convBytes a.certLen) (recordFrom a.certLen) (recordEnd a.certLen)
        (by simp only [recordFrom]; omega) (by simp only [recordEnd]; omega),
        show 1 + convBytes a.certLen - (1 + a.certLen) = recordBytes by simp only [convBytes]; omega]
    · rw [bools_dropk_ne _ _ _ (by omega), bools_drop_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega),
        bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_setk_eq _ _ _ _ rfl]
      rw [slice_bytes out (1 + convBytes a.certLen) (1 + convBytes a.certLen + (8 + env)) (recordEnd a.certLen)
        (envelopeEnd a.certLen env) (by simp only [recordEnd]; omega) (by simp only [envelopeEnd, recordEnd]; omega),
        show 1 + convBytes a.certLen + (8 + env) - (1 + convBytes a.certLen) = 8 + env by omega]
    · intro x hx hxe
      rw [bools_dropk_ne _ _ _ (by omega), bools_drop_ne _ _ _ hxe, bools_dropk_ne _ _ _ (by omega),
        bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega),
        bools_setk_ne _ _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega),
        bools_setk_ne _ _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega)]
  obtain ⟨J5, hrun, h6, h7, hst⟩ := key
  rw [hrun]
  constructor
  · intro hacc
    have hst' : bitsOf (out.take 1) = bitsOf [255] := by rw [hacc]
    unfold afterStatus
    rw [if_pos hst']
    simp only [seqs_cons, seqs_nil]
    rw [pubRun_free, pubRun_openThen E ⟨n + 7⟩ _ _ _ (bitsOf ((out.drop (1 + convBytes a.certLen)).take (8 + env)))
      (by dsimp only; rw [bools_dropk_ne _ _ _ (by omega), h7])]
    simp only [seqs_cons, seqs_nil]
    rw [pubRun_free, pubRun_free]
    refine ⟨by simp only [pubRun, bytesOf_bitsOf], rfl, ?_, ?_⟩
    · dsimp only [pubRun]
      rw [bools_drop_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), h6]
    · intro x hx hxe hxs
      dsimp only [pubRun]
      rw [bools_drop_ne _ _ _ hxs, bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), hst x hx hxe]
  · intro hrej
    have hst' : bitsOf (out.take 1) ≠ bitsOf [255] := fun e => hrej (bitsOf_inj _ _ e)
    unfold afterStatus
    rw [if_neg hst']
    simp only [seqs_cons, seqs_nil]
    rw [pubRun_free, pubRun_free, pubRun_free]
    refine ⟨rfl, rfl, ?_⟩
    intro x hx hxe
    dsimp only [pubRun]
    rw [bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega),
      hst x hx hxe]

/-- **Op 41's first phase in the model**: the conversation, the widths kernel, the flags' opening. -/
theorem sealScript_run (E : Env) (n : Nat) (a : SealArgs) (certB record : B8) (I : Ideal) (Cw : Circuit)
    (official : Bool) (classes : Nat)
    (hcl : textClass a.text.length = some (official, classes)) (hcert : a.certLen ≤ 1024)
    (hW : E.circuits (widthsName a.certLen) = some Cw)
    (hWw : (bitsOf (certB ++ record)).length = Cw.inWidth)
    (hc : I.bools a.cert.id = some (bitsOf certB)) (hs : I.bools a.state.id = some (bitsOf record)) :
    let flags := Cw.eval (bitsOf (certB ++ record))
    let J := ((I.setBool ⟨n⟩ (bitsOf (certB ++ record))).setBool ⟨n + 1⟩ flags).dropBool ⟨n + 1⟩
    pubRun E (sealScript n a) I =
      ((pubRun E (afterWidths n a official classes flags) J).1, (pubRun E (afterWidths n a official classes flags) J).2.1,
        ⟨widthsLabel, .bits flags⟩ :: (pubRun E (afterWidths n a official classes flags) J).2.2) := by
  dsimp only
  unfold sealScript
  rw [hcl]
  dsimp only
  rw [if_pos hcert]
  simp only [widthsBlock, seqs_cons, seqs_nil]
  rw [pubRun_concat E _ _ _ _ [bitsOf certB, bitsOf record] (by simp [hc, hs]),
    show [bitsOf certB, bitsOf record].flatten = bitsOf (certB ++ record) by simp,
    pubRun_run E _ _ _ _ _ _ Cw (bitsOf (certB ++ record)) hW (by simp) (by rw [hWw, Nat.one_mul]),
    runCopies_one _ _ hWw, pubRun_openThen E ⟨n + 1⟩ _ _ _ (Cw.eval (bitsOf (certB ++ record)))
      (bools_setk_eq _ _ _ _ rfl)]
  simp only [pubRun_free]

/-- What the model of op 41 needs: the values behind the handles (certificate ‖ record, the sender
key, the agreements), the ids below the session counter `n` and the freed ones distinct, the widths
kernel loaded (as any circuit). -/
structure SealModel (E : Env) (n : Nat) (a : SealArgs) (certB record : B8) (db eb tb : Bits) (I : Ideal)
    (Cw : Circuit) (official : Bool) (classes : Nat) : Prop where
  cls : textClass a.text.length = some (official, classes)
  certLe : a.certLen ≤ 1024
  certLen : certB.length = a.certLen
  recLen : record.length = recordBytes
  pkLen : a.ephPublic.length = 32
  dbLen : db.length = 255
  ebLen : eb.length = 255
  tbLen : tb.length = 255
  wk : E.circuits (widthsName a.certLen) = some Cw
  wkIn : (bitsOf (certB ++ record)).length = Cw.inWidth
  cn : a.cert.id < n
  sn : a.state.id < n
  dn : a.sender.id < n
  tn : a.static.id < n
  en : a.ephAgreement.id < n
  es : a.ephAgreement.id ≠ a.state.id
  ec : a.ephAgreement.id ≠ a.cert.id
  cs : a.cert.id ≠ a.state.id
  vc : I.bools a.cert.id = some (bitsOf certB)
  vs : I.bools a.state.id = some (bitsOf record)
  vd : I.bools a.sender.id = some db
  ve : I.bools a.ephAgreement.id = some eb
  vt : I.bools a.static.id = some tb

/-- **Op 41 in the model, whole**: the releases are the flags, the status and (only on 255) the
timestamp ‖ envelope; on 255 the result is the timestamp, the envelope and `n + 6`, which holds the
kept record, and the certificate's value is untouched; otherwise `none` and the stored state's value
is untouched. -/
theorem seal_outcome (E : Env) (n : Nat) (a : SealArgs) (certB record : B8) (db eb tb : Bits) (I : Ideal)
    (Cw : Circuit) (official : Bool) (classes : Nat) (h : SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : sealEnvBytes a.certLen classes official cw pw ew iw ≤ maxEnvelope)
    (hS : E.circuits (sealName official a.certLen classes cw pw ew iw) =
      some (shapedCircuit (sealK a.certLen cw pw ew iw classes official) mk)) :
    let flags := Cw.eval (bitsOf (certB ++ record))
    let out := sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + convBytes a.certLen)).take (8 + sealEnvBytes a.certLen classes official cw pw ew iw)
    let r := pubRun E (sealScript n a) I
    (out.take 1 = [255] →
      r.1 = some (some ⟨te.take 8, [te.drop 8], ⟨n + 6⟩⟩) ∧
      r.2.2 = [⟨widthsLabel, .bits flags⟩, ⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩,
        ⟨envelopeLabel, .bits (bitsOf te)⟩] ∧
      r.2.1.bools (n + 6) = some (bitsOf ((out.drop (1 + a.certLen)).take recordBytes)) ∧
      ∀ x, x < n → x ≠ a.ephAgreement.id → x ≠ a.state.id → r.2.1.bools x = I.bools x) ∧
    (out.take 1 ≠ [255] →
      r.1 = some none ∧ r.2.2 = [⟨widthsLabel, .bits flags⟩, ⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩] ∧
      r.2.1.bools a.state.id = some (bitsOf record)) := by
  dsimp only
  have hn := h.cn
  have hs := h.sn
  have hd := h.dn
  have ht := h.tn
  have he := h.en
  rw [sealScript_run E n a certB record I Cw official classes h.cls h.certLe h.wk h.wkIn h.vc h.vs]
  have hJ : ∀ x, x < n → (((I.setBool ⟨n⟩ (bitsOf (certB ++ record))).setBool ⟨n + 1⟩
      (Cw.eval (bitsOf (certB ++ record)))).dropBool ⟨n + 1⟩).bools x = I.bools x := by
    intro x hx
    rw [bools_dropk_ne _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega)]
  have key := afterWidths_run E n a official classes (Cw.eval (bitsOf (certB ++ record))) certB record db eb tb mk
    (((I.setBool ⟨n⟩ (bitsOf (certB ++ record))).setBool ⟨n + 1⟩ (Cw.eval (bitsOf (certB ++ record)))).dropBool ⟨n + 1⟩)
    cw pw ew iw h.certLen h.recLen h.cls h.certLe h.pkLen h.dbLen h.ebLen h.tbLen hw henv hS h.dn h.tn h.en h.sn h.es
    (by rw [bools_dropk_ne _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega), bools_setk_eq _ _ _ _ rfl])
    (by rw [hJ _ h.dn, h.vd]) (by rw [hJ _ h.en, h.ve]) (by rw [hJ _ h.tn, h.vt])
  dsimp only at key
  obtain ⟨kA, kR⟩ := key
  refine ⟨fun hacc => ?_, fun hrej => ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := kA hacc
    refine ⟨e1, by rw [e2], e3, fun x hx hxe hxs => ?_⟩
    rw [e4 x hx hxe hxs, hJ x hx]
  · obtain ⟨e1, e2, e3⟩ := kR hrej
    refine ⟨e1, by rw [e2], ?_⟩
    rw [e3 _ h.sn (fun e => h.es e.symm), hJ _ h.sn, h.vs]

/-- **What the accepted op 41 computed** (`seal_accepted_value` on the script's own bundle): the
reference send step accepts the stored state, the kept record with the certificate is
`SealSend.advancedRecord`, the opened envelope is `sealV1` of the reference message. -/
theorem sealOut_values (a : SealArgs) (certB record : B8) (db eb tb : Bits) (official : Bool)
    (classes cw pw ew iw : Nat) (hcB : certB.length = a.certLen) (hr : record.length = recordBytes)
    (hcl : textClass a.text.length = some (official, classes)) (hcert : a.certLen ≤ 1024)
    (hw : cw ≤ 10 ∧ pw ≤ 10 ∧ ew ≤ 10 ∧ iw ≤ 10) :
    let conv := certB ++ record
    let w := wordBits a.ephPublic ++ (db ++ (eb ++ tb))
    let sa := shapedAssign (sealK a.certLen cw pw ew iw classes official).inputs (bitsOf conv ++ (bitsOf a.text ++ w))
    let get := fun name => (lookup (KernelSpecs.SealFixed.sealInputs a.certLen classes official) name).map
      (BVExpr.eval sa)
    let out := sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + convBytes a.certLen)).take (8 + sealEnvBytes a.certLen classes official cw pw ew iw)
    let newRecord := (out.drop (1 + a.certLen)).take recordBytes
    out.take 1 = [255] →
    let staged := KernelSpecs.SealFixed.stagedOf ((conv.drop a.certLen).take (182 + 80)) a.text
    let i := KernelSpecs.SealFixed.inputOf 0 staged a.text (KernelSpecs.SealFixed.contentBytes classes official)
    let p := SpqrSend.canonical ⟨cw, pw, false⟩ ⟨ew, iw, 1, false⟩ i
    SpqrSend.accepted ⟨cw, pw, false⟩ ⟨ew, iw, 1, false⟩ i ∧
    certB ++ newRecord = KernelSpecs.SealSend.advancedRecord a.certLen conv staged p ∧
    te.take 8 = (a.text.drop (2 + KernelSpecs.SealFixed.contentBytes classes official)).take 8 ∧
    te.drop 8 = KernelSpecs.SealValue.Reference.sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic")
      (get "ephemeralAgreement") (get "staticAgreement") certB p.wire := by
  intro conv w sa get out te newRecord hst staged i p
  obtain ⟨hT, -⟩ := textClass_some hcl
  obtain ⟨-, hcls4⟩ := textClass_le hcl
  have hcl1 : 1 ≤ classes := textClass_pos hcl
  have hb := sealBound_of a.certLen cw pw ew iw classes official hcert hcls4 hw
  have hconv : conv.length = convBytes a.certLen := by simp [conv, hcB, hr, convBytes]
  have hct : conv.take a.certLen = certB := List.take_left' hcB
  obtain ⟨hA, -, hrec, hte⟩ := seal_accepted_value a.certLen cw pw ew iw classes official conv a.text w hconv hT hb
    hcl1 hst
  rw [hct] at hrec hte
  have hts : ((a.text.drop (2 + KernelSpecs.SealFixed.contentBytes classes official)).take 8).length = 8 := by
    obtain ⟨hT', -⟩ := textBytes_eq classes official hcl1
    simp only [List.length_take, List.length_drop, hT, hT']
    omega
  have hte' : te = (a.text.drop (2 + KernelSpecs.SealFixed.contentBytes classes official)).take 8 ++
      KernelSpecs.SealValue.Reference.sealV1 i.receiver (get "ephemeralPublic") (get "senderPublic")
        (get "ephemeralAgreement") (get "staticAgreement") certB p.wire := hte
  refine ⟨hA, hrec, ?_, ?_⟩
  · rw [hte', List.take_left' hts]
  · rw [hte', List.drop_left' hts]

/-- **F57: op 41 against any adversary, by value.** Whatever the adversary does, what it sees of op
41 is a prefix of: the width flags (the widths kernel's output on certificate ‖ record), the status
byte, and only when the status is 255, timestamp ‖ envelope (with `sealOut_values`: the built text's
timestamp and `sealV1` of the reference message). On a refused status: at most the flags and the
status. The honest party's view is the same prefix bound; a result, if any, is `pubRun`'s. -/
theorem seal_view (E : Env) (me : Party) (adv : Adversary) (σ : Store) (vD : List Release)
    (n : Nat) (a : SealArgs) (certB record : B8) (db eb tb : Bits) (I : Ideal)
    (Cw : Circuit) (official : Bool) (classes : Nat) (h : SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : sealEnvBytes a.certLen classes official cw pw ew iw ≤ maxEnvelope)
    (hS : E.circuits (sealName official a.certLen classes cw pw ew iw) =
      some (shapedCircuit (sealK a.certLen cw pw ew iw classes official) mk)) :
    let flags := Cw.eval (bitsOf (certB ++ record))
    let out := sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + convBytes a.certLen)).take (8 + sealEnvBytes a.certLen classes official cw pw ew iw)
    let o := withAdv E me adv (sealScript n a) σ I vD
    (out.take 1 = [255] →
      o.viewD <+: [⟨widthsLabel, .bits flags⟩, ⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩,
        ⟨envelopeLabel, .bits (bitsOf te)⟩]) ∧
    (out.take 1 ≠ [255] →
      o.viewD <+: [⟨widthsLabel, .bits flags⟩, ⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩] ∧
      ∀ x, o.result = some x → x = none) := by
  dsimp only
  obtain ⟨v1, -, v3⟩ := withAdv_pub E me adv (sealScript_pubs n a) σ I vD
  obtain ⟨kA, kR⟩ := seal_outcome E n a certB record db eb tb I Cw official classes h cw pw ew iw mk hw henv hS
  refine ⟨fun hacc => ?_, fun hrej => ?_⟩
  · rw [← (kA hacc).2.1]; exact v1
  · refine ⟨by rw [← (kR hrej).2.1]; exact v1, fun x hx => ?_⟩
    have := v3 x hx
    rw [(kR hrej).1] at this
    exact (Option.some.inj this).symm

/-- **F57, the flags only**: when the opened flags are not all 0/255 (`widthsOf` refuses), the
adversary sees at most the flags. -/
theorem seal_view_flags (E : Env) (me : Party) (adv : Adversary) (σ : Store) (vD : List Release)
    (n : Nat) (a : SealArgs) (certB record : B8) (I : Ideal) (Cw : Circuit) (official : Bool) (classes : Nat)
    (hcl : textClass a.text.length = some (official, classes)) (hcert : a.certLen ≤ 1024)
    (hW : E.circuits (widthsName a.certLen) = some Cw) (hWw : (bitsOf (certB ++ record)).length = Cw.inWidth)
    (hc : I.bools a.cert.id = some (bitsOf certB)) (hs : I.bools a.state.id = some (bitsOf record))
    (hw : widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = none) :
    (withAdv E me adv (sealScript n a) σ I vD).viewD <+: [⟨widthsLabel, .bits (Cw.eval (bitsOf (certB ++ record)))⟩] := by
  obtain ⟨v1, -, -⟩ := withAdv_pub E me adv (sealScript_pubs n a) σ I vD
  have e := sealScript_run E n a certB record I Cw official classes hcl hcert hW hWw hc hs
  dsimp only at e
  rw [e] at v1
  unfold afterWidths at v1
  rw [hw] at v1
  exact v1

/-- **F51 for op 41: two honest parties.** Both end with the same result: on status 255 the timestamp,
the envelope and the new state handle `n + 6`, which holds the kept record (the advanced one,
`sealOut_values`); both saw exactly the flags, the status and timestamp ‖ envelope. On any other
status both return `none`, the stored state's value is kept, and both saw only the flags and the
status. -/
theorem seal_joint (E : Env) (σA σB : Store) (n : Nat) (a : SealArgs) (certB record : B8) (db eb tb : Bits)
    (I : Ideal) (Cw : Circuit) (official : Bool) (classes : Nat)
    (h : SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : sealEnvBytes a.certLen classes official cw pw ew iw ≤ maxEnvelope)
    (hS : E.circuits (sealName official a.certLen classes cw pw ew iw) =
      some (shapedCircuit (sealK a.certLen cw pw ew iw classes official) mk)) :
    let flags := Cw.eval (bitsOf (certB ++ record))
    let out := sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + convBytes a.certLen)).take (8 + sealEnvBytes a.certLen classes official cw pw ew iw)
    let sd : Sealed := ⟨te.take 8, [te.drop 8], ⟨n + 6⟩⟩
    let o := jointRun E (sealScript n a) (sealScript n a) σA σB I
    (out.take 1 = [255] →
      o.result = some (some sd, some sd) ∧
      o.viewA = [⟨widthsLabel, .bits flags⟩, ⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩,
        ⟨envelopeLabel, .bits (bitsOf te)⟩] ∧ o.viewB = o.viewA ∧
      o.ideal.bools (n + 6) = some (bitsOf ((out.drop (1 + a.certLen)).take recordBytes)) ∧
      ∀ x, x < n → x ≠ a.ephAgreement.id → x ≠ a.state.id → o.ideal.bools x = I.bools x) ∧
    (out.take 1 ≠ [255] →
      o.result = some (none, none) ∧
      o.viewA = [⟨widthsLabel, .bits flags⟩, ⟨envelopeLabel, .bits (bitsOf (out.take 1))⟩] ∧ o.viewB = o.viewA ∧
      o.ideal.bools a.state.id = some (bitsOf record)) := by
  dsimp only
  obtain ⟨r1, r2, r3, r4⟩ := jointRun_pub E (sealScript_pubs n a) σA σB I
  obtain ⟨kA, kR⟩ := seal_outcome E n a certB record db eb tb I Cw official classes h cw pw ew iw mk hw henv hS
  refine ⟨fun hacc => ?_, fun hrej => ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := kA hacc
    refine ⟨by rw [r1, e1]; rfl, by rw [r3, e2], by rw [r4, r3], by rw [r2, e3], fun x hx hxe hxs => by
      rw [r2, e4 x hx hxe hxs]⟩
  · obtain ⟨e1, e2, e3⟩ := kR hrej
    refine ⟨by rw [r1, e1]; rfl, by rw [r3, e2], by rw [r4, r3], by rw [r2, e3]⟩

/-! ## Op 42 in the model, and ORD-1 at script level (F59) -/

/-- **Op 42 reads only the state it is given** (and the certificate): two honest parties end with the
handle `m + 1` holding certificate ‖ the first record of that state's value, release nothing, and
leave every other handle below `m` as it was. -/
theorem request_joint (E : Env) (σA σB : Store) (m : Nat) (cert state : BoolH) (certB st : B8) (I : Ideal)
    (hcm : cert.id < m) (hst : recordBytes ≤ st.length)
    (hc : I.bools cert.id = some (bitsOf certB)) (hs : I.bools state.id = some (bitsOf st)) :
    let o := jointRun E (requestScript m cert state) (requestScript m cert state) σA σB I
    o.result = some (⟨m + 1⟩, ⟨m + 1⟩) ∧ o.viewA = [] ∧ o.viewB = [] ∧
    o.ideal.bools (m + 1) = some (bitsOf (certB ++ st.take recordBytes)) ∧
    ∀ x, x < m → o.ideal.bools x = I.bools x := by
  dsimp only
  obtain ⟨r1, r2, r3, r4⟩ := jointRun_pub E (requestScript_pubs m cert state) σA σB I
  have e : pubRun E (requestScript m cert state) I =
      (some ⟨m + 1⟩, (((I.setBool ⟨m⟩ (bitsOf (st.take recordBytes))).setBool ⟨m + 1⟩
        (bitsOf (certB ++ st.take recordBytes))).dropBool ⟨m⟩), []) := by
    unfold requestScript
    simp only [seqs_cons, seqs_nil]
    rw [pubRun_slice E _ _ _ _ _ _ (bitsOf st) hs (Nat.zero_le _) (by rw [length_bitsOf]; omega),
      slice_bytes st 0 recordBytes 0 (8 * recordBytes) rfl rfl, List.drop_zero, Nat.sub_zero,
      pubRun_concat E _ _ _ _ [bitsOf certB, bitsOf (st.take recordBytes)]
        (by rw [List.mapM_cons, List.mapM_cons, List.mapM_nil, bools_setk_ne _ _ _ _ (by omega), hc,
          bools_setk_eq _ _ _ _ rfl]; rfl),
      show [bitsOf certB, bitsOf (st.take recordBytes)].flatten = bitsOf (certB ++ st.take recordBytes) by simp,
      pubRun_free]
    rfl
  rw [e] at r1 r2 r3 r4
  refine ⟨r1, r3, r4, ?_, fun x hx => ?_⟩
  · rw [r2, bools_dropk_ne _ _ _ (by omega), bools_setk_eq _ _ _ _ rfl]
  · rw [r2, bools_dropk_ne _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega)]

/-- **F59, ORD-1 at script level.** On the accepted path, the new state handle op 41 returns is
`n + 6`, whose value (the kept record) the seal kernel's run defined before the envelope's opening;
op 42 run on that handle (with fresh ids above it) reads exactly that value: the request's
conversation is certificate ‖ the kept record, so the request is built from the state op 41 produced
(and, by `sealOut_values`, from the advanced ratchet state). No other operation of the send changes
the contact's entry: the backend's only table write is `put contact {e with state := sd.state}` after
an accepted op 41 (`SendBackend.«seal»`), op 42 and the record seal only read. -/
theorem send_state_order (E : Env) (σA σB : Store) (n : Nat) (a : SealArgs) (certB record : B8) (db eb tb : Bits)
    (I : Ideal) (Cw : Circuit) (official : Bool) (classes : Nat)
    (h : SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : sealEnvBytes a.certLen classes official cw pw ew iw ≤ maxEnvelope)
    (hS : E.circuits (sealName official a.certLen classes cw pw ew iw) =
      some (shapedCircuit (sealK a.certLen cw pw ew iw classes official) mk))
    (m : Nat) (hm : n + 8 ≤ m) (σA' σB' : Store) :
    let out := sealOutOf a certB record db eb tb official classes cw pw ew iw
    let newRecord := (out.drop (1 + a.certLen)).take recordBytes
    let o := jointRun E (sealScript n a) (sealScript n a) σA σB I
    out.take 1 = [255] →
    (∃ sd : Sealed, o.result = some (some sd, some sd) ∧ sd.state = ⟨n + 6⟩) ∧
    let o2 := jointRun E (requestScript m a.cert ⟨n + 6⟩) (requestScript m a.cert ⟨n + 6⟩) σA' σB' o.ideal
    o2.result = some (⟨m + 1⟩, ⟨m + 1⟩) ∧ o2.viewA = [] ∧
    o2.ideal.bools (m + 1) = some (bitsOf (certB ++ newRecord)) := by
  dsimp only
  intro hacc
  obtain ⟨kA, -⟩ := seal_joint E σA σB n a certB record db eb tb I Cw official classes h cw pw ew iw mk hw henv hS
  obtain ⟨e1, -, -, e4, e5⟩ := kA hacc
  refine ⟨⟨_, e1, rfl⟩, ?_⟩
  have hlen : recordBytes ≤ ((sealOutOf a certB record db eb tb official classes cw pw ew iw).drop
      (1 + a.certLen) |>.take recordBytes).length := by
    obtain ⟨-, hcls4⟩ := textClass_le h.cls
    have hl := sealOut_length a certB record db eb tb official classes cw pw ew iw
      (sealBound_of a.certLen cw pw ew iw classes official h.certLe hcls4 (widthsOf_le hw)) (textClass_pos h.cls)
    simp only [List.length_take, List.length_drop, hl, convBytes]
    omega
  have e5' : (jointRun E (sealScript n a) (sealScript n a) σA σB I).ideal.bools a.cert.id = some (bitsOf certB) := by
    rw [e5 _ h.cn (fun e => h.ec e.symm) h.cs, h.vc]
  obtain ⟨q1, q2, -, q4, -⟩ := request_joint E σA' σB' m a.cert ⟨n + 6⟩ certB _ _ (by have := h.cn; omega)
    hlen e5' e4
  refine ⟨q1, q2, ?_⟩
  rw [q4, List.take_of_length_le (by
    simp only [List.length_take]; omega)]

end TlsMpc.Node.Flows.Send
