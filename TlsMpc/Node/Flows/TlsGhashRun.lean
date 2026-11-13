import TlsMpc.Node.Flows.TlsOpenRun

/-!
# P-GHASH through `jointRun`: the key share, the doubling rounds, a whole `ensure` (gap F20)

REORGANIZATION_PLAN.md stage S12, plan 7.1 P-GHASH (a), (d), (e) at the level of the scripts' runs in
the ideal model (`Engine/Model.lean`), the two resharing kernels' circuits computing their Lean
definitions (`GhashLoaded`, T2's trust).

  * `keyShare_honest`: two honest parties run `keyShareScript` (A's mask from its store); the run
    returns, A's store is unchanged and B's destination slot holds `gcm-key-share`'s output on the
    traffic block and A's mask (`H ⊕ mask`, `keyShare_value`).
  * `pick_layout`, `runCopies_blocks`: the round's pick lays out, for copy `j`, A's and B's left
    share `j`, both shares of H and A's mask `j`; `c` copies of a circuit on such blocks are the
    circuit on each block, concatenated.
  * `round_honest`: two honest parties run `roundScript` with the inputs the backend stashes (each
    party's left shares `lefts · t` and share of H, A's `c` masks); B's destination slot then holds
    the opened products `Ghash.roundOpened` (one per odd power of the round).
  * **`EnsureRuns` and `ensure_shared` (P-GHASH (a) over a whole `ensure`)**: the shares the two
    parties hold after the first resharing and any sequence of doubling rounds (each a RETURNING joint
    run of the scripts, B's odd values read from its slot as `TlsBackend.ensure` does with
    `wsOfBits`; or the local square for the round from 1 to 2 powers), are XOR shares of H¹ … Hⁿ for
    the traffic block's GHASH key H.
  * `round_disclosure_A` (value-level T3, A honest): against ANY adversary B, B's view of a round is
    at most ONE release, labelled `ghashMaskedPower`, whose value is, copy by copy, `gcm-multiply` on
    A's left share and share of H, B's own contributions and A's fresh mask `j`; with
    `Ghash.multiply_hides` every copy is a bijection of A's mask (P-GHASH (d)). With B honest, A sees
    nothing (`round_viewD_B`, Flows/Ghash.lean).
  * P-GHASH (e) for the scripts: `tag_deviation` (a half that deviates by a nonzero δ moves the tag
    `tagScript` opens by exactly δ, so the record is not `sealCore`: the server rejects it), and
    `check_deviation` (in `openScript`'s tag check, a deviating half makes the acceptance byte 0 for
    the genuine tag, so the typed kernel releases only the rejection, `open_rejected`).

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.Ghash

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Tls (bools_set_self bools_set_ne bools_drop_ne localStep_public localStep_concat
  localStep_run localStep_free runLocal_step runLocal_nil runCopies_circuitOf ex_local ex_done ex_both
  localStep_concat2 localStep_concat5 localStep_runK)

/-! ## Two more steps: A's own input, an opening to B -/

section Ex

variable (E : Env) {α β : Type}

theorem ex_boolInputA (out : BoolH) (w : Nat) (once rev : Bool) (slotA slotB : Nat) (tA : Script α) (tB : Script β)
    (σA σB : Store) (I : Ideal) (a : α) (b : β) (sA sB : Store) (Q : Ideal → Prop)
    (hl : (σA.bits slotA).length = w)
    (hk : ∃ J, JRet (jointRun E tA tB σA σB (I.setBool out (σA.bits slotA))) a b J sA sB ∧ Q J) :
    ∃ J, JRet (jointRun E (seq (.boolInput out .a w once rev slotA) tA) (seq (.boolInput out .a w once rev slotB) tB)
      σA σB I) a b J sA sB ∧ Q J := by
  obtain ⟨J, hJ, hQ⟩ := hk
  refine ⟨J, ?_, hQ⟩
  unfold seq
  refine jret_step E _ _ _ _ σA σB I (.boolInput out .a w once rev (σA.bits slotA)) (.boolInput out .a w once rev [])
    (I.setBool out (σA.bits slotA)) none none a b J sA sB rfl (by simp [fill, hl]) (by simp [fill])
    (by simp [idealStep, Wire.part, hl]) ?_
  rw [absorb_none, absorb_none]
  exact hJ

theorem ex_openToB (h : BoolH) (l : Label) (dstA dstB : Nat) (tA : Script α) (tB : Script β)
    (σA σB : Store) (I : Ideal) (v : Bits) (a : α) (b : β) (sA sB : Store) (Q : Ideal → Prop)
    (hv : I.bools h.id = some v)
    (hk : ∃ J, JRet (jointRun E tA tB σA (σB.setBits dstB v) I) a b J sA sB ∧ Q J) :
    ∃ J, JRet (jointRun E (seq (.openBoolTo h .b l dstA) tA) (seq (.openBoolTo h .b l dstB) tB) σA σB I)
      a b J sA sB ∧ Q J := by
  obtain ⟨J, hJ, hQ⟩ := hk
  refine ⟨J, ?_, hQ⟩
  unfold seq
  refine jret_step E _ _ _ _ σA σB I (.openBoolTo h .b l ()) (.openBoolTo h .b l ()) I none (some ⟨l, .bits v⟩)
    a b J sA sB rfl (by simp [fill, InstrP.map]) (by simp [fill, InstrP.map]) (by simp [idealStep, hv]) ?_
  rw [absorb_none]
  exact hJ

end Ex

/-! ## The first resharing -/

theorem keyShare_inWidth : (circuitOf HybridKernel.gcmKeyShare).inWidth = 8 * 76 := by
  simp [circuitOf, kernelCircuit, kernelInBytes, HybridKernel.gcmKeyShare, HybridKernel.Shape.variables]

/-- **The first resharing, two honest parties** (`keyShareScript`; each party its own slots): the run
returns; A's store is unchanged; B's destination slot holds `gcm-key-share` on the traffic block `K`
and A's mask `m` (`H ⊕ m`). -/
theorem keyShare_honest (E : Env) (hE : GhashLoaded E) (n : Nat) (traffic : BoolH) (htn : traffic.id < n)
    (K m : B8) (hK : K.length = 60) (hm : m.length = 16) (maskA maskB dstA dstB : Nat) (σA σB : Store) (I : Ideal)
    (hIt : I.bools traffic.id = some (bitsOf K)) (hσ : σA.bits maskA = bitsOf m) :
    ∃ J, JRet (jointRun E (keyShareScript n traffic maskA dstA) (keyShareScript n traffic maskB dstB) σA σB I) () ()
      J σA (σB.setBits dstB (bitsOf (kernelOut HybridKernel.gcmKeyShare (K ++ m)))) ∧ True := by
  have hw : 8 * (K ++ m).length = (circuitOf HybridKernel.gcmKeyShare).inWidth := by
    rw [keyShare_inWidth, List.length_append, hK, hm]
  unfold keyShareScript keyShareBlock
  simp only [seqs_cons, seqs_nil]
  refine ex_boolInputA E ⟨n⟩ 128 true false maskA maskB _ _ σA σB I _ _ _ _ _ (by rw [hσ, length_bitsOf, hm]) ?_
  rw [hσ]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ _ _ _ (localStep_concat2 E ⟨n + 1⟩ traffic ⟨n⟩ _ (bitsOf K) (bitsOf m)
    (bitsOf (K ++ m)) (by ival_tac) (by ival_tac) (by rw [bitsOf_append])) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ _ _ _ (localStep_runK E ⟨n + 2⟩ _ ⟨n + 1⟩ _ _ _ _ hE.keyShare
    (by ival_tac) hw rfl) ?_
  refine ex_openToB E ⟨n + 2⟩ masked dstA dstB _ _ σA σB _ _ _ _ _ _ _ (by ival_tac) ?_
  refine ex_local E _ rfl _ _ σA _ _ _ _ _ _ _ _ (localStep_free E _ _) ?_
  exact ex_done E () () σA _ _ _ trivial

/-! ## The round's layout -/

theorem getD_app_left (l r : Bits) (i : Nat) (h : i < l.length) : (l ++ r).getD i false = l.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right (l r : Bits) (i : Nat) (h : l.length ≤ i) :
    (l ++ r).getD i false = r.getD (i - l.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- 128 consecutive positions of a list, read one by one, are its slice. -/
theorem getD_range (V : Bits) (s : Nat) (h : s + 128 ≤ V.length) :
    (List.range 128).map (fun b => V.getD (s + b) false) = (V.drop s).take 128 := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s + i < V.length by omega), Option.getD_some]

theorem range_getD_self (R : Bits) (h : R.length = 128) : (List.range 128).map (fun b => R.getD b false) = R := by
  have := getD_range R 0 (by omega)
  simp only [Nat.zero_add, List.drop_zero] at this
  rw [this, List.take_of_length_le (by omega)]

/-- **The pick of a round** (`layout c` on lefts A ‖ lefts B ‖ H share A ‖ H share B ‖ masks A):
copy `j` reads A's left share `j`, B's left share `j`, both shares of H and A's mask `j`. -/
theorem pick_layout (c : Nat) (LA LB RA RB M : Bits) (hA : LA.length = 128 * c) (hB : LB.length = 128 * c)
    (hRA : RA.length = 128) (hRB : RB.length = 128) (hM : M.length = 128 * c) :
    (layout c).map (fun i => (LA ++ (LB ++ (RA ++ (RB ++ M)))).getD i false) =
      (List.range c).flatMap fun j =>
        (LA.drop (j * 128)).take 128 ++ (LB.drop (j * 128)).take 128 ++ RA ++ RB ++ (M.drop (j * 128)).take 128 := by
  unfold layout
  rw [List.map_flatMap]
  unfold List.flatMap
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  simp only [List.map_append, List.map_map]
  have e1 : (List.range 128).map ((fun i => (LA ++ (LB ++ (RA ++ (RB ++ M)))).getD i false) ∘ fun b => j * 128 + b) =
      (LA.drop (j * 128)).take 128 := by
    rw [← getD_range LA (j * 128) (by rw [hA]; omega)]
    apply List.map_congr_left
    intro b hb
    rw [List.mem_range] at hb
    simp only [Function.comp]
    rw [getD_app_left _ _ _ (by rw [hA]; omega)]
  have e2 : (List.range 128).map ((fun i => (LA ++ (LB ++ (RA ++ (RB ++ M)))).getD i false) ∘
      fun b => c * 128 + j * 128 + b) = (LB.drop (j * 128)).take 128 := by
    rw [← getD_range LB (j * 128) (by rw [hB]; omega)]
    apply List.map_congr_left
    intro b hb
    rw [List.mem_range] at hb
    simp only [Function.comp]
    rw [getD_app_right _ _ _ (by rw [hA]; omega), getD_app_left _ _ _ (by rw [hB, hA]; omega), hA]
    congr 1
    omega
  have e3 : (List.range 128).map ((fun i => (LA ++ (LB ++ (RA ++ (RB ++ M)))).getD i false) ∘
      fun b => 2 * c * 128 + b) = RA := by
    refine Eq.trans ?_ (range_getD_self RA hRA)
    apply List.map_congr_left
    intro b hb
    rw [List.mem_range] at hb
    simp only [Function.comp]
    rw [getD_app_right _ _ _ (by rw [hA]; omega), getD_app_right _ _ _ (by rw [hA, hB]; omega),
      getD_app_left _ _ _ (by rw [hA, hB, hRA]; omega), hA, hB,
      show 2 * c * 128 + b - 128 * c - 128 * c = b by omega]
  have e4 : (List.range 128).map ((fun i => (LA ++ (LB ++ (RA ++ (RB ++ M)))).getD i false) ∘
      fun b => 2 * c * 128 + 128 + b) = RB := by
    refine Eq.trans ?_ (range_getD_self RB hRB)
    apply List.map_congr_left
    intro b hb
    rw [List.mem_range] at hb
    simp only [Function.comp]
    rw [getD_app_right _ _ _ (by rw [hA]; omega), getD_app_right _ _ _ (by rw [hA, hB]; omega),
      getD_app_right _ _ _ (by rw [hA, hB, hRA]; omega), getD_app_left _ _ _ (by rw [hA, hB, hRA, hRB]; omega),
      hA, hB, hRA, show 2 * c * 128 + 128 + b - 128 * c - 128 * c - 128 = b by omega]
  have e5 : (List.range 128).map ((fun i => (LA ++ (LB ++ (RA ++ (RB ++ M)))).getD i false) ∘
      fun b => 2 * c * 128 + 256 + j * 128 + b) = (M.drop (j * 128)).take 128 := by
    rw [← getD_range M (j * 128) (by rw [hM]; omega)]
    apply List.map_congr_left
    intro b hb
    rw [List.mem_range] at hb
    simp only [Function.comp]
    rw [getD_app_right _ _ _ (by rw [hA]; omega), getD_app_right _ _ _ (by rw [hA, hB]; omega),
      getD_app_right _ _ _ (by rw [hA, hB, hRA]; omega), getD_app_right _ _ _ (by rw [hA, hB, hRA, hRB]; omega),
      hA, hB, hRA, hRB, show 2 * c * 128 + 256 + j * 128 + b - 128 * c - 128 * c - 128 - 128 = j * 128 + b by omega]
  rw [e1, e2, e3, e4, e5]

theorem flatMap_length (c k : Nat) (f : Nat → Bits) (hf : ∀ j, j < c → (f j).length = k) :
    ((List.range c).flatMap f).length = c * k := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih (fun j hj => hf j (by omega))]
    simp [hf c (by omega), Nat.succ_mul]

theorem flatMap_block (k : Nat) (f : Nat → Bits) :
    ∀ c, (∀ j, j < c → (f j).length = k) → ∀ j, j < c → (((List.range c).flatMap f).drop (j * k)).take k = f j
  | 0, _, j, hj => absurd hj (by omega)
  | c + 1, hf, j, hj => by
    rw [List.range_succ, List.flatMap_append]
    have hl := flatMap_length c k f (fun i hi => hf i (by omega))
    by_cases h : j < c
    · have h1 : j * k ≤ ((List.range c).flatMap f).length := by
        rw [hl]
        exact Nat.mul_le_mul_right k (by omega)
      have h2 : k ≤ (((List.range c).flatMap f).drop (j * k)).length := by
        rw [List.length_drop, hl, ← Nat.sub_mul]
        exact Nat.le_mul_of_pos_left k (by omega)
      rw [List.drop_append_of_le_length h1, List.take_append_of_le_length h2]
      exact flatMap_block k f c (fun i hi => hf i (by omega)) j h
    · have e : j = c := by omega
      rw [e, List.drop_left' hl]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.take_of_length_le (Nat.le_of_eq (hf c (by omega)))

/-- **`c` copies of a circuit on `c` blocks of its input width** are the circuit on each block. -/
theorem runCopies_blocks (C : Engine.Circuit) (c : Nat) (f : Nat → Bits) (hf : ∀ j, j < c → (f j).length = C.inWidth) :
    runCopies C c ((List.range c).flatMap f) = ((List.range c).map fun j => C.eval (f j)).flatten := by
  unfold runCopies
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [flatMap_block C.inWidth f c hf j hj]

/-- 128 bits of a list of shares, at share `j`, are that share's bits. -/
theorem bitsOfWs_block (ws : List W) (j : Nat) (hj : j < ws.length) :
    ((bitsOfWs ws).drop (j * 128)).take 128 = bitsOfW (ws.getD j 0) := by
  induction ws generalizing j with
  | nil => simp at hj
  | cons w ws ih =>
    cases j with
    | zero =>
      simp only [bitsOfWs, List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getD_cons_zero]
      rw [List.take_left' (length_bitsOfW w)]
    | succ j =>
      simp only [List.length_cons] at hj
      simp only [bitsOfWs, List.flatMap_cons, List.getD_cons_succ]
      rw [show (j + 1) * 128 = 128 + j * 128 by omega, ← List.drop_drop, List.drop_left' (length_bitsOfW w)]
      exact ih j (by omega)

theorem bitsOf_flatten : ∀ (L : List B8), bitsOf L.flatten = (L.map bitsOf).flatten
  | [] => rfl
  | x :: L => by rw [List.flatten_cons, bitsOf_append, bitsOf_flatten L]; rfl

theorem multiply_out_length (x : B8) : (kernelOut HybridKernel.gcmMultiply x).length = 16 := by
  obtain ⟨o, ho⟩ := multiply_outputs
  have hk := outputs_one _ o ho x
  rw [HybridKernel.gcmMultiply_spec] at hk
  simp only [List.cons.injEq, and_true] at hk
  rw [← hk]
  simp only [Aes.addRoundKey, List.length_zipWith, HybridKernel.inputValue_length]
  rw [show Gcm.concrete.unpack = Local.Ghash.toBytes from rfl, Local.Ghash.toBytes_length]
  rfl

theorem multiply_inWidth : (circuitOf HybridKernel.gcmMultiply).inWidth = 8 * 80 := by
  simp [circuitOf, kernelCircuit, kernelInBytes, HybridKernel.gcmMultiply, HybridKernel.Shape.variables]

theorem localStep_pick (E : Env) (out h : BoolH) (idx : List Nat) (I : Ideal) (v w : Bits)
    (hv : I.bools h.id = some v) (hb : idx.all (· < v.length) = true) (hw : idx.map (v.getD · false) = w) :
    localStep E (.pick out h idx) I = some (I.setBool out w) := by
  subst hw
  simp [localStep, idealStep, blankWire, InstrP.map, hv, hb, List.getD_eq_getElem?_getD]

theorem localStep_run_eq (E : Env) (out : BoolH) (name : Bytes) (copies : Nat) (input : BoolH) (I : Ideal)
    (c : Engine.Circuit) (v w : Bits) (hc : E.circuits name = some c) (hv : I.bools input.id = some v)
    (hl : v.length = copies * c.inWidth) (hw : runCopies c copies v = w) :
    localStep E (.run out name copies input) I = some (I.setBool out w) := by
  rw [localStep_run E out name copies input I c v hc hv hl, hw]

/-! ## A round of the doubling schedule -/

/-- **A round, two honest parties** (`roundScript` with the inputs `TlsBackend.ensure` stashes: each
party's left shares `lefts · t` and share of H, A's `c` masks `mw`, `c = oddCount m t`): the run
returns; A's store is unchanged; B's destination slot holds the round's opened products
(`Ghash.roundOpened`, copy `j` = `gcm-multiply` on both parties' left shares `j`, shares of H and
A's mask `j`). -/
theorem round_honest (E : Env) (hE : GhashLoaded E) (n : Nat) (a b : List W) (t : Nat) (hab : b.length = a.length)
    (hc0 : 0 < Local.Ghash.oddCount a.length t) (hc1 : Local.Ghash.oddCount a.length t ≤ 1024) (mw : List W)
    (hmw : mw.length = Local.Ghash.oddCount a.length t)
    (leftA leftB rightA rightB maskA maskB dstA dstB : Nat) (σA σB : Store) (I : Ideal)
    (hLA : σA.bits leftA = bitsOfWs (Local.Ghash.lefts a t)) (hLB : σB.bits leftB = bitsOfWs (Local.Ghash.lefts b t))
    (hRA : σA.bits rightA = bitsOfW (a.getD 0 0)) (hRB : σB.bits rightB = bitsOfW (b.getD 0 0))
    (hM : σA.bits maskA = bitsOfWs mw) :
    ∃ J, JRet (jointRun E (roundScript n (Local.Ghash.oddCount a.length t) leftA rightA maskA dstA)
        (roundScript n (Local.Ghash.oddCount a.length t) leftB rightB maskB dstB) σA σB I) () () J σA
        (σB.setBits dstB (bitsOf (roundOpened a b t (mw.map Local.Ghash.toBytes)).flatten)) ∧ True := by
  generalize hc : Local.Ghash.oddCount a.length t = c at hc0 hc1 hmw ⊢
  have lA : (bitsOfWs (Local.Ghash.lefts a t)).length = 128 * c := by
    rw [length_bitsOfWs, Local.Ghash.length_lefts, hc]
  have lB : (bitsOfWs (Local.Ghash.lefts b t)).length = 128 * c := by
    rw [length_bitsOfWs, Local.Ghash.length_lefts, hab, hc]
  have lM : (bitsOfWs mw).length = 128 * c := by rw [length_bitsOfWs, hmw]
  have hpick := pick_layout c _ _ _ _ _ lA lB (length_bitsOfW (a.getD 0 0)) (length_bitsOfW (b.getD 0 0)) lM
  -- the blocks, as byte strings
  have hblock : ∀ j, j < c →
      ((bitsOfWs (Local.Ghash.lefts a t)).drop (j * 128)).take 128 ++
        ((bitsOfWs (Local.Ghash.lefts b t)).drop (j * 128)).take 128 ++ bitsOfW (a.getD 0 0) ++
        bitsOfW (b.getD 0 0) ++ ((bitsOfWs mw).drop (j * 128)).take 128 =
      bitsOf (Local.Ghash.toBytes ((Local.Ghash.lefts a t).getD j 0) ++
        Local.Ghash.toBytes ((Local.Ghash.lefts b t).getD j 0) ++ Local.Ghash.toBytes (a.getD 0 0) ++
        Local.Ghash.toBytes (b.getD 0 0) ++ (mw.map Local.Ghash.toBytes).getD j []) := by
    intro j hj
    rw [bitsOfWs_block _ j (by rw [Local.Ghash.length_lefts, hc]; exact hj),
      bitsOfWs_block _ j (by rw [Local.Ghash.length_lefts, hab, hc]; exact hj), bitsOfWs_block _ j (by omega)]
    have : (mw.map Local.Ghash.toBytes).getD j [] = Local.Ghash.toBytes (mw.getD j 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show j < mw.length by omega)]
    rw [this]
    simp only [bitsOfW, bitsOf_append]
  have hwidth : ∀ j, j < c → (bitsOf (Local.Ghash.toBytes ((Local.Ghash.lefts a t).getD j 0) ++
        Local.Ghash.toBytes ((Local.Ghash.lefts b t).getD j 0) ++ Local.Ghash.toBytes (a.getD 0 0) ++
        Local.Ghash.toBytes (b.getD 0 0) ++ (mw.map Local.Ghash.toBytes).getD j [])).length =
      (circuitOf HybridKernel.gcmMultiply).inWidth := by
    intro j hj
    have : (mw.map Local.Ghash.toBytes).getD j [] = Local.Ghash.toBytes (mw.getD j 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show j < mw.length by omega)]
    rw [this, multiply_inWidth]
    simp only [length_bitsOf, List.length_append, Local.Ghash.toBytes_length]
  have hR : runCopies (circuitOf HybridKernel.gcmMultiply) c ((List.range c).flatMap fun j =>
      ((bitsOfWs (Local.Ghash.lefts a t)).drop (j * 128)).take 128 ++
        ((bitsOfWs (Local.Ghash.lefts b t)).drop (j * 128)).take 128 ++ bitsOfW (a.getD 0 0) ++
        bitsOfW (b.getD 0 0) ++ ((bitsOfWs mw).drop (j * 128)).take 128) =
      bitsOf (roundOpened a b t (mw.map Local.Ghash.toBytes)).flatten := by
    refine (runCopies_blocks _ c _ (fun j hj => by rw [hblock j hj]; exact hwidth j hj)).trans ?_
    simp only [bitsOf_flatten, roundOpened, hc, List.map_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    simp only [Function.comp]
    rw [hblock j hj, Tls.circuitOf_eval]
  have hlen : ((List.range c).flatMap fun j =>
      ((bitsOfWs (Local.Ghash.lefts a t)).drop (j * 128)).take 128 ++
        ((bitsOfWs (Local.Ghash.lefts b t)).drop (j * 128)).take 128 ++ bitsOfW (a.getD 0 0) ++
        bitsOfW (b.getD 0 0) ++ ((bitsOfWs mw).drop (j * 128)).take 128).length =
      c * (circuitOf HybridKernel.gcmMultiply).inWidth :=
    flatMap_length c _ _ (fun j hj => by rw [hblock j hj]; exact hwidth j hj)
  unfold roundScript
  have hcc : 0 < c ∧ c ≤ 1024 := ⟨hc0, hc1⟩
  rw [if_pos hcc, if_pos hcc]
  unfold roundBlock
  simp only [seqs_cons, seqs_nil]
  refine ex_both E ⟨n⟩ ⟨n + 1⟩ (128 * c) true false leftA leftB _ _ σA σB I _ _ _ _ _
    (by rw [hLA, lA]) (by rw [hLB, lB]) ?_
  refine ex_both E ⟨n + 2⟩ ⟨n + 3⟩ 128 true false rightA rightB _ _ σA σB _ _ _ _ _ _
    (by rw [hRA, length_bitsOfW]) (by rw [hRB, length_bitsOfW]) ?_
  refine ex_boolInputA E ⟨n + 4⟩ (128 * c) true false maskA maskB _ _ σA σB _ _ _ _ _ _ (by rw [hM, lM]) ?_
  rw [hLA, hLB, hRA, hRB, hM]
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ _ _ _ (localStep_concat5 E ⟨n + 5⟩ ⟨n⟩ ⟨n + 1⟩ ⟨n + 2⟩ ⟨n + 3⟩ ⟨n + 4⟩ _
    _ _ _ _ _ _ (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) rfl) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ _ _ _ (localStep_pick E ⟨n + 6⟩ ⟨n + 5⟩ (layout c) _ _ _ (by ival_tac)
    (by
      rw [List.all_eq_true]
      intro j hj
      have := layout_bound c j hj
      simp only [List.length_append, lA, lB, lM, length_bitsOfW, decide_eq_true_eq]
      omega)
    hpick) ?_
  refine ex_local E _ rfl _ _ σA σB _ _ _ _ _ _ _ (localStep_run_eq E ⟨n + 7⟩ _ c ⟨n + 6⟩ _ _ _ _ hE.multiply
    (by ival_tac) hlen hR) ?_
  refine ex_openToB E ⟨n + 7⟩ masked dstA dstB _ _ σA σB _ _ _ _ _ _ _ (by ival_tac) ?_
  refine ex_local E _ rfl _ _ σA _ _ _ _ _ _ _ _ (localStep_free E _ _) ?_
  exact ex_done E () () σA _ _ _ trivial

/-! ## A whole `ensure` -/

/-- A joint run determines its final stores. -/
theorem jret_unique {α β : Type} {o : Outcome2 α β} {a a' : α} {b b' : β} {J J' : Ideal} {sA sA' sB sB' : Store}
    (h1 : JRet o a b J sA sB) (h2 : JRet o a' b' J' sA' sB') : sA = sA' ∧ sB = sB' :=
  ⟨h1.2.2.1.symm.trans h2.2.2.1, h1.2.2.2.symm.trans h2.2.2.2⟩

theorem setBits_self (σ : Store) (slot : Nat) (v : Bits) : (σ.setBits slot v).bits slot = v := by
  simp [Store.setBits]

theorem wsOfBits_flatten : ∀ (L : List B8), (∀ x ∈ L, x.length = 16) →
    wsOfBits L.length (bitsOf L.flatten) = L.map Local.Ghash.ofBytes
  | [], _ => rfl
  | x :: L, h => by
    have hx : (bitsOf x).length = 128 := by rw [length_bitsOf, h x (by simp)]
    simp only [List.length_cons, wsOfBits, List.flatten_cons, bitsOf_append, List.map_cons]
    rw [List.take_left' hx, List.drop_left' hx, wsOfBits_flatten L (fun y hy => h y (by simp [hy])), wOfBits,
      bytesOf_bitsOf]

/-- **The shares the parties hold after the steps of `TlsBackend.ensure`, each run through
`jointRun`**: the first resharing (`keyShareScript`, A's mask from its store; B's share read from
its slot), the local square from 1 to 2 powers (no odd power: `oddCount 1 2 = 0`), and doubling
rounds (`roundScript` with the inputs the backend stashes; A's odd values its masks, B's read from
its slot with `wsOfBits`, as the backend does). Each step is a RETURNING joint run (`JRet`). -/
inductive EnsureRuns (E : Env) (K : B8) : List W → List W → Prop
  | start (n : Nat) (traffic : BoolH) (m : B8) (maskA maskB dstA dstB : Nat) (σA σB : Store) (I J : Ideal)
      (sA sB : Store) (htn : traffic.id < n) (hm : m.length = 16) (hIt : I.bools traffic.id = some (bitsOf K))
      (hσ : σA.bits maskA = bitsOf m)
      (hrun : JRet (jointRun E (keyShareScript n traffic maskA dstA) (keyShareScript n traffic maskB dstB) σA σB I)
        () () J sA sB) :
      EnsureRuns E K [Local.Ghash.ofBytes m] [wOfBits (sB.bits dstB)]
  | square (a b : List W) (h1 : a.length = 1) (prev : EnsureRuns E K a b) :
      EnsureRuns E K (Local.Ghash.extend a 2 []) (Local.Ghash.extend b 2 [])
  | round (a b : List W) (t n : Nat) (mw : List W) (leftA leftB rightA rightB maskA maskB dstA dstB : Nat)
      (σA σB : Store) (I J : Ideal) (sA sB : Store) (prev : EnsureRuns E K a b) (hm : 1 ≤ a.length)
      (hmt : a.length ≤ t) (ht : t ≤ 2 * a.length) (hc0 : 0 < Local.Ghash.oddCount a.length t)
      (hc1 : Local.Ghash.oddCount a.length t ≤ 1024) (hmw : mw.length = Local.Ghash.oddCount a.length t)
      (hLA : σA.bits leftA = bitsOfWs (Local.Ghash.lefts a t)) (hLB : σB.bits leftB = bitsOfWs (Local.Ghash.lefts b t))
      (hRA : σA.bits rightA = bitsOfW (a.getD 0 0)) (hRB : σB.bits rightB = bitsOfW (b.getD 0 0))
      (hM : σA.bits maskA = bitsOfWs mw)
      (hrun : JRet (jointRun E (roundScript n (Local.Ghash.oddCount a.length t) leftA rightA maskA dstA)
        (roundScript n (Local.Ghash.oddCount a.length t) leftB rightB maskB dstB) σA σB I) () () J sA sB) :
      EnsureRuns E K (Local.Ghash.extend a t mw)
        (Local.Ghash.extend b t (wsOfBits (Local.Ghash.oddCount a.length t) (sB.bits dstB)))

/-- **P-GHASH (a) over a whole `ensure`, through `jointRun`** (gap F20 (a)): after the first resharing
and any sequence of doubling rounds (and the local square), each a returning joint run of the
scripts with the kernels' circuits computing their Lean definitions, A's and B's share lists are XOR
shares of H¹ … Hⁿ (`n` the lists' length) for the traffic block's GHASH key `H = hashKeyOf K`. -/
theorem ensure_shared (E : Env) (hE : GhashLoaded E) (K : B8) (hK : K.length = 60) (a b : List W)
    (h : EnsureRuns E K a b) : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) a.length := by
  induction h with
  | start n traffic m maskA maskB dstA dstB σA σB I J sA sB htn hm hIt hσ hrun =>
    obtain ⟨J', hJ', -⟩ := keyShare_honest E hE n traffic htn K m hK hm maskA maskB dstA dstB σA σB I hIt hσ
    rw [(jret_unique hrun hJ').2, setBits_self, wOfBits, bytesOf_bitsOf]
    exact keyShare_shared K m hK hm
  | square a b h1 prev ih =>
    rw [h1] at ih
    rw [Local.Ghash.extend_length a 2 [] (by omega)]
    refine Local.Ghash.shared_extend a b _ 1 2 [] [] ih (by omega) (by omega) (by omega) (fun i hi ho => ?_)
    omega
  | round a b t n mw leftA leftB rightA rightB maskA maskB dstA dstB σA σB I J sA sB prev hm hmt ht hc0 hc1 hmw
      hLA hLB hRA hRB hM hrun ih =>
    have hab : b.length = a.length := by rw [ih.2.1, ih.1]
    obtain ⟨J', hJ', -⟩ := round_honest E hE n a b t hab hc0 hc1 mw hmw leftA leftB rightA rightB maskA maskB dstA dstB
      σA σB I hLA hLB hRA hRB hM
    have hlen : (roundOpened a b t (mw.map Local.Ghash.toBytes)).length = Local.Ghash.oddCount a.length t := by
      simp [roundOpened]
    rw [(jret_unique hrun hJ').2, setBits_self, ← hlen,
      wsOfBits_flatten _ (fun x hx => by
        simp only [roundOpened, List.mem_map, List.mem_range] at hx
        obtain ⟨j, -, rfl⟩ := hx
        exact multiply_out_length _),
      Local.Ghash.extend_length a t mw (by omega)]
    have hA : Local.Ghash.extend a t mw = Local.Ghash.extend a t ((mw.map Local.Ghash.toBytes).map Local.Ghash.ofBytes) := by
      have hid : ∀ l : List W, l.map (Local.Ghash.ofBytes ∘ Local.Ghash.toBytes) = l := fun l => by
        induction l with
        | nil => rfl
        | cons x l ih => simp only [List.map_cons, Function.comp, Local.Ghash.ofBytes_toBytes, ih]
      rw [List.map_map, hid]
    rw [hA]
    exact round_shared a b _ a.length t _ ih hm hmt ht (fun x hx => by
        simp only [List.mem_map] at hx
        obtain ⟨w, -, rfl⟩ := hx
        exact Local.Ghash.toBytes_length w)
      (by rw [List.length_map, hmw])

/-! ## T3 for a round, A honest: B sees one masked value per copy -/

theorem bitsOfByte_byteOfBits (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    bitsOfByte (byteOfBits b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

/-- Whole bytes of wire bits read back as bytes and again as bits are the same bits. -/
theorem bitsOf_bytesOf : ∀ (s : Bits), s.length % 8 = 0 → bitsOf (bytesOf s) = s
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h => by
    simp only [bytesOf, bitsOf_cons, bitsOf_bytesOf rest (by simp at h; omega), bitsOfByte_byteOfBits]
    rfl
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | [_, _, _, _], h => by simp at h
  | [_, _, _, _, _], h => by simp at h
  | [_, _, _, _, _, _], h => by simp at h
  | [_, _, _, _, _, _, _], h => by simp at h

/-- **Both parties' inputs, the adversary B's chosen**: A's run either stops there (the adversary
aborted or gave the wrong width: nothing released) or goes on from the state holding A's bits and
the adversary's `pb` of the declared width, with the adversary's view unchanged. -/
theorem viewD_both {α : Type} (E : Env) (adv : Adversary) (oa ob : BoolH) (w : Nat) (once rev : Bool) (slot : Nat)
    (s : Script α) (σ : Store) (I : Ideal) (vD : List Release) (hl : (σ.bits slot).length = w) :
    (withAdv E .a adv (seq (.boolInputBoth oa ob w once rev slot) s) σ I vD).viewD = [] ∨
      ∃ pb : Bits, pb.length = w ∧ (withAdv E .a adv (seq (.boolInputBoth oa ob w once rev slot) s) σ I vD).viewD =
        (withAdv E .a adv s σ ((I.setBool oa (σ.bits slot)).setBool ob pb) vD).viewD := by
  simp only [seq, withAdv, fill, hl, if_true, Wire.early, Option.toList_none, List.append_nil]
  split
  · exact Or.inl rfl
  · next part _ =>
    by_cases hb : part.bits.length = w
    · have hs : idealStep E .a (.boolInputBoth oa ob w once rev (σ.bits slot)) part I =
          some ((I.setBool oa (σ.bits slot)).setBool ob part.bits, none, none) := by
        simp [idealStep, hl, hb]
      rw [hs]
      simp only [absorb_none, Option.toList_none, List.append_nil, List.nil_append]
      exact Or.inr ⟨part.bits, hb, rfl⟩
    · have hs : idealStep E .a (.boolInputBoth oa ob w once rev (σ.bits slot)) part I = none := by
        simp [idealStep, hl, hb]
      rw [hs]
      exact Or.inl rfl

/-- **Value-level T3 for a round, A honest** (gap F20): against ANY adversary B, B's view of
`roundScript` is at most ONE release, labelled `ghashMaskedPower`, whose value is, copy by copy,
`gcm-multiply` on A's left share `j`, a left share `lb_j` and a share of H `rb` that B chose
(16 bytes each), A's share of H, and A's fresh mask `j`. With `Ghash.multiply_hides` each copy's
value determines A's mask `j` bijectively, whatever B supplied: B learns nothing about the key
powers (P-GHASH (d)). -/
theorem round_disclosure_A (E : Env) (hE : GhashLoaded E) (adv : Adversary) (σ : Store) (I : Ideal)
    (vD : List Release) (n c leftSlot rightSlot maskSlot dst : Nat) (hc : 0 < c ∧ c ≤ 1024) (la mw : List W) (ra : W)
    (hla : la.length = c) (hmw : mw.length = c) (hL : σ.bits leftSlot = bitsOfWs la) (hR : σ.bits rightSlot = bitsOfW ra)
    (hM : σ.bits maskSlot = bitsOfWs mw) :
    ∃ (lb : List B8) (rb : B8), (∀ x ∈ lb, x.length = 16) ∧ lb.length = c ∧ rb.length = 16 ∧
      (withAdv E .a adv (roundScript n c leftSlot rightSlot maskSlot dst) σ I vD).viewD <+:
        [⟨masked, .bits (bitsOf ((List.range c).map fun j => kernelOut HybridKernel.gcmMultiply
          (Local.Ghash.toBytes (la.getD j 0) ++ lb.getD j [] ++ Local.Ghash.toBytes ra ++ rb ++
            Local.Ghash.toBytes (mw.getD j 0))).flatten)⟩] := by
  -- the continuation after both inputs, for any adversary bits of the right widths
  have lA : (bitsOfWs la).length = 128 * c := by rw [length_bitsOfWs, hla]
  have lM : (bitsOfWs mw).length = 128 * c := by rw [length_bitsOfWs, hmw]
  have key : ∀ pl pr : Bits, pl.length = 128 * c → pr.length = 128 →
      (withAdv E .a adv (seqs [.boolInput ⟨n + 4⟩ .a (128 * c) true false maskSlot,
          .concat ⟨n + 5⟩ [⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩], .pick ⟨n + 6⟩ ⟨n + 5⟩ (layout c),
          .run ⟨n + 7⟩ multiplyName c ⟨n + 6⟩, .openBoolTo ⟨n + 7⟩ .b masked dst, .freeBool ⟨n + 7⟩] (.done ()))
        σ ((((I.setBool ⟨n⟩ (σ.bits leftSlot)).setBool ⟨n + 1⟩ pl).setBool ⟨n + 2⟩ (σ.bits rightSlot)).setBool
          ⟨n + 3⟩ pr) vD).viewD <+:
        [⟨masked, .bits (bitsOf ((List.range c).map fun j => kernelOut HybridKernel.gcmMultiply
          (Local.Ghash.toBytes (la.getD j 0) ++ ((List.range c).map fun i => bytesOf ((pl.drop (i * 128)).take 128)).getD j [] ++
            Local.Ghash.toBytes ra ++ bytesOf pr ++ Local.Ghash.toBytes (mw.getD j 0))).flatten)⟩] := by
    intro pl pr hpl hpr
    have hσM : (σ.bits maskSlot).length = 128 * c := by rw [hM, lM]
    simp only [seqs_cons, seqs_nil]
    refine viewD_seq_boolInput E .a adv (n + 4) (128 * c) maskSlot true false _ σ _ vD _ hσM ?_
    rw [hL, hR, hM]
    have hpick := pick_layout c _ _ _ _ _ lA hpl (length_bitsOfW ra) hpr lM
    have hblock : ∀ j, j < c →
        ((bitsOfWs la).drop (j * 128)).take 128 ++ (pl.drop (j * 128)).take 128 ++ bitsOfW ra ++ pr ++
          ((bitsOfWs mw).drop (j * 128)).take 128 =
        bitsOf (Local.Ghash.toBytes (la.getD j 0) ++
          ((List.range c).map fun i => bytesOf ((pl.drop (i * 128)).take 128)).getD j [] ++
          Local.Ghash.toBytes ra ++ bytesOf pr ++ Local.Ghash.toBytes (mw.getD j 0)) := by
      intro j hj
      have hg : ((List.range c).map fun i => bytesOf ((pl.drop (i * 128)).take 128)).getD j [] =
          bytesOf ((pl.drop (j * 128)).take 128) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
      rw [bitsOfWs_block _ j (by omega), bitsOfWs_block _ j (by omega), hg]
      simp only [bitsOfW, bitsOf_append]
      rw [bitsOf_bytesOf _ (by simp; omega), bitsOf_bytesOf _ (by omega)]
    have hwidth : ∀ j, j < c →
        (((bitsOfWs la).drop (j * 128)).take 128 ++ (pl.drop (j * 128)).take 128 ++ bitsOfW ra ++ pr ++
          ((bitsOfWs mw).drop (j * 128)).take 128).length = (circuitOf HybridKernel.gcmMultiply).inWidth := by
      intro j hj
      rw [multiply_inWidth]
      simp only [List.length_append, List.length_take, List.length_drop, lA, lM, hpl, hpr, length_bitsOfW]
      omega
    have hR' : runCopies (circuitOf HybridKernel.gcmMultiply) c ((List.range c).flatMap fun j =>
        ((bitsOfWs la).drop (j * 128)).take 128 ++ (pl.drop (j * 128)).take 128 ++ bitsOfW ra ++ pr ++
          ((bitsOfWs mw).drop (j * 128)).take 128) =
        bitsOf ((List.range c).map fun j => kernelOut HybridKernel.gcmMultiply
          (Local.Ghash.toBytes (la.getD j 0) ++
            ((List.range c).map fun i => bytesOf ((pl.drop (i * 128)).take 128)).getD j [] ++
            Local.Ghash.toBytes ra ++ bytesOf pr ++ Local.Ghash.toBytes (mw.getD j 0))).flatten := by
      refine (runCopies_blocks _ c _ hwidth).trans ?_
      simp only [bitsOf_flatten, List.map_map]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      simp only [Function.comp]
      rw [hblock j hj, Tls.circuitOf_eval]
    have hlen := flatMap_length c _ _ hwidth
    -- the plain block: concat, pick, run
    rw [show seq (InstrP.concat ⟨n + 5⟩ [⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩])
        (seq (InstrP.pick ⟨n + 6⟩ ⟨n + 5⟩ (layout c)) (seq (InstrP.run ⟨n + 7⟩ multiplyName c ⟨n + 6⟩)
          (seq (InstrP.openBoolTo ⟨n + 7⟩ .b masked dst) (seq (InstrP.freeBool ⟨n + 7⟩) (Script.done ()))))) =
      seqs [InstrP.concat ⟨n + 5⟩ [⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩], InstrP.pick ⟨n + 6⟩ ⟨n + 5⟩ (layout c),
          InstrP.run ⟨n + 7⟩ multiplyName c ⟨n + 6⟩]
        (seq (InstrP.openBoolTo ⟨n + 7⟩ Party.a.other masked dst) (seq (InstrP.freeBool ⟨n + 7⟩) (Script.done ())))
      from rfl]
    refine viewD_locals E .a adv _ σ _ _ (by simp [isLocal]) _ vD (fun I' hI' => ?_)
    rw [runLocal_step E _ _ _ _ (localStep_concat5 E ⟨n + 5⟩ ⟨n⟩ ⟨n + 1⟩ ⟨n + 2⟩ ⟨n + 3⟩ ⟨n + 4⟩ _ _ _ _ _ _ _
        (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) (by ival_tac) rfl),
      runLocal_step E _ _ _ _ (localStep_pick E ⟨n + 6⟩ ⟨n + 5⟩ (layout c) _ _ _ (by ival_tac)
        (by
          rw [List.all_eq_true]
          intro j hj
          have := layout_bound c j hj
          simp only [List.length_append, lA, lM, hpl, hpr, length_bitsOfW, decide_eq_true_eq]
          omega)
        hpick),
      runLocal_step E _ _ _ _ (localStep_run_eq E ⟨n + 7⟩ _ c ⟨n + 6⟩ _ _ _ _ hE.multiply (by ival_tac) hlen hR'),
      runLocal_nil, Option.some.injEq] at hI'
    subst hI'
    refine viewD_seq_openBoolTo E .a adv _ masked dst _ σ _ vD [] _ (by ival_tac) ?_
    exact silent_prefix E .a adv _ (Silent.seq rfl (Silent.done _)) _ _ _ _
  have hbl : ∀ s : Bits, s.length = 128 → (bytesOf s).length = 16 := by
    intro s hs
    have h := congrArg List.length (bitsOf_bytesOf s (by omega))
    rw [length_bitsOf, hs] at h
    omega
  have dflt : (∀ x ∈ List.replicate c (List.replicate 16 (0 : BitVec 8)), x.length = 16) ∧
      (List.replicate c (List.replicate 16 (0 : BitVec 8))).length = c ∧ (List.replicate 16 (0 : BitVec 8)).length = 16 := by
    refine ⟨fun x hx => ?_, by simp, by simp⟩
    rw [(List.mem_replicate.mp hx).2, List.length_replicate]
  unfold roundScript
  rw [if_pos hc]
  unfold roundBlock
  rw [seqs_cons, seqs_cons]
  rcases viewD_both E adv ⟨n⟩ ⟨n + 1⟩ (128 * c) true false leftSlot _ σ I vD (by rw [hL, lA]) with h1 | ⟨pl, hpl, h1⟩
  · exact ⟨_, _, dflt.1, dflt.2.1, dflt.2.2, by rw [h1]; exact List.nil_prefix⟩
  rcases viewD_both E adv ⟨n + 2⟩ ⟨n + 3⟩ 128 true false rightSlot _ σ _ vD (by rw [hR, length_bitsOfW])
    with h2 | ⟨pr, hpr, h2⟩
  · exact ⟨_, _, dflt.1, dflt.2.1, dflt.2.2, by rw [h1, h2]; exact List.nil_prefix⟩
  refine ⟨(List.range c).map (fun i => bytesOf ((pl.drop (i * 128)).take 128)), bytesOf pr, fun x hx => ?_,
    by simp, hbl pr hpr, ?_⟩
  · simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hbl _ (by simp; omega)
  · rw [h1, h2]
    exact key pl pr hpl hpr

/-! ## P-GHASH (e) for the scripts: a deviating half -/

theorem xor_cancel_bytes : ∀ (X Y Z : B8), X.length = Y.length → X.length = Z.length →
    Aes.addRoundKey Gcm.concrete.aes X Y = Aes.addRoundKey Gcm.concrete.aes X Z → Y = Z
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _ => by simp at h
  | x :: X, y :: Y, z :: Z, h1, h2, h => by
    simp only [Aes.addRoundKey, List.zipWith_cons_cons, List.cons.injEq] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    have hyz : y = z := by
      have e := congrArg (x ^^^ ·) h.1
      change x ^^^ (x ^^^ y) = x ^^^ (x ^^^ z) at e
      rwa [← BitVec.xor_assoc, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.zero_xor] at e
    rw [hyz, xor_cancel_bytes X Y Z h1 h2 h.2]

theorem toBytes_xor_ne (x δ : W) (hδ : δ ≠ 0) : Local.Ghash.toBytes (x ^^^ δ) ≠ Local.Ghash.toBytes x := by
  intro h
  have e := congrArg Local.Ghash.ofBytes h
  rw [Local.Ghash.ofBytes_toBytes, Local.Ghash.ofBytes_toBytes] at e
  apply hδ
  have e2 := congrArg (x ^^^ ·) e
  change x ^^^ (x ^^^ δ) = x ^^^ x at e2
  rwa [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] at e2

/-- `gcm-tag` on pad ‖ half ‖ half (16 bytes each) is their XOR. -/
theorem tag_out (P A B : B8) (hp : P.length = 16) (ha : A.length = 16) (hb : B.length = 16) :
    kernelOut HybridKernel.gcmTag (P ++ (A ++ B)) =
      Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes P A) B := by
  obtain ⟨o, ho⟩ := Tls.tag_outputs
  have hk := outputs_one _ o ho (P ++ (A ++ B))
  rw [HybridKernel.gcmTag_spec] at hk
  simp only [List.cons.injEq, and_true] at hk
  rw [← hk, inputValue_assignOf _ 0 16 (by simp; omega), inputValue_assignOf _ 16 16 (by simp; omega),
    inputValue_assignOf _ 32 16 (by simp; omega), List.drop_zero, List.take_left' hp, List.drop_left' hp,
    List.take_left' ha, ← List.append_assoc, List.drop_left' (by simp; omega), List.take_of_length_le (by omega)]

/-- **P-GHASH (e), the seal** (`tagScript`): if one party's half deviates from its honest value by a
nonzero `δ`, the tag the script opens is not the honest one; with `seal_is_record`, the record the
parties produce is then NOT `TlsRecord.sealCore` (`seal_deviation_rejected`), so the server rejects
it. -/
theorem tag_deviation (P : B8) (hp : P.length = 16) (xa xb δ : W) (hδ : δ ≠ 0) :
    kernelOut HybridKernel.gcmTag (P ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes (xb ^^^ δ))) ≠
      kernelOut HybridKernel.gcmTag (P ++ (Local.Ghash.toBytes xa ++ Local.Ghash.toBytes xb)) := by
  rw [tag_out _ _ _ hp (Local.Ghash.toBytes_length _) (Local.Ghash.toBytes_length _),
    tag_out _ _ _ hp (Local.Ghash.toBytes_length _) (Local.Ghash.toBytes_length _)]
  intro h
  refine toBytes_xor_ne xb δ hδ (xor_cancel_bytes _ _ _ ?_ ?_ h)
  · simp [Aes.addRoundKey, hp, Local.Ghash.toBytes_length]
  · simp [Aes.addRoundKey, hp, Local.Ghash.toBytes_length]

theorem seal_deviation_rejected (kind size padding : Nat) (K seqB C : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (hC : C.length = size) (a b : List W) (nPow : Nat) (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow)
    (hn : Local.Ghash.needed 5 (Tls.innerLength size padding) ≤ nPow) (δ : W) (hδ : δ ≠ 0) :
    let out := kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))
    let hc := out.take (5 + Tls.innerLength size padding)
    let pad := (out.drop (5 + Tls.innerLength size padding)).take 16
    hc ++ kernelOut HybridKernel.gcmTag (pad ++ (Local.Ghash.toBytes (Local.Ghash.half a (hc.take 5) (hc.drop 5)) ++
        Local.Ghash.toBytes (Local.Ghash.half b (hc.take 5) (hc.drop 5) ^^^ δ))) ≠
      TlsRecord.sealCore Gcm.concrete ((K.drop 32).take 16) ((K.drop 48).take 12) seqB C kind padding := by
  have hrec := Tls.seal_is_record kind size padding K seqB C hK hs hC a b nPow hsh hn
  dsimp only at hrec ⊢
  have hpl : (((kernelOut (HybridKernel.tlsSealCtr kind size padding) (K ++ (seqB ++ C))).drop
      (5 + Tls.innerLength size padding)).take 16).length = 16 := by
    obtain ⟨hout, -⟩ := Tls.sealCtr_kernelOut kind size padding K seqB C hK hs hC
    have hH := Tls.header_length (Tls.innerLength size padding + 16)
    have hCT : (HybridKernel.ctrOf K seqB (TlsRecord.inner Gcm.concrete C kind padding)).length =
        Tls.innerLength size padding := by
      rw [HybridKernel.ctrOf_length _ _ _ hK, Tls.inner_length, hC]
    rw [hout]
    simp only [List.length_take, List.length_drop, List.length_append, hH, hCT, Tls.padOf_length K seqB hK]
    omega
  intro h
  rw [← hrec] at h
  exact tag_deviation _ hpl _ _ δ hδ (List.append_cancel_left h)

/-- `gcm-check` on traffic ‖ sequence ‖ half ‖ half ‖ tag (60, 8, 16, 16, 16 bytes). -/
theorem check_out (K seqB xa xb tag : B8) (hK : K.length = 60) (hs : seqB.length = 8) (ha : xa.length = 16)
    (hb : xb.length = 16) (ht : tag.length = 16) :
    kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (xa ++ (xb ++ tag)))) =
      [if Aes.addRoundKey Gcm.concrete.aes (Aes.addRoundKey Gcm.concrete.aes (HybridKernel.padOf K seqB) xa) xb = tag
        then 255 else 0] := by
  have e1 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 0 60 = K := by
    rw [inputValue_assignOf _ _ _ (by simp; omega), List.drop_zero, List.take_left' hK]
  have e2 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 60 8 = seqB := by
    rw [inputValue_assignOf _ _ _ (by simp; omega), List.drop_left' hK, List.take_left' hs]
  have e3 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 68 16 = xa := by
    rw [inputValue_assignOf _ _ _ (by simp; omega), ← List.append_assoc, List.drop_left' (by simp; omega),
      List.take_left' ha]
  have e4 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 84 16 = xb := by
    rw [inputValue_assignOf _ _ _ (by simp; omega),
      show K ++ (seqB ++ (xa ++ (xb ++ tag))) = (K ++ seqB ++ xa) ++ (xb ++ tag) by simp,
      List.drop_left' (by simp; omega), List.take_left' hb]
  have e5 : HybridKernel.inputValue (assignOf (K ++ (seqB ++ (xa ++ (xb ++ tag))))) 100 16 = tag := by
    rw [inputValue_assignOf _ _ _ (by simp; omega),
      show K ++ (seqB ++ (xa ++ (xb ++ tag))) = (K ++ seqB ++ xa ++ xb) ++ tag by simp,
      List.drop_left' (by simp; omega), List.take_of_length_le (by omega)]
  obtain ⟨o, ho⟩ : ∃ o, HybridKernel.gcmCheck.outputs = [o] := ⟨_, rfl⟩
  have hk := outputs_one _ o ho (K ++ (seqB ++ (xa ++ (xb ++ tag))))
  rw [HybridKernel.gcmCheck_spec, e1, e2, e3, e4, e5] at hk
  simp only [List.cons.injEq, and_true] at hk
  rw [← hk]

/-- **P-GHASH (e), the open** (`openScript`'s tag check): with honest halves of shared key powers
except that one half deviates by a nonzero `δ`, the GENUINE tag (GCM's tag of the record) is
refused: the acceptance byte bound to `tls-open-typed` is 0, so the typed open releases only the
rejection (`open_rejected`). -/
theorem check_deviation (K seqB hdr ct : B8) (hK : K.length = 60) (hs : seqB.length = 8) (a b : List W) (nPow : Nat)
    (hsh : Local.Ghash.Shared a b (HybridKernel.hashKeyOf K) nPow) (hn : (Local.Ghash.blocks hdr ct).length ≤ nPow)
    (δ : W) (hδ : δ ≠ 0) :
    kernelOut HybridKernel.gcmCheck (K ++ (seqB ++ (Local.Ghash.toBytes (Local.Ghash.half a hdr ct) ++
        (Local.Ghash.toBytes (Local.Ghash.half b hdr ct ^^^ δ) ++
          Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB))))) = [0] := by
  have hpad := Tls.padOf_length K seqB hK
  have hg : (Aes.addRoundKey Gcm.concrete.aes (HybridKernel.ghashOf K hdr ct) (HybridKernel.padOf K seqB)).length = 16 := by
    rw [← Local.Ghash.halves_xor K hdr ct a b nPow hsh hn]
    simp [Aes.addRoundKey, Local.Ghash.toBytes_length, hpad]
  rw [check_out _ _ _ _ _ hK hs (Local.Ghash.toBytes_length _) (Local.Ghash.toBytes_length _) hg, if_neg]
  intro h
  rw [← Local.Ghash.halves_xor K hdr ct a b nPow hsh hn,
    ← HybridKernel.xor_rotate (HybridKernel.padOf K seqB) (Local.Ghash.toBytes (Local.Ghash.half a hdr ct))
      (Local.Ghash.toBytes (Local.Ghash.half b hdr ct))] at h
  refine toBytes_xor_ne (Local.Ghash.half b hdr ct) δ hδ (xor_cancel_bytes
    (Aes.addRoundKey Gcm.concrete.aes (HybridKernel.padOf K seqB) (Local.Ghash.toBytes (Local.Ghash.half a hdr ct)))
    (Local.Ghash.toBytes (Local.Ghash.half b hdr ct ^^^ δ)) (Local.Ghash.toBytes (Local.Ghash.half b hdr ct)) ?_ ?_ h)
  · simp [Aes.addRoundKey, hpad, Local.Ghash.toBytes_length]
  · simp [Aes.addRoundKey, hpad, Local.Ghash.toBytes_length]

end TlsMpc.Node.Flows.Ghash
