import TlsMpc.FieldProgramsV3

/-!
# Compiled field programs: when a translated artifact cannot abort (PROOF_GAPS F22a)

Stage S11. `FieldDagV3.eval_ofArtifact_some` says a translated artifact never aborts (with nonzero
masks) when the denominators of the COMPILED node list are nonzero (`DivisorsNonzero … a.nodes`).
The node list is the output of `compileAll`, whose cache uses native hashing, so no per-program
statement about it can be computed in the kernel. This file proves, once for every compilation the
validator accepts, that the compiled nodes contain only subterms of the source expressions
(`compileAll_good`: an invariant of the memoising generator `FieldDag.generate`, through the
`Std.HashMap` lemmas), so the condition moves to the SOURCE expressions:

  * `DivOk input e`: every division `a / b` inside `e` has `b ≠ 0` on `input` (a structural
    predicate, proved per program from the program's own definition);
  * `compileAll_divisors`: `compileAll es = some a` and every `e ∈ es` is `DivOk` ⇒
    `DivisorsNonzero input #[] a.nodes`;
  * `Decl.live`: a declaration's V3 program (`Decl.program`) on such an input never aborts with
    masks that are nonzero below its mask count (the masks above it are never read);
  * `Decl.outputs_length`: its output count is the declaration's expression count.

No program is evaluated and no DAG is computed: everything is generic in `es`.
-/

namespace TlsMpc.FieldDag.Compiled

open TlsMpc.FieldDag

/-! ## Divisions of a source expression -/

/-- Every division `a / b` inside `e` has a nonzero denominator on `input`. -/
def DivOk (input : Nat → F) : Expr → Prop
  | .input _ => True
  | .const _ => True
  | .bin op a b => DivOk input a ∧ DivOk input b ∧ (op = .div → b.eval input ≠ 0)

theorem divOk_bin {input : Nat → F} {op : Bin} {a b : Expr} :
    DivOk input (.bin op a b) ↔ DivOk input a ∧ DivOk input b ∧ (op = .div → b.eval input ≠ 0) := by
  simp only [DivOk]

/-- The subterms of a list of expressions. -/
inductive InExprs (es : List Expr) : Expr → Prop
  | top {e : Expr} : e ∈ es → InExprs es e
  | left {op : Bin} {a b : Expr} : InExprs es (.bin op a b) → InExprs es a
  | right {op : Bin} {a b : Expr} : InExprs es (.bin op a b) → InExprs es b

theorem InExprs.divOk {input : Nat → F} {es : List Expr} (h : ∀ e ∈ es, DivOk input e) {e : Expr}
    (he : InExprs es e) : DivOk input e := by
  induction he with
  | top m => exact h _ m
  | left _ ih => exact (divOk_bin.mp ih).1
  | right _ ih => exact (divOk_bin.mp ih).2.1

/-! ## Runs of node lists -/

theorem step_size {B : Type} (ops : Ops B) (V : Array B) (n : Node) : (FieldDag.step ops V n).size = V.size + 1 := by
  cases n <;> simp [FieldDag.step]

theorem step_lt {B : Type} (ops : Ops B) (V : Array B) (n : Node) (i : Nat) (hi : i < V.size) :
    (FieldDag.step ops V n)[i]? = V[i]? := by
  cases n <;> simp only [FieldDag.step, Array.getElem?_push, if_neg (Nat.ne_of_lt hi)]

theorem run_prefix {B : Type} (ops : Ops B) : ∀ (ns : List Node) (V : Array B) (i : Nat), i < V.size →
    (run ops ns V)[i]? = V[i]?
  | [], _, _, _ => rfl
  | n :: ns, V, i, hi => by
    show (run ops ns (FieldDag.step ops V n))[i]? = _
    rw [run_prefix ops ns _ i (by rw [step_size]; omega), step_lt ops V n i hi]

theorem run_append {B : Type} (ops : Ops B) (ns : List Node) (n : Node) (V : Array B) :
    run ops (ns ++ [n]) V = FieldDag.step ops (run ops ns V) n := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem run_size {B : Type} (ops : Ops B) : ∀ (ns : List Node) (V : Array B), (run ops ns V).size = V.size + ns.length
  | [], _ => rfl
  | n :: ns, V => by
    show (run ops ns (FieldDag.step ops V n)).size = _
    rw [run_size ops ns, step_size, List.length_cons]
    omega

theorem get_map (input : Nat → F) (V : Array Expr) (b : Nat) :
    V3.get (V.map (Expr.eval input)) b = (V[b]?.getD (.const 0)).eval input := by
  unfold V3.get
  rw [Array.getElem?_map]
  cases V[b]? <;> rfl

/-- **The denominators of a node list are nonzero** when every expression its symbolic run
produces is `DivOk`. -/
theorem divisors_of_good (input : Nat → F) :
    ∀ (ns : List Node) (V : Array Expr),
      (∀ (i : Nat) (e : Expr), (run symbolic ns V)[i]? = some e → DivOk input e) →
      V3.DivisorsNonzero input (V.map (Expr.eval input)) ns
  | [], _, _ => trivial
  | n :: ns, V, h => by
    refine ⟨?_, ?_⟩
    · cases n with
      | input i => trivial
      | const c => trivial
      | bin op a b =>
        cases op with
        | add => trivial
        | sub => trivial
        | mul => trivial
        | div =>
          show V3.get (V.map (Expr.eval input)) b ≠ 0
          have hp : (run symbolic ns (FieldDag.step symbolic V (.bin .div a b)))[V.size]? =
              some (.bin .div (V[a]?.getD (.const 0)) (V[b]?.getD (.const 0))) := by
            rw [run_prefix symbolic ns _ V.size (by rw [step_size]; omega)]
            exact Array.getElem?_push_size
          have hok := divOk_bin.mp (h V.size _ hp)
          rw [get_map]
          exact hok.2.2 rfl
    · rw [← step_map input V n]
      exact divisors_of_good input ns _ h

/-! ## The memoising generator keeps only subterms -/

/-- The symbolic values of a draft's nodes. -/
def symOf (s : Draft) : Array Expr := run symbolic s.nodes.toList

/-- Every node of the draft is a subterm of `es`, and the cache maps an expression to a node that
computes it. -/
structure GenInv (es : List Expr) (s : Draft) : Prop where
  good : ∀ (i : Nat) (e : Expr), (symOf s)[i]? = some e → InExprs es e
  cache : ∀ (e : Expr) (r : Nat), s.cache[e]? = some r → (symOf s)[r]? = some e
  size : (symOf s).size = s.nodes.size

/-- The draft `s'` extends `s`. -/
def DExt (s s' : Draft) : Prop := ∀ (i : Nat) (e : Expr), (symOf s)[i]? = some e → (symOf s')[i]? = some e

theorem ext_refl (s : Draft) : DExt s s := fun _ _ h => h

theorem ext_trans {s s' s'' : Draft} (h1 : DExt s s') (h2 : DExt s' s'') : DExt s s'' := fun i e h => h2 i e (h1 i e h)

theorem lt_of_getElem? {α : Type} {V : Array α} {i : Nat} {e : α} (h : V[i]? = some e) : i < V.size := by
  rcases Nat.lt_or_ge i V.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h
    cases h

theorem insert_inv (es : List Expr) (s : Draft) (e : Expr) (node : Node) (h : GenInv es s) (he : InExprs es e)
    (hn : FieldDag.step symbolic (symOf s) node = (symOf s).push e) :
    GenInv es (FieldDag.insert s e node).2 ∧ (symOf (FieldDag.insert s e node).2)[(FieldDag.insert s e node).1]? = some e ∧
      DExt s (FieldDag.insert s e node).2 := by
  have hs : symOf (FieldDag.insert s e node).2 = (symOf s).push e := by
    show run symbolic (s.nodes.push node).toList = _
    rw [Array.toList_push, run_append]
    exact hn
  have hsz := h.size
  refine ⟨⟨fun i x hx => ?_, fun x r hx => ?_, ?_⟩, ?_, fun i x hx => ?_⟩
  · rw [hs, Array.getElem?_push] at hx
    split at hx
    · cases hx
      exact he
    · exact h.good i x hx
  · rw [hs]
    simp only [FieldDag.insert, Std.HashMap.getElem?_insert] at hx
    split at hx
    · next hb =>
      cases hx
      have hxe : e = x := eq_of_beq hb
      subst hxe
      rw [← hsz]
      exact Array.getElem?_push_size
    · have := h.cache x r hx
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt (lt_of_getElem? this))]
      exact this
  · rw [hs, Array.size_push, hsz]
    show _ = (s.nodes.push node).size
    rw [Array.size_push]
  · rw [hs]
    show ((symOf s).push e)[s.nodes.size]? = some e
    rw [← hsz]
    exact Array.getElem?_push_size
  · rw [hs, Array.getElem?_push, if_neg (Nat.ne_of_lt (lt_of_getElem? hx))]
    exact hx

theorem generate_inv (es : List Expr) : ∀ (e : Expr) (s : Draft), GenInv es s → InExprs es e →
    GenInv es (generate e s).2 ∧ (symOf (generate e s).2)[(generate e s).1]? = some e ∧ DExt s (generate e s).2 := by
  intro e
  induction e with
  | input i =>
    intro s h he
    unfold generate
    split
    · next r hr => exact ⟨h, h.cache _ r hr, ext_refl s⟩
    · exact insert_inv es s _ _ h he rfl
  | const n =>
    intro s h he
    unfold generate
    split
    · next r hr => exact ⟨h, h.cache _ r hr, ext_refl s⟩
    · exact insert_inv es s _ _ h he rfl
  | bin op a b iha ihb =>
    intro s h he
    unfold generate
    split
    · next r hr => exact ⟨h, h.cache _ r hr, ext_refl s⟩
    · obtain ⟨ia, ra_eq, ea⟩ := iha s h (InExprs.left he)
      rcases hga : generate a s with ⟨ra, sa⟩
      rw [hga] at ia ra_eq ea
      obtain ⟨ib, rb_eq, eb⟩ := ihb sa ia (InExprs.right he)
      rcases hgb : generate b sa with ⟨rb, sb⟩
      rw [hgb] at ib rb_eq eb
      simp only [hga, hgb]
      dsimp only at ra_eq ea ib rb_eq eb
      have hra : (symOf sb)[ra]? = some a := eb ra a ra_eq
      obtain ⟨i1, i2, i3⟩ := insert_inv es sb (.bin op a b) (.bin op ra rb) ib he (by
        show (symOf sb).push (Expr.bin op ((symOf sb)[ra]?.getD (Expr.const 0)) ((symOf sb)[rb]?.getD (Expr.const 0))) = _
        rw [hra, rb_eq]
        rfl)
      exact ⟨i1, i2, ext_trans ea (ext_trans eb i3)⟩

theorem generateAll_inv (es : List Expr) : ∀ (l : List Expr) (s : Draft), GenInv es s → (∀ e ∈ l, InExprs es e) →
    GenInv es (generateAll l s).2
  | [], _, h, _ => h
  | e :: rest, s, h, hl => by
    have g := generate_inv es e s h (hl e (by simp))
    unfold generateAll
    rcases hg : generate e s with ⟨r, s1⟩
    rw [hg] at g
    have ih := generateAll_inv es rest s1 g.1 (fun x hx => hl x (by simp [hx]))
    rcases hr : generateAll rest s1 with ⟨rs, s2⟩
    rw [hr] at ih
    simp only [hr]
    exact ih

theorem inv_empty (es : List Expr) : GenInv es {} := by
  refine ⟨fun i e he => ?_, fun e r he => ?_, rfl⟩
  · simp [symOf, run] at he
  · simp at he

/-- **Every node of an accepted compilation computes a subterm of the source expressions.** -/
theorem compileAll_good (es : List Expr) (a : MultiArtifact) (hc : compileAll es = some a) :
    ∀ (i : Nat) (e : Expr), (run symbolic a.nodes)[i]? = some e → InExprs es e := by
  unfold compileAll at hc
  dsimp only at hc
  cases hg : generateAll (ShareCommon.shareCommon' es) {} with
  | mk outputs draft =>
    rw [hg] at hc
    dsimp only at hc
    split at hc
    · cases hc
      have := generateAll_inv es (ShareCommon.shareCommon' es) {} (inv_empty es) (fun e he => .top he)
      rw [hg] at this
      exact this.good
    · contradiction

/-- **The compiled denominators are nonzero when the source divisions are** (`DivOk`). -/
theorem compileAll_divisors (input : Nat → F) (es : List Expr) (a : MultiArtifact) (hc : compileAll es = some a)
    (hd : ∀ e ∈ es, DivOk input e) : V3.DivisorsNonzero input #[] a.nodes := by
  have := divisors_of_good input a.nodes #[] (fun i e he => (compileAll_good es a hc i e he).divOk hd)
  simpa using this

/-! ## Liveness of a translated program, masks bounded -/

open TlsMpc.FieldDag.V3 (FieldInverse Program Row State ofNodes divCount ofArtifact)

theorem runFrom_ofNodes_live (hinv : FieldInverse) (rows : List Row) (input mask : Nat → F) :
    ∀ (ns : List Node) (k : Nat) (s : State), (∀ j, k ≤ j → j < k + divCount ns → mask j ≠ 0) →
      V3.DivisorsNonzero input s.vals ns → ∃ s', (ofNodes k ns).foldlM (V3.step rows input mask) s = some s' := by
  intro ns
  induction ns with
  | nil => intro k s _ _; exact ⟨s, rfl⟩
  | cons n ns ih =>
    intro k s hm hd
    obtain ⟨h0, hd⟩ := hd
    rw [V3.fieldDag_step] at hd
    cases n with
    | input i =>
      have e : divCount (.input i :: ns) = divCount ns := rfl
      rw [e] at hm
      simp only [ofNodes, List.foldlM_cons, V3.step, Option.bind_eq_bind, Option.bind_some]
      exact ih k _ hm hd
    | const c =>
      have e : divCount (.const c :: ns) = divCount ns := rfl
      rw [e] at hm
      simp only [ofNodes, List.foldlM_cons, V3.step, Option.bind_eq_bind, Option.bind_some]
      exact ih k _ hm hd
    | bin op a b =>
      cases op with
      | add =>
        have e : divCount (.bin .add a b :: ns) = divCount ns := rfl
        rw [e] at hm
        simp only [ofNodes, List.foldlM_cons, V3.step, Option.bind_eq_bind, Option.bind_some]
        exact ih k _ hm hd
      | sub =>
        have e : divCount (.bin .sub a b :: ns) = divCount ns := rfl
        rw [e] at hm
        simp only [ofNodes, List.foldlM_cons, V3.step, Option.bind_eq_bind, Option.bind_some]
        exact ih k _ hm hd
      | mul =>
        have e : divCount (.bin .mul a b :: ns) = divCount ns := rfl
        rw [e] at hm
        simp only [ofNodes, List.foldlM_cons, V3.step, Option.bind_eq_bind, Option.bind_some]
        exact ih k _ hm hd
      | div =>
        have e : divCount (.bin .div a b :: ns) = divCount ns + 1 := rfl
        rw [e] at hm
        have ho : V3.get s.vals b * mask k ≠ 0 := V3.mul_ne_zero hinv h0 (hm k (Nat.le_refl k) (by omega))
        simp only [ofNodes, List.foldlM_cons, V3.step, Option.bind_eq_bind, if_neg ho, Option.bind_some]
        refine ih (k + 1) _ (fun j h1 h2 => hm j (by omega) (by omega)) ?_
        simp only [Bin.eval] at hd
        rw [V3.inverseFast_eq, V3.masked_div hinv _ _ _ ho]
        exact hd

/-- With masks nonzero below the mask count, a translated artifact aborts only on a zero
denominator of the compiled nodes. -/
theorem eval_ofArtifact_live (hinv : FieldInverse) (inputs : Nat) (a : MultiArtifact)
    (marks : Nat → V3.OMark) (input mask : Nat → F) (hm : ∀ j, j < divCount a.nodes → mask j ≠ 0)
    (hd : V3.DivisorsNonzero input #[] a.nodes) :
    (V3.eval (ofArtifact inputs a marks) input mask).isSome := by
  obtain ⟨s, hs⟩ := runFrom_ofNodes_live hinv (ofNodes 0 a.nodes) input mask a.nodes 0 {}
    (fun j _ h2 => hm j (by omega)) hd
  simp [V3.eval, V3.runFrom, ofArtifact, hs]

/-! ## Declarations -/

/-- **A declaration's V3 program never aborts on an input where its source divisions are
nonzero**, with any masks that are nonzero below its mask count. -/
theorem Decl.live (hinv : FieldInverse) (d : FieldProgramsV3.Decl) (p : Program) (hp : d.program = some p)
    (input : Nat → F) (hd : ∀ e ∈ d.exprs, DivOk input e) (mask : Nat → F)
    (hm : ∀ j, j < p.masks → mask j ≠ 0) : (V3.eval p input mask).isSome := by
  obtain ⟨a, ha, rfl⟩ := FieldProgramsV3.Decl.program_eq hp
  exact eval_ofArtifact_live hinv _ a _ input mask hm (compileAll_divisors input d.exprs a ha hd)

/-- A declaration's V3 program has one output per source expression. -/
theorem Decl.outputs_length (d : FieldProgramsV3.Decl) (p : Program) (hp : d.program = some p) :
    p.outputs.length = d.exprs.length := by
  obtain ⟨a, ha, rfl⟩ := FieldProgramsV3.Decl.program_eq hp
  have := congrArg List.length (FieldDag.compileAll_correct d.exprs a ha (fun _ => 0))
  simp only [List.length_map] at this
  simp [ofArtifact, this]

end TlsMpc.FieldDag.Compiled
