import TlsMpc.Node.Flows.ContactsPrepare

/-!
# J8: the identity scalar's swap-bit handles survive every joined agreement

STACK_NOTES J8. Op 55 (`Account.openStep`) and op 46 (`Account.admitStep`) leave the identity
scalar's 252 ladder swap bits as FIELD handles (`Account.State.identity`); the joined agreements
(`Join.receiveAgree`, used by S14's receive, S15's `refreshOps` agree, op 66's static agreement and
the sender key, `Flows/ContactsPrepare.lean`) take them as the job's swap bits
(`Join.AgreeSlots.swaps`, `Join.jobBits_swaps`) instead of a coins slot. The identity serves every
message of the session, so no agreement may lose them. In the engine (Engine.lean design note
item 5, D3) a field handle is lost in exactly two ways: `freeField`, or being a MASK of a `program`
instruction (consumed); field handles have no `once`, a `program`'s INPUTS are only required live
(and their marks do not flow to its outputs), so as ladder inputs (`Curve.agree`, `x25519-fast`'s
`ins`) the handles stay. (Their marks: `bitsToField`'s outputs, private; nothing opens them.)

PROVED (`receiveAgree_spares`): along every branch of `Join.receiveAgree sl jobs` run from a state
`st`, no instruction frees or consumes a handle of `S`, for any `S` whose ids are below the state's
field counter (allocated before: op 55 ran earlier) and that holds no field handle of a word mask
of the state's pool (the pool's masks are the only older handles the run frees: P-F2W frees its
mask). The proof follows the run (`PostG`): every handle the run frees or consumes is one it
allocated (at or above the counter) or a pool mask's field handle. Corollaries for the users:
`senderPublicG_spares` (J12) and `agreeG_spares` (S15's agreement step).
-/

namespace TlsMpc.Node.Flows.JoinIdentity

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs)
open TlsMpc.Node.Flows.Receive (Gen St Job)
open TlsMpc.Node.Flows.Run (openFieldThen sayThen)
open TlsMpc.Node.Flows.Join

/-- The field handles an instruction frees or consumes. -/
def consumes : Instr → List FieldH
  | .freeField h => [h]
  | .program _ _ _ masks _ _ => masks
  | _ => []

/-- A handle the run may lose: allocated by it (at or above `c`), or a pool mask's (`P0`). -/
def Fine (c : Nat) (P0 : List FieldH) (h : FieldH) : Prop := c ≤ h.id ∨ h ∈ P0

def FineI (c : Nat) (P0 : List FieldH) (i : Instr) : Prop := ∀ h ∈ consumes i, Fine c P0 h

/-! ## Every instruction, and a property of the result -/

inductive Post {α : Type} (P : Instr → Prop) (Q : α → Prop) : Script α → Prop
  | done {a : α} : Q a → Post P Q (.done a)
  | abort (r : String) : Post P Q (.abort r)
  | step {i : Instr} {k : Reply → Script α} : P i → (∀ r, Post P Q (k r)) → Post P Q (.step i k)

namespace Post

variable {α β : Type} {P : Instr → Prop}

theorem bind {Q : α → Prop} {R : β → Prop} {s : Script α} {f : α → Script β} (h : Post P Q s)
    (hf : ∀ a, Q a → Post P R (f a)) : Post P R (s.bind f) := by
  induction h with
  | done hq => exact hf _ hq
  | abort r => exact .abort r
  | step hi _ ih => exact .step hi ih

theorem monoQ {Q Q' : α → Prop} {s : Script α} (h : Post P Q s) (hq : ∀ a, Q a → Q' a) : Post P Q' s := by
  induction h with
  | done hp => exact .done (hq _ hp)
  | abort r => exact .abort r
  | step hi _ ih => exact .step hi ih

theorem every {P' : Instr → Prop} {Q : α → Prop} {s : Script α} (h : Post P Q s) (hp : ∀ i, P i → P' i) :
    Every P' s := by
  induction h with
  | done _ => exact Every.done _
  | abort r => exact Every.abort r
  | step hi _ ih => exact Every.step _ _ (hp _ hi) ih

theorem seq {Q : α → Prop} {i : Instr} {s : Script α} (hi : P i) (h : Post P Q s) : Post P Q (Contacts.seq i s) := by
  refine .step hi fun r => ?_
  cases r with
  | unit => exact h
  | bits _ => exact .abort _
  | elems _ => exact .abort _
  | exchanged _ _ => exact .abort _

theorem seqs {Q : α → Prop} {s : Script α} : ∀ (is : List Instr), (∀ i ∈ is, P i) → Post P Q s →
    Post P Q (Contacts.seqs is s)
  | [], _, h => h
  | i :: is, hi, h => seq (hi i (by simp)) (seqs is (fun j hj => hi j (by simp [hj])) h)

theorem openField {Q : α → Prop} {hs : List FieldH} {l : Label} {k : List TlsMpc.FieldDag.F → Script α}
    (hi : P (.openField hs l)) (hk : ∀ v, Post P Q (k v)) : Post P Q (openFieldThen hs l k) := by
  refine .step hi fun r => ?_
  cases r with
  | elems v => exact hk v
  | unit => exact .abort _
  | bits _ => exact .abort _
  | exchanged _ _ => exact .abort _

theorem openBool {Q : α → Prop} {h : BoolH} {l : Label} {k : Bits → Script α}
    (hi : P (.openBool h l)) (hk : ∀ v, Post P Q (k v)) : Post P Q (Contacts.openThen h l k) := by
  refine .step hi fun r => ?_
  cases r with
  | bits v => exact hk v
  | unit => exact .abort _
  | elems _ => exact .abort _
  | exchanged _ _ => exact .abort _

theorem say {Q : α → Prop} {len : Nat} {l : Label} {b : Bytes} {k : Bytes → Script α}
    (hi : P (.exchange len l (.plain b))) (hk : ∀ v, Post P Q (k v)) : Post P Q (sayThen len l b k) := by
  refine .step hi fun r => ?_
  cases r with
  | exchanged _ v => exact hk v
  | unit => exact .abort _
  | bits _ => exact .abort _
  | elems _ => exact .abort _

end Post

/-! ## The scripts the agreements run -/

section Scripts

variable (c : Nat) (P0 : List FieldH)

theorem fine_nil (i : Instr) (h : consumes i = []) : FineI c P0 i := by
  intro x hx; rw [h] at hx; cases hx

theorem fine_free (h : FieldH) (hf : Fine c P0 h) : FineI c P0 (.freeField h) := by
  intro x hx; simp [consumes] at hx; subst hx; exact hf

theorem hs_ge {f k : Nat} : ∀ h ∈ Curve.hs f k, f ≤ h.id := by
  intro h hh; simp only [Curve.hs, List.mem_map, List.mem_range] at hh
  obtain ⟨i, _, rfl⟩ := hh; simp

theorem fine_frees {hs : List FieldH} (hf : ∀ h ∈ hs, Fine c P0 h) : ∀ i ∈ Curve.freeFs hs, FineI c P0 i := by
  intro i hi; simp only [Curve.freeFs, List.mem_map] at hi
  obtain ⟨h, hh, rfl⟩ := hi; exact fine_free c P0 h (hf h hh)

/-- P-F2W: frees its mask's field handle (`m.field`) and its own `f0`; consumes nothing. -/
theorem f2w_post (n0 f0 : Nat) (v : FieldH) (m : Conv.WordMask) (hm : m.field ∈ P0) (hf : c ≤ f0) :
    Post (FineI c P0) (fun _ => True) (Convert.fieldToWord n0 f0 v m) := by
  unfold Convert.fieldToWord
  refine Post.seq (fine_nil c P0 _ rfl) (Post.openField (fine_nil c P0 _ rfl) fun cs => ?_)
  unfold Convert.f2wRest
  split
  · refine Post.say (fine_nil c P0 _ rfl) fun peer => ?_
    split
    · refine Post.seqs _ (fun i hi => ?_) (.done trivial)
      simp only [Convert.f2wTail, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fine_nil c P0 _ rfl
      · exact fine_nil c P0 _ rfl
      · exact fine_nil c P0 _ rfl
      · exact fine_nil c P0 _ rfl
      · exact fine_nil c P0 _ rfl
      · exact fine_nil c P0 _ rfl
      · exact fine_free c P0 _ (Or.inr hm)
      · exact fine_free c P0 _ (Or.inl hf)
    · exact .abort _
  · exact .abort _

/-- P-BITS: consumes nothing; its result is `bitsOuts f0 252`. -/
theorem bits_post (f0 n slot : Nat) :
    Post (FineI c P0) (fun bs => bs = Convert.bitsOuts f0 n) (Convert.sharedBits f0 n slot) := by
  unfold Convert.sharedBits
  refine Post.seq (fine_nil c P0 _ rfl) (Post.seq (fine_nil c P0 _ rfl) (Post.openField (fine_nil c P0 _ rfl) fun z => ?_))
  split
  · exact Post.seq (fine_nil c P0 _ rfl) (.done rfl)
  · exact .abort _

/-- The masked quotients: masks and frees of its own block (`f …`); results at `f + 3n + 2j`. -/
theorem quotientMany_post (f slot : Nat) (pairs : List (FieldH × FieldH)) (hf : c ≤ f) :
    Post (FineI c P0) (fun rs => ∀ r ∈ rs, c ≤ r.1.id) (Curve.quotientMany f slot pairs) := by
  unfold Curve.quotientMany
  dsimp only
  split
  · exact .done (by simp)
  · refine Post.seqs _ (fun i hi => ?_) (Post.openField (fine_nil c P0 _ rfl) fun fl => ?_)
    · simp only [List.mem_append, Curve.sharedBlock, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hi
      rcases hi with (rfl | ⟨j, _, rfl⟩) | hi
      · exact fine_nil c P0 _ rfl
      · exact fine_nil c P0 _ rfl
      · rw [hi]
        intro h hh
        simp only [consumes, Curve.sharedOut] at hh
        have := hs_ge h hh
        exact Or.inl (by omega)
    · split
      · refine Post.seqs _ (fun i hi => ?_) (.done ?_)
        · rw [List.mem_append] at hi
          rcases hi with hi | hi
          · exact fine_frees c P0 (fun h hh => Or.inl (by have := hs_ge h hh; omega)) i hi
          · refine fine_frees c P0 (fun h hh => Or.inl ?_) i hi
            simp only [Curve.quotFlags, Curve.quotFlag, List.mem_map, List.mem_range] at hh
            obtain ⟨j, _, rfl⟩ := hh; simp; omega
        · intro r hr
          simp only [List.mem_map, List.mem_range] at hr
          obtain ⟨j, _, rfl⟩ := hr
          simp [Curve.quotResult]; omega
      · exact .abort _

/-- S11's ladder agreements: their own block only; results in it. -/
theorem agree_post (f slot : Nat) (jobs : List (List FieldH × FieldH)) (hf : c ≤ f) :
    Post (FineI c P0) (fun rs => ∀ r ∈ rs, c ≤ r.1.id) (Curve.agree f slot jobs) := by
  unfold Curve.agree
  dsimp only
  split
  · exact .done (by simp)
  · split
    · refine Post.seqs _ (fun i hi => ?_) (quotientMany_post c P0 _ slot _ (by omega))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact fine_nil c P0 _ rfl
      · exact fine_nil c P0 _ rfl
      · exact fine_free c P0 _ (Or.inl hf)
    · exact .abort _

end Scripts

/-! ## The state-threaded runs -/

/-- The state: the counter at or above `c`, every pool mask's field handle in `P0`. -/
def Ok (c : Nat) (P0 : List FieldH) (st : St) : Prop :=
  c ≤ st.table.ctr.field ∧ ∀ m ∈ st.pool.words, m.field ∈ P0

def PostG (c : Nat) (P0 : List FieldH) {α : Type} (Q : α → Prop) (g : Gen α) : Prop :=
  ∀ st, Ok c P0 st → Post (FineI c P0) (fun p => Ok c P0 p.2 ∧ Q p.1) (g st)

namespace PostG

variable {c : Nat} {P0 : List FieldH} {α β : Type}

theorem bind {Q : α → Prop} {R : β → Prop} {x : Gen α} {f : α → Gen β} (hx : PostG c P0 Q x)
    (hf : ∀ a, Q a → PostG c P0 R (f a)) : PostG c P0 R (x >>= f) := by
  intro st hok
  have e : (x >>= f) st = Script.bind (x st) (fun p => f p.1 p.2) := rfl
  rw [e]
  exact (hx st hok).bind fun p hp => hf p.1 hp.2 p.2 hp.1

theorem pure {Q : α → Prop} {a : α} (h : Q a) : PostG c P0 Q (Pure.pure a : Gen α) := fun _ hok => .done ⟨hok, h⟩

theorem mono {Q Q' : α → Prop} {g : Gen α} (h : PostG c P0 Q g) (hq : ∀ a, Q a → Q' a) : PostG c P0 Q' g :=
  fun st hok => (h st hok).monoQ fun _ hp => ⟨hp.1, hq _ hp.2⟩

theorem lift {Q : α → Prop} {s : Script α} (h : Post (FineI c P0) Q s) : PostG c P0 Q (Receive.Gen.lift s) := by
  intro st hok
  show Post _ _ (Script.bind s fun a => .done (a, st))
  exact h.bind fun a ha => .done ⟨hok, ha⟩

theorem fail {Q : α → Prop} (r : String) : PostG c P0 Q (Receive.Gen.fail r : Gen α) :=
  fun _ _ => .abort r

theorem ite {Q : α → Prop} {p : Prop} [Decidable p] {x y : Gen α} (hx : PostG c P0 Q x) (hy : PostG c P0 Q y) :
    PostG c P0 Q (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem allocF (k : Nat) : PostG c P0 (fun f => c ≤ f) (Receive.Gen.allocF k) := by
  intro st hok
  refine .done ⟨⟨?_, hok.2⟩, hok.1⟩
  simp [Counters.allocF]; have := hok.1; omega

theorem allocB (k : Nat) : PostG c P0 (fun _ => True) (Receive.Gen.allocB k) := by
  intro st hok
  exact .done ⟨⟨by simpa [Contacts.Table.alloc, Counters.allocB] using hok.1, hok.2⟩, trivial⟩

theorem takeWord : PostG c P0 (fun m => m.field ∈ P0) Receive.Gen.takeWord := by
  intro st hok
  unfold Receive.Gen.takeWord
  split
  · next m p hp =>
    unfold Conv.MaskPool.takeWord at hp
    split at hp
    · next m' rest hw =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine .done ⟨⟨hok.1, fun x hx => hok.2 x (by rw [hw]; exact List.mem_cons_of_mem _ hx)⟩, ?_⟩
      exact hok.2 _ (by rw [hw]; exact List.mem_cons_self)
    · cases hp
  · exact .abort _

theorem takeSlot (k : Nat) : PostG c P0 (fun _ => True) (Receive.Gen.takeSlot k) := by
  intro st hok
  unfold Receive.Gen.takeSlot
  split
  · split
    · exact .done ⟨hok, trivial⟩
    · exact .abort _
  · exact .abort _

theorem instrs {is : List Instr} (h : ∀ i ∈ is, FineI c P0 i) : PostG c P0 (fun _ => True) (Receive.Gen.instrs is) :=
  lift (Post.seqs is h (.done trivial))

theorem freeFields {hs : List FieldH} (h : ∀ x ∈ hs, Fine c P0 x) : PostG c P0 (fun _ => True) (Receive.Gen.freeFields hs) := by
  refine instrs fun i hi => ?_
  simp only [Receive.freeFieldsI, List.mem_map] at hi
  obtain ⟨x, hx, rfl⟩ := hi
  exact fine_free c P0 x (h x hx)

end PostG

section Runs

variable {c : Nat} {P0 : List FieldH}

theorem toWord_post (v : FieldH) : PostG c P0 (fun _ => True) (Receive.toWord v) := by
  unfold Receive.toWord
  refine PostG.bind PostG.takeWord fun m hm => PostG.bind (PostG.allocB _) fun _ _ =>
    PostG.bind (PostG.allocF _) fun f hf => PostG.lift (f2w_post c P0 _ _ _ _ hm hf)

theorem publicField_post (v : TlsMpc.FieldDag.F) : PostG c P0 (fun h => c ≤ h.id) (Receive.publicField v) := by
  unfold Receive.publicField
  exact PostG.bind (PostG.allocF _) fun f hf => PostG.bind (PostG.instrs fun i hi => by
    simp at hi; subst hi; exact fine_nil c P0 _ rfl) fun _ _ => PostG.pure hf

theorem jobBits_post (sl : AgreeSlots) (j : Job) : PostG c P0 (fun b => ∀ h ∈ b.2, c ≤ h.id) (jobBits sl j) := by
  unfold jobBits
  split
  · exact PostG.pure (by simp)
  · refine PostG.bind (PostG.allocF _) fun f hf => ?_
    refine PostG.bind (PostG.lift (bits_post c P0 f 252 _)) fun bs hbs => ?_
    refine PostG.bind (PostG.freeFields fun x hx => Or.inl ?_) fun _ _ => PostG.pure ?_
    · simp only [List.mem_append, Convert.bitsA, Convert.bitsB, Convert.bitsChk, List.mem_map, List.mem_range] at hx
      rcases hx with (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩ <;> simp <;> omega
    · subst hbs
      intro h hh
      simp only [Convert.bitsOuts, List.mem_map, List.mem_range] at hh
      obtain ⟨i, _, rfl⟩ := hh
      simp; omega

theorem jobPoint_post (p : Receive.Point) : PostG c P0 (fun q => ∀ h ∈ q.2, c ≤ h.id) (jobPoint p) := by
  cases p with
  | handle h => exact PostG.pure (by simp)
  | base =>
    exact PostG.bind (publicField_post _) fun h hh => PostG.pure (by simpa using hh)

theorem jobsIn_post (sl : AgreeSlots) : ∀ jobs, PostG c P0 (fun r => ∀ h ∈ r.2, c ≤ h.id) (jobsIn sl jobs)
  | [] => PostG.pure (by simp)
  | j :: js => by
    unfold jobsIn
    refine PostG.bind (jobBits_post sl j) fun b hb => PostG.bind (jobPoint_post _) fun p hp =>
      PostG.bind (jobsIn_post sl js) fun r hr => PostG.pure ?_
    intro h hh
    simp only [List.mem_append] at hh
    rcases hh with (hh | hh) | hh
    · exact hb h hh
    · exact hp h hh
    · exact hr h hh

theorem wordsOf_post : ∀ rs, PostG c P0 (fun _ => True) (wordsOf rs)
  | [] => PostG.pure trivial
  | r :: rs => by
    unfold wordsOf
    exact PostG.bind (toWord_post _) fun _ _ => PostG.bind (wordsOf_post rs) fun _ _ => PostG.pure trivial

theorem agreeTail_post (made : List FieldH) (f n : Nat) (rs : List (FieldH × Bool))
    (hm : ∀ h ∈ made, c ≤ h.id) (hf : c ≤ f) (hr : ∀ r ∈ rs, c ≤ r.1.id) :
    PostG c P0 (fun _ => True) (agreeTail made f n rs) := by
  unfold agreeTail
  refine PostG.ite (PostG.fail _) ?_
  refine PostG.bind (wordsOf_post rs) fun _ _ => PostG.bind (PostG.freeFields fun x hx => Or.inl ?_) fun _ _ =>
    PostG.pure trivial
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with (hx | hx) | ⟨r, hr', rfl⟩
  · exact hm x hx
  · have := hs_ge x hx; omega
  · exact hr r hr'

theorem receiveAgree_post (sl : AgreeSlots) (jobs : List Job) : PostG c P0 (fun _ => True) (receiveAgree sl jobs) := by
  unfold receiveAgree
  refine PostG.ite (PostG.pure trivial) ?_
  refine PostG.bind (jobsIn_post sl jobs) fun ins hins => ?_
  refine PostG.bind (PostG.takeSlot _) fun slot _ => ?_
  refine PostG.bind (PostG.allocF _) fun f hf => ?_
  refine PostG.bind (PostG.lift (agree_post c P0 f slot ins.1 hf)) fun rs hrs => ?_
  exact agreeTail_post _ _ _ _ hins hf hrs

end Runs

/-! ## The handles spared -/

/-- The instruction neither frees nor consumes a handle of `S`. -/
def Spares (S : List FieldH) (i : Instr) : Prop := ∀ h ∈ consumes i, h ∉ S

theorem spares_of_post {α : Type} (S : List FieldH) (g : Gen α) (st : St)
    (hg : PostG st.table.ctr.field (st.pool.words.map (·.field)) (fun _ => True) g)
    (hbelow : ∀ h ∈ S, h.id < st.table.ctr.field) (hpool : ∀ m ∈ st.pool.words, m.field ∉ S) :
    Every (Spares S) (g st) := by
  refine (hg st ⟨Nat.le_refl _, fun m hm => List.mem_map_of_mem hm⟩).every fun i hi h hh hS => ?_
  rcases hi h hh with hc | hp
  · have := hbelow h hS; omega
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
    exact hpool m hm hS

/-- **J8: the joined agreements spare the identity's swap-bit handles** (any handles `S` allocated
before the run and not a pool mask): along every branch, no instruction frees them or takes them
as a `program` mask. -/
theorem receiveAgree_spares (sl : AgreeSlots) (jobs : List Job) (st : St) (S : List FieldH)
    (hbelow : ∀ h ∈ S, h.id < st.table.ctr.field) (hpool : ∀ m ∈ st.pool.words, m.field ∉ S) :
    Every (Spares S) (receiveAgree sl jobs st) :=
  spares_of_post S _ st (receiveAgree_post sl jobs) hbelow hpool

/-- The sender key (J12) spares them too. -/
theorem senderPublicG_spares (sl : AgreeSlots) (st : St) (S : List FieldH)
    (hbelow : ∀ h ∈ S, h.id < st.table.ctr.field) (hpool : ∀ m ∈ st.pool.words, m.field ∉ S) :
    Every (Spares S) (ContactsPrepare.senderPublicG sl st) := by
  refine spares_of_post S _ st ?_ hbelow hpool
  unfold ContactsPrepare.senderPublicG
  refine PostG.bind (receiveAgree_post sl _) fun ws _ => ?_
  split
  · exact PostG.pure trivial
  · exact PostG.fail _

/-- S15's agreement step (`Join.agreeG`: the points into the field, the seven jobs, the points
freed) spares them. -/
theorem agreeG_spares (sl : AgreeSlots) (ip sp : BoolH) (o : Option BoolH) (st : St) (S : List FieldH)
    (hbelow : ∀ h ∈ S, h.id < st.table.ctr.field) (hpool : ∀ m ∈ st.pool.words, m.field ∉ S) :
    Every (Spares S) (agreeG sl ip sp o st) := by
  refine spares_of_post S _ st ?_ hbelow hpool
  have toField_post : ∀ u, PostG st.table.ctr.field (st.pool.words.map (·.field)) (fun h : FieldH => st.table.ctr.field ≤ h.id)
      (Receive.toField u) := by
    intro u
    unfold Receive.toField
    refine PostG.bind PostG.takeWord fun m hm => PostG.bind (PostG.allocB _) fun _ _ =>
      PostG.bind (PostG.allocF _) fun f hf => PostG.lift ?_
    unfold Convert.wordToField
    refine Post.seqs _ (fun i hi => ?_) (Post.openBool (fine_nil _ _ _ rfl) fun b => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact fine_nil _ _ _ rfl
    · unfold Convert.w2fRest
      split
      · refine Post.say (fine_nil _ _ _ rfl) fun peer => ?_
        split
        · refine Post.seqs _ (fun i hi => ?_) (.done (by simp; omega))
          simp only [Convert.w2fTail, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact fine_nil _ _ _ rfl
          · exact fine_nil _ _ _ rfl
          · exact fine_nil _ _ _ rfl
          · exact fine_nil _ _ _ rfl
          · exact fine_nil _ _ _ rfl
          · exact fine_free _ _ _ (Or.inr hm)
          · exact fine_free _ _ _ (Or.inl hf)
        · exact .abort _
      · exact .abort _
  unfold agreeG
  refine PostG.bind (toField_post _) fun ipf hip => PostG.bind (toField_post _) fun spf hsp => ?_
  refine PostG.bind (PostG.mono (Q := fun r : Option FieldH => ∀ x ∈ r.toList, st.table.ctr.field ≤ x.id) ?_ fun _ h => h)
    fun opf hop => ?_
  · cases o with
    | none => exact PostG.pure (by simp)
    | some o =>
      exact PostG.bind (toField_post o) fun x hx => PostG.pure (by simpa using hx)
  · refine PostG.bind (receiveAgree_post sl _) fun _ _ => PostG.bind (PostG.freeFields fun x hx => Or.inl ?_) fun _ _ =>
      PostG.pure trivial
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl) | hx
    · exact hip
    · exact hsp
    · exact hop x hx

end TlsMpc.Node.Flows.JoinIdentity
