import TlsMpc.Node.Flows.TlsBase

/-!
# `Ghash.keyShare`, `Ghash.round`: XOR shares of the GHASH key powers (P-GHASH)

REORGANIZATION_PLAN.md stage S12, section 7.1 P-GHASH. Replaces the engine part of
`handshake_backend/EmpHybridWork/gcm_shares.h` (`GcmShares::reshare`, `ensure`, lines 36-56); the
local part is `Local/Ghash.lean`. Advance work in a new file; the C++ stays in use until the
controller switches (the TLS backend of `Flows/TlsBackend.lean` is selectable, not selected).

WHAT THE C++ DOES, AND THE SCRIPTS HERE (Boolean handles; `n` the session's next free handle id;
bits of bytes least significant first):

  `GcmShares::reshare` on `gcm-key-share` (inputs traffic 60, mask 16 bytes; output `masked`
  16 bytes, audience 2: to B only): A inputs a fresh random mask privately, the kernel computes
  `AES_K(0¹²⁸) ⊕ mask` and it is opened to B. A keeps the mask as its share of `H`, B the opened
  value.
    `keyShareScript n traffic maskSlot dst`: boolInput n (owner A, 128 bits, once, from A's store
    slot `maskSlot`; B sends nothing), concat n+1 := traffic ‖ n, run `gcm-key-share` -> n+2,
    OPEN n+2 TO B (label ghashMaskedPower, into B's store slot `dst`), free n+2.

  `GcmShares::ensure` for an odd power k on `gcm-multiply` (inputs leftA, leftB, rightA, rightB,
  mask, 16 bytes each; output `masked`, to B only): one engine round PER odd power, inputs A's and
  B's shares of H^(k−1) and of H, A's fresh mask.
    `roundScript n c leftSlot rightSlot maskSlot dst` (DEVIATION: all `c` odd powers of a round of
    the doubling schedule, `Local.Ghash.oddPowers`, in ONE run of `c` copies, so one agreement round
    per doubling): boolInputBoth n, n+1 (each party's `c` left shares, 128·c bits, once),
    boolInputBoth n+2, n+3 (each party's share of H, 128 bits, once), boolInput n+4 (A's `c` masks),
    concat n+5, pick n+6 := the per-copy layout `layout c` (leftA_j ‖ leftB_j ‖ rightA ‖ rightB ‖
    mask_j; the shares of H picked once per copy), run `gcm-multiply` with `c` copies -> n+7, OPEN
    n+7 TO B (ghashMaskedPower, into `dst`), free n+7.

  Each input is `once`: consumed by the concat, whose result the pick consumes, whose result the
  run consumes (decision D3); so each of A's masks reaches exactly one kernel copy (a mask used
  twice would show B the XOR of two powers).

PROVED (`GhashLoaded E`: the two kernels' circuits compute their Lean definitions):
  P-GHASH (a): `keyShare_value`, `multiply_value` (the kernels on values, from
    `gcmKeyShare_reshare`, `gcmMultiply_reshare`), `keyShare_shared` (A's mask and B's opened
    value share H = `hashKeyOf` of the traffic block), `round_shared` (a round of the schedule with
    the engines' values keeps `Local.Ghash.Shared`), so by induction every list of shares the
    schedule builds is a sharing of H¹ … Hⁿ.
  P-GHASH (d) (hiding, the bijection form of plan 7.0 that `ghash_share_hides` and
    `proofs/` consume): `keyShare_hides` (for any two traffic keys, the mask shift
    `m ↦ m ⊕ H ⊕ H'` is an involution of A's masks that gives B the same opened value) and
    `multiply_hides` (for fixed inputs, `m ↦` the opened product is a bijection, whatever B
    supplied).
  T3 (disclosure): `keyShare_reveals`, `round_reveals` (kind ghashMaskedPower only);
    `keyShare_toB`, `round_toB` and `keyShare_viewD_B`, `round_viewD_B` (with B honest the
    adversary A's view is EMPTY, against any adversary); `keyShare_disclosure_A` (with A honest
    the adversary B receives exactly one value, the kernel's output on the traffic block and A's
    mask: by `keyShare_value`, `H ⊕ mask`).
  WF: `keyShare_wfp` / `keyShare_wf` (the shell's `check` accepts every instruction, from any
    context with the traffic handle live, 480 bits, not once, and the counter fresh).
NOT PROVED: the round script's run-level value (`runCopies` through the pick layout; its
  function-level statement is `round_shared`); WF of `roundScript` is stated with the layout's
  bound as a hypothesis-free lemma (`layout_bound`) but the full `roundScript_wf` is open
  (S12_NOTES.md, gaps).
-/

namespace TlsMpc.Node.Flows.Ghash

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open Std.Tactic.BVDecide

abbrev W := BitVec 128

/-! ## Names, labels, circuits -/

def keyShareName : Bytes := name0 "gcm-key-share"
def multiplyName : Bytes := name0 "gcm-multiply"

/-- `Reveal.ghashMaskedPower`: a key power masked by A's fresh mask, to B only. -/
def masked : Label := Label.ghashMaskedPower

/-- The two resharing kernels' circuits compute their Lean definitions (T2's trust, as
`Contacts.Loaded`). -/
structure GhashLoaded (E : Env) : Prop where
  keyShare : E.circuits keyShareName = some (circuitOf HybridKernel.gcmKeyShare)
  multiply : E.circuits multiplyName = some (circuitOf HybridKernel.gcmMultiply)

theorem keyShare_inBytes : kernelInBytes HybridKernel.gcmKeyShare = 76 := rfl
theorem multiply_inBytes : kernelInBytes HybridKernel.gcmMultiply = 80 := rfl

/-! ## The scripts -/

def keyShareBlock (n : Nat) (traffic : BoolH) (maskSlot dst : Nat) : List Instr :=
  [.boolInput ⟨n⟩ .a 128 true false maskSlot,
   .concat ⟨n + 1⟩ [traffic, ⟨n⟩],
   .run ⟨n + 2⟩ keyShareName 1 ⟨n + 1⟩,
   .openBoolTo ⟨n + 2⟩ .b masked dst,
   .freeBool ⟨n + 2⟩]

/-- **H's first resharing** (`GcmShares::reshare` on `gcm-key-share`). A's store slot `maskSlot`
holds its fresh 128-bit mask; B's slot `dst` receives `H ⊕ mask`. Uses ids `n … n+2`. -/
def keyShareScript (n : Nat) (traffic : BoolH) (maskSlot dst : Nat) : Script Unit :=
  seqs (keyShareBlock n traffic maskSlot dst) (.done ())

/-- The per-copy input layout of a round's `gcm-multiply` run: copy `j` reads A's left share `j`,
B's left share `j`, both shares of H, A's mask `j` (16 bytes each), from the concatenation
lefts A (128c) ‖ lefts B (128c) ‖ H share A ‖ H share B ‖ masks A (128c). -/
def layout (c : Nat) : List Nat :=
  (List.range c).flatMap fun j =>
    (List.range 128).map (fun b => j * 128 + b) ++
    (List.range 128).map (fun b => c * 128 + j * 128 + b) ++
    (List.range 128).map (fun b => 2 * c * 128 + b) ++
    (List.range 128).map (fun b => 2 * c * 128 + 128 + b) ++
    (List.range 128).map (fun b => 2 * c * 128 + 256 + j * 128 + b)

def roundBlock (n c : Nat) (leftSlot rightSlot maskSlot dst : Nat) : List Instr :=
  [.boolInputBoth ⟨n⟩ ⟨n + 1⟩ (128 * c) true false leftSlot,
   .boolInputBoth ⟨n + 2⟩ ⟨n + 3⟩ 128 true false rightSlot,
   .boolInput ⟨n + 4⟩ .a (128 * c) true false maskSlot,
   .concat ⟨n + 5⟩ [⟨n⟩, ⟨n + 1⟩, ⟨n + 2⟩, ⟨n + 3⟩, ⟨n + 4⟩],
   .pick ⟨n + 6⟩ ⟨n + 5⟩ (layout c),
   .run ⟨n + 7⟩ multiplyName c ⟨n + 6⟩,
   .openBoolTo ⟨n + 7⟩ .b masked dst,
   .freeBool ⟨n + 7⟩]

/-- **One round of the doubling schedule** (`c` odd powers in one `gcm-multiply` run). Slots: the
party's `c` left shares (`Local.Ghash.lefts`), its share of H, A's `c` fresh masks; B's slot `dst`
receives the `c` masked products. Uses ids `n … n+7`. -/
def roundScript (n c : Nat) (leftSlot rightSlot maskSlot dst : Nat) : Script Unit :=
  if 0 < c ∧ c ≤ 1024 then seqs (roundBlock n c leftSlot rightSlot maskSlot dst) (.done ())
  else .abort "GHASH round size"

/-! ## The kernels on values (P-GHASH (a), kernel level) -/

/-- A one-output kernel's outputs on an input are its `kernelOut`. -/
theorem outputs_one (K : HybridKernel.Kernel) (o : HybridKernel.Output) (h : K.outputs = [o]) (input : B8) :
    K.outputs.map (fun field => field.value.map (BVExpr.eval (assignOf input))) = [kernelOut K input] := by
  simp [kernelOut, h]

theorem keyShare_outputs : ∃ o, HybridKernel.gcmKeyShare.outputs = [o] := ⟨_, rfl⟩
theorem multiply_outputs : ∃ o, HybridKernel.gcmMultiply.outputs = [o] := ⟨_, rfl⟩

theorem drop_take_mid (p x q : B8) (k : Nat) (hp : p.length = k) : ((p ++ (x ++ q)).drop k).take x.length = x := by
  rw [List.drop_left' hp, List.take_left' rfl]

/-- **`gcm-key-share` on values**: the opened value is `H ⊕ mask`, `H = hashKeyOf K`. -/
theorem keyShare_value (K m : B8) (hK : K.length = 60) (hm : m.length = 16) :
    Local.Ghash.ofBytes (kernelOut HybridKernel.gcmKeyShare (K ++ m)) =
      HybridKernel.hashKeyOf K ^^^ Local.Ghash.ofBytes m := by
  have e1 : HybridKernel.inputValue (assignOf (K ++ m)) 0 60 = K := by
    rw [inputValue_assignOf _ 0 60 (by simp; omega), List.drop_zero, List.take_left' hK]
  have e2 : HybridKernel.inputValue (assignOf (K ++ m)) 60 16 = m := by
    rw [inputValue_assignOf _ 60 16 (by simp; omega), List.drop_left' hK, List.take_of_length_le (by omega)]
  obtain ⟨o, ho⟩ := keyShare_outputs
  have hr := HybridKernel.gcmKeyShare_reshare (assignOf (K ++ m)) _ (outputs_one _ o ho (K ++ m))
  rw [e1, e2] at hr
  simp only [HybridKernel.Schedule.reshare, Prod.mk.injEq] at hr
  exact hr.2

/-- **`gcm-multiply` on values**: the opened value is `(la ⊕ lb)·(ra ⊕ rb) ⊕ m`. -/
theorem multiply_value (la lb ra rb m : B8) (h1 : la.length = 16) (h2 : lb.length = 16)
    (h3 : ra.length = 16) (h4 : rb.length = 16) (h5 : m.length = 16) :
    Local.Ghash.ofBytes (kernelOut HybridKernel.gcmMultiply (la ++ lb ++ ra ++ rb ++ m)) =
      Local.Ghash.mul (Local.Ghash.ofBytes la ^^^ Local.Ghash.ofBytes lb)
        (Local.Ghash.ofBytes ra ^^^ Local.Ghash.ofBytes rb) ^^^ Local.Ghash.ofBytes m := by
  have hl : (la ++ lb ++ ra ++ rb ++ m).length = 80 := by simp; omega
  have get : ∀ (s : Nat) (x : B8), s + 16 ≤ 80 → x.length = 16 →
      ((la ++ lb ++ ra ++ rb ++ m).drop s).take 16 = x → HybridKernel.inputValue (assignOf (la ++ lb ++ ra ++ rb ++ m)) s 16 = x :=
    fun s x hs _ hx => by rw [inputValue_assignOf _ s 16 (by omega), hx]
  have e1 := get 0 la (by omega) h1 (by
    have := drop_take_mid [] la (lb ++ ra ++ rb ++ m) 0 rfl
    rw [h1] at this
    simpa [List.append_assoc] using this)
  have e2 := get 16 lb (by omega) h2 (by
    have := drop_take_mid la lb (ra ++ rb ++ m) 16 h1
    rw [h2] at this
    simpa [List.append_assoc] using this)
  have e3 := get 32 ra (by omega) h3 (by
    have := drop_take_mid (la ++ lb) ra (rb ++ m) 32 (by simp; omega)
    rw [h3] at this
    simpa [List.append_assoc] using this)
  have e4 := get 48 rb (by omega) h4 (by
    have := drop_take_mid (la ++ lb ++ ra) rb m 48 (by simp; omega)
    rw [h4] at this
    simpa [List.append_assoc] using this)
  have e5 := get 64 m (by omega) h5 (by
    have := drop_take_mid (la ++ lb ++ ra ++ rb) m [] 64 (by simp; omega)
    rw [h5] at this
    simpa [List.append_assoc] using this)
  obtain ⟨o, ho⟩ := multiply_outputs
  have hr := HybridKernel.gcmMultiply_reshare (assignOf (la ++ lb ++ ra ++ rb ++ m)) _
    (outputs_one _ o ho (la ++ lb ++ ra ++ rb ++ m))
  rw [e1, e2, e3, e4, e5] at hr
  simp only [HybridKernel.Schedule.reshare, HybridKernel.Schedule.product, Prod.mk.injEq] at hr
  exact hr.2

/-! ## P-GHASH (a): the shares the flows produce share the key powers -/

theorem xor_cancel (x y : W) : x ^^^ (y ^^^ x) = y := Local.Ghash.xor_unmask x y

/-- **The first resharing gives shares of H**: A's mask and B's opened value XOR to
`H = hashKeyOf K` (P-GHASH (a), first power). -/
theorem keyShare_shared (K m : B8) (hK : K.length = 60) (hm : m.length = 16) :
    Local.Ghash.Shared [Local.Ghash.ofBytes m] [Local.Ghash.ofBytes (kernelOut HybridKernel.gcmKeyShare (K ++ m))]
      (HybridKernel.hashKeyOf K) 1 := by
  rw [keyShare_value K m hK hm]
  refine ⟨rfl, rfl, fun k hk => ?_⟩
  have : k = 0 := by omega
  subst this
  exact xor_cancel _ _

/-- The opened products of a round: copy `j` of `gcm-multiply` on A's and B's left shares `j`,
their shares of H and A's mask `j`. -/
def roundOpened (a b : List W) (t : Nat) (masks : List B8) : List B8 :=
  (List.range (Local.Ghash.oddCount a.length t)).map fun j =>
    kernelOut HybridKernel.gcmMultiply
      (Local.Ghash.toBytes ((Local.Ghash.lefts a t).getD j 0) ++ Local.Ghash.toBytes ((Local.Ghash.lefts b t).getD j 0) ++
        Local.Ghash.toBytes (a.getD 0 0) ++ Local.Ghash.toBytes (b.getD 0 0) ++ masks.getD j [])

/-- **A round keeps the sharing** (P-GHASH (a), every further power). With shares of H¹ … Hᵐ, A's
odd values its masks and B's the opened products of the round, the extended lists share H¹ … Hᵗ
(`m ≤ t ≤ 2m`). -/
theorem round_shared (a b : List W) (h : W) (m t : Nat) (masks : List B8)
    (hs : Local.Ghash.Shared a b h m) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 2 * m)
    (hmask : ∀ x ∈ masks, x.length = 16) (hcount : masks.length = Local.Ghash.oddCount m t) :
    Local.Ghash.Shared (Local.Ghash.extend a t (masks.map Local.Ghash.ofBytes))
      (Local.Ghash.extend b t ((roundOpened a b t masks).map Local.Ghash.ofBytes)) h t := by
  have la := hs.1
  have lb := hs.2.1
  refine Local.Ghash.shared_extend a b h m t _ _ hs hm hmt ht (fun i hi ho => ?_)
  have ho' : (a.length + 1 + i) % 2 = 1 := by rw [la]; exact ho
  have ho'' : (b.length + 1 + i) % 2 = 1 := by rw [lb]; exact ho
  obtain ⟨hc, -⟩ := Local.Ghash.oddPowers_getD m t i hi ho
  have hj : i / 2 < masks.length := by rw [hcount]; exact hc
  have hmj : (masks.getD (i / 2) []).length = 16 := by
    apply hmask
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  have hA : (masks.map Local.Ghash.ofBytes).getD (i / 2) 0 = Local.Ghash.ofBytes (masks.getD (i / 2) []) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hB : ((roundOpened a b t masks).map Local.Ghash.ofBytes).getD (i / 2) 0 =
      Local.Ghash.ofBytes (kernelOut HybridKernel.gcmMultiply
        (Local.Ghash.toBytes ((Local.Ghash.lefts a t).getD (i / 2) 0) ++
          Local.Ghash.toBytes ((Local.Ghash.lefts b t).getD (i / 2) 0) ++
          Local.Ghash.toBytes (a.getD 0 0) ++ Local.Ghash.toBytes (b.getD 0 0) ++ masks.getD (i / 2) [])) := by
    have hc' : i / 2 < Local.Ghash.oddCount a.length t := by rw [la]; exact hc
    simp [roundOpened, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc']
  rw [hA, hB, multiply_value _ _ _ _ _ (Local.Ghash.toBytes_length _) (Local.Ghash.toBytes_length _)
    (Local.Ghash.toBytes_length _) (Local.Ghash.toBytes_length _) hmj]
  simp only [Local.Ghash.ofBytes_toBytes]
  have ea := Local.Ghash.lefts_getD a t i (by rw [la]; exact hi) ho'
  have eb := Local.Ghash.lefts_getD b t i (by rw [lb]; exact hi) ho''
  rw [ea, eb, la, lb]
  exact xor_cancel _ _

/-! ## P-GHASH (d): hiding (the bijection form of plan 7.0) -/

/-- **The key share hides H.** For any two traffic keys `K`, `K'`, the shift of A's mask by
`H ⊕ H'` (an involution: shifting back gives the mask again) makes B's opened value under `K'`
the same as under `K`. So, A's mask being uniform, B's view is independent of the key. -/
theorem keyShare_hides (K K' m : B8) (hK : K.length = 60) (hK' : K'.length = 60) (hm : m.length = 16) :
    let shift := fun (x : B8) => Local.Ghash.toBytes
      (Local.Ghash.ofBytes x ^^^ HybridKernel.hashKeyOf K ^^^ HybridKernel.hashKeyOf K')
    Local.Ghash.ofBytes (kernelOut HybridKernel.gcmKeyShare (K' ++ shift m)) =
        Local.Ghash.ofBytes (kernelOut HybridKernel.gcmKeyShare (K ++ m)) ∧
      Local.Ghash.ofBytes (shift (Local.Ghash.toBytes (Local.Ghash.ofBytes (shift m) ^^^
        HybridKernel.hashKeyOf K' ^^^ HybridKernel.hashKeyOf K))) = Local.Ghash.ofBytes (shift m) ∧
      Local.Ghash.ofBytes (Local.Ghash.toBytes (Local.Ghash.ofBytes (shift m) ^^^
        HybridKernel.hashKeyOf K' ^^^ HybridKernel.hashKeyOf K)) = Local.Ghash.ofBytes m := by
  intro shift
  have hs : (shift m).length = 16 := Local.Ghash.toBytes_length _
  refine ⟨?_, ?_, ?_⟩
  · rw [keyShare_value K' _ hK' hs, keyShare_value K m hK hm]
    simp only [shift, Local.Ghash.ofBytes_toBytes]
    ext i
    simp only [BitVec.getElem_xor]
    cases (HybridKernel.hashKeyOf K')[i] <;> cases (HybridKernel.hashKeyOf K)[i] <;>
      cases (Local.Ghash.ofBytes m)[i] <;> rfl
  · simp only [shift, Local.Ghash.ofBytes_toBytes]
    ext i
    simp only [BitVec.getElem_xor]
    cases (HybridKernel.hashKeyOf K')[i] <;> cases (HybridKernel.hashKeyOf K)[i] <;>
      cases (Local.Ghash.ofBytes m)[i] <;> rfl
  · simp only [shift, Local.Ghash.ofBytes_toBytes]
    ext i
    simp only [BitVec.getElem_xor]
    cases (HybridKernel.hashKeyOf K')[i] <;> cases (HybridKernel.hashKeyOf K)[i] <;>
      cases (Local.Ghash.ofBytes m)[i] <;> rfl

/-- **A product's opening hides the product.** For fixed left and right inputs (any values B
supplied), A's mask `m` determines the opened value by `m ↦ product ⊕ m`: for every value B could
see there is exactly one mask giving it (`GhashShares.share_hides`). -/
theorem multiply_hides (la lb ra rb : B8) (h1 : la.length = 16) (h2 : lb.length = 16)
    (h3 : ra.length = 16) (h4 : rb.length = 16) (seen : W) :
    ∃ mask : W, ∀ m : B8, m.length = 16 →
      (Local.Ghash.ofBytes (kernelOut HybridKernel.gcmMultiply (la ++ lb ++ ra ++ rb ++ m)) = seen ↔
        Local.Ghash.ofBytes m = mask) := by
  obtain ⟨mask, hmask, huniq⟩ := GhashShares.share_hides
    (Local.Ghash.mul (Local.Ghash.ofBytes la ^^^ Local.Ghash.ofBytes lb)
      (Local.Ghash.ofBytes ra ^^^ Local.Ghash.ofBytes rb)) seen
  refine ⟨mask, fun m hm => ?_⟩
  rw [multiply_value la lb ra rb m h1 h2 h3 h4 hm]
  exact ⟨fun h => huniq _ h, fun h => h ▸ hmask⟩

/-! ## T3: the kinds, and to B only -/

/-- The GHASH flows release under `ghashMaskedPower` only. -/
def ghashKinds : List TlsMpc.Node.RevealKind := [.ghashMaskedPower]

theorem keyShare_reveals (n : Nat) (traffic : BoolH) (maskSlot dst : Nat) :
    Reveals ghashKinds (keyShareScript n traffic maskSlot dst) := by
  refine every_seqs (Every.done _) _ ?_
  intro i hi
  simp only [keyShareBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact LabelIn.of_none rfl
  · exact LabelIn.of_none rfl
  · exact LabelIn.of_none rfl
  · exact LabelIn.of_mem (k := .ghashMaskedPower) (by simp [ghashKinds]) rfl
  · exact LabelIn.of_none rfl

theorem round_reveals (n c : Nat) (leftSlot rightSlot maskSlot dst : Nat) :
    Reveals ghashKinds (roundScript n c leftSlot rightSlot maskSlot dst) := by
  unfold roundScript
  split
  · refine every_seqs (Every.done _) _ ?_
    intro i hi
    simp only [roundBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact LabelIn.of_none rfl
      | exact LabelIn.of_mem (k := .ghashMaskedPower) (by simp [ghashKinds]) rfl
  · exact Every.abort _

theorem keyShare_toB (n : Nat) (traffic : BoolH) (maskSlot dst : Nat) :
    Every (ToMe .b) (keyShareScript n traffic maskSlot dst) := by
  refine every_seqs (Every.done _) _ ?_
  intro i hi
  simp only [keyShareBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem round_toB (n c : Nat) (leftSlot rightSlot maskSlot dst : Nat) :
    Every (ToMe .b) (roundScript n c leftSlot rightSlot maskSlot dst) := by
  unfold roundScript
  split
  · refine every_seqs (Every.done _) _ ?_
    intro i hi
    simp only [roundBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · exact Every.abort _

section Disclosure

variable (E : Env) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)

/-- **T3, B honest: the adversary A learns nothing** from a key share (everything is opened to B). -/
theorem keyShare_viewD_B (n : Nat) (traffic : BoolH) (maskSlot dst : Nat) :
    (withAdv E .b adv (keyShareScript n traffic maskSlot dst) σ I vD).viewD = [] :=
  viewD_nil_of_toMe E .b adv _ (keyShare_toB n traffic maskSlot dst) σ I vD

/-- **T3, B honest: the adversary A learns nothing** from a round. -/
theorem round_viewD_B (n c : Nat) (leftSlot rightSlot maskSlot dst : Nat) :
    (withAdv E .b adv (roundScript n c leftSlot rightSlot maskSlot dst) σ I vD).viewD = [] :=
  viewD_nil_of_toMe E .b adv _ (round_toB n c leftSlot rightSlot maskSlot dst) σ I vD

/-- **T3, A honest: the adversary B receives exactly one value**, labelled ghashMaskedPower: the
`gcm-key-share` kernel's output on the traffic block and A's mask (by `keyShare_value`, `H ⊕
mask`). -/
theorem keyShare_disclosure_A (hE : GhashLoaded E) (n : Nat) (traffic : BoolH) (maskSlot dst : Nat)
    (K m : B8) (hK : K.length = 60) (hm : m.length = 16) (htn : traffic.id < n)
    (hk : I.bools traffic.id = some (bitsOf K)) (hσ : σ.bits maskSlot = bitsOf m) :
    (withAdv E .a adv (keyShareScript n traffic maskSlot dst) σ I vD).viewD <+:
      [⟨masked, .bits (bitsOf (kernelOut HybridKernel.gcmKeyShare (K ++ m)))⟩] := by
  have hlen : (σ.bits maskSlot).length = 128 := by simp [hσ, hm]
  have htn0 : traffic.id ≠ n := by omega
  have hc := hE.keyShare
  unfold keyShareScript keyShareBlock
  simp only [seqs_cons, seqs_nil]
  refine viewD_seq_boolInput E .a adv n 128 maskSlot true false _ σ I vD _ hlen ?_
  rw [hσ]
  have hrest : seq (.concat ⟨n + 1⟩ [traffic, ⟨n⟩]) (seq (.run ⟨n + 2⟩ keyShareName 1 ⟨n + 1⟩)
      (seq (.openBoolTo ⟨n + 2⟩ .b masked dst) (seq (.freeBool ⟨n + 2⟩) (.done ())))) =
      seqs [.concat ⟨n + 1⟩ [traffic, ⟨n⟩], .run ⟨n + 2⟩ keyShareName 1 ⟨n + 1⟩]
        (seq (.openBoolTo ⟨n + 2⟩ Party.a.other masked dst) (seq (.freeBool ⟨n + 2⟩) (.done ()))) := rfl
  rw [hrest]
  apply viewD_seqs E .a adv _ σ _ _ (by simp [plain]) _ vD
  intro I' hI'
  have hw : 8 * K.length + 8 * m.length = (kernelCircuit HybridKernel.gcmKeyShare
      (kernelInBytes HybridKernel.gcmKeyShare) (kernelMarks HybridKernel.gcmKeyShare)).inWidth := by
    simp [kernelCircuit, keyShare_inBytes, hK, hm]
  simp [runPlain, plainStep, idealStep, blankWire, InstrP.map, Ideal.setBool, hk, htn0, hc, circuitOf] at hI'
  simp only [hw, if_true] at hI'
  simp only [Option.some.injEq] at hI'
  subst hI'
  have hev : (kernelCircuit HybridKernel.gcmKeyShare (kernelInBytes HybridKernel.gcmKeyShare)
      (kernelMarks HybridKernel.gcmKeyShare)).eval (bitsOf K ++ bitsOf m) =
      bitsOf (kernelOut HybridKernel.gcmKeyShare (K ++ m)) := by
    show bitsOf (kernelOut _ (bytesOf (bitsOf K ++ bitsOf m))) = _
    rw [← bitsOf_append, bytesOf_bitsOf]
  refine viewD_seq_openBoolTo E .a adv _ masked dst _ σ _ vD [] _ ?_ ?_
  · rw [runCopies_one' _ _ (by simp [kernelCircuit, keyShare_inBytes, hK, hm])]
    simp [hev]
  · exact silent_prefix E .a adv _ (Silent.seq rfl (Silent.done _)) _ _ _ _

end Disclosure

/-! ## Well-formedness -/

/-- What a key share leaves: the handles below `n` as before, nothing defined from `n + 3` on. -/
def KeySharePost (c : Ctx) (n : Nat) (c' : Ctx) (_ : Unit) : Prop :=
  (∀ g : BoolH, g.id < n → g.id ≠ n → c'.bool? g = c.bool? g) ∧ Fresh c' (n + 3)

theorem keyShare_wfp (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic : BoolH) (maskSlot dst : Nat)
    (hf : Fresh c n) (htn : traffic.id < n) (hk : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩)
    (hsig : sigs keyShareName = some ⟨8 * 76, List.replicate 128 .toB⟩) :
    WFP sigs (KeySharePost c n) c (keyShareScript n traffic maskSlot dst) := by
  unfold keyShareScript keyShareBlock
  simp only [seqs_cons, seqs_nil]
  have hf1 := hf.push n (Nat.le_refl n) ⟨List.replicate 128 (Mark.ofInput false), true⟩
  refine WFP_seq sigs c _ _ _ (check_boolInput sigs hf .a 128 true false (by decide)) ?_
  have hf2 := hf1.drop n
  refine WFP_seq sigs _ _ _ _ (check_concat sigs
    (useBools_cons (useBool_keep ((bool?_push_of_ne _ _ _ _ (by omega)).trans hk) rfl)
      (useBools_cons (useBool_once (bool?_push_self _ _ _) rfl) (useBools_nil _))) hf2
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate, maxWidth_eq]; omega)) ?_
  have hf3 := (hf2.push (n + 1) (Nat.le_refl _) ⟨(List.map BoolInfo.marks [⟨List.replicate 480 Mark.never, false⟩,
    ⟨List.replicate 128 (Mark.ofInput false), true⟩]).flatten, true⟩).drop (n + 1)
  refine WFP_seq sigs _ _ _ _ (check_run sigs hsig Nat.one_pos (useBool_once (bool?_push_self _ _ _) rfl)
    (by simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.length_replicate]) hf3 (by decide)
    (by simp only [List.length_replicate, maxWidth_eq]; omega)) ?_
  refine WFP_seq sigs _ _ _ _ (check_openBoolTo sigs (by decide) (useBool_keep (bool?_push_self _ _ _) rfl)
    (by
      rw [List.all_eq_true]
      intro x hx
      simp only [List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_replicate] at hx
      rw [hx.2]
      rfl)) ?_
  refine WFP_seq sigs _ _ _ _ (check_freeBool' sigs (by rw [bool?_push_self]; rfl)) ?_
  refine WFP.done _ _ ⟨fun g hg _ => ?_, ((hf3.push (n + 2) (Nat.le_refl _) _).drop (n + 2))⟩
  have e0 : g.id ≠ n := by omega
  have e1 : g.id ≠ n + 1 := by omega
  have e2 : g.id ≠ n + 2 := by omega
  simp only [bool?_push, bool?_drop, e0, e1, e2, if_false]

theorem keyShare_wf (sigs : Bytes → Option Sig) (c : Ctx) (n : Nat) (traffic : BoolH) (maskSlot dst : Nat)
    (hf : Fresh c n) (htn : traffic.id < n) (hk : c.bool? traffic = some ⟨List.replicate 480 .never, false⟩)
    (hsig : sigs keyShareName = some ⟨8 * 76, List.replicate 128 .toB⟩) :
    WF sigs c (keyShareScript n traffic maskSlot dst) :=
  (keyShare_wfp sigs c n traffic maskSlot dst hf htn hk hsig).wf

/-- Every index of the round layout is inside the concatenated inputs (`5 · 128` per copy over
`3 · 128c + 256` bits), so the pick is accepted. -/
theorem layout_bound (c j : Nat) (h : j ∈ layout c) : j < 128 * c + 128 * c + 128 + 128 + 128 * c := by
  simp only [layout, List.mem_flatMap, List.mem_range, List.mem_append, List.mem_map] at h
  obtain ⟨i, hi, h⟩ := h
  rcases h with (((⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩) | ⟨b, hb, rfl⟩ <;>
    omega

theorem sum_const (c k : Nat) : ((List.range c).map (fun _ => k)).sum = c * k := by
  induction c with
  | zero => simp
  | succ c ih => simp [List.range_succ, ih, Nat.succ_mul]

theorem length_layout (c : Nat) : (layout c).length = c * 640 := by
  simp [layout, List.length_flatMap, sum_const]

end TlsMpc.Node.Flows.Ghash
