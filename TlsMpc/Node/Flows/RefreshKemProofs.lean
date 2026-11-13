import TlsMpc.Node.Flows.RefreshSlotProofs
import TlsMpc.KernelSpecs.KemCompose

/-!
# T4-REFRESH, the encapsulation: the script's wiring is `kernels_compose`'s, so Kyber-1024

REORGANIZATION_PLAN.md stage S15. No I/O; no emitter imports this module.

`KemCompose.kernels_compose` says: IF every `kem-*` kernel's named inputs carry the named outputs of
the earlier kernels, `kem-finish`'s outputs are `pipeline` (and `pipeline_valid_accept`,
`pipeline_invalid`: the reference encapsulation on a valid key, all zero on an invalid one). Its
twenty-one name-binding hypotheses are about how the worker wires the kernels. Here the wiring is
the script's (`kemHashInstrs`, `kemRowInstrs`, `kemFinishInstrs`): which slice of which output feeds
which input, in which order. `kemFlow` is that wiring on bytes, with the script's own offsets
(the slices `k+4 … k+7` of `kem-hash` at bytes 0, 32, 64, 96; `rhat` 0–1536; a row 0–1536 and its
ok byte 1536; `u` 0–352; `v` 0–160; and every concatenation in the kernels' declared input order).

PROVED:
  * `kem_bindings` / `kemFlow_pipeline`: every hypothesis of `kernels_compose` holds for the
    script's wiring (the string comparisons of the kernels' field names included,
    `row_name_ne`), so `kemFlow K eA eB = (pipeline true K eA eB).flatten`;
  * `kemFlow_accept` (valid key, the specification succeeds): status 255, then the reference
    ciphertext and shared secret (`pipeline_valid_accept`); `kemFlow_invalid` (any other key):
    every byte zero (`pipeline_invalid`), so nothing derived from an invalid key reaches the
    session.

NOT PROVED here: that the instructions of `kemBlock` leave `kemFlow`'s bits in handle `k + 32` in
the model (`runPlain` through the 45 instructions; `kemFlow` is written with the same offsets and
input orders as the instructions, the vectors check the instruction list against it; the parse's
analogue IS proved in the model, `parse_fields`). Gap listed in S15_NOTES.md.

HYPOTHESIS `KemWidths`: the byte widths of the kernels' output fields (the layouts the loader pins;
the stages' length lemmas are not in the repository). Gap listed in S15_NOTES.md.
-/

namespace TlsMpc.Node.Flows.Refresh

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open Std.Tactic.BVDecide
open TlsMpc.MlKemFastKernel (kemHash kemNtt kemMatrix kemU kemV kemFinish hashInputs nttInputs matrixInputs uInputs
  vInputs finishInputs)

/-- The kernels' output values. -/
abbrev kvals := TlsMpc.EstablishKernel.Kernel.values

/-- Bytes `[off, off + len)`. -/
def fieldAt (L : B8) (off len : Nat) : B8 := (L.drop off).take len

/-- **The output widths of the KEM kernels** (bytes per output field). -/
structure KemWidths : Prop where
  hash : ∀ a, (kvals (kemHash true) a).map List.length = [32, 32, 32, 1]
  ntt : ∀ a, (kvals (kemNtt ()) a).map List.length = [1536]
  matrix : ∀ r a, (kvals (kemMatrix r) a).map List.length = [1536, 1]
  u : ∀ r a, (kvals (kemU r) a).map List.length = [352]
  v : ∀ a, (kvals (kemV ()) a).map List.length = [160]

/-! ## Fields of a concatenation -/

theorem fieldAt_get : ∀ (vs : List B8) (ws : List Nat), vs.map List.length = ws → ∀ i,
    fieldAt vs.flatten ((ws.take i).sum) (ws.getD i 0) = vs.getD i []
  | [], [], _, i => by simp [fieldAt]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | v :: vs, w :: ws, h, 0 => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp [fieldAt, ← h.1]
  | v :: vs, w :: ws, h, i + 1 => by
    simp only [List.map_cons, List.cons.injEq] at h
    have ih := fieldAt_get vs ws h.2 i
    simp only [fieldAt] at ih ⊢
    simp only [List.flatten_cons, List.take_succ_cons, List.sum_cons, List.getD_cons_succ]
    rw [← h.1, ← List.drop_drop, List.drop_left]
    exact ih

theorem getD_length : ∀ (vs : List B8) (ws : List Nat), vs.map List.length = ws → ∀ i,
    (vs.getD i []).length = ws.getD i 0
  | [], [], _, i => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | v :: vs, w :: ws, h, 0 => by simp only [List.map_cons, List.cons.injEq] at h; simp [h.1]
  | v :: vs, w :: ws, h, i + 1 => by
    simp only [List.map_cons, List.cons.injEq] at h
    simpa using getD_length vs ws h.2 i

theorem flatten_length (vs : List B8) (ws : List Nat) (h : vs.map List.length = ws) :
    vs.flatten.length = ws.sum := by
  rw [List.length_flatten, ← h]

theorem fieldAt_get' (vs : List B8) (ws : List Nat) (h : vs.map List.length = ws) (i off len : Nat)
    (ho : off = (ws.take i).sum) (hl : len = ws.getD i 0) : fieldAt vs.flatten off len = vs.getD i [] := by
  subst ho hl
  exact fieldAt_get vs ws h i

/-! ## The script's wiring on bytes -/

def kHash (K eA eB : B8) : B8 := (kvals (kemHash true) (assignOf [K, eA, eB].flatten)).flatten
def kMessage (K eA eB : B8) : B8 := fieldAt (kHash K eA eB) 0 32
def kKbar (K eA eB : B8) : B8 := fieldAt (kHash K eA eB) 32 32
def kCoins (K eA eB : B8) : B8 := fieldAt (kHash K eA eB) 64 32
def kKeyValid (K eA eB : B8) : B8 := fieldAt (kHash K eA eB) 96 1
def kRhat (K eA eB : B8) : B8 := fieldAt (kvals (kemNtt ()) (assignOf [kCoins K eA eB].flatten)).flatten 0 1536
def kRow (K : B8) (r : Nat) : B8 := fieldAt (kvals (kemMatrix r) (assignOf [K].flatten)).flatten 0 1536
def kOk (K : B8) (r : Nat) : B8 := fieldAt (kvals (kemMatrix r) (assignOf [K].flatten)).flatten 1536 1
def kUIn (K eA eB : B8) (r : Nat) : List B8 := [kRow K r, kRhat K eA eB, kCoins K eA eB]
def kU (K eA eB : B8) (r : Nat) : B8 := fieldAt (kvals (kemU r) (assignOf (kUIn K eA eB r).flatten)).flatten 0 352
def kVIn (K eA eB : B8) : List B8 := [K, kRhat K eA eB, kCoins K eA eB, kMessage K eA eB]
def kV (K eA eB : B8) : B8 := fieldAt (kvals (kemV ()) (assignOf (kVIn K eA eB).flatten)).flatten 0 160
def kFinishIn (K eA eB : B8) : List B8 :=
  [kU K eA eB 0, kU K eA eB 1, kU K eA eB 2, kU K eA eB 3, kV K eA eB, kKbar K eA eB,
   kOk K 0, kOk K 1, kOk K 2, kOk K 3, kKeyValid K eA eB]

/-- **The encapsulation as the script wires it**, on bytes. -/
def kemFlow (K eA eB : B8) : B8 := (kvals (kemFinish true) (assignOf (kFinishIn K eA eB).flatten)).flatten

/-! ## Each binding of `kernels_compose` -/

theorem row_toList : (toString "row").toList = ['r', 'o', 'w'] := by decide

theorem row_name_ne (i : Nat) (s : String) (hs : s.toList.take 2 ≠ ['r', 'o']) : (s!"row{i}" == s) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg (fun s : String => s.toList.take 2) h
  simp [row_toList] at this
  exact hs this.symm

/-- A kernel input read under the assignment of a concatenation is the corresponding piece. -/
theorem piece (ps : List B8) (j off len : Nat) (hoff : off = ((ps.map List.length).take j).sum)
    (hlen : len = (ps.map List.length).getD j 0) (hle : off + len ≤ ps.flatten.length) :
    (ByteCircuit.inputBytes off len).map (BVExpr.eval (assignOf ps.flatten)) = ps.getD j [] := by
  rw [bytes_assignOf _ _ _ hle]
  exact fieldAt_get' ps _ rfl j off len hoff hlen

open TlsMpc.HybridKernel (lookup lookupFrom Shape) in
theorem lookup_u (i : Nat) :
    lookup (uInputs i) s!"row{i}" = ByteCircuit.inputBytes 0 1536 ∧
      lookup (uInputs i) "rhat" = ByteCircuit.inputBytes 1536 1536 ∧
      lookup (uInputs i) "coins" = ByteCircuit.inputBytes 3072 32 := by
  have h1 := row_name_ne i "rhat" (by decide)
  have h2 := row_name_ne i "coins" (by decide)
  simp only [lookup, uInputs, lookupFrom, beq_self_eq_true, if_true, h1, h2, Bool.false_eq_true, if_false,
    Shape.variables]
  refine ⟨trivial, trivial, ?_⟩
  simp (config := { decide := true })

/-- **Every name binding of `kernels_compose` holds for the script's wiring**: the encapsulation
the script computes is `pipeline`. -/
theorem kemFlow_pipeline (K eA eB : B8) (hW : KemWidths) (hK : K.length = 1568) (hA : eA.length = 32)
    (hB : eB.length = 32) : kemFlow K eA eB = (TlsMpc.KernelSpecs.KemCompose.pipeline true K eA eB).flatten := by
  have lh := hW.hash (assignOf [K, eA, eB].flatten)
  have hc : kCoins K eA eB = (kvals (kemHash true) (assignOf [K, eA, eB].flatten)).getD 2 [] :=
    fieldAt_get' _ _ lh 2 64 32 rfl rfl
  have hm : kMessage K eA eB = (kvals (kemHash true) (assignOf [K, eA, eB].flatten)).getD 0 [] :=
    fieldAt_get' _ _ lh 0 0 32 rfl rfl
  have hkb : kKbar K eA eB = (kvals (kemHash true) (assignOf [K, eA, eB].flatten)).getD 1 [] :=
    fieldAt_get' _ _ lh 1 32 32 rfl rfl
  have hkv : kKeyValid K eA eB = (kvals (kemHash true) (assignOf [K, eA, eB].flatten)).getD 3 [] :=
    fieldAt_get' _ _ lh 3 96 1 rfl rfl
  have lc : (kCoins K eA eB).length = 32 := by rw [hc, getD_length _ _ lh 2]; rfl
  have lm : (kMessage K eA eB).length = 32 := by rw [hm, getD_length _ _ lh 0]; rfl
  have lkb : (kKbar K eA eB).length = 32 := by rw [hkb, getD_length _ _ lh 1]; rfl
  have lkv : (kKeyValid K eA eB).length = 1 := by rw [hkv, getD_length _ _ lh 3]; rfl
  have ln := hW.ntt (assignOf [kCoins K eA eB].flatten)
  have hr : kRhat K eA eB = (kvals (kemNtt ()) (assignOf [kCoins K eA eB].flatten)).getD 0 [] :=
    fieldAt_get' _ _ ln 0 0 1536 rfl rfl
  have lr : (kRhat K eA eB).length = 1536 := by rw [hr, getD_length _ _ ln 0]; rfl
  have hrow : ∀ r, kRow K r = (kvals (kemMatrix r) (assignOf [K].flatten)).getD 0 [] :=
    fun r => fieldAt_get' _ _ (hW.matrix r _) 0 0 1536 rfl rfl
  have hok : ∀ r, kOk K r = (kvals (kemMatrix r) (assignOf [K].flatten)).getD 1 [] :=
    fun r => fieldAt_get' _ _ (hW.matrix r _) 1 1536 1 rfl rfl
  have lrow : ∀ r, (kRow K r).length = 1536 := fun r => by rw [hrow, getD_length _ _ (hW.matrix r _) 0]; rfl
  have lok : ∀ r, (kOk K r).length = 1 := fun r => by rw [hok, getD_length _ _ (hW.matrix r _) 1]; rfl
  have hu : ∀ r, kU K eA eB r = (kvals (kemU r) (assignOf (kUIn K eA eB r).flatten)).getD 0 [] :=
    fun r => fieldAt_get' _ _ (hW.u r _) 0 0 352 rfl rfl
  have lu : ∀ r, (kU K eA eB r).length = 352 := fun r => by rw [hu, getD_length _ _ (hW.u r _) 0]; rfl
  have hv : kV K eA eB = (kvals (kemV ()) (assignOf (kVIn K eA eB).flatten)).getD 0 [] :=
    fieldAt_get' _ _ (hW.v _) 0 0 160 rfl rfl
  have lv : (kV K eA eB).length = 160 := by rw [hv, getD_length _ _ (hW.v _) 0]; rfl
  have lH : ([K, eA, eB].map List.length) = [1568, 32, 32] := by simp [hK, hA, hB]
  have lN : ([kCoins K eA eB].map List.length) = [32] := by simp [lc]
  have lM : ([K].map List.length) = [1568] := by simp [hK]
  have lU : ∀ r, ((kUIn K eA eB r).map List.length) = [1536, 1536, 32] := fun r => by simp [kUIn, lrow, lr, lc]
  have lV : ((kVIn K eA eB).map List.length) = [1568, 1536, 32, 32] := by simp [kVIn, hK, lr, lc, lm]
  have lF : ((kFinishIn K eA eB).map List.length) = [352, 352, 352, 352, 160, 32, 1, 1, 1, 1, 1] := by
    simp [kFinishIn, lu, lv, lkb, lok, lkv]
  have fH := flatten_length _ _ lH
  have fN := flatten_length _ _ lN
  have fM := flatten_length _ _ lM
  have fV := flatten_length _ _ lV
  have fF := flatten_length _ _ lF
  unfold kemFlow
  refine congrArg List.flatten (TlsMpc.KernelSpecs.KemCompose.kernels_compose true K eA eB
    (assignOf [K, eA, eB].flatten) (assignOf [kCoins K eA eB].flatten) (assignOf (kVIn K eA eB).flatten)
    (assignOf (kFinishIn K eA eB).flatten) (fun _ => assignOf [K].flatten) (fun r => assignOf (kUIn K eA eB r).flatten)
    ?h1 ?h2 ?h3 ?n ?m ?u1 ?u2 ?u3 ?v1 ?v2 ?v3 ?v4 ?f0 ?f1 ?f2 ?f3 ?fv ?fk ?o0 ?o1 ?o2 ?o3 ?kv)
  case h1 =>
    show (ByteCircuit.inputBytes 0 1568).map _ = _
    rw [piece _ 0 0 1568 (by rw [lH]; rfl) (by rw [lH]; rfl) (by rw [fH]; decide)]; rfl
  case h2 =>
    show (ByteCircuit.inputBytes 1568 32).map _ = _
    rw [piece _ 1 1568 32 (by rw [lH]; rfl) (by rw [lH]; rfl) (by rw [fH]; decide)]; rfl
  case h3 =>
    show (ByteCircuit.inputBytes 1600 32).map _ = _
    rw [piece _ 2 1600 32 (by rw [lH]; rfl) (by rw [lH]; rfl) (by rw [fH]; decide)]; rfl
  case n =>
    show (ByteCircuit.inputBytes 0 32).map _ = _
    rw [piece _ 0 0 32 (by rw [lN]; rfl) (by rw [lN]; rfl) (by rw [fN]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hc
  case m =>
    intro i
    show (ByteCircuit.inputBytes 0 1568).map _ = _
    rw [piece _ 0 0 1568 (by rw [lM]; rfl) (by rw [lM]; rfl) (by rw [fM]; decide)]; rfl
  case u1 =>
    intro i
    rw [(lookup_u i).1, piece _ 0 0 1536 (by rw [lU]; rfl) (by rw [lU]; rfl)
      (by rw [flatten_length _ _ (lU i)]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hrow i
  case u2 =>
    intro i
    rw [(lookup_u i).2.1, piece _ 1 1536 1536 (by rw [lU]; rfl) (by rw [lU]; rfl)
      (by rw [flatten_length _ _ (lU i)]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hr
  case u3 =>
    intro i
    rw [(lookup_u i).2.2, piece _ 2 3072 32 (by rw [lU]; rfl) (by rw [lU]; rfl)
      (by rw [flatten_length _ _ (lU i)]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hc
  case v1 =>
    show (ByteCircuit.inputBytes 0 1568).map _ = _
    rw [piece _ 0 0 1568 (by rw [lV]; rfl) (by rw [lV]; rfl) (by rw [fV]; decide)]; rfl
  case v2 =>
    show (ByteCircuit.inputBytes 1568 1536).map _ = _
    rw [piece _ 1 1568 1536 (by rw [lV]; rfl) (by rw [lV]; rfl) (by rw [fV]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hr
  case v3 =>
    show (ByteCircuit.inputBytes 3104 32).map _ = _
    rw [piece _ 2 3104 32 (by rw [lV]; rfl) (by rw [lV]; rfl) (by rw [fV]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hc
  case v4 =>
    show (ByteCircuit.inputBytes 3136 32).map _ = _
    rw [piece _ 3 3136 32 (by rw [lV]; rfl) (by rw [lV]; rfl) (by rw [fV]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hm
  case f0 =>
    show (ByteCircuit.inputBytes 0 352).map _ = _
    rw [piece _ 0 0 352 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hu 0
  case f1 =>
    show (ByteCircuit.inputBytes 352 352).map _ = _
    rw [piece _ 1 352 352 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hu 1
  case f2 =>
    show (ByteCircuit.inputBytes 704 352).map _ = _
    rw [piece _ 2 704 352 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hu 2
  case f3 =>
    show (ByteCircuit.inputBytes 1056 352).map _ = _
    rw [piece _ 3 1056 352 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hu 3
  case fv =>
    show (ByteCircuit.inputBytes 1408 160).map _ = _
    rw [piece _ 4 1408 160 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hv
  case fk =>
    show (ByteCircuit.inputBytes 1568 32).map _ = _
    rw [piece _ 5 1568 32 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hkb
  case o0 =>
    show (ByteCircuit.inputBytes 1600 1).map _ = _
    rw [piece _ 6 1600 1 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hok 0
  case o1 =>
    show (ByteCircuit.inputBytes 1601 1).map _ = _
    rw [piece _ 7 1601 1 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hok 1
  case o2 =>
    show (ByteCircuit.inputBytes 1602 1).map _ = _
    rw [piece _ 8 1602 1 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hok 2
  case o3 =>
    show (ByteCircuit.inputBytes 1603 1).map _ = _
    rw [piece _ 9 1603 1 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hok 3
  case kv =>
    show (ByteCircuit.inputBytes 1604 1).map _ = _
    rw [piece _ 10 1604 1 (by rw [lF]; rfl) (by rw [lF]; rfl) (by rw [fF]; decide)]
    simp only [kUIn, kVIn, kFinishIn, List.getD_cons_succ, List.getD_cons_zero]
    rw [TlsMpc.KernelSpecs.KemCompose.outVal]
    exact hkv

/-- **Valid key, the specification succeeds**: the script's encapsulation is status 255, then
exactly the reference ciphertext and shared secret (`KemCompose.pipeline_valid_accept`). -/
theorem kemFlow_accept (K eA eB : B8) (hW : KemWidths) (hK : K.length = 1568) (hA : eA.length = 32)
    (hB : eB.length = 32) (hvalid : TlsMpc.KernelSpecs.KemCompose.KeyValid K)
    (hs : (TlsMpc.KernelSpecs.KemCompose.specEnc true K eA eB).success = 255) :
    kemFlow K eA eB = [255] ++ (TlsMpc.KernelSpecs.KemCompose.specEnc true K eA eB).bytes.take 1568 ++
      (TlsMpc.KernelSpecs.KemCompose.specEnc true K eA eB).bytes.drop 1568 := by
  rw [kemFlow_pipeline K eA eB hW hK hA hB,
    TlsMpc.KernelSpecs.KemCompose.pipeline_valid_accept true K eA eB hvalid (Or.inl rfl) hs]
  simp

/-- **Invalid key**: every byte of the script's encapsulation (status, ciphertext, secret) is zero
(`KemCompose.pipeline_invalid`); `establish-session` then refuses (its status is not 255). -/
theorem kemFlow_invalid (K eA eB : B8) (hW : KemWidths) (hK : K.length = 1568) (hA : eA.length = 32)
    (hB : eB.length = 32) (h : ¬ TlsMpc.KernelSpecs.KemCompose.KeyValid K) :
    ∀ b ∈ kemFlow K eA eB, b = 0 := by
  rw [kemFlow_pipeline K eA eB hW hK hA hB]
  intro b hb
  obtain ⟨f, hf, hbf⟩ := List.mem_flatten.mp hb
  exact TlsMpc.KernelSpecs.KemCompose.pipeline_invalid true K eA eB h f hf b hbf

end TlsMpc.Node.Flows.Refresh
