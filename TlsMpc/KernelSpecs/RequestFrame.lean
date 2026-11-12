import TlsMpc.KernelSpecs.RequestCtr
import TlsMpc.Node.Policy.Request

/-!
# The request frames the controller builds in the clear (T8, for the three request sealers)

It changes no definition and no emitter imports it.

`signal-request-ctr`, `bundle-fetch-ctr` and `bundle-request-ctr` encrypt
`insertSlots frame mask payloadAt slots` (`TlsMpc/KernelSpecs/RequestCtr.lean`), where `frame` is
the masked WebSocket frame that `PublicRequest.build` / `buildFetch` / `buildDevices`
(`TlsMpc/Node/Policy/Request.lean`, the definitions the controller runs) built in the clear with
zero bytes in the slots. This file proves what that plaintext is: exactly the masked WebSocket
frame of the message with every slot replaced by its secret field. The theorems are about the
controller's own builders: there is no restated copy.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `build_eq`, `assemble_eq` (with `buildFetch_eq`, `buildDevices_eq`): the builders as functions.
  `build` accepts exactly a payload of 126..65535 bytes and a 4-byte mask and returns the 8-byte
  header `[130, 254, size / 256, size] ‖ mask` followed by `body` (the message's text bytes masked
  from payload position 0, each slot a run of zero bytes), and the slot offsets; `assemble` the
  same with a 2- or 4-byte length header.
* `build_ok`: every frame `build` returns has its payload at frame index 8, so the fixed
  `mask[(i − 8) % 4]` of `signal-request-ctr` is the right mask byte (the 8-byte WebSocket header
  assumption is a property of every frame the controller builds for that kernel, not a hypothesis).
* `insertSlots_frame`, `insertSlots_offsets`: slots of a message never overlap (`table_disjoint`),
  the frame is zero in every slot, and inserting values of the slots' widths at the returned
  offsets gives `header ‖ maskFrom mask 0 (render values msg)`: the WebSocket frame of the message
  with each slot replaced by its value. The order of the kernel's slot list does not matter.
* `signalRequestCtr_built`, `bundleFetchCtr_built`, `bundleRequestCtr_built`: on a frame the
  builder returned, with the kernel named by its length, payload start and offsets as the controller
  names it, the kernel's outputs are `sealedRequest` of exactly that filled frame (the contact's
  UUID text, base64 access key, space-padded device and registration ids in place; slot widths
  36, 24, 3, 10 are proved: `uuid_length`, `base64_length`, `paddedDecimal_length`).

Trusted, not proved: that the C++ worker passes the controller's frame, mask and offsets unchanged
into the kernel inputs and name (the hypotheses `built`, `hframe`, `hmask`, `paired`).
-/
namespace TlsMpc.KernelSpecs.RequestFrame
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide

abbrev Byte := BitVec 8

/-! The controller's request builders and the messages they frame (`TlsMpc/Node/Policy/Request.lean`). -/
open PublicRequest (Piece total field officialJson sendMessage build assemble fetchMessage buildFetch
  devicesMessage buildDevices)

/-! ### The frame, piece by piece -/

/-- `bytes` masked with the WebSocket mask, the first at payload position `pos`. -/
def maskFrom (mask : List Byte) : Nat → List Byte → List Byte
  | _, [] => []
  | pos, b :: rest => (b ^^^ mask.getD (pos % 4) 0) :: maskFrom mask (pos + 1) rest

/-- The payload as the controller builds it: text masked, each slot `width` zero bytes. -/
def body (mask : List Byte) : Nat → List Piece → List Byte
  | _, [] => []
  | pos, .bytes v :: rest => maskFrom mask pos v ++ body mask (pos + v.length) rest
  | pos, .slot _ w :: rest => List.replicate w 0 ++ body mask (pos + w) rest

/-- The message with slot `k` replaced by `values k`, unmasked: what the server reads. -/
def render (values : Nat → List Byte) : List Piece → List Byte
  | [] => []
  | .bytes v :: rest => v ++ render values rest
  | .slot k _ :: rest => values k ++ render values rest

/-- The slot pieces as (index, frame offset, width), the pieces laid out from frame offset `at`. -/
def slotTable : Nat → List Piece → List (Nat × Nat × Nat)
  | _, [] => []
  | here, .bytes v :: rest => slotTable (here + v.length) rest
  | here, .slot k w :: rest => (k, here, w) :: slotTable (here + w) rest

/-- The offsets array as the builders' loop leaves it. -/
def offsetsFold : Array Nat → Nat → List Piece → Array Nat
  | o, _, [] => o
  | o, here, .bytes v :: rest => offsetsFold o (here + v.length) rest
  | o, here, .slot k w :: rest => offsetsFold (o.set! k here) (here + w) rest

/-! ### The builders' loops, as folds -/

theorem forIn_eq_foldl' {α β : Type} (l : List α) (init : β) (g : α → β → Except String (ForInStep β))
    (f : α → β → β) (h : ∀ x r, g x r = pure (.yield (f x r))) :
    forIn l init g = pure (l.foldl (fun r x => f x r) init) := by
  have : g = fun x r => pure (.yield (f x r)) := funext fun x => funext fun r => h x r
  subst this
  exact List.forIn_pure_yield_eq_foldl f init

/-- One step of `assemble`'s loop. -/
def stepA (hl : Nat) (mask : List Byte) (piece : Piece) (r : MProd (Array Byte) (Array Nat)) :
    MProd (Array Byte) (Array Nat) :=
  match piece with
  | .bytes v => ⟨v.foldl (fun F b => F.push (b ^^^ mask.getD ((F.size - hl) % 4) 0)) r.fst, r.snd⟩
  | .slot k w => ⟨r.fst ++ Array.replicate w 0, r.snd.set! k r.fst.size⟩

/-- One step of `build`'s loop (the frame is a list there, the header 8 bytes). -/
def stepB (mask : List Byte) (piece : Piece) (r : MProd (List Byte) (Array Nat)) : MProd (List Byte) (Array Nat) :=
  match piece with
  | .bytes v => ⟨v.foldl (fun F b => F ++ [b ^^^ mask.getD ((F.length - 8) % 4) 0]) r.fst, r.snd⟩
  | .slot k w => ⟨r.fst ++ List.replicate w 0, r.snd.set! k r.fst.length⟩

theorem pushFold (hl : Nat) (mask v : List Byte) (F : Array Byte) (h : hl ≤ F.size) :
    (v.foldl (fun F b => F.push (b ^^^ mask.getD ((F.size - hl) % 4) 0)) F).toList =
      F.toList ++ maskFrom mask (F.size - hl) v ∧
    (v.foldl (fun F b => F.push (b ^^^ mask.getD ((F.size - hl) % 4) 0)) F).size = F.size + v.length := by
  induction v generalizing F with
  | nil => simp [maskFrom]
  | cons b v ih =>
      obtain ⟨h1, h2⟩ := ih (F.push (b ^^^ mask.getD ((F.size - hl) % 4) 0)) (by simp; omega)
      simp only [List.foldl_cons, h1, h2, Array.toList_push, Array.size_push, maskFrom, List.append_assoc,
        List.singleton_append, List.length_cons]
      refine ⟨?_, by omega⟩
      have : F.size + 1 - hl = F.size - hl + 1 := by omega
      rw [this]

theorem maskFrom_length (mask : List Byte) (pos : Nat) (v : List Byte) : (maskFrom mask pos v).length = v.length := by
  induction v generalizing pos with
  | nil => rfl
  | cons b v ih => simp [maskFrom, ih]

theorem appendFold (mask v F : List Byte) (h : 8 ≤ F.length) :
    v.foldl (fun F b => F ++ [b ^^^ mask.getD ((F.length - 8) % 4) 0]) F = F ++ maskFrom mask (F.length - 8) v := by
  induction v generalizing F with
  | nil => simp [maskFrom]
  | cons b v ih =>
      simp only [List.foldl_cons]
      rw [ih _ (by simp; omega)]
      simp only [maskFrom, List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
      have : F.length + 1 - 8 = F.length - 8 + 1 := by omega
      rw [this]

theorem foldA (hl : Nat) (mask : List Byte) (msg : List Piece) (F : Array Byte) (O : Array Nat) (h : hl ≤ F.size) :
    (msg.foldl (fun r x => stepA hl mask x r) ⟨F, O⟩).fst.toList = F.toList ++ body mask (F.size - hl) msg ∧
    (msg.foldl (fun r x => stepA hl mask x r) ⟨F, O⟩).snd = offsetsFold O F.size msg := by
  induction msg generalizing F O with
  | nil => simp [body, offsetsFold]
  | cons piece rest ih =>
      cases piece with
      | bytes v =>
          obtain ⟨p1, p2⟩ := pushFold hl mask v F h
          rw [List.foldl_cons]
          have e : stepA hl mask (.bytes v) ⟨F, O⟩ =
              ⟨v.foldl (fun F b => F.push (b ^^^ mask.getD ((F.size - hl) % 4) 0)) F, O⟩ := rfl
          rw [e]
          obtain ⟨i1, i2⟩ := ih (v.foldl (fun F b => F.push (b ^^^ mask.getD ((F.size - hl) % 4) 0)) F) O
            (by rw [p2]; omega)
          rw [i1, i2, p1, p2]
          simp only [body, offsetsFold, List.append_assoc]
          refine ⟨?_, by trivial⟩
          have : F.size + v.length - hl = F.size - hl + v.length := by omega
          rw [this]
      | slot k w =>
          rw [List.foldl_cons]
          have e : stepA hl mask (.slot k w) ⟨F, O⟩ = ⟨F ++ Array.replicate w 0, O.set! k F.size⟩ := rfl
          rw [e]
          obtain ⟨i1, i2⟩ := ih (F ++ Array.replicate w 0) (O.set! k F.size) (by simp; omega)
          rw [i1, i2]
          simp only [body, offsetsFold, List.append_assoc, Array.toList_append, Array.toList_replicate,
            Array.size_append, Array.size_replicate]
          refine ⟨?_, by trivial⟩
          have : F.size + w - hl = F.size - hl + w := by omega
          rw [this]

theorem foldB (mask : List Byte) (msg : List Piece) (F : List Byte) (O : Array Nat) (h : 8 ≤ F.length) :
    (msg.foldl (fun r x => stepB mask x r) ⟨F, O⟩).fst = F ++ body mask (F.length - 8) msg ∧
    (msg.foldl (fun r x => stepB mask x r) ⟨F, O⟩).snd = offsetsFold O F.length msg := by
  induction msg generalizing F O with
  | nil => simp [body, offsetsFold]
  | cons piece rest ih =>
      cases piece with
      | bytes v =>
          rw [List.foldl_cons]
          have e : stepB mask (.bytes v) ⟨F, O⟩ =
              ⟨v.foldl (fun F b => F ++ [b ^^^ mask.getD ((F.length - 8) % 4) 0]) F, O⟩ := rfl
          rw [e, appendFold mask v F h]
          obtain ⟨i1, i2⟩ := ih (F ++ maskFrom mask (F.length - 8) v) O (by simp; omega)
          rw [i1, i2]
          simp only [body, offsetsFold, List.append_assoc, List.length_append, maskFrom_length]
          refine ⟨?_, by trivial⟩
          have : F.length + v.length - 8 = F.length - 8 + v.length := by omega
          rw [this]
      | slot k w =>
          rw [List.foldl_cons]
          have e : stepB mask (.slot k w) ⟨F, O⟩ = ⟨F ++ List.replicate w 0, O.set! k F.length⟩ := rfl
          rw [e]
          obtain ⟨i1, i2⟩ := ih (F ++ List.replicate w 0) (O.set! k F.length) (by simp; omega)
          rw [i1, i2]
          simp only [body, offsetsFold, List.append_assoc, List.length_append, List.length_replicate]
          refine ⟨?_, by trivial⟩
          have : F.length + w - 8 = F.length - 8 + w := by omega
          rw [this]

/-- The header `assemble` writes: 2 bytes (payload under 126) or 4, then the mask. -/
def assembleHeader (size : Nat) (mask : List Byte) : List Byte :=
  (if size < 126 then [130, BitVec.ofNat 8 (128 + size)]
    else [130, 254, BitVec.ofNat 8 (size / 256), BitVec.ofNat 8 size]) ++ mask

set_option maxHeartbeats 1000000 in
/-- **`assemble` as a function**: when it accepts, the frame is the header followed by the payload
`body` (text masked from payload position 0, zero bytes in each slot), the payload starts after the
header, and the offsets are what the slot pieces set. -/
theorem assemble_eq (message : List Piece) (mask : List Byte) (slots : Nat) :
    assemble message mask slots =
      if (decide (0 < total message) && decide (total message < 65536) && mask.length == 4) = true then
        .ok (assembleHeader (total message) mask ++ body mask 0 message, (assembleHeader (total message) mask).length,
          (offsetsFold (Array.replicate slots 0) (assembleHeader (total message) mask).length message).toList)
      else .error "request size" := by
  unfold assemble
  simp only [pure_bind, bind_pure_comp, map_pure]
  split
  · rw [forIn_eq_foldl' _ _ _ (stepA (assembleHeader (total message) mask).length mask) (by
      intro piece r
      cases piece <;> simp [stepA, map_pure, List.forIn_pure_yield_eq_foldl, assembleHeader])]
    obtain ⟨f1, f2⟩ := foldA (assembleHeader (total message) mask).length mask message
      (assembleHeader (total message) mask).toArray (Array.replicate slots 0) (by simp)
    simp only [List.size_toArray, Nat.sub_self] at f1 f2
    simp only [assembleHeader, map_pure] at f1 f2 ⊢
    rw [f1, f2]
    rfl
  · rfl

/-! ### The three messages (`sendMessage`, `fetchMessage`, `devicesMessage`: the builders' own) -/

/-- The 8-byte header `build` writes: FIN + binary, masked, 16-bit payload length, the mask. -/
def buildHeader (size : Nat) (mask : List Byte) : List Byte :=
  [130, 254, BitVec.ofNat 8 (size / 256), BitVec.ofNat 8 size] ++ mask

/-- **`build` as a function.** It accepts exactly when the payload is 126..65535 bytes and the
mask 4 bytes; then the frame is the 8-byte header and the payload `body`, and the offsets are what
the slot pieces set (from `#[0, 0, 0, 0]`). -/
theorem build_eq (envelope : List Byte) (timestamp id : Nat) (mask : List Byte) (official : Bool) :
    build envelope timestamp id mask official =
      if (decide (126 ≤ total (sendMessage envelope timestamp id official)) &&
          decide (total (sendMessage envelope timestamp id official) < 65536) && mask.length == 4) = true then
        .ok (buildHeader (total (sendMessage envelope timestamp id official)) mask ++
            body mask 0 (sendMessage envelope timestamp id official),
          (offsetsFold #[0, 0, 0, 0] 8 (sendMessage envelope timestamp id official)).toList)
      else .error "request size" := by
  unfold build
  simp only [pure_bind, bind_pure_comp, map_pure]
  generalize sendMessage envelope timestamp id official = m
  by_cases hc : (decide (126 ≤ total m) && decide (total m < 65536) && mask.length == 4) = true
  · rw [if_pos hc, if_pos hc]
    have h4 : mask.length = 4 := by simp at hc; exact hc.2
    rw [forIn_eq_foldl' _ _ _ (stepB mask) (by intro piece r; cases piece <;> simp [stepB, map_pure, List.forIn_pure_yield_eq_foldl])]
    obtain ⟨f1, f2⟩ := foldB mask m (buildHeader (total m) mask) #[0, 0, 0, 0] (by simp [buildHeader, h4])
    have len : (buildHeader (total m) mask).length = 8 := by simp [buildHeader, h4]
    rw [len] at f1 f2
    simp only [buildHeader, map_pure, Nat.sub_self] at f1 f2 ⊢
    rw [f1, f2]
    rfl
  · rw [if_neg hc, if_neg hc]
    rfl

theorem buildFetch_eq (id : Nat) (mask : List Byte) : buildFetch id mask = assemble (fetchMessage id) mask 2 := rfl

theorem buildDevices_eq (envelopes : List (List Byte)) (timestamp id : Nat) (mask : List Byte) (official : Bool) :
    buildDevices envelopes timestamp id mask official =
      if envelopes.isEmpty then .error "no devices"
      else assemble (devicesMessage envelopes timestamp id official) mask (2 + 2 * envelopes.length) := by
  unfold buildDevices
  cases h : envelopes.isEmpty <;> rfl

/-! ### Inserting the slots into the frame -/

/-- The slot list for the kernels: each slot's frame offset with its value. -/
def slotsOf (values : Nat → List Byte) (table : List (Nat × Nat × Nat)) : List (Nat × List Byte) :=
  table.map (fun e => (e.2.1, values e.1))

/-- The payload with every slot filled with its value, masked: text masked as in `body`, slot `k`
replaced by `values k` masked from its position. -/
def filled (mask : List Byte) (values : Nat → List Byte) : Nat → List Piece → List Byte
  | _, [] => []
  | pos, .bytes v :: rest => maskFrom mask pos v ++ filled mask values (pos + v.length) rest
  | pos, .slot k w :: rest => maskFrom mask pos (values k) ++ filled mask values (pos + w) rest

/-- Every slot of the table is filled with a value of exactly its width. -/
def Fits (values : Nat → List Byte) (table : List (Nat × Nat × Nat)) : Prop :=
  ∀ e ∈ table, (values e.1).length = e.2.2

def covers (s : Nat × List Byte) (i : Nat) : Prop := s.1 ≤ i ∧ i < s.1 + s.2.length

/-- `insertSlots` from frame index `k` on (on values). -/
def insertFrom (S : List (Nat × List Byte)) (hl : Nat) (mask : List Byte) (k : Nat) (l : List Byte) : List Byte :=
  (l.zipIdx k).map (fun pair => match slotAt (0 : Byte) S pair.2 with
    | some secret => pair.1 ^^^ (secret ^^^ mask.getD ((pair.2 - hl) % 4) 0)
    | none => pair.1)

theorem insertSlots_eq_insertFrom (S : List (Nat × List Byte)) (hl : Nat) (mask frame : List Byte) :
    insertSlots ByteAuth.concrete 0 frame mask hl S = insertFrom S hl mask 0 frame := by
  unfold insertSlots insertFrom
  congr 1
  funext pair
  cases h : slotAt (0 : Byte) S pair.2 <;> simp only [h] <;> rfl

theorem insertFrom_append (S : List (Nat × List Byte)) (hl : Nat) (mask : List Byte) (k : Nat) (l₁ l₂ : List Byte) :
    insertFrom S hl mask k (l₁ ++ l₂) = insertFrom S hl mask k l₁ ++ insertFrom S hl mask (k + l₁.length) l₂ := by
  simp [insertFrom, List.zipIdx_append]

theorem insertFrom_none (S : List (Nat × List Byte)) (hl : Nat) (mask : List Byte) :
    ∀ (l : List Byte) (k : Nat), (∀ j, j < l.length → slotAt (0 : Byte) S (k + j) = none) → insertFrom S hl mask k l = l
  | [], _, _ => rfl
  | b :: l, k, h => by
      have h0 := h 0 (by simp)
      have rest := insertFrom_none S hl mask l (k + 1) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [show k + (j + 1) = k + 1 + j by omega] at this)
      simp only [Nat.add_zero] at h0
      simp only [insertFrom, List.zipIdx_cons, List.map_cons, h0] at rest ⊢
      rw [rest]

theorem insertFrom_slot (S : List (Nat × List Byte)) (hl : Nat) (mask : List Byte) :
    ∀ (v : List Byte) (k : Nat), hl ≤ k → (∀ j, j < v.length → slotAt (0 : Byte) S (k + j) = some (v.getD j 0)) →
      insertFrom S hl mask k (List.replicate v.length 0) = maskFrom mask (k - hl) v
  | [], _, _, _ => rfl
  | b :: v, k, hk, h => by
      have h0 := h 0 (by simp)
      have rest := insertFrom_slot S hl mask v (k + 1) (by omega) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [show k + (j + 1) = k + 1 + j by omega] at this)
      simp only [Nat.add_zero, List.getD_cons_zero] at h0
      simp only [insertFrom, List.length_cons, List.replicate_succ, List.zipIdx_cons, List.map_cons, h0] at rest ⊢
      rw [rest, show k + 1 - hl = k - hl + 1 by omega]
      simp [maskFrom]

theorem slotTable_ge : ∀ (start : Nat) (msg : List Piece), ∀ e ∈ slotTable start msg, start ≤ e.2.1
  | _, [], _, h => by simp [slotTable] at h
  | start, .bytes v :: rest, e, h => by
      have := slotTable_ge (start + v.length) rest e h
      omega
  | start, .slot k w :: rest, e, h => by
      simp only [slotTable, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · have := slotTable_ge (start + w) rest e h
        omega

theorem slotAt_none_of (L : List (Nat × List Byte)) (i : Nat) (h : ∀ s ∈ L, ¬ covers s i) :
    slotAt (0 : Byte) L i = none := by
  unfold slotAt
  rw [List.findSome?_eq_none_iff]
  intro s hs
  have := h s hs
  simp only [covers] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [if_neg this]

theorem slotAt_table_below (values : Nat → List Byte) (start : Nat) (msg : List Piece) (i : Nat) (hi : i < start) :
    slotAt (0 : Byte) (slotsOf values (slotTable start msg)) i = none := by
  apply slotAt_none_of
  intro s hs hc
  simp only [slotsOf, List.mem_map] at hs
  obtain ⟨e, he, rfl⟩ := hs
  have := slotTable_ge start msg e he
  simp only [covers] at hc
  omega

theorem fits_cons_slot (values : Nat → List Byte) (start k w : Nat) (rest : List Piece)
    (h : Fits values (slotTable start (.slot k w :: rest))) :
    (values k).length = w ∧ Fits values (slotTable (start + w) rest) := by
  refine ⟨h (k, start, w) (by simp [slotTable]), fun e he => h e (by simp [slotTable, he])⟩

/-- The payload part: with `S` agreeing with the table from `hl + pos` on, inserting into the built
payload gives the filled payload. -/
theorem insertFrom_body (S : List (Nat × List Byte)) (hl : Nat) (mask : List Byte) (values : Nat → List Byte) :
    ∀ (msg : List Piece) (pos : Nat), Fits values (slotTable (hl + pos) msg) →
      (∀ i, hl + pos ≤ i → slotAt (0 : Byte) S i = slotAt 0 (slotsOf values (slotTable (hl + pos) msg)) i) →
      insertFrom S hl mask (hl + pos) (body mask pos msg) = filled mask values pos msg
  | [], _, _, _ => rfl
  | .bytes v :: rest, pos, fits, same => by
      simp only [body, filled, insertFrom_append, maskFrom_length]
      have tail : slotTable (hl + pos) (.bytes v :: rest) = slotTable (hl + (pos + v.length)) rest := by
        simp [slotTable, Nat.add_assoc]
      rw [tail] at fits same
      have ih := insertFrom_body S hl mask values rest (pos + v.length) fits
        (fun i hi => same i (by omega))
      rw [show hl + pos + v.length = hl + (pos + v.length) by omega, ih]
      congr 1
      rw [insertFrom_none S hl mask (maskFrom mask pos v) (hl + pos) (fun j hj => by
        rw [maskFrom_length] at hj
        rw [same _ (by omega)]
        exact slotAt_table_below values _ rest _ (by omega))]
  | .slot k w :: rest, pos, fits, same => by
      obtain ⟨wk, fits'⟩ := fits_cons_slot values (hl + pos) k w rest fits
      simp only [body, filled, insertFrom_append, List.length_replicate]
      have ih := insertFrom_body S hl mask values rest (pos + w) (by rwa [Nat.add_assoc] at fits')
        (fun i hi => by
          rw [same i (by omega)]
          simp only [slotsOf, slotTable, List.map_cons]
          unfold slotAt
          rw [List.findSome?_cons]
          simp only [Bool.and_eq_true, decide_eq_true_eq, wk]
          rw [if_neg (by omega), Nat.add_assoc])
      rw [show hl + pos + w = hl + (pos + w) by omega, ih]
      congr 1
      rw [← wk, insertFrom_slot S hl mask (values k) (hl + pos) (by omega) (fun j hj => by
        rw [same _ (by omega)]
        simp only [slotsOf, slotTable, List.map_cons]
        unfold slotAt
        rw [List.findSome?_cons]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [if_pos ⟨by omega, by omega⟩, show hl + pos + j - (hl + pos) = j by omega]),
        show hl + pos - hl = pos by omega]

theorem maskFrom_append (mask : List Byte) : ∀ (pos : Nat) (a b : List Byte),
    maskFrom mask pos (a ++ b) = maskFrom mask pos a ++ maskFrom mask (pos + a.length) b
  | _, [], _ => rfl
  | pos, x :: a, b => by
      simp only [List.cons_append, maskFrom, maskFrom_append mask (pos + 1) a b, List.length_cons]
      rw [show pos + 1 + a.length = pos + (a.length + 1) by omega]

/-- The filled payload is the rendered message, masked. -/
theorem filled_eq (mask : List Byte) (values : Nat → List Byte) :
    ∀ (msg : List Piece) (start pos : Nat), Fits values (slotTable start msg) →
      filled mask values pos msg = maskFrom mask pos (render values msg)
  | [], _, _, _ => rfl
  | .bytes v :: rest, start, pos, fits => by
      simp only [filled, render, maskFrom_append, filled_eq mask values rest (start + v.length) (pos + v.length) fits]
  | .slot k w :: rest, start, pos, fits => by
      obtain ⟨wk, fits'⟩ := fits_cons_slot values start k w rest fits
      simp only [filled, render, maskFrom_append, filled_eq mask values rest (start + w) (pos + w) fits', wk]

/-- **The plaintext of a request kernel is the frame of the filled message.** Let `frame` be a
header followed by the built payload of `msg` (text masked, zero slots), and let the kernel's slot
list `S` agree with the slot table (each slot at its frame offset, holding its value) at every
index. If every value has its slot's width, `insertSlots` gives the header followed by the
rendered message, masked from payload position 0. -/
theorem insertSlots_frame (header mask : List Byte) (msg : List Piece) (values : Nat → List Byte)
    (S : List (Nat × List Byte)) (fits : Fits values (slotTable header.length msg))
    (same : ∀ i, slotAt (0 : Byte) S i = slotAt 0 (slotsOf values (slotTable header.length msg)) i) :
    insertSlots ByteAuth.concrete 0 (header ++ body mask 0 msg) mask header.length S =
      header ++ maskFrom mask 0 (render values msg) := by
  rw [insertSlots_eq_insertFrom, insertFrom_append]
  congr 1
  · exact insertFrom_none S header.length mask header 0 (fun j hj => by
      rw [same]
      exact slotAt_table_below values _ msg _ (by omega))
  · have h := insertFrom_body S header.length mask values msg 0 (by simpa using fits)
      (fun i _ => by simpa using same i)
    simp only [Nat.add_zero] at h
    rw [Nat.zero_add, h, filled_eq mask values msg header.length 0 fits]

/-! ### Slots do not overlap; the order of the kernel's slot list does not matter -/

theorem slotAt_eq_some (L : List (Nat × List Byte)) (i : Nat) (t : Nat × List Byte) (ht : t ∈ L) (ct : covers t i)
    (unique : ∀ s ∈ L, covers s i → s = t) : slotAt (0 : Byte) L i = some (t.2.getD (i - t.1) 0) := by
  induction L with
  | nil => cases ht
  | cons s rest ih =>
      unfold slotAt
      rw [List.findSome?_cons]
      by_cases cs : covers s i
      · have := unique s (by simp) cs
        subst this
        simp only [covers] at cs
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [if_pos cs]
      · have hs : ¬ (s.1 ≤ i ∧ i < s.1 + s.2.length) := cs
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [if_neg hs]
        have tr : t ∈ rest := by
          rcases List.mem_cons.mp ht with h | h
          · subst h; exact absurd ct cs
          · exact h
        have := ih tr (fun s' hs' => unique s' (by simp [hs']))
        unfold slotAt at this
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this

/-- `slotAt` depends only on the members of the list, when no two members cover the same index. -/
theorem slotAt_congr (L L' : List (Nat × List Byte)) (i : Nat) (mem : ∀ s, s ∈ L ↔ s ∈ L')
    (disjoint : ∀ s ∈ L', ∀ t ∈ L', covers s i → covers t i → s = t) :
    slotAt (0 : Byte) L i = slotAt 0 L' i := by
  by_cases h : ∃ t ∈ L', covers t i
  · obtain ⟨t, ht, ct⟩ := h
    rw [slotAt_eq_some L i t ((mem t).mpr ht) ct (fun s hs cs => disjoint s ((mem s).mp hs) t ht cs ct),
      slotAt_eq_some L' i t ht ct (fun s hs cs => disjoint s hs t ht cs ct)]
  · have none : ∀ s ∈ L', ¬ covers s i := fun s hs cs => h ⟨s, hs, cs⟩
    rw [slotAt_none_of L i (fun s hs => none s ((mem s).mp hs)), slotAt_none_of L' i none]

/-- No two slots of a message cover the same frame index. -/
theorem table_disjoint (values : Nat → List Byte) (i : Nat) :
    ∀ (msg : List Piece) (start : Nat), Fits values (slotTable start msg) →
      ∀ s ∈ slotsOf values (slotTable start msg), ∀ t ∈ slotsOf values (slotTable start msg),
        covers s i → covers t i → s = t
  | [], _, _ => by simp [slotTable, slotsOf]
  | .bytes v :: rest, start, fits => table_disjoint values i rest (start + v.length) fits
  | .slot k w :: rest, start, fits => by
      obtain ⟨wk, fits'⟩ := fits_cons_slot values start k w rest fits
      have ih := table_disjoint values i rest (start + w) fits'
      have far : ∀ s ∈ slotsOf values (slotTable (start + w) rest), start + w ≤ s.1 := by
        intro s hs
        simp only [slotsOf, List.mem_map] at hs
        obtain ⟨e, he, rfl⟩ := hs
        exact slotTable_ge _ rest e he
      intro s hs t ht cs ct
      simp only [slotsOf, slotTable, List.map_cons, List.mem_cons] at hs ht
      change s = (start, values k) ∨ s ∈ slotsOf values (slotTable (start + w) rest) at hs
      change t = (start, values k) ∨ t ∈ slotsOf values (slotTable (start + w) rest) at ht
      simp only [covers] at cs ct
      rcases hs with rfl | hs <;> rcases ht with rfl | ht
      · rfl
      · have := far t ht; simp only [wk] at cs; omega
      · have := far s hs; simp only [wk] at ct; omega
      · exact ih s hs t ht cs ct

/-! ### The offsets the builders return -/

/-- The slot indices of a message, in order. -/
def indicesOf : List Piece → List Nat
  | [] => []
  | .bytes _ :: rest => indicesOf rest
  | .slot k _ :: rest => k :: indicesOf rest

theorem slotTable_indices : ∀ (start : Nat) (msg : List Piece), (slotTable start msg).map (·.1) = indicesOf msg
  | _, [] => rfl
  | start, .bytes v :: rest => slotTable_indices (start + v.length) rest
  | start, .slot k w :: rest => by simp [slotTable, indicesOf, slotTable_indices (start + w) rest]

theorem offsetsFold_size : ∀ (O : Array Nat) (start : Nat) (msg : List Piece), (offsetsFold O start msg).size = O.size
  | _, _, [] => rfl
  | O, start, .bytes v :: rest => offsetsFold_size O (start + v.length) rest
  | O, start, .slot k w :: rest => by
      simp only [offsetsFold, offsetsFold_size _ (start + w) rest, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem offsetsFold_notin (k : Nat) :
    ∀ (O : Array Nat) (start : Nat) (msg : List Piece), k ∉ indicesOf msg → (offsetsFold O start msg)[k]? = O[k]?
  | _, _, [], _ => rfl
  | O, start, .bytes v :: rest, h => offsetsFold_notin k O (start + v.length) rest h
  | O, start, .slot j w :: rest, h => by
      simp only [indicesOf, List.mem_cons, not_or] at h
      simp only [offsetsFold]
      rw [offsetsFold_notin k _ (start + w) rest h.2, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
        if_neg (Ne.symm h.1)]

theorem offsetsFold_get :
    ∀ (O : Array Nat) (start : Nat) (msg : List Piece), (indicesOf msg).Nodup →
      ∀ e ∈ slotTable start msg, e.1 < O.size → (offsetsFold O start msg)[e.1]? = some e.2.1
  | _, _, [], _, e, he, _ => by simp [slotTable] at he
  | O, start, .bytes v :: rest, nd, e, he, small => offsetsFold_get O (start + v.length) rest nd e he small
  | O, start, .slot j w :: rest, nd, e, he, small => by
      simp only [indicesOf, List.nodup_cons] at nd
      simp only [slotTable, List.mem_cons] at he
      simp only [offsetsFold]
      rcases he with rfl | he
      · rw [offsetsFold_notin _ _ (start + w) rest nd.1, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
          if_pos rfl, if_pos small]
      · exact offsetsFold_get _ (start + w) rest nd.2 e he (by
          rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact small)

/-- **The slots the kernels receive, from the builders' offsets, insert the values.** If the kernel's
slot list is `(offsets[k], values k)` for the slot indices `ks` (any order; the same indices as the
message's, which are distinct and within the offsets array), and every value has its slot's width,
the plaintext is the header followed by the rendered message, masked. -/
theorem insertSlots_offsets (header mask : List Byte) (msg : List Piece) (values : Nat → List Byte)
    (O : Array Nat) (ks : List Nat) (fits : Fits values (slotTable header.length msg))
    (same : ∀ k, k ∈ ks ↔ k ∈ indicesOf msg) (nodup : (indicesOf msg).Nodup)
    (small : ∀ k ∈ indicesOf msg, k < O.size) :
    insertSlots ByteAuth.concrete 0 (header ++ body mask 0 msg) mask header.length
        (ks.map (fun k => ((offsetsFold O header.length msg).toList.getD k 0, values k))) =
      header ++ maskFrom mask 0 (render values msg) := by
  have get : ∀ e ∈ slotTable header.length msg, (offsetsFold O header.length msg).toList.getD e.1 0 = e.2.1 := by
    intro e he
    have inIdx : e.1 ∈ indicesOf msg := by
      rw [← slotTable_indices header.length msg]
      exact List.mem_map_of_mem he
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      offsetsFold_get O header.length msg nodup e he (small _ inIdx)]
    rfl
  apply insertSlots_frame header mask msg values _ fits
  intro i
  apply slotAt_congr _ _ i _ (table_disjoint values i msg header.length fits)
  intro s
  constructor
  · intro hs
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
    have inIdx := (same k).mp hk
    rw [← slotTable_indices header.length msg] at inIdx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp inIdx
    rw [get e he]
    exact List.mem_map_of_mem (f := fun e => (e.2.1, values e.1)) he
  · intro hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    have inIdx : e.1 ∈ indicesOf msg := by
      rw [← slotTable_indices header.length msg]
      exact List.mem_map_of_mem he
    refine List.mem_map.mpr ⟨e.1, (same e.1).mpr inIdx, ?_⟩
    rw [get e he]

/-! ### Slot indices and widths of the three messages -/

/-- The slot pieces of a message as (index, width), in order. -/
def pairsOf : List Piece → List (Nat × Nat)
  | [] => []
  | .bytes _ :: rest => pairsOf rest
  | .slot k w :: rest => (k, w) :: pairsOf rest

theorem pairsOf_append : ∀ (a b : List Piece), pairsOf (a ++ b) = pairsOf a ++ pairsOf b
  | [], _ => rfl
  | .bytes _ :: a, b => pairsOf_append a b
  | .slot k w :: a, b => by simp [pairsOf, pairsOf_append a b]

theorem pairsOf_field (tag : Nat) (ps : List Piece) : pairsOf (field tag ps) = pairsOf ps := rfl

theorem pairsOf_flatten : ∀ (L : List (List Piece)), pairsOf L.flatten = L.flatMap pairsOf
  | [] => rfl
  | p :: L => by simp [pairsOf_append, pairsOf_flatten L]

theorem indicesOf_pairs : ∀ msg : List Piece, indicesOf msg = (pairsOf msg).map (·.1)
  | [] => rfl
  | .bytes _ :: rest => indicesOf_pairs rest
  | .slot k w :: rest => by simp [indicesOf, pairsOf, indicesOf_pairs rest]

theorem fits_of_pairs (values : Nat → List Byte) :
    ∀ (start : Nat) (msg : List Piece), (∀ p ∈ pairsOf msg, (values p.1).length = p.2) → Fits values (slotTable start msg)
  | _, [], _ => by simp [Fits, slotTable]
  | start, .bytes v :: rest, h => fits_of_pairs values (start + v.length) rest h
  | start, .slot k w :: rest, h => by
      intro e he
      simp only [slotTable, List.mem_cons] at he
      rcases he with rfl | he
      · exact h (k, w) (by simp [pairsOf])
      · exact fits_of_pairs values (start + w) rest (fun p hp => h p (by simp [pairsOf, hp])) e he

theorem sendMessage_pairs (envelope : List Byte) (timestamp id : Nat) (official : Bool) :
    pairsOf (sendMessage envelope timestamp id official) = [(0, 36), (2, 3), (3, 10), (1, 24)] := by
  cases official <;> simp [sendMessage, officialJson, pairsOf_append, pairsOf_field, pairsOf_flatten, pairsOf]

theorem fetchMessage_pairs (id : Nat) : pairsOf (fetchMessage id) = [(0, 36), (1, 24)] := by
  simp [fetchMessage, pairsOf_append, pairsOf_field, pairsOf]

/-- The device slots of `buildDevices`: device `i` has its id at slot `2 + 2i` (3 bytes) and its
registration id at `3 + 2i` (10 bytes). -/
def deviceSlotPairs (count : Nat) : List (Nat × Nat) :=
  (List.range count).flatMap (fun i => [(2 + 2 * i, 3), (3 + 2 * i, 10)])

theorem zipIdx_flatMap_snd {α β : Type} (l : List α) (g : Nat → List β) :
    l.zipIdx.flatMap (fun p => g p.2) = (List.range l.length).flatMap g := by
  have gen : ∀ (l : List α) (n : Nat), (l.zipIdx n).flatMap (fun p => g p.2) =
      (List.range' n l.length).flatMap g := by
    intro l
    induction l with
    | nil => intro n; rfl
    | cons x l ih => intro n; simp [List.zipIdx_cons, List.range'_succ, ih]
  rw [gen l 0, List.range_eq_range']

theorem devicesMessage_pairs (envelopes : List (List Byte)) (timestamp id : Nat)
    (official : Bool) :
    pairsOf (devicesMessage envelopes timestamp id official) =
      [(0, 36)] ++ deviceSlotPairs envelopes.length ++ [(1, 24)] := by
  have block : ∀ (f : List Byte × Nat → List Piece),
      (∀ p, pairsOf (f p) = [(2 + 2 * p.2, 3), (3 + 2 * p.2, 10)]) →
      pairsOf (envelopes.zipIdx.map f).flatten = deviceSlotPairs envelopes.length := by
    intro f hf
    rw [pairsOf_flatten, List.flatMap_map]
    simp only [hf]
    exact zipIdx_flatMap_snd envelopes (fun i => [(2 + 2 * i, 3), (3 + 2 * i, 10)])
  cases official
  · simp only [devicesMessage, pairsOf, pairsOf_append, pairsOf_field, Bool.false_eq_true, if_false]
    rw [block _ (fun p => by simp [pairsOf])]
    simp [pairsOf]
  · simp only [devicesMessage, officialJson, pairsOf, pairsOf_append, pairsOf_field, if_true]
    rw [block _ (fun p => by simp [pairsOf, pairsOf_append])]
    simp

/-! ### Widths of the slot encoders -/

theorem uuid_length {B : Type} (a : ByteAuth.Ops B) (raw : List B) : (RelayEncoding.uuid a raw).length = 36 := by
  simp [RelayEncoding.uuid, List.length_flatMap, apply_ite List.length]
  decide

theorem base64_length {B : Type} (a : ByteAuth.Ops B) (raw : List B) :
    (RelayEncoding.base64 a raw).length = 4 * ((raw.length + 2) / 3) := by
  simp [RelayEncoding.base64, List.length_flatMap]
  have rep : ∀ n : Nat, (List.replicate n 4).sum = 4 * n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]; omega
  rw [List.map_const', List.length_range, rep]

theorem paddedDecimal_length (n : BitVec 64) (width : Nat) (h : width ≤ 20) :
    (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0 n width).2.length = width := by
  simp [paddedDecimalWith, PrivateDecimal.encode, PrivateProtobuf.gate, PrivateBuffer.finish, ByteAuth.release,
    PrivateBuffer.make]
  omega

/-! ### What the server receives: the three request kernels on the frames the controller builds -/

/-- **What `build` returns.** It returns a frame only for a payload of 126..65535 bytes and a
4-byte mask, and then the frame is the 8-byte header `[130, 254, size / 256, size] ‖ mask`
followed by the built payload. So the WebSocket payload of every frame `build` returns starts at
frame index 8: `signal-request-ctr`'s fixed `mask[(i − 8) % 4]` is the right mask byte for it. -/
theorem build_ok (envelope : List Byte) (timestamp id : Nat) (mask frame : List Byte)
    (official : Bool) (offsets : List Nat) (built : build envelope timestamp id mask official = .ok (frame, offsets)) :
    let msg := sendMessage envelope timestamp id official
    126 ≤ total msg ∧ total msg < 65536 ∧ mask.length = 4 ∧ (buildHeader (total msg) mask).length = 8 ∧
      frame = buildHeader (total msg) mask ++ body mask 0 msg ∧ offsets = (offsetsFold #[0, 0, 0, 0] 8 msg).toList := by
  intro msg
  rw [build_eq] at built
  by_cases hc : (decide (126 ≤ total msg) && decide (total msg < 65536) && mask.length == 4) = true
  · rw [if_pos hc] at built
    simp only [Except.ok.injEq, Prod.mk.injEq] at built
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, by simp [buildHeader, hc.2], built.1.symm, built.2.symm⟩
  · rw [if_neg hc] at built
    cases built

/-- The values of `signal-request-ctr`'s four slots (0 UUID, 1 access key, 2 device id,
3 registration id), from the conversation record (`signalRequestSlots`). -/
def requestValues (cert : Nat) (conversation : List Byte) (k : Nat) : List Byte :=
  ((signalRequestSlots cert 0 0 0 0 conversation).2.getD k (0, [])).2

open TlsMpc.HybridKernel (lookup) in
/-- **`signal-request-ctr` on a frame `build` returned seals the WebSocket frame of the filled
request.** For every input assignment whose `frame` and `mask` are a frame and mask `build`
returned, with the kernel named by that frame's length and offsets (as the controller names it):
the kernel's outputs are `sealedRequest` of `header ‖ masked(render values msg)` — the 8-byte
header and the request message with the contact's UUID, base64 access key and space-padded device
and registration ids in place of the four slots, masked with the WebSocket mask. -/
theorem signalRequestCtr_built (envelope : List Byte) (timestamp id : Nat)
    (mask frame : List Byte) (official : Bool) (offsets : List Nat)
    (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (cert : Nat) (assign : BVExpr.Assignment)
    (hframe : (lookup (signalRequestInputs cert frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (signalRequestInputs cert frame.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (signalRequestInputs cert frame.length) name).map (BVExpr.eval assign)
    let msg := sendMessage envelope timestamp id official
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (buildHeader (total msg) mask ++ maskFrom mask 0 (render (requestValues cert (get "conversation")) msg))
        (signalRequestSlots cert 0 0 0 0 (get "conversation")).1 := by
  intro get msg
  obtain ⟨_, _, _, h8, hf, ho⟩ := build_ok envelope timestamp id mask frame official offsets built
  rw [signalRequestCtr_spec]
  have convLength : (get "conversation").length = HybridKernel.conversationBytes cert 80 := by
    simp [get, lookup, HybridKernel.lookupFrom, signalRequestInputs, ByteCircuit.inputBytes]
  have hget : ∀ name, (lookup (signalRequestInputs cert frame.length) name).map (BVExpr.eval assign) = get name :=
    fun _ => rfl
  simp only [hget] at hframe hmask ⊢
  rw [hframe, hmask]
  have kernelSlots : (signalRequestSlots cert (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0) (offsets.getD 3 0)
      (get "conversation")).2 =
      [0, 1, 2, 3].map (fun k => ((offsetsFold #[0, 0, 0, 0] 8 msg).toList.getD k 0,
        requestValues cert (get "conversation") k)) := by
    rw [← ho]
    rfl
  have valid : (signalRequestSlots cert (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0) (offsets.getD 3 0)
      (get "conversation")).1 = (signalRequestSlots cert 0 0 0 0 (get "conversation")).1 := rfl
  rw [kernelSlots, valid, hf]
  congr 1
  have key := insertSlots_offsets (buildHeader (total msg) mask) mask msg (requestValues cert (get "conversation"))
    #[0, 0, 0, 0] [0, 1, 2, 3]
  rw [h8] at key
  apply key
  · apply fits_of_pairs
    rw [sendMessage_pairs]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact uuid_length _ _
    · exact paddedDecimal_length _ 3 (by omega)
    · exact paddedDecimal_length _ 10 (by omega)
    · show (RelayEncoding.base64 _ _).length = 24
      rw [base64_length]
      simp [convLength, HybridKernel.conversationBytes]
  · intro k
    rw [indicesOf_pairs, sendMessage_pairs]
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    omega
  · rw [indicesOf_pairs, sendMessage_pairs]; decide
  · rw [indicesOf_pairs, sendMessage_pairs]
    intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
    show k < 4
    omega

/-- **What `assemble` returns** (`buildFetch`, `buildDevices`): a frame only for a payload of
1..65535 bytes and a 4-byte mask; then the payload starts right after the header (2 + 4 or 4 + 4
bytes), and the frame is that header followed by the built payload. -/
theorem assemble_ok (message : List Piece) (mask frame : List Byte) (slots payloadAt : Nat) (offsets : List Nat)
    (built : assemble message mask slots = .ok (frame, payloadAt, offsets)) :
    0 < total message ∧ total message < 65536 ∧ mask.length = 4 ∧
      payloadAt = (assembleHeader (total message) mask).length ∧
      frame = assembleHeader (total message) mask ++ body mask 0 message ∧
      offsets = (offsetsFold (Array.replicate slots 0) payloadAt message).toList := by
  rw [assemble_eq] at built
  by_cases hc : (decide (0 < total message) && decide (total message < 65536) && mask.length == 4) = true
  · rw [if_pos hc] at built
    simp only [Except.ok.injEq, Prod.mk.injEq] at built
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨f, p, o⟩ := built
    subst f p o
    exact ⟨hc.1.1, hc.1.2, hc.2, rfl, rfl, rfl⟩
  · rw [if_neg hc] at built
    cases built

/-- The values of `bundle-fetch-ctr`'s two slots (0 UUID, 1 access key), from the record. -/
def fetchValues (record : List Byte) (k : Nat) : List Byte :=
  [RelayEncoding.uuid ByteAuth.concrete ((record.drop 262).take 16),
    RelayEncoding.base64 ByteAuth.concrete ((record.drop 278).take 16)].getD k []

open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-fetch-ctr` on a frame `buildFetch` returned seals the WebSocket frame of
`GET /v2/keys/{uuid}/*` with the contact's UUID and base64 access key in place**, valid when the
record is live. -/
theorem bundleFetchCtr_built (id : Nat) (mask frame : List Byte) (payloadAt : Nat) (offsets : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets)) (assign : BVExpr.Assignment)
    (hframe : (lookup (fetchInputs frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (fetchInputs frame.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (fetchInputs frame.length) name).map (BVExpr.eval assign)
    (BundleKernel.bundleFetchCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0)).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total (fetchMessage id)) mask ++ maskFrom mask 0 (render (fetchValues (get "record")) (fetchMessage id)))
        (liveValue (get "record")) := by
  intro get
  rw [buildFetch_eq] at built
  obtain ⟨_, _, _, hp, hf, ho⟩ := assemble_ok _ mask frame 2 payloadAt offsets built
  rw [bundleFetchCtr_spec]
  have recordLength : (get "record").length = BundleKernel.recordBytes := by
    simp [get, lookup, HybridKernel.lookupFrom, fetchInputs, BundleKernel.requestInputs, ByteCircuit.inputBytes]
  have hget : ∀ name, (lookup (fetchInputs frame.length) name).map (BVExpr.eval assign) = get name := fun _ => rfl
  simp only [hget] at hframe hmask ⊢
  rw [hframe, hmask]
  have kernelSlots : [(offsets.getD 0 0, RelayEncoding.uuid ByteAuth.concrete (((get "record").drop 262).take 16)),
      (offsets.getD 1 0, RelayEncoding.base64 ByteAuth.concrete (((get "record").drop 278).take 16))] =
      [0, 1].map (fun k => ((offsetsFold (Array.replicate 2 0) payloadAt (fetchMessage id)).toList.getD k 0,
        fetchValues (get "record") k)) := by
    rw [← ho]
    rfl
  rw [kernelSlots, hf]
  congr 1
  have key := insertSlots_offsets (assembleHeader (total (fetchMessage id)) mask) mask (fetchMessage id)
    (fetchValues (get "record")) (Array.replicate 2 0) [0, 1]
  rw [← hp] at key
  apply key
  · apply fits_of_pairs
    rw [fetchMessage_pairs]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact uuid_length _ _
    · show (RelayEncoding.base64 _ _).length = 24
      rw [base64_length]
      simp [recordLength, BundleKernel.recordBytes]
  · intro k
    rw [indicesOf_pairs, fetchMessage_pairs]
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  · rw [indicesOf_pairs, fetchMessage_pairs]; decide
  · rw [indicesOf_pairs, fetchMessage_pairs]
    intro k hk
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
    simp only [Array.size_replicate]
    omega

/-! #### `bundle-request-ctr` -/

/-- Device `i`'s space-padded device id and registration id, from its record (as `deviceValue`). -/
def deviceBytes (records : List Byte) (i : Nat) : List Byte := ((deviceValue records (0, 0) i).2.getD 0 (0, [])).2
def registrationBytes (records : List Byte) (i : Nat) : List Byte := ((deviceValue records (0, 0) i).2.getD 1 (0, [])).2

theorem deviceValue_snd (records : List Byte) (slot : Nat × Nat) (i : Nat) :
    (deviceValue records slot i).2 = [(slot.1, deviceBytes records i), (slot.2, registrationBytes records i)] := rfl

/-- The values of `bundle-request-ctr`'s slots: 0 UUID and 1 access key of the first record,
`2 + 2i` device `i`'s id, `3 + 2i` its registration id. -/
def devicesValues (records : List Byte) (k : Nat) : List Byte :=
  if k = 0 then RelayEncoding.uuid ByteAuth.concrete ((records.drop 262).take 16)
  else if k = 1 then RelayEncoding.base64 ByteAuth.concrete ((records.drop 278).take 16)
  else if k % 2 = 0 then deviceBytes records ((k - 2) / 2) else registrationBytes records ((k - 2) / 2)

theorem devicesValues_device (records : List Byte) (i : Nat) :
    devicesValues records (2 + 2 * i) = deviceBytes records i := by
  simp only [devicesValues]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (2 + 2 * i - 2) / 2 = i by omega]

theorem devicesValues_registration (records : List Byte) (i : Nat) :
    devicesValues records (3 + 2 * i) = registrationBytes records i := by
  simp only [devicesValues]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (3 + 2 * i - 2) / 2 = i by omega]

theorem pairs_spec : ∀ (l : List Nat) (ds : List (Nat × Nat)), BundleKernel.pairs l = some ds →
    ds = (List.range (l.length / 2)).map (fun i => (l.getD (2 * i) 0, l.getD (2 * i + 1) 0))
  | [], ds, h => by simp [BundleKernel.pairs] at h; subst h; rfl
  | [_], ds, h => by simp [BundleKernel.pairs] at h
  | x :: y :: rest, ds, h => by
      simp only [BundleKernel.pairs, Option.map_eq_some_iff] at h
      obtain ⟨ds', h', rfl⟩ := h
      rw [pairs_spec rest ds' h']
      simp only [List.length_cons, show (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 by omega,
        List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.mul_zero, List.getD_cons_zero, Nat.zero_add, List.getD_cons_succ, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, show 2 * (i + 1) = 2 * i + 1 + 1 by omega,
        show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl, List.getD_cons_succ]

theorem range_zipIdx (m : Nat) : (List.range m).zipIdx = (List.range m).map (fun i => (i, i)) := by
  have gen : ∀ m n, (List.range' n m).zipIdx n = (List.range' n m).map (fun i => (i, i)) := by
    intro m
    induction m with
    | zero => intro; rfl
    | succ m ih => intro n; simp [List.range'_succ, List.zipIdx_cons, ih]
  rw [List.range_eq_range', gen]

/-- The device slot indices `2, 3, …, 2m + 1`. -/
def deviceIndices (m : Nat) : List Nat := (List.range m).flatMap (fun i => [2 + 2 * i, 3 + 2 * i])

theorem deviceIndices_eq (m : Nat) : deviceIndices m = (List.range (2 * m)).map (· + 2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [deviceIndices] at ih ⊢
      rw [List.range_succ, List.flatMap_append, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.range_succ,
        List.range_succ]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append]
      rw [show 2 + 2 * m = 2 * m + 2 by omega, show 3 + 2 * m = 2 * m + 1 + 2 by omega]

theorem mem_deviceIndices (m k : Nat) : k ∈ deviceIndices m ↔ 2 ≤ k ∧ k < 2 + 2 * m := by
  rw [deviceIndices_eq]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨k - 2, by omega, by omega⟩

theorem deviceSlotPairs_fst (m : Nat) : (deviceSlotPairs m).map (·.1) = deviceIndices m := by
  simp [deviceSlotPairs, deviceIndices, List.map_flatMap]

set_option maxHeartbeats 1000000 in
open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-request-ctr` on a frame `buildDevices` returned seals the WebSocket frame of
`PUT /v1/messages/{uuid}` with the contact's UUID and access key and every device's padded ids in
place**, valid when every device's record is live and its numbers fit. The kernel is named as the
controller names it: frame length, payload start, the UUID and key offsets, and the device slot
offsets paired up as `find` pairs them (`BundleKernel.pairs (offsets.drop 2) = some devices`). -/
theorem bundleRequestCtr_built (envelopes : List (List Byte)) (timestamp id : Nat)
    (mask frame : List Byte) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let msg := devicesMessage envelopes timestamp id official
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (assembleHeader (total msg) mask ++ maskFrom mask 0 (render (devicesValues (get "records")) msg))
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 := by
  intro get msg
  rw [buildDevices_eq] at built
  by_cases empty : envelopes.isEmpty = true
  · rw [if_pos empty] at built; cases built
  rw [if_neg empty] at built
  obtain ⟨_, _, _, hp, hf, ho⟩ := assemble_ok _ mask frame _ payloadAt offsets built
  have nonempty : 0 < envelopes.length := by
    cases envelopes with
    | nil => exact absurd rfl empty
    | cons _ _ => simp
  generalize hm : envelopes.length = m at built nonempty ho
  have offsetsLength : offsets.length = 2 + 2 * m := by
    rw [ho]; simp [offsetsFold_size]
  have hdev : devices = (List.range m).map (fun i => (offsets.getD (2 + 2 * i) 0, offsets.getD (3 + 2 * i) 0)) := by
    rw [pairs_spec _ devices paired]
    simp only [List.length_drop, offsetsLength, show (2 + 2 * m - 2) / 2 = m by omega, List.getD_eq_getElem?_getD,
      List.getElem?_drop]
    apply List.map_congr_left
    intro i _
    rw [show 2 + (2 * i + 1) = 3 + 2 * i by omega]
  have devLength : devices.length = m := by rw [hdev]; simp
  rw [bundleRequestCtr_spec]
  have hget : ∀ name, (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign) = get name :=
    fun _ => rfl
  simp only [hget] at hframe hmask ⊢
  rw [hframe, hmask]
  have recordsLength : (get "records").length = BundleKernel.recordBytes * m := by
    simp [get, lookup, HybridKernel.lookupFrom, requestInputsOf, BundleKernel.requestInputs, ByteCircuit.inputBytes,
      devLength]
  let o := fun k => (offsetsFold (Array.replicate (2 + 2 * m) 0) payloadAt msg).toList.getD k 0
  have ho' : ∀ k, offsets.getD k 0 = o k := by intro k; rw [ho]
  have kernelSlots : (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).2 =
      ([0, 1] ++ deviceIndices m).map (fun k => (o k, devicesValues (get "records") k)) := by
    simp only [bundleRequestValue, hdev, List.zipIdx_map, range_zipIdx, List.map_map, Function.comp_def,
      List.map_append, deviceIndices, List.map_flatMap, List.flatMap_map, List.map_cons, List.map_nil,
      devicesValues_device, devicesValues_registration, deviceValue_snd, ho']
    have h01 : [(o 0, devicesValues (get "records") 0), (o 1, devicesValues (get "records") 1)] =
        [(o 0, RelayEncoding.uuid ByteAuth.concrete ((get "records").drop 262 |>.take 16)),
          (o 1, RelayEncoding.base64 ByteAuth.concrete ((get "records").drop 278 |>.take 16))] := by
      simp [devicesValues]
    rw [h01]
    rfl
  rw [kernelSlots, hf]
  congr 1
  have key := insertSlots_offsets (assembleHeader (total msg) mask) mask msg (devicesValues (get "records"))
    (Array.replicate (2 + 2 * m) 0) ([0, 1] ++ deviceIndices m)
  rw [← hp] at key
  have pairsMsg := devicesMessage_pairs envelopes timestamp id official
  rw [hm] at pairsMsg
  have indices : indicesOf msg = [0] ++ deviceIndices m ++ [1] := by
    rw [indicesOf_pairs, pairsMsg]
    simp [deviceSlotPairs_fst]
  apply key
  · apply fits_of_pairs
    rw [pairsMsg]
    intro p hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, deviceSlotPairs, List.mem_flatMap,
      List.mem_range] at hp
    rcases hp with (rfl | ⟨i, hi, rfl | rfl⟩) | rfl
    · exact uuid_length _ _
    · simp only [devicesValues_device, deviceBytes, deviceValue]
      exact paddedDecimal_length _ 3 (by omega)
    · simp only [devicesValues_registration, registrationBytes, deviceValue]
      exact paddedDecimal_length _ 10 (by omega)
    · show (RelayEncoding.base64 _ _).length = 24
      rw [base64_length]
      have : 1 ≤ m := nonempty
      simp [recordsLength, BundleKernel.recordBytes]
      omega
  · intro k
    rw [indices]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ((h | h) | h) <;> simp [h]
    · rintro ((h | h) | h) <;> simp [h]
  · rw [indices]
    have nd : (deviceIndices m).Nodup := by
      rw [deviceIndices_eq, List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun h e => h (by omega))
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨by simp, nd, ?_⟩, by simp, ?_⟩
    · intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rw [mem_deviceIndices] at hb
      omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rw [mem_deviceIndices] at ha
      omega
  · rw [indices]
    intro k hk
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, mem_deviceIndices] at hk
    simp only [Array.size_replicate]
    omega

#print axioms build_eq
#print axioms assemble_eq
#print axioms build_ok
#print axioms assemble_ok
#print axioms insertSlots_frame
#print axioms insertSlots_offsets
#print axioms signalRequestCtr_built
#print axioms bundleFetchCtr_built
#print axioms bundleRequestCtr_built

end TlsMpc.KernelSpecs.RequestFrame
