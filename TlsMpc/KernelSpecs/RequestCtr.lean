import TlsMpc.SealCtrProofs
import TlsMpc.BundleKernels

/-!
Kernel-level specifications of the three slot sealers whose record goes to the Signal server:
`signal-request-ctr` (`HybridKernel.signalRequestCtr`), `bundle-fetch-ctr` and
`bundle-request-ctr` (`BundleKernel.bundleFetchCtr`, `bundleRequestCtr`).

New file; it changes no definition and no emitter imports it.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `insertSlots_map`, `slotAt_map`, `paddedDecimal_map`: the slot insertion and the
  space-padded decimal, written once over the operation records, commute with any
  homomorphism of the operations (the repository's usual `_map` pattern).
* `signalRequestCtr_spec`, `bundleFetchCtr_spec`, `bundleRequestCtr_spec`: on every input
  assignment, the kernel's four outputs (`accepted`, `header`, `ciphertext`, `pad`) are
  `[valid]`, the TLS record header of the inner plaintext, the AES-CTR encryption
  (`ctrOf`, as in `tlsSealCtr_spec`) of the inner plaintext released under `valid`, and the
  GCM pad (`padOf`). The plaintext is `insertSlots` on concrete bytes: the public frame with,
  at every index a slot covers, frame ⊕ slot byte ⊕ the WebSocket mask byte for that index.
  `valid` and the slot contents are the concrete instances of the same encoders
  (`RelayEncoding.uuid`, `base64`, `paddedDecimalWith` over `PrivateDecimal.encode`).
  The two bundle kernels go through `sealSlots_spec` (their shared `BundleKernel.sealSlots`).
* `signalRequestCtr_rejects`, `bundleFetchCtr_rejects`, `bundleRequestCtr_rejects`
  (and `sealedRequest_rejects`, `sealSlots_rejects`): when the opened `accepted` is 0 the
  opened ciphertext is all zero (so a refused request releases nothing beyond the header,
  whose length field depends on the public frame size only).
* `insertSlots_outside`, `insertSlots_inside`, `insertSlots_inside_zero`: what the insertion
  does to one index: a byte no slot covers is the frame byte, unchanged; a byte that the FIRST
  covering slot covers is frame ⊕ slot byte ⊕ mask byte, so where the controllers left the
  frame zero it is the WebSocket-masked slot byte.

Observation (not a counterexample): `signal-request-ctr` takes the mask byte of frame index `i`
as `mask[(i - 8) % 4]`, i.e. it assumes an 8-byte WebSocket header (payload length 126..65535);
`find` does not check that. For a payload under 126 bytes the header is 6 bytes and the slots
would be masked with the wrong mask bytes (corrupted, not leaked beyond what the server sees).
The two bundle kernels take the payload offset as a parameter.

The "spec" here is the kernel's own encoders on concrete values (as for the `receive-*` and
bundle kernels). NOT PROVED: that `uuid` / `base64` / the padded decimal are the RFC 4122 /
RFC 4648 / decimal encodings, and that the frame built in the clear (`PublicRequest.*`) has
zero bytes at the slots and no overlapping slots (T8). `find` checks that the slots of the two
bundle kernels do not overlap (`slotsOk`); for `signal-request-ctr` it checks bounds only.
-/
namespace TlsMpc.KernelSpecs
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape lookup lookupFrom pub priv sl inputValue ctrOf padOf)

/-! ### Slot insertion, over any operations -/

/-- The slot byte at frame index `index`: from the first slot (in list order) that covers it. -/
def slotAt (zero : B) (slots : List (Nat × List B)) (index : Nat) : Option B :=
  slots.findSome? (fun slot =>
    if slot.1 ≤ index && index < slot.1 + slot.2.length then some (slot.2.getD (index - slot.1) zero) else none)

/-- The plaintext the request kernels encrypt: the public `frame`, with every byte a slot covers
XORed with that slot byte and the WebSocket mask byte of its payload position. -/
def insertSlots (a : ByteAuth.Ops B) (zero : B) (frame mask : List B) (payloadAt : Nat)
    (slots : List (Nat × List B)) : List B :=
  frame.zipIdx.map (fun pair => match slotAt zero slots pair.2 with
    | some secret => a.xor pair.1 (a.xor secret (mask.getD ((pair.2 - payloadAt) % 4) zero))
    | none => pair.1)

/-- `HybridKernel.paddedDecimal` over any operations. -/
def paddedDecimalWith (d : RelayEncoding.DecimalOps B W) (a : ByteAuth.Ops B) (zero : B) (number : W)
    (width : Nat) : B × List B :=
  let buffer := PrivateDecimal.encode d a number
  (a.and buffer.valid (ByteAuth.zeroMask a (buffer.data.getD width zero)),
   (buffer.data.take width).map (fun byte => TlsInner.select a (ByteAuth.zeroMask a byte) (a.const 32) byte))

def mapSlots (f : B → B') (slots : List (Nat × List B)) : List (Nat × List B') :=
  slots.map (fun slot => (slot.1, slot.2.map f))

theorem getD_map' (f : B → B') (l : List B) (i : Nat) (d : B) : (l.map f).getD i (f d) = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD]

theorem slotAt_map (f : B → B') (zero : B) (slots : List (Nat × List B)) (index : Nat) :
    (slotAt zero slots index).map f = slotAt (f zero) (mapSlots f slots) index := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      unfold slotAt at ih ⊢
      simp only [mapSlots, List.map_cons, List.findSome?_cons, List.length_map] at ih ⊢
      by_cases h : (slot.1 ≤ index && index < slot.1 + slot.2.length) = true
      · simp only [h, if_true, Option.map_some, getD_map']
      · simp only [h, if_false, Bool.false_eq_true]
        exact ih

theorem zipIdx_map' (f : B → B') (l : List B) :
    (l.map f).zipIdx = l.zipIdx.map (fun pair => (f pair.1, pair.2)) := by
  rw [List.zipIdx_map]
  rfl

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha

theorem insertSlots_map (zero : B) (frame mask : List B) (payloadAt : Nat) (slots : List (Nat × List B)) :
    (insertSlots a zero frame mask payloadAt slots).map f =
      insertSlots a' (f zero) (frame.map f) (mask.map f) payloadAt (mapSlots f slots) := by
  unfold insertSlots
  rw [zipIdx_map', List.map_map, List.map_map]
  apply List.map_congr_left
  intro pair _
  have h := slotAt_map f zero slots pair.2
  simp only [Function.comp_apply]
  cases hs : slotAt zero slots pair.2 with
  | none =>
      rw [hs] at h
      simp only [Option.map_none] at h
      rw [← h]
  | some secret =>
      rw [hs] at h
      simp only [Option.map_some] at h
      rw [← h]
      simp only [ha.xor, getD_map']

variable {W W' : Type} {d : RelayEncoding.DecimalOps B W} {d' : RelayEncoding.DecimalOps B' W'} {fw : W → W'}
  (hd : RelayEncoding.DecimalHom d d' f fw)
include hd

theorem paddedDecimal_map (zero : B) (number : W) (width : Nat) :
    f (paddedDecimalWith d a zero number width).1 = (paddedDecimalWith d' a' (f zero) (fw number) width).1 ∧
    (paddedDecimalWith d a zero number width).2.map f = (paddedDecimalWith d' a' (f zero) (fw number) width).2 := by
  have enc := PrivateDecimal.encode_map hd ha number
  have valid := congrArg PrivateBuffer.Buffer.valid enc
  have data := congrArg PrivateBuffer.Buffer.data enc
  simp only [PrivateBuffer.Buffer.map] at valid data
  refine ⟨?_, ?_⟩
  · show f (a.and _ (ByteAuth.zeroMask a _)) = _
    rw [ha.and, ByteAuth.zeroMask_map ha, ← getD_map' f, valid, data]
    rfl
  · simp only [paddedDecimalWith, List.map_map, Function.comp_def, TlsInner.select_map ha,
      ByteAuth.zeroMask_map ha, ha.const]
    rw [← data, ← List.map_take, List.map_map]
    rfl

end Refinement

/-! ### What the insertion does to one index -/

theorem insertSlots_getElem (a : ByteAuth.Ops B) (zero : B) (frame mask : List B) (payloadAt : Nat)
    (slots : List (Nat × List B)) (i : Nat) (hi : i < frame.length) :
    (insertSlots a zero frame mask payloadAt slots)[i]'(by simpa [insertSlots] using hi) =
      match slotAt zero slots i with
      | some secret => a.xor frame[i] (a.xor secret (mask.getD ((i - payloadAt) % 4) zero))
      | none => frame[i] := by
  simp [insertSlots, List.getElem_zipIdx]

/-- A byte no slot covers is the frame byte. -/
theorem insertSlots_outside (a : ByteAuth.Ops B) (zero : B) (frame mask : List B) (payloadAt : Nat)
    (slots : List (Nat × List B)) (i : Nat) (hi : i < frame.length)
    (outside : ∀ slot ∈ slots, ¬ (slot.1 ≤ i ∧ i < slot.1 + slot.2.length)) :
    (insertSlots a zero frame mask payloadAt slots)[i]'(by simpa [insertSlots] using hi) = frame[i] := by
  have none : slotAt zero slots i = none := by
    unfold slotAt
    rw [List.findSome?_eq_none_iff]
    intro slot member
    have h := outside slot member
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [if_neg h]
  rw [insertSlots_getElem, none]

/-- A byte covered by the first slot that covers it is frame ⊕ slot byte ⊕ mask byte. -/
theorem insertSlots_inside (a : ByteAuth.Ops B) (zero : B) (frame mask : List B) (payloadAt : Nat)
    (before : List (Nat × List B)) (start : Nat) (bytes : List B) (after : List (Nat × List B))
    (i : Nat) (hi : i < frame.length)
    (earlier : ∀ slot ∈ before, ¬ (slot.1 ≤ i ∧ i < slot.1 + slot.2.length))
    (lo : start ≤ i) (up : i < start + bytes.length) :
    (insertSlots a zero frame mask payloadAt (before ++ (start, bytes) :: after))[i]'(by simpa [insertSlots] using hi) =
      a.xor frame[i] (a.xor (bytes.getD (i - start) zero) (mask.getD ((i - payloadAt) % 4) zero)) := by
  have found : slotAt zero (before ++ (start, bytes) :: after) i = some (bytes.getD (i - start) zero) := by
    unfold slotAt
    rw [List.findSome?_append]
    have none : before.findSome? (fun slot =>
        if slot.1 ≤ i && i < slot.1 + slot.2.length then some (slot.2.getD (i - slot.1) zero) else none) = none := by
      rw [List.findSome?_eq_none_iff]
      intro slot member
      have h := earlier slot member
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [if_neg h]
    rw [none, Option.none_or, List.findSome?_cons]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [if_pos ⟨lo, up⟩]
  rw [insertSlots_getElem, found]

/-! ### `signal-request-ctr` -/

def signalRequestInputs (cert size : Nat) : List (String × Shape) :=
  [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8),
    ("conversation", .bytes (HybridKernel.conversationBytes cert 80)), ("frame", .bytes size), ("mask", .bytes 4)]

/-- The four outputs of the request sealers, on values. -/
def sealedRequest (traffic sequence plaintext : List (BitVec 8)) (valid : BitVec 8) : List (List (BitVec 8)) :=
  let inner := TlsRecord.inner Gcm.concrete plaintext 23 0
  [[valid], TlsRecord.header Gcm.concrete (inner.length + 16),
    ByteAuth.release ByteAuth.concrete valid (ctrOf traffic sequence inner), padOf traffic sequence]

/-- The slots of `signal-request-ctr`, on values: the contact's UUID, access key in base64, and
the space-padded device id and registration id, from the conversation record's metadata. -/
def signalRequestSlots (cert uuidAt keyAt deviceAt registrationAt : Nat) (conversation : List (BitVec 8)) :
    BitVec 8 × List (Nat × List (BitVec 8)) :=
  let a := ByteAuth.concrete
  let metadata := (conversation.drop (cert + 262)).take 57
  let device := paddedDecimalWith RelayEncoding.decimalConcrete a 0
    (RelayRequest.word Varint64.concrete a metadata 48 1) 3
  let registration := paddedDecimalWith RelayEncoding.decimalConcrete a 0
    (RelayRequest.word Varint64.concrete a metadata 49 4) 10
  (a.and device.1 registration.1,
    [(uuidAt, RelayEncoding.uuid a ((metadata.drop 0).take 16)), (keyAt, RelayEncoding.base64 a ((metadata.drop 16).take 16)),
      (deviceAt, device.2), (registrationAt, registration.2)])

theorem signalRequestCtr_spec (cert size uuidAt keyAt deviceAt registrationAt : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (signalRequestInputs cert size) name).map (BVExpr.eval assign)
    let slots := signalRequestSlots cert uuidAt keyAt deviceAt registrationAt (get "conversation")
    (HybridKernel.signalRequestCtr cert size uuidAt keyAt deviceAt registrationAt).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (insertSlots ByteAuth.concrete 0 (get "frame") (get "mask") 8 slots.2) slots.1 := by
  have ha := ByteAuth.evaluationHom assign
  have hd := RelayEncoding.decimalEvaluationHom assign
  have hv := Varint64.evaluationHom assign
  let get := lookup (signalRequestInputs cert size)
  let metadata := sl (get "conversation") (cert + 262) 57
  let device := paddedDecimalWith RelayEncoding.decimalSymbolic ByteAuth.symbolic (.const 0)
    (RelayRequest.word Varint64.symbolic ByteAuth.symbolic metadata 48 1) 3
  let registration := paddedDecimalWith RelayEncoding.decimalSymbolic ByteAuth.symbolic (.const 0)
    (RelayRequest.word Varint64.symbolic ByteAuth.symbolic metadata 49 4) 10
  let slotsSym : List (Nat × List (BVExpr 8)) := [(uuidAt, RelayEncoding.uuid ByteAuth.symbolic (sl metadata 0 16)),
    (keyAt, RelayEncoding.base64 ByteAuth.symbolic (sl metadata 16 16)), (deviceAt, device.2),
    (registrationAt, registration.2)]
  let valid := ByteAuth.symbolic.and device.1 registration.1
  let inner := TlsRecord.inner Gcm.symbolic (insertSlots ByteAuth.symbolic (.const 0) (get "frame") (get "mask") 8 slotsSym) 23 0
  have shape : (HybridKernel.signalRequestCtr cert size uuidAt keyAt deviceAt registrationAt).outputs =
      [pub "accepted" [valid], pub "header" (TlsRecord.header Gcm.symbolic (inner.length + 16)),
        pub "ciphertext" (ByteAuth.release ByteAuth.symbolic valid
          (Gcm.ctr Gcm.symbolic (HybridKernel.gcmExpanded (get "clientApplication"))
            (TlsRecord.nonce Gcm.symbolic (HybridKernel.blockIv (get "clientApplication")) (get "sequence")) inner)),
        priv "pad" (HybridKernel.gcmPad (get "clientApplication") (get "sequence"))] := by
    unfold HybridKernel.signalRequestCtr
    simp only [pub, priv, List.cons.injEq, and_true]
    refine ⟨rfl, ?_, ?_, rfl⟩ <;>
    · simp only [inner, valid, slotsSym, device, registration, get, metadata, signalRequestInputs, insertSlots, slotAt,
        HybridService.at', paddedDecimalWith, HybridKernel.paddedDecimal]
      congr
      all_goals
        funext pair
        split <;> rename_i h <;> simp only [h]
  have zero : BVExpr.eval assign (.const 0 : BVExpr 8) = 0 := rfl
  have dev := paddedDecimal_map ha hd (.const 0) (RelayRequest.word Varint64.symbolic ByteAuth.symbolic metadata 48 1) 3
  have reg := paddedDecimal_map ha hd (.const 0) (RelayRequest.word Varint64.symbolic ByteAuth.symbolic metadata 49 4) 10
  rw [RelayRequest.word_map hv ha, zero] at dev reg
  have plain := insertSlots_map ha (.const 0) (get "frame") (get "mask") 8 slotsSym
  simp only [slotsSym, device, registration, mapSlots, List.map_cons, List.map_nil, RelayEncoding.uuid_map ha,
    RelayEncoding.base64_map ha, zero, dev.2, reg.2] at plain
  have hvalid : BVExpr.eval assign valid =
      ByteAuth.concrete.and (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0
        (RelayRequest.word Varint64.concrete ByteAuth.concrete (metadata.map (BVExpr.eval assign)) 48 1) 3).1
        (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0
        (RelayRequest.word Varint64.concrete ByteAuth.concrete (metadata.map (BVExpr.eval assign)) 49 4) 10).1 := by
    simp only [valid, device, registration, ha.and, dev.1, reg.1]
  have hinner : inner.map (BVExpr.eval assign) = TlsRecord.inner Gcm.concrete
      (insertSlots ByteAuth.concrete 0 ((get "frame").map (BVExpr.eval assign)) ((get "mask").map (BVExpr.eval assign)) 8
        [(uuidAt, RelayEncoding.uuid ByteAuth.concrete ((sl metadata 0 16).map (BVExpr.eval assign))),
          (keyAt, RelayEncoding.base64 ByteAuth.concrete ((sl metadata 16 16).map (BVExpr.eval assign))),
          (deviceAt, (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0
            (RelayRequest.word Varint64.concrete ByteAuth.concrete (metadata.map (BVExpr.eval assign)) 48 1) 3).2),
          (registrationAt, (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0
            (RelayRequest.word Varint64.concrete ByteAuth.concrete (metadata.map (BVExpr.eval assign)) 49 4) 10).2)]) 23 0 := by
    simp only [inner, slotsSym, device, registration, TlsRecord.inner_map (Gcm.evaluationHom assign), plain]
  have innerLength : inner.length = (inner.map (BVExpr.eval assign)).length := (List.length_map _).symm
  rw [shape]
  simp only [pub, priv, List.map_cons, List.map_nil, TlsRecord.header_map (Gcm.evaluationHom assign),
    ByteAuth.release_map ha, HybridKernel.ctr_eval, HybridKernel.gcmPad_eval, innerLength, hinner, hvalid]
  simp only [sealedRequest, signalRequestSlots, metadata, sl, get, List.map_take, List.map_drop]

/-- A refused request (`accepted` = 0) opens an all-zero ciphertext. -/
theorem sealedRequest_rejects (traffic sequence plaintext : List (BitVec 8)) :
    ∀ byte ∈ (sealedRequest traffic sequence plaintext 0).getD 2 [], byte = 0 := by
  intro byte member
  simp only [sealedRequest, List.getD_cons_succ, List.getD_cons_zero, ByteAuth.release_reject] at member
  exact List.eq_of_mem_replicate member

theorem signalRequestCtr_rejects (cert size uuidAt keyAt deviceAt registrationAt : Nat) (assign : BVExpr.Assignment)
    (refused : ((HybridKernel.signalRequestCtr cert size uuidAt keyAt deviceAt registrationAt).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((HybridKernel.signalRequestCtr cert size uuidAt keyAt deviceAt registrationAt).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 2 [], byte = 0 := by
  rw [signalRequestCtr_spec] at refused ⊢
  simp only [sealedRequest, List.getD_cons_zero, List.cons.injEq, and_true] at refused
  simp only [sealedRequest, List.getD_cons_succ, List.getD_cons_zero, refused]
  intro byte member
  rw [ByteAuth.release_reject] at member
  exact List.eq_of_mem_replicate member

/-! ### `bundle-fetch-ctr` and `bundle-request-ctr`: the shared `sealSlots` -/

theorem sealSlots_spec (name : String) (extra : String × Shape) (size payloadAt : Nat) (valid : BVExpr 8)
    (slots : List (Nat × List (BVExpr 8))) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (BundleKernel.requestInputs extra size) name).map (BVExpr.eval assign)
    (BundleKernel.sealSlots name extra size payloadAt valid slots).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (insertSlots ByteAuth.concrete 0 (get "frame") (get "mask") payloadAt (mapSlots (BVExpr.eval assign) slots))
        (BVExpr.eval assign valid) := by
  have ha := ByteAuth.evaluationHom assign
  let get := lookup (BundleKernel.requestInputs extra size)
  let inner := TlsRecord.inner Gcm.symbolic (insertSlots ByteAuth.symbolic (.const 0) (get "frame") (get "mask") payloadAt slots) 23 0
  have shape : (BundleKernel.sealSlots name extra size payloadAt valid slots).outputs =
      [pub "accepted" [valid], pub "header" (TlsRecord.header Gcm.symbolic (inner.length + 16)),
        pub "ciphertext" (ByteAuth.release ByteAuth.symbolic valid
          (Gcm.ctr Gcm.symbolic (HybridKernel.gcmExpanded (get "clientApplication"))
            (TlsRecord.nonce Gcm.symbolic (HybridKernel.blockIv (get "clientApplication")) (get "sequence")) inner)),
        priv "pad" (HybridKernel.gcmPad (get "clientApplication") (get "sequence"))] := by
    unfold BundleKernel.sealSlots
    simp only [pub, priv, List.cons.injEq, and_true, true_and]
    refine ⟨?_, ?_, rfl⟩ <;>
    · simp only [inner, get, insertSlots, slotAt, HybridService.at']
      congr
      all_goals
        funext pair
        split <;> rename_i h <;> simp only [h]
  have zero : BVExpr.eval assign (.const 0 : BVExpr 8) = 0 := rfl
  have plain := insertSlots_map ha (.const 0) (get "frame") (get "mask") payloadAt slots
  rw [zero] at plain
  have hinner : inner.map (BVExpr.eval assign) = TlsRecord.inner Gcm.concrete
      (insertSlots ByteAuth.concrete 0 ((get "frame").map (BVExpr.eval assign)) ((get "mask").map (BVExpr.eval assign))
        payloadAt (mapSlots (BVExpr.eval assign) slots)) 23 0 := by
    simp only [inner, TlsRecord.inner_map (Gcm.evaluationHom assign), plain]
  have innerLength : inner.length = (inner.map (BVExpr.eval assign)).length := (List.length_map _).symm
  rw [shape]
  simp only [pub, priv, List.map_cons, List.map_nil, TlsRecord.header_map (Gcm.evaluationHom assign),
    ByteAuth.release_map ha, HybridKernel.ctr_eval, HybridKernel.gcmPad_eval, innerLength, hinner]
  rfl

theorem sealSlots_rejects (name : String) (extra : String × Shape) (size payloadAt : Nat) (valid : BVExpr 8)
    (slots : List (Nat × List (BVExpr 8))) (assign : BVExpr.Assignment)
    (refused : ((BundleKernel.sealSlots name extra size payloadAt valid slots).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((BundleKernel.sealSlots name extra size payloadAt valid slots).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 2 [], byte = 0 := by
  rw [sealSlots_spec] at refused ⊢
  simp only [sealedRequest, List.getD_cons_zero, List.cons.injEq, and_true] at refused
  simp only [sealedRequest, List.getD_cons_succ, List.getD_cons_zero, refused]
  intro byte member
  rw [ByteAuth.release_reject] at member
  exact List.eq_of_mem_replicate member

theorem at'_eval (assign : BVExpr.Assignment) (bytes : List (BVExpr 8)) (index : Nat) :
    BVExpr.eval assign (HybridService.at' bytes index) = (bytes.map (BVExpr.eval assign)).getD index 0 := by
  unfold HybridService.at'
  rw [← getD_map' (BVExpr.eval assign)]
  rfl

theorem paddedDecimal_eval (assign : BVExpr.Assignment) (number : BVExpr 64) (width : Nat) :
    BVExpr.eval assign (HybridKernel.paddedDecimal number width).1 =
      (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0 (BVExpr.eval assign number) width).1 ∧
    (HybridKernel.paddedDecimal number width).2.map (BVExpr.eval assign) =
      (paddedDecimalWith RelayEncoding.decimalConcrete ByteAuth.concrete 0 (BVExpr.eval assign number) width).2 :=
  paddedDecimal_map (ByteAuth.evaluationHom assign) (RelayEncoding.decimalEvaluationHom assign) (.const 0) number width

/-- `BundleKernel.live` on values: 255 exactly when the record's first byte (the session
version) is 4. -/
def liveValue (record : List (BitVec 8)) : BitVec 8 :=
  ByteAuth.eqMask ByteAuth.concrete (record.getD 0 0) (ByteAuth.concrete.const 4)

theorem live_eval (assign : BVExpr.Assignment) (record : List (BVExpr 8)) :
    BVExpr.eval assign (BundleKernel.live record) = liveValue (record.map (BVExpr.eval assign)) := by
  simp only [BundleKernel.live, liveValue, ByteAuth.eqMask_map (ByteAuth.evaluationHom assign),
    (ByteAuth.evaluationHom assign).const, at'_eval]

def fetchInputs (size : Nat) : List (String × Shape) :=
  BundleKernel.requestInputs ("record", Shape.bytes BundleKernel.recordBytes) size

/-- `bundle-fetch-ctr`: the contact's UUID and base64 access key from one record, valid when
the record is live. -/
theorem bundleFetchCtr_spec (size payloadAt uuidAt keyAt : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (fetchInputs size) name).map (BVExpr.eval assign)
    (BundleKernel.bundleFetchCtr size payloadAt uuidAt keyAt).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (insertSlots ByteAuth.concrete 0 (get "frame") (get "mask") payloadAt
          [(uuidAt, RelayEncoding.uuid ByteAuth.concrete (((get "record").drop 262).take 16)),
            (keyAt, RelayEncoding.base64 ByteAuth.concrete (((get "record").drop 278).take 16))])
        (liveValue (get "record")) := by
  have ha := ByteAuth.evaluationHom assign
  simp only [BundleKernel.bundleFetchCtr]
  rw [sealSlots_spec]
  simp only [fetchInputs, mapSlots, List.map_cons, List.map_nil, RelayEncoding.uuid_map ha, RelayEncoding.base64_map ha,
    sl, List.map_take, List.map_drop, live_eval]

/-! `bundle-request-ctr` -/

def requestInputsOf (size count : Nat) : List (String × Shape) :=
  BundleKernel.requestInputs ("records", Shape.bytes (BundleKernel.recordBytes * count)) size

/-- One device's validity and slots, on values: the record is live and both numbers fit their
padded slots. -/
def deviceValue (records : List (BitVec 8)) (slot : Nat × Nat) (index : Nat) :
    BitVec 8 × List (Nat × List (BitVec 8)) :=
  let a := ByteAuth.concrete
  let record := (records.drop (BundleKernel.recordBytes * index)).take BundleKernel.recordBytes
  let metadata := (record.drop 262).take 57
  let device := paddedDecimalWith RelayEncoding.decimalConcrete a 0 (RelayRequest.word Varint64.concrete a metadata 48 1) 3
  let registration := paddedDecimalWith RelayEncoding.decimalConcrete a 0
    (RelayRequest.word Varint64.concrete a metadata 49 4) 10
  (a.and (liveValue record) (a.and device.1 registration.1), [(slot.1, device.2), (slot.2, registration.2)])

/-- `bundle-request-ctr`'s validity and slots, on values: the UUID and access key of the first
record, then every device's two numbers; valid when every device is. -/
def bundleRequestValue (records : List (BitVec 8)) (uuidAt keyAt : Nat) (devices : List (Nat × Nat)) :
    BitVec 8 × List (Nat × List (BitVec 8)) :=
  let each := devices.zipIdx.map (fun pair => deviceValue records pair.1 pair.2)
  (each.foldl (fun mask device => ByteAuth.concrete.and mask device.1) 255,
    [(uuidAt, RelayEncoding.uuid ByteAuth.concrete ((records.drop 262).take 16)),
      (keyAt, RelayEncoding.base64 ByteAuth.concrete ((records.drop 278).take 16))] ++ each.flatMap (·.2))

theorem foldl_and_eval (assign : BVExpr.Assignment) (each : List (BVExpr 8 × List (Nat × List (BVExpr 8))))
    (initial : BVExpr 8) :
    BVExpr.eval assign (each.foldl (fun mask device => ByteAuth.symbolic.and mask device.1) initial) =
      (each.map (fun device => (BVExpr.eval assign device.1, mapSlots (BVExpr.eval assign) device.2))).foldl
        (fun mask device => ByteAuth.concrete.and mask device.1) (BVExpr.eval assign initial) := by
  induction each generalizing initial with
  | nil => rfl
  | cons device rest ih =>
      simp only [List.foldl_cons, List.map_cons, ih, (ByteAuth.evaluationHom assign).and]

theorem mapSlots_append (f : B → B') (xs ys : List (Nat × List B)) :
    mapSlots f (xs ++ ys) = mapSlots f xs ++ mapSlots f ys := List.map_append

theorem flatMap_eval (f : B → B') (each : List (B × List (Nat × List B))) :
    mapSlots f (each.flatMap (·.2)) = (each.map (fun device => (f device.1, mapSlots f device.2))).flatMap (·.2) := by
  induction each with
  | nil => rfl
  | cons device rest ih =>
      simp only [List.flatMap_cons, List.map_cons, mapSlots, List.map_append] at ih ⊢
      rw [ih]

/-- One device of `bundle-request-ctr`, evaluated: `deviceValue` on the evaluated records. Stated
right to left, in the form `simp` leaves the kernel's per-device term in. -/
theorem deviceValue_eval (assign : BVExpr.Assignment) (records : List (BVExpr 8)) (x : (Nat × Nat) × Nat) :
    deviceValue (records.map (BVExpr.eval assign)) x.1 x.2 =
      (BVExpr.eval assign (ByteAuth.symbolic.and
          (BundleKernel.live (List.take BundleKernel.recordBytes (List.drop (BundleKernel.recordBytes * x.2) records)))
          (ByteAuth.symbolic.and
            (HybridKernel.paddedDecimal (RelayRequest.word Varint64.symbolic ByteAuth.symbolic
              (List.take 57 (List.drop 262 (List.take BundleKernel.recordBytes
                (List.drop (BundleKernel.recordBytes * x.2) records)))) 48 1) 3).1
            (HybridKernel.paddedDecimal (RelayRequest.word Varint64.symbolic ByteAuth.symbolic
              (List.take 57 (List.drop 262 (List.take BundleKernel.recordBytes
                (List.drop (BundleKernel.recordBytes * x.2) records)))) 49 4) 10).1)),
        mapSlots (BVExpr.eval assign)
          [(x.1.1, (HybridKernel.paddedDecimal (RelayRequest.word Varint64.symbolic ByteAuth.symbolic
              (List.take 57 (List.drop 262 (List.take BundleKernel.recordBytes
                (List.drop (BundleKernel.recordBytes * x.2) records)))) 48 1) 3).2),
            (x.1.2, (HybridKernel.paddedDecimal (RelayRequest.word Varint64.symbolic ByteAuth.symbolic
              (List.take 57 (List.drop 262 (List.take BundleKernel.recordBytes
                (List.drop (BundleKernel.recordBytes * x.2) records)))) 49 4) 10).2)]) := by
  have ha := ByteAuth.evaluationHom assign
  have hv := Varint64.evaluationHom assign
  have dev := paddedDecimal_eval assign (RelayRequest.word Varint64.symbolic ByteAuth.symbolic
    (List.take 57 (List.drop 262 (List.take BundleKernel.recordBytes
      (List.drop (BundleKernel.recordBytes * x.2) records)))) 48 1) 3
  have reg := paddedDecimal_eval assign (RelayRequest.word Varint64.symbolic ByteAuth.symbolic
    (List.take 57 (List.drop 262 (List.take BundleKernel.recordBytes
      (List.drop (BundleKernel.recordBytes * x.2) records)))) 49 4) 10
  rw [RelayRequest.word_map hv ha] at dev reg
  simp only [mapSlots, List.map_cons, List.map_nil, ha.and, live_eval, dev.1, dev.2, reg.1, reg.2]
  simp only [deviceValue, List.map_take, List.map_drop]

theorem bundleRequestCtr_spec (size payloadAt uuidAt keyAt : Nat) (devices : List (Nat × Nat))
    (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (requestInputsOf size devices.length) name).map (BVExpr.eval assign)
    let value := bundleRequestValue (get "records") uuidAt keyAt devices
    (BundleKernel.bundleRequestCtr size payloadAt uuidAt keyAt devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (insertSlots ByteAuth.concrete 0 (get "frame") (get "mask") payloadAt value.2) value.1 := by
  have ha := ByteAuth.evaluationHom assign
  have hv := Varint64.evaluationHom assign
  simp only [BundleKernel.bundleRequestCtr]
  rw [sealSlots_spec]
  simp only [requestInputsOf, bundleRequestValue, mapSlots_append, flatMap_eval, foldl_and_eval, ha.const, List.map_map,
    Function.comp_def]
  simp only [deviceValue_eval assign]
  have full : ByteAuth.concrete.const 255 = 255 := rfl
  simp only [mapSlots, List.map_cons, List.map_nil, RelayEncoding.uuid_map ha, RelayEncoding.base64_map ha, sl,
    List.map_take, List.map_drop, full]

theorem bundleFetchCtr_rejects (size payloadAt uuidAt keyAt : Nat) (assign : BVExpr.Assignment)
    (refused : ((BundleKernel.bundleFetchCtr size payloadAt uuidAt keyAt).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((BundleKernel.bundleFetchCtr size payloadAt uuidAt keyAt).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 2 [], byte = 0 := by
  simp only [BundleKernel.bundleFetchCtr] at refused ⊢
  exact sealSlots_rejects _ _ _ _ _ _ assign refused

theorem bundleRequestCtr_rejects (size payloadAt uuidAt keyAt : Nat) (devices : List (Nat × Nat))
    (assign : BVExpr.Assignment)
    (refused : ((BundleKernel.bundleRequestCtr size payloadAt uuidAt keyAt devices).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 0 [] = [0]) :
    ∀ byte ∈ ((BundleKernel.bundleRequestCtr size payloadAt uuidAt keyAt devices).outputs.map
      (fun field => field.value.map (BVExpr.eval assign))).getD 2 [], byte = 0 := by
  simp only [BundleKernel.bundleRequestCtr] at refused ⊢
  exact sealSlots_rejects _ _ _ _ _ _ assign refused

/-- On values, where the frame built in the clear has a zero byte, the inserted byte is the slot
byte XOR the WebSocket mask byte: the masked field, as the WebSocket payload must carry it. -/
theorem insertSlots_inside_zero (frame mask : List (BitVec 8)) (payloadAt : Nat)
    (before : List (Nat × List (BitVec 8))) (start : Nat) (bytes : List (BitVec 8)) (after : List (Nat × List (BitVec 8)))
    (i : Nat) (hi : i < frame.length) (blank : frame[i] = 0)
    (earlier : ∀ slot ∈ before, ¬ (slot.1 ≤ i ∧ i < slot.1 + slot.2.length))
    (lo : start ≤ i) (up : i < start + bytes.length) :
    (insertSlots ByteAuth.concrete 0 frame mask payloadAt (before ++ (start, bytes) :: after))[i]'(by
        simpa [insertSlots] using hi) =
      bytes.getD (i - start) 0 ^^^ mask.getD ((i - payloadAt) % 4) 0 := by
  rw [insertSlots_inside ByteAuth.concrete 0 frame mask payloadAt before start bytes after i hi earlier lo up, blank]
  exact BitVec.zero_xor

#print axioms signalRequestCtr_spec
#print axioms signalRequestCtr_rejects
#print axioms bundleFetchCtr_rejects
#print axioms bundleRequestCtr_rejects
#print axioms insertSlots_inside_zero
#print axioms bundleFetchCtr_spec
#print axioms bundleRequestCtr_spec
#print axioms sealSlots_spec
#print axioms sealSlots_rejects
#print axioms insertSlots_inside
#print axioms insertSlots_outside

end TlsMpc.KernelSpecs
