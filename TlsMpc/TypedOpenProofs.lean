import TlsMpc.TypedOpenKernels
import TlsMpc.RecordClassProofs
import TlsMpc.HybridKernelsProofs

/-!
Theorems about the two-step record opening (`TlsMpc/TypedOpenKernels.lean`).

GATING. A record that fails authentication opens nothing.
* `rejected_parse`: with the tag-check mask `accepted` = 0 the parse is all
  zero, whatever the record, header, length field and keys are;
  `rejected_independent`: it is the same list for any two records of one size.
* `gating`: for that parse the opened bit is 0 and the event of the first
  kernel is `[0, 0]` (the event `tls-open-application-class` opens for a
  rejected record: `TlsPostHandshake.reject_unauthenticated`).
* `tlsOpenTyped_gated`: the same about the kernel `tls-open-typed CAP` itself:
  under every assignment of its inputs whose `accepted` byte is 0, its opened
  fields evaluate to `[[0], [0, 0]]`.
* `frame_unauthenticated`: `tls-frame`'s parser opens `[0, 0]` for an all-zero parse.

REFINEMENT. The pair computes what `tls-open-application-class CAP` computes.
* `handshakeBit_cases`: the bit is 0 or 255.
* `direct_eq`: when the bit is 0, `TypedOpen.direct` is `TlsPostHandshake.core`
  (the scan is disabled for a type other than handshake and changes nothing).
* `typed_pair_refines`: about the kernels. Under every assignment of the
  inputs, (1) the bit is 0 or 255; (2) when it is 0, the fields `event`,
  `parser`, `length`, `content` of `tls-open-typed` are those of
  `tls-open-application-class`; (3) `tls-frame`, given the same parser state and
  the first kernel's `parsed` field, has exactly the fields of
  `tls-open-application-class` (for either value of the bit; it is run when the
  bit is 255).

Outside these statements, as for every kernel: the lowering to gates
(`compiled_correct`, `FlatLowering`), and the worker's sequencing in
`tls_kernels.h` (which kernel's fields it opens and keeps for which bit).
-/
namespace TlsMpc.TypedOpen
open Std.Tactic.BVDecide
open TlsPostHandshake Signal.Word64

/-! ### From expressions to values -/

section Refinement
variable {o : Ops B W} {o' : Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (ho : Hom o o' f fw) (ha : ByteAuth.Hom a a' f)

include ha

theorem handshakeBit_map (parsed : List B) :
    f (handshakeBit a parsed) = handshakeBit a' (parsed.map f) := by
  simp only [handshakeBit, ByteAuth.eqMask_map ha, get_map ha, ha.const]

include ho

theorem direct_map (state parsed : List B) :
    (direct o a state parsed).map f = direct o' a' (state.map f) (parsed.map f) := by
  simp only [direct, List.map_append, ByteAuth.release_map ha, ha.not, handshakeBit_map ha, List.map_take,
    List.map_drop, finish_map ho ha, Scan.map, decodeState_map ho ha, ha.const]

end Refinement

theorem direct_refines (state parsed : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (direct symbolicMux ByteAuth.symbolic state parsed).map (BVExpr.eval assign) =
      direct concrete ByteAuth.concrete (state.map (BVExpr.eval assign)) (parsed.map (BVExpr.eval assign)) :=
  direct_map (evaluationHomMux assign) (ByteAuth.evaluationHom assign) state parsed

/-! ### Refinement: the bit is 0 -/

theorem handshakeBit_cases (parsed : List (BitVec 8)) :
    handshakeBit ByteAuth.concrete parsed = 0 ∨ handshakeBit ByteAuth.concrete parsed = 255 := by
  unfold handshakeBit
  rw [ByteAuth.eqMask_value]
  split <;> simp

/-- A disabled scan changes nothing. -/
theorem scan_off (length : BitVec 64) (index : Nat) (content : List (BitVec 8))
    (state : Scan (BitVec 8) (BitVec 64)) :
    scan concrete ByteAuth.concrete 0 length index content state = state := by
  induction content generalizing index with
  | nil => rfl
  | cons b rest ih =>
      have hz : ∀ x : BitVec 8, ByteAuth.concrete.and 0 x = 0 := fun _ => BitVec.zero_and
      simp only [scan, hz, RecordClass.choose_off]
      exact ih (index + 1)

/-- For a parse whose type is not handshake, the parser without its scan is the
parser: same event, request flag, state, length and content. -/
theorem direct_eq (parsed : List (BitVec 8)) (h : handshakeBit ByteAuth.concrete parsed = 0)
    (state : List (BitVec 8)) :
    direct concrete ByteAuth.concrete state parsed =
      TlsPostHandshake.core concrete ByteAuth.concrete state parsed := by
  have hs : ByteAuth.eqMask ByteAuth.concrete (get ByteAuth.concrete parsed 1) (ByteAuth.concrete.const 22) = 0 := h
  have hn : ByteAuth.concrete.not (0 : BitVec 8) = 255 := by decide
  simp only [direct, TlsPostHandshake.core, TlsPostHandshake.process, h, hs, hn, scan_off, ByteAuth.release_accept,
    List.take_append_drop]

/-! ### Gating: a record that fails authentication -/

theorem releaseOpened_rejected (headerValid : BitVec 8) (plaintext : List (BitVec 8)) :
    TlsReceive.releaseOpened ByteAuth.concrete headerValid ⟨0, plaintext⟩ =
      List.replicate (plaintext.length + 4) 0 := by
  have hz : ByteAuth.concrete.and headerValid 0 = 0 := BitVec.and_zero
  simp only [TlsReceive.releaseOpened, hz, ByteAuth.release_reject, TlsInnerParallel.decode_length]

/-- With the tag-check mask 0, every byte of the parse is zero: for every
record, header, length field, key schedule and nonce. -/
theorem rejected_parse (expanded nonce wire : List (BitVec 8)) (high low : BitVec 8) :
    RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0 =
      List.replicate
        ((RecordClass.openPlaintext Gcm.concrete ByteAuth.concrete expanded nonce wire high low).2.length + 4) 0 := by
  simp only [RecordClass.openParsed, releaseOpened_rejected]

theorem maskBytes_length (a : ByteAuth.Ops B) (masks bytes : List B) (h : masks.length = bytes.length) :
    (RecordClass.maskBytes a masks bytes).length = bytes.length := by
  induction masks generalizing bytes with
  | nil =>
      cases bytes with
      | nil => rfl
      | cons b bs => simp at h
  | cons m ms ih =>
      cases bytes with
      | nil => simp at h
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp only [RecordClass.maskBytes, List.length_cons, ih bs h]

/-- The size of the parse is public: the record's size less 17. -/
theorem rejected_parse_length (expanded nonce wire : List (BitVec 8)) (high low : BitVec 8)
    (he : expanded.length = 176) :
    RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0 =
      List.replicate (wire.length - 21 + 4) 0 := by
  have hm : (RecordClass.within ByteAuth.concrete high low 16 (TlsReceive.ciphertext wire).length).2.length =
      (TlsReceive.ciphertext wire).length :=
    TlsWebSocketActivity.activity_length ByteAuth.concrete high low 16 _
  have hc := Gcm.ctr_length Gcm.concrete expanded nonce (TlsReceive.ciphertext wire) he
  have hl : (RecordClass.openPlaintext Gcm.concrete ByteAuth.concrete expanded nonce wire high low).2.length =
      wire.length - 21 := by
    simp only [RecordClass.openPlaintext]
    rw [maskBytes_length _ _ _ (by rw [hm, hc]), hc, TlsReceive.ciphertext_length]
  rw [rejected_parse, hl]

/-- The parse of a record that fails authentication does not depend on the
record's bytes, its length field, or the keys: private outputs computed from it
are independent of them too. -/
theorem rejected_independent (expanded nonce wire expanded' nonce' wire' : List (BitVec 8))
    (high low high' low' : BitVec 8) (he : expanded.length = 176) (he' : expanded'.length = 176)
    (hw : wire.length = wire'.length) :
    RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0 =
      RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded' nonce' wire' high' low' 0 := by
  rw [rejected_parse_length _ _ _ _ _ he, rejected_parse_length _ _ _ _ _ he', hw]

private theorem get_zeros (n index : Nat) :
    get ByteAuth.concrete (List.replicate n (0 : BitVec 8)) index = 0 := by
  simp only [TlsPostHandshake.get, List.getElem?_replicate]
  split <;> rfl

theorem handshakeBit_zeros (n : Nat) : handshakeBit ByteAuth.concrete (List.replicate n 0) = 0 := by
  rw [handshakeBit, get_zeros]
  decide

/-- Without the acceptance byte 255, the parser's two opened bytes are zero
whatever the scan's result is. -/
theorem finish_unauthenticated (s : State (BitVec 8) (BitVec 64)) (parsed : List (BitVec 8))
    (after : Scan (BitVec 8) (BitVec 64)) (h : get ByteAuth.concrete parsed 0 ≠ 255) :
    (finish concrete ByteAuth.concrete s parsed after).take 2 = [0, 0] := by
  have hz : ByteAuth.eqMask ByteAuth.concrete (get ByteAuth.concrete parsed 0) (ByteAuth.concrete.const 255) = 0 := by
    change ByteAuth.eqMask ByteAuth.concrete (get ByteAuth.concrete parsed 0) 255 = 0
    rw [ByteAuth.eqMask_value, if_neg h]
  unfold finish
  simp only [hz]
  simp [ByteAuth.concrete, bor]

theorem direct_unauthenticated (state parsed : List (BitVec 8)) (h : get ByteAuth.concrete parsed 0 ≠ 255) :
    (direct concrete ByteAuth.concrete state parsed).take 2 = [0, 0] := by
  have hfin := finish_unauthenticated (decodeState concrete ByteAuth.concrete state) parsed
    ⟨decodeState concrete ByteAuth.concrete state, ByteAuth.concrete.const 0, ByteAuth.concrete.const 0⟩ h
  simp only [direct, hfin]
  simp [ByteAuth.release, ByteAuth.concrete]

theorem direct_event_zeros (state : List (BitVec 8)) (n : Nat) :
    (direct concrete ByteAuth.concrete state (List.replicate n 0)).take 2 = [0, 0] :=
  direct_unauthenticated state _ (by rw [get_zeros]; decide)

/-- `tls-frame`'s parser on an all-zero parse opens `[0, 0]`. -/
theorem frame_unauthenticated (state : List (BitVec 8)) (n : Nat) :
    (TlsPostHandshake.core concrete ByteAuth.concrete state (List.replicate n 0)).take 2 = [0, 0] :=
  TlsPostHandshake.reject_unauthenticated _ _ (by rw [get_zeros]; decide)

/-- GATING. For a record whose tag check failed (`accepted` = 0), whatever its
bytes: the opened bit is 0 and the first kernel's opened event is `[0, 0]`. -/
theorem gating (state expanded nonce wire : List (BitVec 8)) (high low : BitVec 8) :
    handshakeBit ByteAuth.concrete
        (RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0) = 0 ∧
      (direct concrete ByteAuth.concrete state
        (RecordClass.openParsed Gcm.concrete ByteAuth.concrete expanded nonce wire high low 0)).take 2 = [0, 0] := by
  rw [rejected_parse]
  exact ⟨handshakeBit_zeros _, direct_event_zeros state _⟩

#print axioms handshakeBit_cases
#print axioms direct_eq
#print axioms rejected_parse
#print axioms rejected_independent
#print axioms gating
#print axioms frame_unauthenticated

end TlsMpc.TypedOpen

namespace TlsMpc.TypedOpenKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape lookup lookupFrom pub priv sl)

/-- The four fields every record-opening kernel cuts from the parser's output:
event (2), parser state (11), length (2), content. -/
def fields (out : List (BitVec 8)) : List (List (BitVec 8)) :=
  [(out.drop 0).take 2, (out.drop 2).take 11, (out.drop 13).take 2, out.drop 15]

/-- The values of a kernel's output fields under an assignment of its inputs. -/
def fieldValues (k : Kernel) (assign : BVExpr.Assignment) : List (List (BitVec 8)) :=
  k.outputs.map (fun field => field.value.map (BVExpr.eval assign))

/-- What `tls-open-application-class CAP` computes from the parser state and the
record's parse, on values. -/
def classSpec (capacity : Nat) (assign : BVExpr.Assignment) : List (BitVec 8) :=
  TlsPostHandshake.core Word64.concrete ByteAuth.concrete
    ((lookup (typedInputs capacity) "parser").map (BVExpr.eval assign))
    ((typedParsed capacity).map (BVExpr.eval assign))

/-- GATING, about the kernel. Under every assignment of the inputs of
`tls-open-typed CAP` in which the `accepted` byte is 0, the fields the runtime
may open (`handshake`, `event`) evaluate to 0 and `[0, 0]`. -/
theorem tlsOpenTyped_gated (capacity : Nat) (assign : BVExpr.Assignment)
    (h : BVExpr.eval assign (HybridService.at' (lookup (typedInputs capacity) "accepted") 0) = 0) :
    ((tlsOpenTyped capacity).outputs.filter (·.opened)).map (fun field => field.value.map (BVExpr.eval assign)) =
      [[0], [0, 0]] := by
  have hp : ∃ n, (typedParsed capacity).map (BVExpr.eval assign) = List.replicate n 0 := by
    simp only [typedParsed, RecordClass.openParsed_refines, h]
    exact ⟨_, TypedOpen.rejected_parse _ _ _ _ _⟩
  obtain ⟨n, hp⟩ := hp
  show [[BVExpr.eval assign (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed capacity))],
      (sl (TypedOpen.direct Word64.symbolicMux ByteAuth.symbolic (lookup (typedInputs capacity) "parser")
        (typedParsed capacity)) 0 2).map (BVExpr.eval assign)] = _
  simp only [sl, List.map_take, List.drop_zero,
    TypedOpen.handshakeBit_map (ByteAuth.evaluationHom assign), TypedOpen.direct_refines, hp,
    TypedOpen.handshakeBit_zeros, TypedOpen.direct_event_zeros]

/-- The existing kernel's fields are the cuts of `classSpec`. -/
theorem class_fields (capacity : Nat) (assign : BVExpr.Assignment) :
    fieldValues (RecordClassKernel.tlsOpenApplicationClass capacity) assign = fields (classSpec capacity assign) := by
  simp only [fieldValues, classSpec, RecordClassKernel.tlsOpenApplicationClass, typedParsed, typedInputs, fields, pub,
    priv, sl, List.map_cons, List.map_nil, List.map_take, List.map_drop, HybridKernel.tlsOpenApplicationCtr_parser]

/-- When the opened bit is 0, `tls-open-typed`'s fields are: the bit, the four
fields of the existing kernel, and the parse. -/
theorem typed_fields (capacity : Nat) (assign : BVExpr.Assignment)
    (h : BVExpr.eval assign (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed capacity)) = 0) :
    fieldValues (tlsOpenTyped capacity) assign =
      [[0]] ++ fields (classSpec capacity assign) ++ [(typedParsed capacity).map (BVExpr.eval assign)] := by
  have hb : TypedOpen.handshakeBit ByteAuth.concrete ((typedParsed capacity).map (BVExpr.eval assign)) = 0 := by
    rw [← TypedOpen.handshakeBit_map (ByteAuth.evaluationHom assign)]
    exact h
  simp only [fieldValues, classSpec, tlsOpenTyped, fields, pub, priv, sl, List.map_cons, List.map_nil, List.map_take,
    List.map_drop, TypedOpen.direct_refines, TypedOpen.direct_eq _ hb, h, List.cons_append, List.nil_append]

/-- `tls-frame`'s fields are the cuts of the parser applied to its two inputs. -/
theorem frame_fields (capacity : Nat) (assign : BVExpr.Assignment) :
    fieldValues (tlsFrame capacity) assign =
      fields (TlsPostHandshake.core Word64.concrete ByteAuth.concrete
        ((lookup (frameInputs capacity) "parser").map (BVExpr.eval assign))
        ((lookup (frameInputs capacity) "parsed").map (BVExpr.eval assign))) := by
  simp only [fieldValues, tlsFrame, fields, pub, priv, sl, List.map_cons, List.map_nil, List.map_take, List.map_drop,
    HybridKernel.tlsOpenApplicationCtr_parser]

/-- REFINEMENT, about the kernels. `assign` assigns the inputs of
`tls-open-typed CAP`, which are those of `tls-open-application-class CAP`;
`frame` assigns the inputs of `tls-frame CAP`.

1. The opened bit is 0 or 255.
2. When it is 0, `tls-open-typed` returns the bit, then the `event`, `parser`,
   `length` and `content` of `tls-open-application-class` on the same inputs,
   then the parse.
3. When `tls-frame` is given the same parser state and that parse, its `event`,
   `parser`, `length` and `content` are those of `tls-open-application-class`
   (whatever the bit is; the worker runs it when the bit is 255). -/
theorem typed_pair_refines (capacity : Nat) (assign frame : BVExpr.Assignment) :
    let bit := BVExpr.eval assign (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed capacity))
    let existing := fieldValues (RecordClassKernel.tlsOpenApplicationClass capacity) assign
    (bit = 0 ∨ bit = 255) ∧
    (bit = 0 → fieldValues (tlsOpenTyped capacity) assign =
      [[0]] ++ existing ++ [(typedParsed capacity).map (BVExpr.eval assign)]) ∧
    ((lookup (frameInputs capacity) "parser").map (BVExpr.eval frame) =
        (lookup (typedInputs capacity) "parser").map (BVExpr.eval assign) →
      (lookup (frameInputs capacity) "parsed").map (BVExpr.eval frame) =
        (typedParsed capacity).map (BVExpr.eval assign) →
      fieldValues (tlsFrame capacity) frame = existing) := by
  intro bit existing
  refine ⟨?_, ?_, ?_⟩
  · show BVExpr.eval assign (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed capacity)) = 0 ∨
      BVExpr.eval assign (TypedOpen.handshakeBit ByteAuth.symbolic (typedParsed capacity)) = 255
    rw [TypedOpen.handshakeBit_map (ByteAuth.evaluationHom assign)]
    exact TypedOpen.handshakeBit_cases _
  · intro h
    show fieldValues (tlsOpenTyped capacity) assign =
      [[0]] ++ fieldValues (RecordClassKernel.tlsOpenApplicationClass capacity) assign ++ _
    rw [class_fields]
    exact typed_fields capacity assign h
  · intro hparser hparsed
    show fieldValues (tlsFrame capacity) frame = fieldValues (RecordClassKernel.tlsOpenApplicationClass capacity) assign
    rw [frame_fields, class_fields, hparser, hparsed]
    rfl

#print axioms tlsOpenTyped_gated
#print axioms typed_pair_refines

end TlsMpc.TypedOpenKernel
