import TlsMpc.HybridKernels

/-!
Kernel-level specifications of `signal-upgrade`, `signal-upgrade-shared`,
`signal-conversation-view`, `signal-widths`, `tls-parser-initial` and `ws-initial`
(TlsMpc/HybridKernels.lean).

New file; it changes no definition and no emitter imports it.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `signalUpgrade_spec`, `signalUpgradeShared_spec`: the private `content` is
  `RelayUpgrade.request` on concrete bytes of the credentials (for the shared kernel: of the
  byte-wise XOR of the two parties' shares) followed by the nonce.
* `signalConversationView_spec`: the two private outputs are the stated slices of the record
  (the recipient's public key bytes, cert+150..+32; the request id, cert+182+size+40..+8). The
  `recipient` output additionally declares `bits := 255` (HybridKernels.lean), which this
  value statement does not cover.
* `widthFlags_symbolic`, `widthFlagsWith_map`, `signalWidths_spec`: the four opened width-flag
  lists are `widthFlagsWith` on concrete bytes of the session's counter, previous counter,
  SPQR epoch and `ChainSend.nextCounter` of the SPQR counter.
* `tlsParserInitial_spec`: the private parser state is 11 zero bytes, for every input.
* `wsInitial_spec`: the four private outputs are the slices 0..180, 180..206, 206..842,
  842..1774 of the concatenated concrete initial parser states, for every input.

NOT PROVED: that flag k of `widthFlagsWith` is 255 exactly when the big-endian value is at least
2^(7(k+1)) (the varint width meaning stated in the kernel's comment); that `RelayUpgrade.request`
is the HTTP request libsignal sends (tested only).
-/
namespace TlsMpc.KernelSpecs.SignalKernels
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape lookup lookupFrom pub priv sl)

/-! ### signal-upgrade, signal-upgrade-shared -/

def upgradeInputs (passwordBytes : Nat) : List (String × Shape) :=
  [("credentials", Shape.bytes (16 + passwordBytes)), ("nonce", .bytes 16)]

theorem signalUpgrade_spec (passwordBytes : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (upgradeInputs passwordBytes) name).map (BVExpr.eval assign)
    (HybridKernel.signalUpgrade passwordBytes).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [RelayUpgrade.request ByteAuth.concrete passwordBytes (get "credentials" ++ get "nonce")] := by
  intro get
  show [(RelayUpgrade.request ByteAuth.symbolic passwordBytes
      (lookup (upgradeInputs passwordBytes) "credentials" ++ lookup (upgradeInputs passwordBytes) "nonce")).map
        (BVExpr.eval assign)] = _
  rw [RelayUpgrade.request_map (ByteAuth.evaluationHom assign), List.map_append]

def sharedInputs (passwordBytes : Nat) : List (String × Shape) :=
  [("credentialsA", Shape.bytes (16 + passwordBytes)), ("credentialsB", .bytes (16 + passwordBytes)),
    ("nonce", .bytes 16)]

theorem zipWith_xor_eval (assign : BVExpr.Assignment) : ∀ xs ys : List (BVExpr 8),
    (List.zipWith ByteAuth.symbolic.xor xs ys).map (BVExpr.eval assign) =
      List.zipWith (· ^^^ ·) (xs.map (BVExpr.eval assign)) (ys.map (BVExpr.eval assign))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      simp only [List.zipWith_cons_cons, List.map_cons, zipWith_xor_eval assign xs ys,
        (ByteAuth.evaluationHom assign).xor]
      rfl

theorem signalUpgradeShared_spec (passwordBytes : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (sharedInputs passwordBytes) name).map (BVExpr.eval assign)
    (HybridKernel.signalUpgradeShared passwordBytes).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [RelayUpgrade.request ByteAuth.concrete passwordBytes
        (List.zipWith (· ^^^ ·) (get "credentialsA") (get "credentialsB") ++ get "nonce")] := by
  intro get
  show [(RelayUpgrade.request ByteAuth.symbolic passwordBytes
      (List.zipWith ByteAuth.symbolic.xor (lookup (sharedInputs passwordBytes) "credentialsA")
        (lookup (sharedInputs passwordBytes) "credentialsB") ++ lookup (sharedInputs passwordBytes) "nonce")).map
        (BVExpr.eval assign)] = _
  rw [RelayUpgrade.request_map (ByteAuth.evaluationHom assign), List.map_append, zipWith_xor_eval]

/-! ### signal-conversation-view -/

def viewInputs (cert size : Nat) : List (String × Shape) :=
  [("conversation", Shape.bytes (HybridKernel.conversationBytes cert size))]

theorem signalConversationView_spec (cert size : Nat) (assign : BVExpr.Assignment) :
    let record := (lookup (viewInputs cert size) "conversation").map (BVExpr.eval assign)
    (HybridKernel.signalConversationView cert size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [(record.drop (cert + 150)).take 32, (record.drop (cert + 182 + size + 40)).take 8] := by
  intro record
  show [(sl (lookup (viewInputs cert size) "conversation") (cert + 150) 32).map (BVExpr.eval assign),
    (sl (lookup (viewInputs cert size) "conversation") (cert + 182 + size + 40) 8).map (BVExpr.eval assign)] = _
  simp only [sl, List.map_take, List.map_drop, record]

/-! ### signal-widths -/

/-- `HybridKernel.widthFlags` over any operations. -/
def widthFlagsWith (a : ByteAuth.Ops B) (zero : B) (bigEndian : List B) (groups : Nat) : List B :=
  let n := bigEndian.length
  let bit (j : Nat) : B := a.maskBit (bigEndian.getD (n - 1 - j / 8) zero) (j % 8)
  (List.range groups).map (fun k =>
    (List.range (8 * n)).foldl (fun acc j => if 7 * (k + 1) ≤ j then TlsWebSocketUpgrade.either a acc (bit j) else acc)
      (a.const 0))

theorem widthFlags_symbolic (bigEndian : List (BVExpr 8)) (groups : Nat) :
    HybridKernel.widthFlags bigEndian groups = widthFlagsWith ByteAuth.symbolic (.const 0) bigEndian groups := rfl

theorem getD_map' (f : B → B') (l : List B) (i : Nat) (d : B) : (l.map f).getD i (f d) = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD]

theorem widthFlagsWith_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
    (zero : B) (bigEndian : List B) (groups : Nat) :
    (widthFlagsWith a zero bigEndian groups).map f = widthFlagsWith a' (f zero) (bigEndian.map f) groups := by
  have fold : ∀ (k : Nat) (js : List Nat) (acc : B),
      f (js.foldl (fun acc j => if 7 * (k + 1) ≤ j then TlsWebSocketUpgrade.either a acc
        (a.maskBit (bigEndian.getD (bigEndian.length - 1 - j / 8) zero) (j % 8)) else acc) acc) =
      js.foldl (fun acc j => if 7 * (k + 1) ≤ j then TlsWebSocketUpgrade.either a' acc
        (a'.maskBit ((bigEndian.map f).getD ((bigEndian.map f).length - 1 - j / 8) (f zero)) (j % 8)) else acc) (f acc) := by
    intro k js
    induction js with
    | nil => intro acc; rfl
    | cons j js ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        congr 1
        by_cases h : 7 * (k + 1) ≤ j
        · simp only [h, if_true, TlsWebSocketUpgrade.either_map ha, ha.maskBit, getD_map', List.length_map]
        · simp only [h, if_false]
  simp only [widthFlagsWith, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro k _
  rw [fold, ha.const, List.length_map]

def widthsInputs (cert : Nat) : List (String × Shape) :=
  [("conversation", Shape.bytes (HybridKernel.conversationBytes cert 80))]

theorem signalWidths_spec (cert : Nat) (assign : BVExpr.Assignment) :
    let session := (((lookup (widthsInputs cert) "conversation").map (BVExpr.eval assign)).drop cert).take 262
    let flags := fun (bytes : List (BitVec 8)) groups => widthFlagsWith ByteAuth.concrete 0 bytes groups
    (HybridKernel.signalWidths cert).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [flags ((session.drop 1).take 4) 4, flags ((session.drop 5).take 4) 4, flags ((session.drop 109).take 8) 9,
        flags (ChainSend.nextCounter Sha256.concrete ByteAuth.concrete ((session.drop 105).take 4)) 4] := by
  intro session flags
  have ha := ByteAuth.evaluationHom assign
  have zero : BVExpr.eval assign (.const 0 : BVExpr 8) = 0 := rfl
  let s := sl (lookup (widthsInputs cert) "conversation") cert 262
  show [(HybridKernel.widthFlags (sl s 1 4) 4).map (BVExpr.eval assign),
    (HybridKernel.widthFlags (sl s 5 4) 4).map (BVExpr.eval assign),
    (HybridKernel.widthFlags (sl s 109 8) 9).map (BVExpr.eval assign),
    (HybridKernel.widthFlags (ChainSend.nextCounter Sha256.symbolic ByteAuth.symbolic (sl s 105 4)) 4).map
      (BVExpr.eval assign)] = _
  simp only [widthFlags_symbolic, widthFlagsWith_map ha, zero,
    ChainSend.nextCounter_map (Sha256.evaluationHom assign) ha]
  simp only [s, sl, List.map_take, List.map_drop, session, flags]

/-! ### Constant kernels -/

theorem tlsParserInitial_spec (assign : BVExpr.Assignment) :
    HybridKernel.tlsParserInitial.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [List.replicate 11 0] := by
  show [(HybridKernel.zeros 11).map (BVExpr.eval assign)] = _
  simp only [HybridKernel.zeros, List.map_replicate]
  rfl

/-- The concatenated initial parser states, on values. -/
def initialValues : List (BitVec 8) :=
  TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start ByteAuth.concrete) ++
  TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start ByteAuth.concrete HybridService.capacity) ++
  TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial ByteAuth.concrete) ++
  TlsChatResponse.stateBytes Word64.concrete
    (TlsChatResponse.initial Word64.concrete ByteAuth.concrete HybridService.capacity 0)

theorem initialStates_eval (assign : BVExpr.Assignment) :
    HybridService.initialStates.map (BVExpr.eval assign) = initialValues := by
  simp only [HybridService.initialStates, HybridService.constants, List.map_append, List.map_map,
    Function.comp_def, BVExpr.eval_const, List.map_id', initialValues]

theorem wsInitial_spec (assign : BVExpr.Assignment) :
    HybridKernel.wsInitial.outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [(initialValues.drop 0).take 180, (initialValues.drop 180).take 26, (initialValues.drop 206).take 636,
        (initialValues.drop 842).take 932] := by
  show [(sl HybridService.initialStates 0 180).map (BVExpr.eval assign),
    (sl HybridService.initialStates 180 26).map (BVExpr.eval assign),
    (sl HybridService.initialStates 206 636).map (BVExpr.eval assign),
    (sl HybridService.initialStates 842 932).map (BVExpr.eval assign)] = _
  simp only [sl, List.map_take, List.map_drop, initialStates_eval]

#print axioms signalUpgrade_spec
#print axioms signalUpgradeShared_spec
#print axioms signalConversationView_spec
#print axioms widthFlagsWith_map
#print axioms signalWidths_spec
#print axioms tlsParserInitial_spec
#print axioms wsInitial_spec

end TlsMpc.KernelSpecs.SignalKernels
