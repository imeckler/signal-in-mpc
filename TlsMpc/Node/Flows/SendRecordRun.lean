import TlsMpc.Node.Flows.SendRun

/-!
# The request's record seal through `jointRun` (S13, F51 second part)

REORGANIZATION_PLAN.md stage S13. New file; it changes no definition. No I/O; no emitter imports
this module.

  * `requestCtr_joint`: two honest parties run `requestCtrScript` (the request's CTR phase) on the
    traffic block and the request's conversation; with the request kernel loaded as its model circuit
    (`Contacts.kernelCircuit`, T2 for byte kernels) both end with header ‖ ciphertext of the kernel's
    output and the pad's handle `p + 4` holding the pad; both saw exactly accepted ‖ header ‖
    ciphertext.
  * `tag_joint`: two honest parties run S12's `Tls.tagScript` with their halves in their stores; both
    end with the tag `gcm-tag` computes on pad ‖ half A ‖ half B and saw exactly the tag.
  * `send_joint`: op 41 (accepted), op 42 on the handle op 41 returned, the CTR phase on the
    conversation op 42 returned, the tag on the pad the CTR phase returned: both parties end with the
    same bytes for the server, header ‖ ciphertext ‖ tag, which are `TlsRecord.sealCore` of the
    request frame carrying the reference sealed-sender envelope (`Send.send_accepted`), and the same
    new state, the advanced record.
-/

namespace TlsMpc.Node.Flows.Send

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.HybridKernel (Kernel lookup lookupFrom)

theorem requestCtrScript_pubRun (E : Env) (p : Nat) (traffic conv : BoolH) (seqB frame mask : B8) (name : Bytes)
    (Kr : Kernel) (inBytes : Nat) (marks : List Mark) (K C : B8) (I : Ideal)
    (htp : traffic.id < p) (hcp : conv.id < p)
    (hK : I.bools traffic.id = some (bitsOf K)) (hC : I.bools conv.id = some (bitsOf C))
    (hE : E.circuits name = some (kernelCircuit Kr inBytes marks))
    (hin : (requestIn K seqB C frame mask).length = inBytes)
    (hlen : (kernelOut Kr (requestIn K seqB C frame mask)).length = 1 + 5 + innerOf frame.length + 16)
    (hacc : (kernelOut Kr (requestIn K seqB C frame mask)).take 1 = [255]) :
    let ctr := kernelOut Kr (requestIn K seqB C frame mask)
    let L := 1 + 5 + innerOf frame.length
    let r := pubRun E (requestCtrScript p traffic conv seqB frame mask name) I
    r.1 = some ((ctr.take L).drop 1, ⟨p + 4⟩) ∧
    r.2.2 = [⟨Label.sealedRecord, .bits (bitsOf (ctr.take L))⟩] ∧
    r.2.1.bools (p + 4) = some (bitsOf ((ctr.drop L).take 16)) ∧
    ∀ x, x < p → x ≠ conv.id → r.2.1.bools x = I.bools x := by
  dsimp only
  generalize hctr : kernelOut Kr (requestIn K seqB C frame mask) = ctr at hlen hacc
  generalize hL : 1 + 5 + innerOf frame.length = L at hlen
  have hBl : (bitsOf ctr).length = 8 * (L + 16) := by rw [length_bitsOf, hlen]
  have hv : [bitsOf K, bitsOf seqB, bitsOf C, bitsOf frame ++ bitsOf mask].flatten =
      bitsOf (requestIn K seqB C frame mask) := by
    simp [requestIn, List.append_assoc]
  have hev : (kernelCircuit Kr inBytes marks).eval (bitsOf (requestIn K seqB C frame mask)) = bitsOf ctr := by
    rw [← hctr]
    show bitsOf (kernelOut Kr (bytesOf (bitsOf _))) = _
    rw [bytesOf_bitsOf]
  have hw : (bitsOf (requestIn K seqB C frame mask)).length = 1 * (kernelCircuit Kr inBytes marks).inWidth := by
    show _ = 1 * (8 * inBytes)
    rw [length_bitsOf, hin, Nat.one_mul]
  have key : ∃ J, pubRun E (requestCtrScript p traffic conv seqB frame mask name) I =
      pubRun E (openThen ⟨p + 5⟩ Label.sealedRecord fun out =>
        seqs [.freeBool ⟨p + 5⟩]
          (if (bytesOf out).take 1 = [255] then .done ((bytesOf out).drop 1, ⟨p + 4⟩)
           else .abort "private request rejected")) J ∧
      J.bools (p + 5) = some (bitsOf (ctr.take L)) ∧ J.bools (p + 4) = some (bitsOf ((ctr.drop L).take 16)) ∧
      ∀ x, x < p → x ≠ conv.id → J.bools x = I.bools x := by
    refine ⟨?J, ?e, ?f5, ?f4, ?fx⟩
    case e =>
      unfold requestCtrScript
      dsimp only
      simp only [seqs_cons, seqs_nil]
      rw [pubRun_boolPublic, pubRun_boolPublic,
        pubRun_concat E _ _ _ _ [bitsOf K, bitsOf seqB, bitsOf C, bitsOf frame ++ bitsOf mask] (by
          have t0 : (traffic.id = p) = False := by simp; omega
          have t1 : (traffic.id = p + 1) = False := by simp; omega
          have c0 : (conv.id = p) = False := by simp; omega
          have c1 : (conv.id = p + 1) = False := by simp; omega
          have pp : (p = p + 1) = False := by simp
          simp only [List.mapM_cons, List.mapM_nil, setBool_bools, t0, t1, c0, c1, pp, eq_self_iff_true, if_true,
            if_false, hK, hC]
          rfl),
        hv, pubRun_run E _ _ _ _ _ _ _ _ hE (bools_setk_eq _ _ _ _ rfl) hw,
        runCopies_one _ _ (by rw [hw, Nat.one_mul]), hev, hL,
        pubRun_slice E _ _ _ _ _ _ (bitsOf ctr) (bools_setk_eq _ _ _ _ rfl) (by omega) (by rw [hBl]; omega),
        pubRun_slice E _ _ _ _ _ _ (bitsOf ctr) ?hv2 (by omega) (by rw [hBl]; omega),
        pubRun_free, pubRun_free, pubRun_free, pubRun_free, pubRun_free]
      case hv2 =>
        dsimp only
        rw [bools_setk_ne _ _ _ _ (by omega), bools_setk_eq _ _ _ _ rfl]
    case f5 =>
      dsimp only
      rw [bools_drop_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega),
        bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_setk_eq _ _ _ _ rfl,
        slice_bytes ctr 0 L 0 (8 * L) rfl rfl, List.drop_zero, Nat.sub_zero]
    case f4 =>
      rw [bools_drop_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega),
        bools_dropk_ne _ _ _ (by omega), bools_dropk_ne _ _ _ (by omega), bools_setk_ne _ _ _ _ (by omega),
        bools_setk_eq _ _ _ _ rfl, slice_bytes ctr L (L + 16) (8 * L) (8 * L + 128) rfl (by omega),
        show L + 16 - L = 16 by omega]
    case fx =>
      intro x hx hxc
      have hxk : ∀ k, (x = p + k) = False := fun k => by simp; omega
      have hx0 : (x = p) = False := by simp; omega
      have hxc' : (x = conv.id) = False := by simp; exact hxc
      simp only [setBool_bools, dropBool_bools, hxk, hx0, hxc', if_false]
  obtain ⟨J, hrun, h5, h4, hx⟩ := key
  have h1 : ((ctr.take L).take 1) = [255] := by
    rw [List.take_take, show min 1 L = 1 by omega, hacc]
  rw [hrun, pubRun_openThen E _ _ _ _ _ h5]
  simp only [seqs_cons, seqs_nil, pubRun_free, bytesOf_bitsOf, h1, if_true]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · dsimp only [pubRun]
    rw [bools_dropk_ne _ _ _ (by omega), h4]
  · intro x hxp hxc
    dsimp only [pubRun]
    rw [bools_dropk_ne _ _ _ (by omega), hx x hxp hxc]

/-- **The request's CTR phase, two honest parties** (`requestCtrScript`). -/
theorem requestCtr_joint (E : Env) (σA σB : Store) (p : Nat) (traffic conv : BoolH) (seqB frame mask : B8)
    (name : Bytes) (Kr : Kernel) (inBytes : Nat) (marks : List Mark) (K C : B8) (I : Ideal)
    (htp : traffic.id < p) (hcp : conv.id < p)
    (hK : I.bools traffic.id = some (bitsOf K)) (hC : I.bools conv.id = some (bitsOf C))
    (hE : E.circuits name = some (kernelCircuit Kr inBytes marks))
    (hin : (requestIn K seqB C frame mask).length = inBytes)
    (hlen : (kernelOut Kr (requestIn K seqB C frame mask)).length = 1 + 5 + innerOf frame.length + 16)
    (hacc : (kernelOut Kr (requestIn K seqB C frame mask)).take 1 = [255]) :
    let ctr := kernelOut Kr (requestIn K seqB C frame mask)
    let L := 1 + 5 + innerOf frame.length
    let o := jointRun E (requestCtrScript p traffic conv seqB frame mask name)
      (requestCtrScript p traffic conv seqB frame mask name) σA σB I
    o.result = some (((ctr.take L).drop 1, ⟨p + 4⟩), ((ctr.take L).drop 1, ⟨p + 4⟩)) ∧
    o.viewA = [⟨Label.sealedRecord, .bits (bitsOf (ctr.take L))⟩] ∧ o.viewB = o.viewA ∧
    o.ideal.bools (p + 4) = some (bitsOf ((ctr.drop L).take 16)) ∧
    ∀ x, x < p → x ≠ conv.id → o.ideal.bools x = I.bools x := by
  dsimp only
  obtain ⟨r1, r2, r3, r4⟩ := jointRun_pub E (requestCtrScript_pubs p traffic conv seqB frame mask name) σA σB I
  obtain ⟨e1, e2, e3, e4⟩ := requestCtrScript_pubRun E p traffic conv seqB frame mask name Kr inBytes marks K C I
    htp hcp hK hC hE hin hlen hacc
  refine ⟨by rw [r1, e1]; rfl, by rw [r3, e2], by rw [r4, r3], by rw [r2, e3], fun x hx hxc => by rw [r2, e4 x hx hxc]⟩

/-- One step of both parties' Boolean inputs, each from its own store (`boolInputBoth`). -/
theorem jointRun_inputBoth (E : Env) {α : Type} (oa ob : BoolH) (w : Nat) (once rev : Bool) (slot : Nat)
    (s : Script α) (σA σB : Store) (I : Ideal) (hA : (σA.bits slot).length = w) (hB : (σB.bits slot).length = w) :
    let o := jointRun E (seq (.boolInputBoth oa ob w once rev slot) s) (seq (.boolInputBoth oa ob w once rev slot) s)
      σA σB I
    let o' := jointRun E s s σA σB ((I.setBool oa (σA.bits slot)).setBool ob (σB.bits slot))
    o.result = o'.result ∧ o.ideal = o'.ideal ∧ o.viewA = o'.viewA ∧ o.viewB = o'.viewB := by
  dsimp only
  simp [seq, jointRun, fill, hA, hB, idealStep, Wire.part, absorb, InstrP.skel, InstrP.map]

/-- **The tag phase, two honest parties** (S12's `Tls.tagScript`): each party's 16-byte half in its
own store; with `gcm-tag` loaded as its model circuit, both end with the tag `gcm-tag` computes on
pad ‖ half A ‖ half B, and saw exactly that tag. -/
theorem tag_joint (E : Env) (σA σB : Store) (q : Nat) (pad : BoolH) (halfSlot : Nat) (padB hA hB : B8)
    (marks : List Mark) (I : Ideal) (hpq : pad.id < q)
    (hP : I.bools pad.id = some (bitsOf padB)) (hpl : padB.length = 16) (hAl : hA.length = 16) (hBl : hB.length = 16)
    (hsA : σA.bits halfSlot = bitsOf hA) (hsB : σB.bits halfSlot = bitsOf hB)
    (hE : E.circuits Tls.tagName = some (kernelCircuit HybridKernel.gcmTag 48 marks)) :
    let tag := kernelOut HybridKernel.gcmTag (padB ++ (hA ++ hB))
    let o := jointRun E (Tls.tagScript q pad halfSlot) (Tls.tagScript q pad halfSlot) σA σB I
    o.result = some (tag, tag) ∧ o.viewA = [⟨Label.sealedRecord, .bits (bitsOf tag)⟩] ∧ o.viewB = o.viewA := by
  dsimp only
  have hA' : (σA.bits halfSlot).length = 128 := by rw [hsA, length_bitsOf, hAl]
  have hB' : (σB.bits halfSlot).length = 128 := by rw [hsB, length_bitsOf, hBl]
  have hsplit : Tls.tagScript q pad halfSlot = seq (.boolInputBoth ⟨q⟩ ⟨q + 1⟩ 128 true false halfSlot)
      (seq (.concat ⟨q + 2⟩ [pad, ⟨q⟩, ⟨q + 1⟩]) (seq (.run ⟨q + 3⟩ Tls.tagName 1 ⟨q + 2⟩)
        (seq (.freeBool pad) (openThen ⟨q + 3⟩ Label.sealedRecord fun tag =>
          seqs [.freeBool ⟨q + 3⟩] (.done (bytesOf tag)))))) := rfl
  rw [hsplit]
  obtain ⟨j1, -, j3, j4⟩ := jointRun_inputBoth E ⟨q⟩ ⟨q + 1⟩ 128 true false halfSlot
    (seq (.concat ⟨q + 2⟩ [pad, ⟨q⟩, ⟨q + 1⟩]) (seq (.run ⟨q + 3⟩ Tls.tagName 1 ⟨q + 2⟩)
        (seq (.freeBool pad) (openThen ⟨q + 3⟩ Label.sealedRecord fun tag =>
          seqs [.freeBool ⟨q + 3⟩] (.done (bytesOf tag)))))) σA σB I hA' hB'
  rw [hsA, hsB] at j1 j3 j4
  have hpub : Every (fun i => pubInstr i = true)
      (seq (.concat ⟨q + 2⟩ [pad, ⟨q⟩, ⟨q + 1⟩]) (seq (.run ⟨q + 3⟩ Tls.tagName 1 ⟨q + 2⟩)
        (seq (.freeBool pad) (openThen ⟨q + 3⟩ Label.sealedRecord fun tag =>
          seqs [.freeBool ⟨q + 3⟩] (.done (bytesOf tag)))))) :=
    every_seq rfl (every_seq rfl (every_seq rfl (every_openThen (pub_open _ _)
      (fun _ => every_seqs (Every.done _) _ (plain_pub rfl)))))
  obtain ⟨r1, -, r3, r4⟩ := jointRun_pub E hpub σA σB ((I.setBool ⟨q⟩ (bitsOf hA)).setBool ⟨q + 1⟩ (bitsOf hB))
  have hv : [bitsOf padB, bitsOf hA, bitsOf hB].flatten = bitsOf (padB ++ (hA ++ hB)) := by simp
  have hw : (bitsOf (padB ++ (hA ++ hB))).length = 1 * (kernelCircuit HybridKernel.gcmTag 48 marks).inWidth := by
    show _ = 1 * (8 * 48)
    simp [hpl, hAl, hBl]
  have e : (pubRun E (seq (.concat ⟨q + 2⟩ [pad, ⟨q⟩, ⟨q + 1⟩]) (seq (.run ⟨q + 3⟩ Tls.tagName 1 ⟨q + 2⟩)
        (seq (.freeBool pad) (openThen ⟨q + 3⟩ Label.sealedRecord fun tag =>
          seqs [.freeBool ⟨q + 3⟩] (.done (bytesOf tag))))))
        ((I.setBool ⟨q⟩ (bitsOf hA)).setBool ⟨q + 1⟩ (bitsOf hB))).1 =
        some (kernelOut HybridKernel.gcmTag (padB ++ (hA ++ hB))) ∧
      (pubRun E (seq (.concat ⟨q + 2⟩ [pad, ⟨q⟩, ⟨q + 1⟩]) (seq (.run ⟨q + 3⟩ Tls.tagName 1 ⟨q + 2⟩)
        (seq (.freeBool pad) (openThen ⟨q + 3⟩ Label.sealedRecord fun tag =>
          seqs [.freeBool ⟨q + 3⟩] (.done (bytesOf tag))))))
        ((I.setBool ⟨q⟩ (bitsOf hA)).setBool ⟨q + 1⟩ (bitsOf hB))).2.2 =
        [⟨Label.sealedRecord, .bits (bitsOf (kernelOut HybridKernel.gcmTag (padB ++ (hA ++ hB))))⟩] := by
    have p0 : (pad.id = q) = False := by simp; omega
    have p1 : (pad.id = q + 1) = False := by simp; omega
    have qq : (q = q + 1) = False := by simp
    rw [pubRun_concat E _ _ _ _ [bitsOf padB, bitsOf hA, bitsOf hB] (by
          simp only [List.mapM_cons, List.mapM_nil, setBool_bools, p0, p1, qq, eq_self_iff_true, if_true, if_false, hP]
          rfl),
      hv, pubRun_run E _ _ _ _ _ _ _ _ hE (bools_setk_eq _ _ _ _ rfl) hw,
      runCopies_one _ _ (by rw [hw, Nat.one_mul]), pubRun_free,
      pubRun_openThen E ⟨q + 3⟩ _ _ _ (bitsOf (kernelOut HybridKernel.gcmTag (padB ++ (hA ++ hB)))) ?hl]
    case hl =>
      dsimp only
      rw [bools_drop_ne _ _ _ (by omega), bools_setk_eq _ _ _ _ rfl]
      show some (bitsOf (kernelOut _ (bytesOf (bitsOf _)))) = _
      rw [bytesOf_bitsOf]
    constructor <;> simp [pubRun, pubRun_free, bytesOf_bitsOf]
  rw [e.1] at r1
  rw [e.2] at r3 r4
  refine ⟨by rw [j1, r1]; rfl, by rw [j3, r3], by rw [j4, r4, j3, r3]⟩

/-- `signal-request-ctr`'s whole output length on the script's bundle (accepted ‖ header ‖
ciphertext ‖ pad). -/
theorem requestCtr_length (cert : Nat) (env : B8) (ts id : Nat) (mask frame : B8) (official : Bool)
    (offsets : List Nat) (hb : PublicRequest.build env ts id mask official = .ok (frame, offsets))
    (K seqB conv : B8) (hK : K.length = 60) (hs : seqB.length = 8) (hc : conv.length = convBytes cert) :
    (kernelOut (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0)
      (offsets.getD 2 0) (offsets.getD 3 0)) (requestIn K seqB conv frame mask)).length =
      1 + 5 + innerOf frame.length + 16 := by
  have hval := requestCtr_value cert env ts id mask frame official offsets hb K seqB conv hK hs hc
  have hPl := requestPlain_length cert env ts id mask frame official offsets hb K seqB conv hK hs hc
  simp only at hval hPl
  generalize KernelSpecs.RequestFrame.buildHeader (PublicRequest.total (PublicRequest.sendMessage env ts id official))
    mask ++ KernelSpecs.RequestFrame.maskFrom mask 0 (KernelSpecs.RequestFrame.render
      (KernelSpecs.RequestFrame.requestValues cert conv) (PublicRequest.sendMessage env ts id official)) = P at hval hPl
  show (List.map _ _).flatten.length = _
  rw [hval]
  have hH := Tls.header_length (innerOf frame.length + 16)
  have hI : (TlsRecord.inner Gcm.concrete P 23 0).length = innerOf frame.length := by
    rw [Tls.inner_length, hPl]; rfl
  simp only [KernelSpecs.sealedRequest, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
    List.length_cons, List.length_nil, ByteAuth.release, List.length_map, HybridKernel.ctrOf_length _ _ _ hK, hI,
    Tls.padOf_length K seqB hK]
  rw [hH]
  omega

/-- **F51: a whole single-device send through `jointRun`.** Two honest parties run op 41 (accepted),
op 42 on the state handle op 41 returned, the request's CTR phase on the conversation op 42 returned
(with the traffic block), and S12's tag phase on the pad the CTR phase returned (each party's half
in its own store). Both end with the same results at every phase, and the bytes for the server,
header ‖ ciphertext ‖ tag, are exactly the ones `Send.send_accepted` characterises (so they are
`TlsRecord.sealCore` of the request frame carrying the reference sealed-sender envelope), the new
state handle `n + 6` holds the kept record, and both saw exactly the flags, the status, timestamp ‖
envelope, accepted ‖ header ‖ ciphertext and the tag. The kernels are their model circuits (T2:
`shapedCircuit` for the seal kernel, `kernelCircuit` for the request kernel and `gcm-tag`). -/
theorem send_joint (E : Env) (σA σB σA' σB' : Store) (n : Nat) (a : SealArgs) (certB record : B8) (db eb tb : Bits)
    (I : Ideal) (Cw : Circuit) (official : Bool) (classes : Nat)
    (h : SealModel E n a certB record db eb tb I Cw official classes)
    (cw pw ew iw : Nat) (mk : List Mark)
    (hw : widthsOf (bytesOf (Cw.eval (bitsOf (certB ++ record)))) = some (cw, pw, ew, iw))
    (henv : sealEnvBytes a.certLen classes official cw pw ew iw ≤ maxEnvelope)
    (hS : E.circuits (sealName official a.certLen classes cw pw ew iw) =
      some (shapedCircuit (sealK a.certLen cw pw ew iw classes official) mk))
    (traffic : BoolH) (K seqB : B8) (hK : K.length = 60) (hs : seqB.length = 8)
    (htn : traffic.id < n) (hte : traffic.id ≠ a.ephAgreement.id) (hts : traffic.id ≠ a.state.id)
    (hKv : I.bools traffic.id = some (bitsOf K))
    (m p q : Nat) (hm : n + 8 ≤ m) (hp : m + 2 ≤ p) (hq : p + 6 ≤ q)
    (id : Nat) (mask frame : B8) (offsets : List Nat) (marksR marksT : List Mark) (halfSlot : Nat)
    (hR : E.circuits (requestNameOf a.certLen frame offsets) =
      some (kernelCircuit (HybridKernel.signalRequestCtr a.certLen frame.length (offsets.getD 0 0) (offsets.getD 1 0)
        (offsets.getD 2 0) (offsets.getD 3 0)) (68 + convBytes a.certLen + frame.length + 4) marksR))
    (hT : E.circuits Tls.tagName = some (kernelCircuit HybridKernel.gcmTag 48 marksT))
    (ga gb : List Tls.W) :
    let out := sealOutOf a certB record db eb tb official classes cw pw ew iw
    let te := (out.drop (1 + convBytes a.certLen)).take (8 + sealEnvBytes a.certLen classes official cw pw ew iw)
    let newRecord := (out.drop (1 + a.certLen)).take recordBytes
    let ctr := kernelOut (HybridKernel.signalRequestCtr a.certLen frame.length (offsets.getD 0 0) (offsets.getD 1 0)
      (offsets.getD 2 0) (offsets.getD 3 0)) (requestIn K seqB (certB ++ newRecord) frame mask)
    let hc := (ctr.drop 1).take (5 + innerOf frame.length)
    let pad := (ctr.drop (1 + 5 + innerOf frame.length)).take 16
    let hA := Local.Ghash.toBytes (Local.Ghash.half ga (hc.take 5) (hc.drop 5))
    let hB := Local.Ghash.toBytes (Local.Ghash.half gb (hc.take 5) (hc.drop 5))
    out.take 1 = [255] →
    frameFor (te.drop 8) (te.take 8) id mask official = .ok (frame, offsets) →
    ctr.take 1 = [255] →
    σA'.bits halfSlot = bitsOf hA → σB'.bits halfSlot = bitsOf hB →
    let o1 := jointRun E (sealScript n a) (sealScript n a) σA σB I
    let o2 := jointRun E (requestScript m a.cert ⟨n + 6⟩) (requestScript m a.cert ⟨n + 6⟩) σA σB o1.ideal
    let o3 := jointRun E (requestCtrScript p traffic ⟨m + 1⟩ seqB frame mask (requestNameOf a.certLen frame offsets))
      (requestCtrScript p traffic ⟨m + 1⟩ seqB frame mask (requestNameOf a.certLen frame offsets)) σA σB o2.ideal
    let o4 := jointRun E (Tls.tagScript q ⟨p + 4⟩ halfSlot) (Tls.tagScript q ⟨p + 4⟩ halfSlot) σA' σB' o3.ideal
    ∃ (sd : Sealed) (hc' tag : B8),
      o1.result = some (some sd, some sd) ∧ sd.state = ⟨n + 6⟩ ∧ sd.envelopes = [te.drop 8] ∧
      o1.ideal.bools (n + 6) = some (bitsOf newRecord) ∧
      o2.result = some (⟨m + 1⟩, ⟨m + 1⟩) ∧
      o3.result = some ((hc', ⟨p + 4⟩), (hc', ⟨p + 4⟩)) ∧
      o4.result = some (tag, tag) ∧
      hc' ++ tag = hc ++ kernelOut HybridKernel.gcmTag (pad ++ (hA ++ hB)) := by
  intro out te newRecord ctr hc pad hA hB hacc hframe hctr hsA hsB o1 o2 o3 o4
  obtain ⟨kA, -⟩ := seal_joint E σA σB n a certB record db eb tb I Cw official classes h cw pw ew iw mk hw henv hS
  obtain ⟨e1, -, -, e4, e5⟩ := kA hacc
  -- the kept record has a record's length
  obtain ⟨-, hcls4⟩ := textClass_le h.cls
  have hl := sealOut_length a certB record db eb tb official classes cw pw ew iw
    (sealBound_of a.certLen cw pw ew iw classes official h.certLe hcls4 (widthsOf_le hw)) (textClass_pos h.cls)
  have hl' : out.length = 1 + convBytes a.certLen + (8 + sealEnvBytes a.certLen classes official cw pw ew iw) := hl
  have hnr : newRecord.length = recordBytes := by
    show (List.take _ (List.drop _ out)).length = _
    simp only [List.length_take, List.length_drop, hl', convBytes]
    omega
  -- op 42
  have hc1 : o1.ideal.bools a.cert.id = some (bitsOf certB) := by
    rw [e5 _ h.cn (fun e => h.ec e.symm) h.cs, h.vc]
  obtain ⟨q1, -, -, q4, q5⟩ := request_joint E σA σB m a.cert ⟨n + 6⟩ certB newRecord o1.ideal
    (by have := h.cn; omega) (by omega) hc1 e4
  rw [List.take_of_length_le (by omega)] at q4
  -- the CTR phase
  have hK2 : o2.ideal.bools traffic.id = some (bitsOf K) := by
    rw [q5 _ (by omega), e5 _ htn hte hts, hKv]
  have hb : PublicRequest.build (te.drop 8) (beNat (te.take 8)) id mask official = .ok (frame, offsets) := hframe
  have hconv : (certB ++ newRecord).length = convBytes a.certLen := by
    simp only [List.length_append, h.certLen, hnr, convBytes]
  have hlen := requestCtr_length a.certLen (te.drop 8) (beNat (te.take 8)) id mask frame official offsets hb K seqB
    (certB ++ newRecord) hK hs hconv
  have hm4 : mask.length = 4 := (KernelSpecs.RequestFrame.build_ok _ _ _ _ _ _ _ hb).2.2.1
  have hin : (requestIn K seqB (certB ++ newRecord) frame mask).length = 68 + convBytes a.certLen + frame.length + 4 := by
    simp only [requestIn, List.length_append, hK, hs, hconv, hm4]
    omega
  obtain ⟨c1, -, -, c4, -⟩ := requestCtr_joint E σA σB p traffic ⟨m + 1⟩ seqB frame mask
    (requestNameOf a.certLen frame offsets) _ _ marksR K (certB ++ newRecord) o2.ideal (by omega) (by show m + 1 < p; omega)
    hK2 q4 hR hin hlen hctr
  -- the tag phase
  have hlen' : ctr.length = 1 + 5 + innerOf frame.length + 16 := hlen
  have hpadl : pad.length = 16 := by
    show (List.take 16 (List.drop _ ctr)).length = 16
    simp only [List.length_take, List.length_drop, hlen']
    omega
  obtain ⟨t1, -, -⟩ := tag_joint E σA' σB' q ⟨p + 4⟩ halfSlot pad hA hB marksT o3.ideal (by show p + 4 < q; omega)
    c4 hpadl (Local.Ghash.toBytes_length _) (Local.Ghash.toBytes_length _) hsA hsB hT
  refine ⟨_, _, _, e1, rfl, rfl, e4, q1, c1, t1, ?_⟩
  congr 1
  show (ctr.take (1 + 5 + innerOf frame.length)).drop 1 = (ctr.drop 1).take (5 + innerOf frame.length)
  rw [List.drop_take, show 1 + 5 + innerOf frame.length - 1 = 5 + innerOf frame.length by omega]

end TlsMpc.Node.Flows.Send
