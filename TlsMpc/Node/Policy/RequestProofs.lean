import TlsMpc.Node.Policy.RequestSpec
import TlsMpc.KernelSpecs.RequestFrame
import TlsMpc.Node.Policy.Receive

/-!
# The request templates are the requests Signal-Server parses (REORGANIZATION_PLAN.md P2, T8)

New file. It changes no definition; no emitter imports it. The theorems are about the
controller's own builders (`TlsMpc/Node/Policy/Request.lean`: `sendMessage`, `fetchMessage`,
`devicesMessage`, `build`, `assemble`, `buildFetch`, `buildDevices`; `Policy/Receive.lean`:
`clientFrame`, `reply`, `keepalive`, `ping`) against the references of `RequestSpec.lean`
(protobuf, JSON, `IncomingMessageList`, routes and RFC 6455 frames written from the wire formats and
checked against Signal-Server's sources, cited there).

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* Messages. `sendMessage_reference`, `fetchMessage_reference`, `devicesMessage_reference`: with
  each slot filled with a value of its width, the message a builder frames (`render`) is the
  protobuf `WebSocketMessage { REQUEST, WebSocketRequestMessage {...} }` of `sendRequest` (with the
  `IncomingMessageList` JSON of `sendBody`, members in key order or libsignal's order),
  `keysRequest`. On the way: `varint_eq` (the builders' varint is the protobuf varint below
  `2^70`), `devicesJson_render`, `sendJson_render`, `base64_fast` (RFC 4648).
* Frames. `build_reference`, `buildFetch_reference`, `buildDevices_reference`: for every frame the
  builder returns, the filled frame is `clientFrame binary mask (reference).encode`, and RFC 6455's
  reading of it (`decodeFrame`) is one FIN binary frame, masked with that key, with a minimal
  length, carrying exactly the reference message. `clientFrame_reference`, `ping_reference`,
  `ping_decode`, `keepalive_reference`, `keepalive_decode`, `reply_reference`, `reply_decode`: the
  control-path frames are the reference frames (`GET /v1/keepalive`; the `200 OK` response echoing
  the server's id; a ping with the count). `decode_clientFrame`: RFC 6455's reading of any
  `clientFrame` (opcode < 16, 4-byte key, payload < 65536).
* Kernels, end to end. `signalRequestCtr_reference`, `bundleFetchCtr_reference`,
  `bundleRequestCtr_reference`: composing with `RequestFrame.*_built`, the kernels' outputs are
  `sealedRequest` of exactly the RFC 6455 frame of the reference request with the contact's UUID,
  access key and padded ids from the record.
* Nothing else about the contact. `build_public`, `buildFetch_public`, `buildDevices_public`: outside
  the slot ranges `[offset k, offset k + width k)`, the encrypted frame is byte for byte the frame the
  builder computed from public inputs only; `build_two_contacts`: two contacts' frames for the same
  public inputs agree outside the slots. `build_layout`, `buildFetch_layout`, `buildDevices_layout`:
  frame length, payload start and slot offsets depend only on the envelopes' lengths (so the device
  count), the timestamp's digit count, the id's varint length and the profile.

NOT PROVED: `reply` for a server id of `2^70` or more (`reply_reference` is stated for ids below
`2^70`; `varintAt_lt` proves `varintAt` only reads such ids, but that `scan`'s id comes from
`varintAt` is not proved: it needs an invariant through `scan`'s loop); `replies` (pong and close
echoes through `TlsWebSocketControl.encode`); that the C++ worker passes the builder's frame
unchanged (RequestFrame's trusted hypotheses).
-/

namespace TlsMpc.Node.RequestProofs
open TlsMpc TlsMpc.Signal TlsMpc.Node.RequestSpec
open PublicRequest (Piece total field text sendMessage fetchMessage devicesMessage officialJson build assemble
  buildFetch buildDevices)
open TlsMpc.KernelSpecs.RequestFrame (render maskFrom body pairsOf buildHeader assembleHeader)

abbrev Byte := BitVec 8

/-! ## Varints -/

theorem varintFuel_stable : ∀ (f g n : Nat), n ≤ f → n ≤ g → varintFuel f n = varintFuel g n
  | 0, 0, _, _, _ => rfl
  | 0, g + 1, n, hf, _ => by
      have : n = 0 := by omega
      subst this; simp [varintFuel]
  | f + 1, 0, n, _, hg => by
      have : n = 0 := by omega
      subst this; simp [varintFuel]
  | f + 1, g + 1, n, hf, hg => by
      simp only [varintFuel]
      split
      · rfl
      · rw [varintFuel_stable f g (n / 128) (by omega) (by omega)]

theorem pbVarint_eq (n : Nat) :
    pbVarint n = if n < 128 then [BitVec.ofNat 8 n] else BitVec.ofNat 8 (n % 128 + 128) :: pbVarint (n / 128) := by
  unfold pbVarint
  cases n with
  | zero => rfl
  | succ m =>
      simp only [varintFuel]
      split
      · rfl
      · rw [varintFuel_stable m ((m + 1) / 128) ((m + 1) / 128) (by omega) (by omega)]

theorem pbVarint_small (n : Nat) (h : n < 128) : pbVarint n = [BitVec.ofNat 8 n] := by
  rw [pbVarint_eq, if_pos h]

/-- One group of the builders' `varint` (`PublicRequest.varint`, `PublicReceive.varint`). -/
def group (n i : Nat) : Option Byte :=
  let rest := n / 128 ^ i
  if i > 0 && rest == 0 then none
  else some (BitVec.ofNat 8 (rest % 128 + (if rest / 128 == 0 then 0 else 128)))

theorem varint_groups (n : Nat) : PublicRequest.varint n = (List.range 10).filterMap (group n) := rfl
theorem receive_varint (n : Nat) : PublicReceive.varint n = PublicRequest.varint n := rfl

theorem group_succ (n i : Nat) (h : 128 ≤ n) : group n (i + 1) = group (n / 128) i := by
  have e : n / 128 ^ (i + 1) = n / 128 / 128 ^ i := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
  unfold group
  simp only [e]
  cases i with
  | zero =>
      simp; omega
  | succ j => simp

theorem group_small (n i : Nat) (h : n < 128) : group n (i + 1) = none := by
  unfold group
  have : n / 128 ^ (i + 1) = 0 := by
    apply Nat.div_eq_of_lt
    calc n < 128 := h
      _ = 128 ^ 1 := by simp
      _ ≤ 128 ^ (i + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  simp [this]

theorem groups_eq : ∀ (k n : Nat), n < 128 ^ (k + 1) → (List.range (k + 1)).filterMap (group n) = pbVarint n
  | k, n, h => by
      rw [List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
      have g0 : group n 0 = some (BitVec.ofNat 8 (n % 128 + (if n / 128 == 0 then 0 else 128))) := by
        simp [group]
      rw [g0]
      simp only
      by_cases small : n < 128
      · have none : ∀ i, (group n ∘ Nat.succ) i = none := fun i => group_small n i small
        rw [List.filterMap_eq_nil_iff.mpr (fun a _ => none a), pbVarint_small n small]
        have : n / 128 = 0 := by omega
        simp [this, Nat.mod_eq_of_lt small]
      · cases k with
        | zero => simp at h; omega
        | succ k =>
            have shift : (group n ∘ Nat.succ) = group (n / 128) := funext fun i => group_succ n i (by omega)
            rw [shift, groups_eq k (n / 128) (by
              rw [Nat.pow_succ] at h
              exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)), pbVarint_eq n, if_neg small]
            have : (n / 128 == 0) = false := by simp; omega
            simp [this]

/-- **The builders' varint is the protobuf varint** for every value below `2^70` (ten groups; a
`uint64` needs at most ten). -/
theorem varint_eq (n : Nat) (h : n < 2 ^ 70) : PublicRequest.varint n = pbVarint n := by
  rw [varint_groups]
  exact groups_eq 9 n (by
    have : (2 : Nat) ^ 70 = 128 ^ 10 := by decide
    omega)

/-! ## Pieces: lengths and rendering -/

theorem text_eq (s : String) : text s = utf8 s := rfl

theorem utf8_append (s t : String) : utf8 (s ++ t) = utf8 s ++ utf8 t := by
  simp [utf8, String.toUTF8, String.toByteArray_append]

theorem foldl_add (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons]; rw [ih (a + x), ih (0 + x)]; omega

theorem total_nil : total [] = 0 := rfl

theorem total_cons (p : Piece) (ps : List Piece) : total (p :: ps) = p.width + total ps := by
  simp only [total, List.map_cons, List.foldl_cons]
  rw [foldl_add _ (0 + p.width)]
  omega

theorem total_append (a b : List Piece) : total (a ++ b) = total a + total b := by
  induction a with
  | nil => simp [total_nil]
  | cons p a ih => simp only [List.cons_append, total_cons, ih]; omega

theorem total_field (tag : Nat) (ps : List Piece) :
    total (field tag ps) = 1 + (PublicRequest.varint (total ps)).length + total ps := by
  simp only [field, total_cons, Piece.width, List.length_cons]
  omega

theorem render_append (values : Nat → List Byte) (a b : List Piece) :
    render values (a ++ b) = render values a ++ render values b := by
  induction a with
  | nil => rfl
  | cons p a ih => cases p <;> simp [render, ih]

theorem render_flatten (values : Nat → List Byte) (L : List (List Piece)) :
    render values L.flatten = L.flatMap (render values) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [render_append, ih]

/-- Every slot of the pieces is filled with a value of its width. -/
def FitsAll (values : Nat → List Byte) (ps : List Piece) : Prop := ∀ q ∈ pairsOf ps, (values q.1).length = q.2

theorem render_length (values : Nat → List Byte) : ∀ (ps : List Piece), FitsAll values ps →
    (render values ps).length = total ps
  | [], _ => rfl
  | .bytes v :: rest, h => by
      simp only [render, List.length_append, total_cons, Piece.width]
      rw [render_length values rest h]
  | .slot k w :: rest, h => by
      simp only [render, List.length_append, total_cons, Piece.width]
      rw [render_length values rest (fun q hq => h q (by simp [pairsOf, hq])), h (k, w) (by simp [pairsOf])]

/-- A length-delimited field of the builders (`field tag`, `tag = 8 * f + 2`) renders as the
protobuf field `f`. -/
theorem render_field (values : Nat → List Byte) (tag f : Nat) (htag : tag = 8 * f + 2) (small : tag < 128)
    (ps : List Piece) (fits : FitsAll values ps) (size : total ps < 2 ^ 70) :
    render values (field tag ps) = pbBytesField f (render values ps) := by
  simp only [field, render, pbBytesField, pbKey, render_length values ps fits, varint_eq _ size]
  rw [← htag, pbVarint_small tag small]
  rfl

/-- The request id field (`32 :: varint id`) is the protobuf field 4. -/
theorem id_field (id : Nat) (h : id < 2 ^ 70) :
    (32 : Byte) :: PublicRequest.varint id = pbVarintField 4 id := by
  rw [varint_eq id h]
  rfl

theorem fitsAll_append (values : Nat → List Byte) (a b : List Piece) :
    FitsAll values (a ++ b) ↔ FitsAll values a ∧ FitsAll values b := by
  simp only [FitsAll, TlsMpc.KernelSpecs.RequestFrame.pairsOf_append, List.mem_append]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨h1, h2⟩ q (hq | hq)
    · exact h1 q hq
    · exact h2 q hq

theorem fitsAll_field (values : Nat → List Byte) (tag : Nat) (ps : List Piece) :
    FitsAll values (field tag ps) ↔ FitsAll values ps := Iff.rfl

theorem fitsAll_bytes (values : Nat → List Byte) (v : List Byte) (ps : List Piece) :
    FitsAll values (.bytes v :: ps) ↔ FitsAll values ps := Iff.rfl

theorem fitsAll_nil (values : Nat → List Byte) : FitsAll values [] := fun _ h => by simp [pairsOf] at h

theorem fitsAll_slot (values : Nat → List Byte) (k w : Nat) (ps : List Piece) :
    FitsAll values (.slot k w :: ps) ↔ (values k).length = w ∧ FitsAll values ps := by
  simp only [FitsAll, pairsOf, List.mem_cons, forall_eq_or_imp]

theorem render_bytes (values : Nat → List Byte) (v : List Byte) (ps : List Piece) :
    render values (.bytes v :: ps) = v ++ render values ps := rfl

theorem render_slot (values : Nat → List Byte) (k w : Nat) (ps : List Piece) :
    render values (.slot k w :: ps) = values k ++ render values ps := rfl

theorem render_nil (values : Nat → List Byte) : render values [] = [] := rfl

/-! ## The protobuf skeletons of the three request messages -/

/-- The request `sendMessage` and `devicesMessage` frame, around its path and JSON pieces. -/
def putPieces (path json : List Piece) (id : Nat) : List Piece :=
  Piece.bytes [8, 1] :: field 18 (field 10 [.bytes (text "PUT")] ++ field 18 path ++ field 26 json ++
    [.bytes (32 :: PublicRequest.varint id)] ++ field 42 [.bytes (text "content-type: application/json")] ++
    field 42 [.bytes (text "unidentified-access-key: "), .slot 1 24])

theorem putShape (values : Nat → List Byte) (path json : List Piece) (id : Nat)
    (fpath : FitsAll values path) (fjson : FitsAll values json) (key : (values 1).length = 24)
    (hid : id < 2 ^ 70) (size : total (putPieces path json id) < 2 ^ 70) :
    render values (putPieces path json id) =
      (WebSocketMessage.request {
        verb := "PUT", path := render values path, body := some (render values json),
        headers := [utf8 "content-type: application/json", utf8 "unidentified-access-key: " ++ values 1],
        id := id }).encode := by
  unfold putPieces at size ⊢
  simp only [total_cons, total_append, total_field, Piece.width, List.length_cons, total_nil] at size
  have fk : FitsAll values [.bytes (text "unidentified-access-key: "), .slot 1 24] := by
    rw [fitsAll_bytes, fitsAll_slot]; exact ⟨key, fitsAll_nil values⟩
  have fr : FitsAll values (field 10 [.bytes (text "PUT")] ++ field 18 path ++ field 26 json ++
      [.bytes (32 :: PublicRequest.varint id)] ++ field 42 [.bytes (text "content-type: application/json")] ++
      field 42 [.bytes (text "unidentified-access-key: "), .slot 1 24]) := by
    simp only [fitsAll_append, fitsAll_field, fitsAll_bytes]
    exact ⟨⟨⟨⟨⟨fitsAll_nil values, fpath⟩, fjson⟩, fitsAll_nil values⟩, fitsAll_nil values⟩, fk⟩
  rw [render_bytes, render_field values 18 2 rfl (by decide) _ fr (by
    simp only [total_cons, total_append, total_field, Piece.width, List.length_cons, total_nil]; omega)]
  simp only [render_append]
  rw [render_field values 10 1 rfl (by decide) [.bytes (text "PUT")] (fitsAll_nil values)
      (by decide),
    render_field values 18 2 rfl (by decide) path fpath (by omega),
    render_field values 26 3 rfl (by decide) json fjson (by omega),
    render_field values 42 5 rfl (by decide) [.bytes (text "content-type: application/json")] (fitsAll_nil values)
      (by decide),
    render_field values 42 5 rfl (by decide) _ fk (by decide)]
  simp only [render_bytes, render_slot, render_nil, id_field id hid, text_eq, WebSocketMessage.encode,
    WebSocketRequestMessage.encode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-- The request `fetchMessage` frames, around its path pieces. -/
def getPieces (path : List Piece) (id : Nat) : List Piece :=
  Piece.bytes [8, 1] :: field 18 (field 10 [.bytes (text "GET")] ++ field 18 path ++
    [.bytes (32 :: PublicRequest.varint id)] ++ field 42 [.bytes (text "unidentified-access-key: "), .slot 1 24])

theorem getShape (values : Nat → List Byte) (path : List Piece) (id : Nat)
    (fpath : FitsAll values path) (key : (values 1).length = 24)
    (hid : id < 2 ^ 70) (size : total (getPieces path id) < 2 ^ 70) :
    render values (getPieces path id) =
      (WebSocketMessage.request {
        verb := "GET", path := render values path, body := none,
        headers := [utf8 "unidentified-access-key: " ++ values 1], id := id }).encode := by
  unfold getPieces at size ⊢
  simp only [total_cons, total_append, total_field, Piece.width, List.length_cons, total_nil] at size
  have fk : FitsAll values [.bytes (text "unidentified-access-key: "), .slot 1 24] := by
    rw [fitsAll_bytes, fitsAll_slot]; exact ⟨key, fitsAll_nil values⟩
  have fr : FitsAll values (field 10 [.bytes (text "GET")] ++ field 18 path ++
      [.bytes (32 :: PublicRequest.varint id)] ++ field 42 [.bytes (text "unidentified-access-key: "), .slot 1 24]) := by
    simp only [fitsAll_append, fitsAll_field, fitsAll_bytes]
    exact ⟨⟨⟨fitsAll_nil values, fpath⟩, fitsAll_nil values⟩, fk⟩
  rw [render_bytes, render_field values 18 2 rfl (by decide) _ fr (by
    simp only [total_cons, total_append, total_field, Piece.width, List.length_cons, total_nil]; omega)]
  simp only [render_append]
  rw [render_field values 10 1 rfl (by decide) [.bytes (text "GET")] (fitsAll_nil values)
      (by decide),
    render_field values 18 2 rfl (by decide) path fpath (by omega),
    render_field values 42 5 rfl (by decide) _ fk (by decide)]
  simp only [render_bytes, render_slot, render_nil, id_field id hid, text_eq, WebSocketMessage.encode,
    WebSocketRequestMessage.encode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

theorem sendMessage_pieces (envelope : List Byte) (timestamp id : Nat) (official : Bool) :
    sendMessage envelope timestamp id official =
      putPieces ([.bytes (text "/v1/messages/"), .slot 0 36] ++ (if official then [] else [.bytes (text "?story=false")]))
        (if official then officialJson [envelope] timestamp else [
          .bytes (text "{\"messages\":[{\"content\":\"" ++ RelayEncoding.base64 PublicReceive.fast envelope ++
            text "\",\"destinationDeviceId\":"), .slot 2 3,
          .bytes (text ",\"destinationRegistrationId\":"), .slot 3 10,
          .bytes (text (",\"type\":6}],\"online\":false,\"timestamp\":" ++ toString timestamp ++ ",\"urgent\":true}"))])
        id := rfl

theorem fetchMessage_pieces (id : Nat) :
    fetchMessage id = getPieces [.bytes (text "/v2/keys/"), .slot 0 36, .bytes (text "/*")] id := rfl

/-! ## The JSON bodies -/

/-- The base64 the builders write is RFC 4648 (`SlotBase64.base64_eq`, on the controller's fast
byte operations). -/
theorem base64_fast (raw : List Byte) :
    RelayEncoding.base64 PublicReceive.fast raw = TlsMpc.KernelSpecs.SlotBase64.refBase64 raw := by
  rw [PublicReceive.fast_eq]
  exact TlsMpc.KernelSpecs.SlotBase64.base64_eq raw

/-- Device `i`'s message: the envelope, and the texts in slots `2 + 2i` and `3 + 2i`. -/
def deviceMessage (values : Nat → List Byte) (p : List Byte × Nat) : IncomingMessage :=
  { type := unidentifiedSender, destinationDeviceId := values (2 + 2 * p.2),
    destinationRegistrationId := values (3 + 2 * p.2), content := p.1 }

/-- The (envelope, device id text, registration id text) of every device, in order. -/
def devicesOf (values : Nat → List Byte) (envelopes : List (List Byte)) : List (List Byte × List Byte × List Byte) :=
  envelopes.zipIdx.map (fun p => (p.1, values (2 + 2 * p.2), values (3 + 2 * p.2)))

/-- One device's pieces in `devicesMessage` (key order). -/
def itemSorted : List Byte × Nat → List Piece := fun (envelope, index) =>
  [Piece.bytes (text ((if index == 0 then "" else ",") ++ "{\"content\":\"") ++ RelayEncoding.base64 PublicReceive.fast envelope ++
    text "\",\"destinationDeviceId\":"), .slot (2 + 2 * index) 3,
   .bytes (text ",\"destinationRegistrationId\":"), .slot (3 + 2 * index) 10, .bytes (text ",\"type\":6}")]

/-- One device's pieces in `officialJson` (libsignal order). -/
def itemOfficial : List Byte × Nat → List Piece := fun (envelope, index) =>
  [Piece.bytes (text ((if index == 0 then "" else ",") ++ "{\"type\":6,\"destinationDeviceId\":")), .slot (2 + 2 * index) 3,
   .bytes (text ",\"destinationRegistrationId\":"), .slot (3 + 2 * index) 10,
   .bytes (text ",\"content\":\"" ++ RelayEncoding.base64 PublicReceive.fast envelope ++ text "\"}")]

theorem itemSorted_render (values : Nat → List Byte) (p : List Byte × Nat) :
    render values (itemSorted p) = (if p.2 == 0 then [] else utf8 ",") ++ (deviceMessage values p).json false := by
  obtain ⟨envelope, index⟩ := p
  simp only [itemSorted, render_bytes, render_slot, render_nil, text_eq, utf8_append, base64_fast, deviceMessage,
    IncomingMessage.json, jsonObject, commaSeparated, jsonString, jsonNat, unidentifiedSender, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil, Bool.false_eq_true,
    if_false]
  cases index == 0 <;> rfl

theorem itemOfficial_render (values : Nat → List Byte) (p : List Byte × Nat) :
    render values (itemOfficial p) = (if p.2 == 0 then [] else utf8 ",") ++ (deviceMessage values p).json true := by
  obtain ⟨envelope, index⟩ := p
  simp only [itemOfficial, render_bytes, render_slot, render_nil, text_eq, utf8_append, base64_fast, deviceMessage,
    IncomingMessage.json, jsonObject, commaSeparated, jsonString, jsonNat, unidentifiedSender, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil, if_true]
  cases index == 0 <;> rfl

/-- Items written with a leading `,` from the second on are the items separated by `,`. -/
theorem render_items (values : Nat → List Byte) (P : List Byte × Nat → List Piece) (J : List Byte × Nat → List Byte)
    (hP : ∀ p, render values (P p) = (if p.2 == 0 then [] else utf8 ",") ++ J p) (l : List (List Byte)) :
    render values ((l.zipIdx.map P).flatten) = commaSeparated (l.zipIdx.map J) := by
  rw [render_flatten, List.flatMap_map]
  cases l with
  | nil => rfl
  | cons e rest =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.map_cons, commaSeparated, hP]
      simp only [beq_self_eq_true, if_true, List.nil_append, List.flatMap_map]
      congr 1
      rw [List.flatMap_def, List.flatMap_def]
      congr 1
      apply List.map_congr_left
      intro p hp
      have := (List.mem_zipIdx (x := p.1) (i := p.2) hp).1
      rw [hP]
      have h0 : (p.2 == 0) = false := by simp; omega
      simp [h0]

theorem devices_json (values : Nat → List Byte) (envelopes : List (List Byte)) (timestamp : Nat) (official : Bool) :
    ((sendBody (devicesOf values envelopes) timestamp).messages.map (fun m => m.json official)) =
      envelopes.zipIdx.map (fun p => (deviceMessage values p).json official) := by
  simp only [sendBody, devicesOf, List.map_map]
  rfl

/-- The JSON pieces of `devicesMessage`. -/
def devicesJson (envelopes : List (List Byte)) (timestamp : Nat) (official : Bool) : List Piece :=
  if official then
    [.bytes (text "{\"messages\":[")] ++ (envelopes.zipIdx.map itemOfficial).flatten ++
      [.bytes (text ("],\"online\":false,\"urgent\":true,\"timestamp\":" ++ toString timestamp ++ "}"))]
  else
    [.bytes (text "{\"messages\":[")] ++ (envelopes.zipIdx.map itemSorted).flatten ++
      [.bytes (text ("],\"online\":false,\"timestamp\":" ++ toString timestamp ++ ",\"urgent\":true}"))]

theorem devicesMessage_pieces (envelopes : List (List Byte)) (timestamp id : Nat) (official : Bool) :
    devicesMessage envelopes timestamp id official =
      putPieces ([.bytes (text "/v1/messages/"), .slot 0 36] ++ (if official then [] else [.bytes (text "?story=false")]))
        (devicesJson envelopes timestamp official) id := by
  cases official <;> rfl

theorem officialJson_eq (envelopes : List (List Byte)) (timestamp : Nat) :
    officialJson envelopes timestamp = devicesJson envelopes timestamp true := rfl

/-- **The JSON body of a multi-device send is the `IncomingMessageList`** of the devices' messages
(type 6, the device and registration id slots, the envelope in base64), not online, urgent, with
the timestamp: members in key order, or in libsignal's order for the official profile. -/
theorem devicesJson_render (values : Nat → List Byte) (envelopes : List (List Byte)) (timestamp : Nat) (official : Bool) :
    render values (devicesJson envelopes timestamp official) =
      (sendBody (devicesOf values envelopes) timestamp).json official := by
  cases official
  · simp only [devicesJson, Bool.false_eq_true, if_false, render_append, render_bytes, render_nil,
      render_items values itemSorted _ (itemSorted_render values), IncomingMessageList.json, devices_json]
    simp only [sendBody, jsonObject, jsonArray, jsonBool, jsonNat, jsonString, commaSeparated, List.map_cons,
      List.map_nil, List.flatMap_cons, List.flatMap_nil, text_eq, utf8_append, List.append_assoc, List.append_nil,
      Bool.false_eq_true, if_false]
    rfl
  · simp only [devicesJson, if_true, render_append, render_bytes, render_nil,
      render_items values itemOfficial _ (itemOfficial_render values), IncomingMessageList.json, devices_json]
    simp only [sendBody, jsonObject, jsonArray, jsonBool, jsonNat, jsonString, commaSeparated, List.map_cons,
      List.map_nil, List.flatMap_cons, List.flatMap_nil, text_eq, utf8_append, List.append_assoc, List.append_nil,
      if_true]
    rfl

/-- The JSON pieces of `sendMessage` (one device). -/
def sendJson (envelope : List Byte) (timestamp : Nat) (official : Bool) : List Piece :=
  if official then officialJson [envelope] timestamp else [
    .bytes (text "{\"messages\":[{\"content\":\"" ++ RelayEncoding.base64 PublicReceive.fast envelope ++
      text "\",\"destinationDeviceId\":"), .slot 2 3,
    .bytes (text ",\"destinationRegistrationId\":"), .slot 3 10,
    .bytes (text (",\"type\":6}],\"online\":false,\"timestamp\":" ++ toString timestamp ++ ",\"urgent\":true}"))]

set_option maxRecDepth 20000 in
theorem sendJson_render (values : Nat → List Byte) (envelope : List Byte) (timestamp : Nat) (official : Bool) :
    render values (sendJson envelope timestamp official) =
      (sendBody [(envelope, values 2, values 3)] timestamp).json official := by
  cases official
  · simp only [sendJson, Bool.false_eq_true, if_false, render_bytes, render_slot, render_nil, text_eq, utf8_append,
      base64_fast, sendBody, IncomingMessageList.json, IncomingMessage.json, jsonObject, jsonArray, jsonBool, jsonNat,
      jsonString, commaSeparated, unidentifiedSender, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_assoc, List.append_nil]
    rfl
  · have h := devicesJson_render values [envelope] timestamp true
    simp only [sendJson, if_true, officialJson_eq, h]
    rfl

/-! ## The three request messages are the reference requests -/

theorem sendMessage_eq (envelope : List Byte) (timestamp id : Nat) (official : Bool) :
    sendMessage envelope timestamp id official =
      putPieces ([.bytes (text "/v1/messages/"), .slot 0 36] ++ (if official then [] else [.bytes (text "?story=false")]))
        (sendJson envelope timestamp official) id := by
  cases official <;> rfl

theorem sendPath_render (values : Nat → List Byte) (official : Bool) :
    render values ([.bytes (text "/v1/messages/"), .slot 0 36] ++ (if official then [] else [.bytes (text "?story=false")])) =
      utf8 "/v1/messages/" ++ values 0 ++ (if official then [] else utf8 "?story=false") := by
  cases official <;> simp [render_bytes, render_slot, render_nil, text_eq]

theorem fitsAll_of_pairs (values : Nat → List Byte) (ps : List Piece) (pairs : List (Nat × Nat))
    (h : pairsOf ps = pairs) (fits : ∀ q ∈ pairs, (values q.1).length = q.2) : FitsAll values ps := by
  intro q hq; rw [h] at hq; exact fits q hq

/-- **`sendMessage` renders as the reference send request.** With the four slots filled with values
of their widths (UUID text 36, access key 24, device id text 3, registration id text 10), the message
`build` frames is the protobuf `WebSocketMessage { type: REQUEST, request: { verb: "PUT", path:
"/v1/messages/{uuid}[?story=false]", body: IncomingMessageList JSON, id, headers:
["content-type: application/json", "unidentified-access-key: {key}"] } }`. -/
theorem sendMessage_reference (values : Nat → List Byte) (envelope : List Byte) (timestamp id : Nat) (official : Bool)
    (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (w2 : (values 2).length = 3)
    (w3 : (values 3).length = 10) (hid : id < 2 ^ 70)
    (size : total (sendMessage envelope timestamp id official) < 2 ^ 70) :
    render values (sendMessage envelope timestamp id official) =
      (WebSocketMessage.request (sendRequest (values 0) (values 1) (sendBody [(envelope, values 2, values 3)] timestamp)
        id official)).encode := by
  have fall : FitsAll values (sendMessage envelope timestamp id official) :=
    fitsAll_of_pairs values _ _ (TlsMpc.KernelSpecs.RequestFrame.sendMessage_pairs envelope timestamp id official)
      (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl <;> assumption)
  rw [sendMessage_eq] at fall size ⊢
  have fpath : FitsAll values ([.bytes (text "/v1/messages/"), .slot 0 36] ++
      (if official then [] else [.bytes (text "?story=false")])) :=
    fitsAll_of_pairs values _ [(0, 36)] (by cases official <;> rfl) (by simp [w0])
  have fjson : FitsAll values (sendJson envelope timestamp official) := by
    unfold putPieces at fall
    rw [fitsAll_bytes, fitsAll_field, fitsAll_append, fitsAll_append, fitsAll_append, fitsAll_append,
      fitsAll_append] at fall
    exact fall.1.1.1.2
  rw [putShape values _ _ id fpath fjson w1 hid size, sendPath_render, sendJson_render]
  rfl

/-- **`fetchMessage` renders as the reference keys request** `GET /v2/keys/{uuid}/*` with the access
key header and no body. -/
theorem fetchMessage_reference (values : Nat → List Byte) (id : Nat)
    (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (hid : id < 2 ^ 70)
    (size : total (fetchMessage id) < 2 ^ 70) :
    render values (fetchMessage id) = (WebSocketMessage.request (keysRequest (values 0) (values 1) id)).encode := by
  rw [fetchMessage_pieces] at size ⊢
  have fp : FitsAll values [.bytes (text "/v2/keys/"), .slot 0 36, .bytes (text "/*")] := by
    rw [fitsAll_bytes, fitsAll_slot, fitsAll_bytes]; exact ⟨w0, fitsAll_nil values⟩
  rw [getShape values _ id fp w1 hid size]
  simp only [render_bytes, render_slot, render_nil, text_eq, List.append_nil]
  rfl

/-- **`devicesMessage` renders as the reference send request for several devices**: one
`IncomingMessage` per envelope, in order, device `i`'s id and registration id texts from slots
`2 + 2i` and `3 + 2i`. -/
theorem devicesMessage_reference (values : Nat → List Byte) (envelopes : List (List Byte)) (timestamp id : Nat)
    (official : Bool) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (wd : ∀ i < envelopes.length, (values (2 + 2 * i)).length = 3 ∧ (values (3 + 2 * i)).length = 10)
    (hid : id < 2 ^ 70) (size : total (devicesMessage envelopes timestamp id official) < 2 ^ 70) :
    render values (devicesMessage envelopes timestamp id official) =
      (WebSocketMessage.request (sendRequest (values 0) (values 1) (sendBody (devicesOf values envelopes) timestamp)
        id official)).encode := by
  have fall : FitsAll values (devicesMessage envelopes timestamp id official) := by
    apply fitsAll_of_pairs values _ _ (TlsMpc.KernelSpecs.RequestFrame.devicesMessage_pairs envelopes timestamp id official)
    intro q hq
    simp only [TlsMpc.KernelSpecs.RequestFrame.deviceSlotPairs, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap, List.mem_range] at hq
    rcases hq with (rfl | ⟨i, hi, rfl | rfl⟩) | rfl
    · exact w0
    · exact (wd i hi).1
    · exact (wd i hi).2
    · exact w1
  rw [devicesMessage_pieces] at fall size ⊢
  have fpath : FitsAll values ([.bytes (text "/v1/messages/"), .slot 0 36] ++
      (if official then [] else [.bytes (text "?story=false")])) :=
    fitsAll_of_pairs values _ [(0, 36)] (by cases official <;> rfl) (by simp [w0])
  have fjson : FitsAll values (devicesJson envelopes timestamp official) := by
    unfold putPieces at fall
    rw [fitsAll_bytes, fitsAll_field, fitsAll_append, fitsAll_append, fitsAll_append, fitsAll_append,
      fitsAll_append] at fall
    exact fall.1.1.1.2
  rw [putShape values _ _ id fpath fjson w1 hid size, sendPath_render, devicesJson_render]
  rfl

/-! ## WebSocket client frames (RFC 6455) -/

theorem maskFrom_eq (mask : List Byte) : ∀ (k : Nat) (p : List Byte),
    maskFrom mask k p = (p.zipIdx k).map (fun q => q.1 ^^^ mask.getD (q.2 % 4) 0)
  | _, [] => rfl
  | k, b :: p => by simp [maskFrom, maskFrom_eq mask (k + 1) p, List.zipIdx_cons]

theorem maskFrom_zero (mask p : List Byte) : maskFrom mask 0 p = maskPayload mask p := by
  rw [maskFrom_eq]; rfl

theorem ofNat_mod (n : Nat) : BitVec.ofNat 8 (n % 256) = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

/-- The 8-byte header `build` writes is RFC 6455's for a masked binary frame of 126..65535 bytes. -/
theorem buildHeader_frame (mask R : List Byte) (lo : 126 ≤ R.length) (hi : R.length < 65536) :
    buildHeader R.length mask ++ maskFrom mask 0 R = clientFrame binary mask R := by
  have h1 : ¬ R.length < 126 := by omega
  simp only [buildHeader, clientFrame, lengthField, if_neg h1, if_pos hi, maskFrom_zero, binary, ofNat_mod]
  rfl

/-- The header `assemble` writes (2 + 4 or 4 + 4 bytes) is RFC 6455's for a masked binary frame. -/
theorem assembleHeader_frame (mask R : List Byte) (hi : R.length < 65536) :
    assembleHeader R.length mask ++ maskFrom mask 0 R = clientFrame binary mask R := by
  simp only [assembleHeader, clientFrame, lengthField, if_pos hi, maskFrom_zero, binary, ofNat_mod]
  split <;> rfl

/-- **`clientFrame`** (`Policy/Receive.lean`) is RFC 6455's masked binary frame for a payload under
126 bytes (its only callers, `reply` and `keepalive`, check that). -/
theorem clientFrame_reference (mask payload : List Byte) (h : payload.length < 126) :
    PublicReceive.clientFrame mask payload = clientFrame binary mask payload := by
  simp only [PublicReceive.clientFrame, clientFrame, lengthField, if_pos h, binary, maskPayload, PublicReceive.get]
  rfl

/-- **`ping`** is RFC 6455's masked ping frame (FIN, opcode 9) with the one-byte payload `count`
(mod 256). -/
theorem ping_reference (count : Nat) (mask : List Byte) :
    PublicReceive.ping count mask = clientFrame pingOpcode mask [BitVec.ofNat 8 count] := by
  simp only [PublicReceive.ping, clientFrame, lengthField, pingOpcode, maskPayload, PublicReceive.get]
  rfl

theorem varint_length_le (n : Nat) : (PublicRequest.varint n).length ≤ 10 := by
  rw [varint_groups]
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem varint_small (n : Nat) (h : n < 128) : PublicRequest.varint n = [BitVec.ofNat 8 n] := by
  rw [varint_eq n (by omega), pbVarint_small n h]

/-- **`keepalive`** succeeds for every 4-byte mask and id below `2^70`, and its frame is the masked
binary frame of the reference `GET /v1/keepalive` request with that id. -/
theorem keepalive_reference (id : Nat) (mask : List Byte) (hmask : mask.length = 4) (hid : id < 2 ^ 70) :
    PublicReceive.keepalive id mask =
      .ok (clientFrame binary mask (WebSocketMessage.request (keepaliveRequest id)).encode) := by
  have hv : PublicReceive.varint id = pbVarint id := by rw [receive_varint, varint_eq id hid]
  have hl : (pbVarint id).length ≤ 10 := by rw [← hv, receive_varint]; exact varint_length_le id
  have e1 : List.map (fun b : UInt8 => BitVec.ofNat 8 b.toNat) "GET".toUTF8.data.toList = utf8 "GET" := rfl
  have e2 : List.map (fun b : UInt8 => BitVec.ofNat 8 b.toNat) "/v1/keepalive".toUTF8.data.toList =
    utf8 "/v1/keepalive" := rfl
  have l1 : (utf8 "GET").length = 3 := by decide
  have l2 : (utf8 "/v1/keepalive").length = 13 := by decide
  simp only [PublicReceive.keepalive, hv, e1, e2]
  generalize hreq : ([10, 3] ++ utf8 "GET" ++ [18, 13] ++ utf8 "/v1/keepalive" ++ [32] ++ pbVarint id : List Byte) = req
  have hlen : req.length = 21 + (pbVarint id).length := by
    rw [← hreq]; simp only [List.length_append, List.length_cons, List.length_nil, l1, l2]
  have hv2 : PublicReceive.varint req.length = [BitVec.ofNat 8 req.length] := by
    rw [receive_varint]; exact varint_small _ (by omega)
  have hX : (keepaliveRequest id).encode = req := by
    rw [← hreq]
    simp only [WebSocketRequestMessage.encode, keepaliveRequest, List.flatMap_nil, List.append_nil]
    rfl
  have cond : (decide (([8, 1, 18] ++ [BitVec.ofNat 8 req.length] ++ req : List Byte).length < 126) &&
      mask.length == 4) = true := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen, hmask]
    simp; omega
  rw [hv2, if_pos cond]
  show Except.ok _ = Except.ok _
  rw [clientFrame_reference mask _ (by simp only [List.length_append, List.length_cons, List.length_nil, hlen]; omega)]
  simp only [WebSocketMessage.encode, pbBytesField, hX, pbVarint_small req.length (by omega)]
  rfl

theorem varintAt_go_lt (bytes : List Byte) : ∀ (fuel pos shift acc v j : Nat),
    PublicReceive.varintAt.go bytes fuel pos shift acc = some (v, j) → acc < 2 ^ shift → v < 2 ^ (shift + 7 * fuel)
  | 0, _, _, _, _, _, h, _ => by simp [PublicReceive.varintAt.go] at h
  | fuel + 1, pos, shift, acc, v, j, h, hacc => by
      unfold PublicReceive.varintAt.go at h
      have hc : (PublicReceive.get bytes pos).toNat % 128 ≤ 127 := by omega
      have m : (PublicReceive.get bytes pos).toNat % 128 * 2 ^ shift ≤ 127 * 2 ^ shift := Nat.mul_le_mul_right _ hc
      have p7 : 2 ^ (shift + 7) = 2 ^ shift * 128 := by rw [Nat.pow_add]
      have mono : 2 ^ (shift + 7) ≤ 2 ^ (shift + 7 * (fuel + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      have next : acc + (PublicReceive.get bytes pos).toNat % 128 * 2 ^ shift < 2 ^ (shift + 7) := by omega
      split at h
      · cases h
      · simp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega
        · have := varintAt_go_lt bytes fuel (pos + 1) (shift + 7) _ v j h next
          rw [show shift + 7 + 7 * fuel = shift + 7 * (fuel + 1) by omega] at this
          exact this

/-- Every value `varintAt` reads (at most ten groups) is below `2^70`. -/
theorem varintAt_lt (bytes : List Byte) (index v j : Nat) (h : PublicReceive.varintAt bytes index = some (v, j)) :
    v < 2 ^ 70 :=
  varintAt_go_lt bytes 10 index 0 0 v j h (by decide)

/-- **`reply`**: every frame it returns is RFC 6455's masked binary frame of the protobuf
`WebSocketMessage { type: RESPONSE, response: { id, status: 200, message: "OK" } }` for the id
`scan` read from the server's request (any id below `2^70`; `varintAt` reads only such ids). -/
theorem reply_reference (request mask frame : List Byte) (delivered : Bool)
    (h : PublicReceive.reply request mask = .ok (frame, delivered)) :
    ∃ id, (PublicReceive.scan request true).2.id = some id ∧ mask.length = 4 ∧
      (id < 2 ^ 70 → frame = clientFrame binary mask (WebSocketMessage.response (okResponse id)).encode) := by
  unfold PublicReceive.reply at h
  generalize PublicReceive.scan request true = s at h ⊢
  obtain ⟨need, fields⟩ := s
  cases hid : fields.id with
  | none =>
      simp only [hid] at h
      cases h
  | some id =>
      simp only [hid, bind, Except.bind, pure, Except.pure] at h
      refine ⟨id, rfl, ?_⟩
      split at h
      · split at h
        · rename_i c
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c
          refine ⟨c.2, fun small => ?_⟩
          rw [← h.1, clientFrame_reference mask _ c.1]
          have hv : PublicReceive.varint id = pbVarint id := by rw [receive_varint, varint_eq id small]
          rw [hv] at c ⊢
          generalize hr : ([8] ++ pbVarint id ++ [16, 200, 1, 26, 2, 79, 75] : List Byte) = resp at c ⊢
          have rl : resp.length < 126 := by simp only [List.length_append] at c; omega
          have hX : (okResponse id).encode = resp := by
            rw [← hr]
            simp only [okResponse, WebSocketResponseMessage.encode, pbVarintField, pbBytesField, List.append_assoc]
            rfl
          simp only [WebSocketMessage.encode, pbBytesField, hX, receive_varint, varint_small _ (by omega : resp.length < 128),
            pbVarint_small _ (by omega : resp.length < 128)]
          rfl
        · cases h
      · cases h

theorem maskFrom_twice (mask : List Byte) : ∀ (k : Nat) (p : List Byte), maskFrom mask k (maskFrom mask k p) = p
  | _, [] => rfl
  | k, b :: p => by simp [maskFrom, maskFrom_twice mask (k + 1) p, BitVec.xor_assoc]

theorem maskPayload_twice (mask p : List Byte) : maskPayload mask (maskPayload mask p) = p := by
  rw [← maskFrom_zero, ← maskFrom_zero, maskFrom_twice]

theorem maskPayload_length (mask p : List Byte) : (maskPayload mask p).length = p.length := by
  rw [← maskFrom_zero, TlsMpc.KernelSpecs.RequestFrame.maskFrom_length]

theorem toNat_small (x : Nat) (h : x < 256) : (BitVec.ofNat 8 x).toNat = x := by
  simp [BitVec.toNat_ofNat]; omega

/-- **What the server reads off a client frame.** RFC 6455's reading of `clientFrame op key payload`
(opcode below 16, 4-byte key, payload under 65536 bytes) is one complete frame with FIN set, that
opcode, the MASK bit set, that key, the payload unmasked back, and a minimal-length header. -/
theorem decode_clientFrame (op : Nat) (key payload : List Byte) (hop : op < 16) (hkey : key.length = 4)
    (hlen : payload.length < 65536) :
    decodeFrame (clientFrame op key payload) =
      some { fin := true, opcode := op, masked := true, key := key, payload := payload, minimalLength := true } := by
  have t0 := toNat_small (128 + op) (by omega)
  have m0 : (128 + op) / 16 % 8 = 0 := by omega
  have k4 : (key ++ maskPayload key payload).take 4 = key := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have d4 : (key ++ maskPayload key payload).drop 4 = maskPayload key payload := by
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
  by_cases small : payload.length < 126
  · have t1 := toNat_small (128 + payload.length) (by omega)
    have shape : clientFrame op key payload = BitVec.ofNat 8 (128 + op) :: BitVec.ofNat 8 (128 + payload.length) ::
        (key ++ maskPayload key payload) := by
      simp [clientFrame, lengthField, small]
    rw [shape, decodeFrame]
    simp only [t0, t1, show (128 + payload.length) % 128 = payload.length by omega, if_pos small, List.drop_zero,
      List.length_append, maskPayload_length, k4, d4, hkey, m0, maskPayload_twice,
      show decide (128 ≤ 128 + payload.length) = true by simp, show decide (128 ≤ 128 + op) = true by simp,
      show (128 + op) % 16 = op by omega, if_true]
    rw [if_neg (by omega)]
  · have t1 := toNat_small (128 + 126) (by omega)
    have hi := toNat_small (payload.length / 256) (by omega)
    have lo := toNat_small (payload.length % 256) (by omega)
    have shape : clientFrame op key payload = BitVec.ofNat 8 (128 + op) :: BitVec.ofNat 8 (128 + 126) ::
        (BitVec.ofNat 8 (payload.length / 256) :: BitVec.ofNat 8 (payload.length % 256) :: (key ++ maskPayload key payload)) := by
      simp [clientFrame, lengthField, small, hlen]
    rw [shape, decodeFrame]
    simp only [t0, t1, show (128 + 126) % 128 = 126 by omega, show ¬ (126 < 126) by omega, if_false, if_true,
      List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, bigEndian, List.foldl_cons, List.foldl_nil,
      hi, lo, List.length_append, List.length_cons, maskPayload_length, k4, d4, hkey, m0, maskPayload_twice,
      show decide (128 ≤ 128 + 126) = true by simp, show decide (128 ≤ 128 + op) = true by simp,
      show (128 + op) % 16 = op by omega,
      show (0 * 256 + payload.length / 256) * 256 + payload.length % 256 = payload.length by omega,
      show decide (126 ≤ payload.length) = true by simp; omega]
    rw [if_neg (by omega)]

/-- A frame as a client sends it: FIN, the opcode, MASK with the key, minimal length. -/
def sentFrame (op : Nat) (key payload : List Byte) : Frame :=
  { fin := true, opcode := op, masked := true, key := key, payload := payload, minimalLength := true }

/-- **The ping frame, read by RFC 6455**: FIN, opcode 9, masked, minimal length, payload the count. -/
theorem ping_decode (count : Nat) (mask : List Byte) (hmask : mask.length = 4) :
    decodeFrame (PublicReceive.ping count mask) = some (sentFrame pingOpcode mask [BitVec.ofNat 8 count]) := by
  rw [ping_reference]
  exact decode_clientFrame pingOpcode mask _ (by decide) hmask (by simp)

/-- **The keepalive frame, read by RFC 6455**: FIN, binary, masked, minimal, the keepalive request. -/
theorem keepalive_decode (id : Nat) (mask frame : List Byte) (hid : id < 2 ^ 70)
    (h : PublicReceive.keepalive id mask = .ok frame) :
    decodeFrame frame = some (sentFrame binary mask (WebSocketMessage.request (keepaliveRequest id)).encode) := by
  have hmask : mask.length = 4 := by
    unfold PublicReceive.keepalive at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i c; simp only [Bool.and_eq_true, beq_iff_eq] at c; exact c.2
    · cases h
  rw [keepalive_reference id mask hmask hid] at h
  cases h
  apply decode_clientFrame binary mask _ (by decide) hmask
  have hl : (pbVarint id).length ≤ 10 := by rw [← varint_eq id hid]; exact varint_length_le id
  have l1 : (utf8 "GET").length = 3 := by decide
  have l2 : (utf8 "/v1/keepalive").length = 13 := by decide
  have hX : (keepaliveRequest id).encode.length = 21 + (pbVarint id).length := by
    simp only [WebSocketRequestMessage.encode, keepaliveRequest, pbBytesField, pbVarintField, pbKey,
      List.flatMap_nil, List.length_append, l1, l2, List.length_nil]
    simp only [pbVarint_small _ (by decide : 8 * 1 + 2 < 128), pbVarint_small _ (by decide : 8 * 2 + 2 < 128),
      pbVarint_small _ (by decide : 8 * 4 + 0 < 128), pbVarint_small _ (by decide : 3 < 128),
      pbVarint_small _ (by decide : 13 < 128), List.length_singleton]
    omega
  simp only [WebSocketMessage.encode, pbBytesField, pbVarintField, List.length_append, hX,
    pbVarint_small (21 + (pbVarint id).length) (by omega)]
  simp only [pbKey, pbVarint_small _ (by decide : 8 * 1 + 0 < 128), pbVarint_small _ (by decide : 1 < 128),
    pbVarint_small _ (by decide : 8 * 2 + 2 < 128), List.length_singleton]
  omega

/-- **The reply frame, read by RFC 6455**: FIN, binary, masked, minimal, the `200 OK` response
echoing the server's request id. -/
theorem reply_decode (request mask frame : List Byte) (delivered : Bool)
    (h : PublicReceive.reply request mask = .ok (frame, delivered)) :
    ∃ id, (PublicReceive.scan request true).2.id = some id ∧
      (id < 2 ^ 70 → decodeFrame frame =
        some (sentFrame binary mask (WebSocketMessage.response (okResponse id)).encode)) := by
  obtain ⟨id, hid, hmask, hframe⟩ := reply_reference request mask frame delivered h
  refine ⟨id, hid, fun small => ?_⟩
  rw [hframe small]
  apply decode_clientFrame binary mask _ (by decide) hmask
  have hl : (pbVarint id).length ≤ 10 := by rw [← varint_eq id small]; exact varint_length_le id
  have l1 : (utf8 "OK").length = 2 := by decide
  have hX : (okResponse id).encode.length = 8 + (pbVarint id).length := by
    simp only [WebSocketResponseMessage.encode, okResponse, pbBytesField, pbVarintField, pbKey,
      List.length_append, l1]
    simp only [pbVarint_small _ (by decide : 8 * 1 + 0 < 128), pbVarint_small _ (by decide : 8 * 2 + 0 < 128),
      pbVarint_small _ (by decide : 8 * 3 + 2 < 128), pbVarint_small _ (by decide : 2 < 128),
      List.length_singleton]
    have : (pbVarint 200).length = 2 := by decide
    omega
  simp only [WebSocketMessage.encode, pbBytesField, pbVarintField, List.length_append, hX,
    pbVarint_small (8 + (pbVarint id).length) (by omega)]
  simp only [pbKey, pbVarint_small _ (by decide : 8 * 1 + 0 < 128), pbVarint_small _ (by decide : 2 < 128),
    pbVarint_small _ (by decide : 8 * 3 + 2 < 128), List.length_singleton]
  omega

/-! ## The frames the builders return, filled, are the reference frames -/

theorem sendMessage_fits (values : Nat → List Byte) (envelope : List Byte) (timestamp id : Nat) (official : Bool)
    (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (w2 : (values 2).length = 3)
    (w3 : (values 3).length = 10) : FitsAll values (sendMessage envelope timestamp id official) :=
  fitsAll_of_pairs values _ _ (TlsMpc.KernelSpecs.RequestFrame.sendMessage_pairs envelope timestamp id official)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> assumption)

theorem fetchMessage_fits (values : Nat → List Byte) (id : Nat)
    (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) : FitsAll values (fetchMessage id) :=
  fitsAll_of_pairs values _ _ (TlsMpc.KernelSpecs.RequestFrame.fetchMessage_pairs id)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> assumption)

theorem devicesMessage_fits (values : Nat → List Byte) (envelopes : List (List Byte)) (timestamp id : Nat)
    (official : Bool) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (wd : ∀ i < envelopes.length, (values (2 + 2 * i)).length = 3 ∧ (values (3 + 2 * i)).length = 10) :
    FitsAll values (devicesMessage envelopes timestamp id official) := by
  apply fitsAll_of_pairs values _ _ (TlsMpc.KernelSpecs.RequestFrame.devicesMessage_pairs envelopes timestamp id official)
  intro q hq
  simp only [TlsMpc.KernelSpecs.RequestFrame.deviceSlotPairs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap, List.mem_range] at hq
  rcases hq with (rfl | ⟨i, hi, rfl | rfl⟩) | rfl
  · exact w0
  · exact (wd i hi).1
  · exact (wd i hi).2
  · exact w1

/-- **`build`, filled: the WebSocket frame of the reference send request.** For a frame `build`
returned and any slot values of the slots' widths, the frame with the values in place (what
`signal-request-ctr` encrypts, `RequestFrame.insertSlots_offsets`) is RFC 6455's masked binary
frame of `WebSocketMessage { REQUEST, PUT /v1/messages/{uuid} … }`; read back by RFC 6455 it is
one FIN frame, opcode 2, masked with the frame's key, minimal length, carrying exactly that
message. -/
theorem build_reference (envelope : List Byte) (timestamp id : Nat) (mask frame : List Byte) (official : Bool)
    (offsets : List Nat) (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (w2 : (values 2).length = 3) (w3 : (values 3).length = 10) (hid : id < 2 ^ 70) :
    let msg := sendMessage envelope timestamp id official
    let request := WebSocketMessage.request
      (sendRequest (values 0) (values 1) (sendBody [(envelope, values 2, values 3)] timestamp) id official)
    buildHeader (total msg) mask ++ maskFrom mask 0 (render values msg) = clientFrame binary mask request.encode ∧
      decodeFrame (clientFrame binary mask request.encode) =
        some (sentFrame binary mask request.encode) := by
  intro msg request
  obtain ⟨lo, hi, hm, _, _, _⟩ := TlsMpc.KernelSpecs.RequestFrame.build_ok envelope timestamp id mask frame official
    offsets built
  have lo' : 126 ≤ total msg := lo
  have hi' : total msg < 65536 := hi
  have len := render_length values msg (sendMessage_fits values envelope timestamp id official w0 w1 w2 w3)
  have R := sendMessage_reference values envelope timestamp id official w0 w1 w2 w3 hid (by omega)
  have elen : request.encode.length < 65536 := by
    show (WebSocketMessage.request _).encode.length < 65536
    rw [← R, len]; exact hi
  refine ⟨?_, decode_clientFrame binary mask _ (by decide) hm elen⟩
  rw [← len, buildHeader_frame mask _ (by omega) (by omega)]
  exact congrArg _ R

/-- **`buildFetch`, filled: the WebSocket frame of the reference keys request.** -/
theorem buildFetch_reference (id : Nat) (mask frame : List Byte) (payloadAt : Nat) (offsets : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (hid : id < 2 ^ 70) :
    let request := WebSocketMessage.request (keysRequest (values 0) (values 1) id)
    assembleHeader (total (fetchMessage id)) mask ++ maskFrom mask 0 (render values (fetchMessage id)) =
        clientFrame binary mask request.encode ∧
      decodeFrame (clientFrame binary mask request.encode) =
        some (sentFrame binary mask request.encode) := by
  intro request
  rw [TlsMpc.KernelSpecs.RequestFrame.buildFetch_eq] at built
  obtain ⟨_, hi, hm, _, _, _⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask frame 2 payloadAt offsets built
  have len := render_length values _ (fetchMessage_fits values id w0 w1)
  have R := fetchMessage_reference values id w0 w1 hid (by omega)
  have elen : request.encode.length < 65536 := by
    show (WebSocketMessage.request _).encode.length < 65536
    rw [← R, len]; exact hi
  refine ⟨?_, decode_clientFrame binary mask _ (by decide) hm elen⟩
  rw [← len, assembleHeader_frame mask _ (by omega)]
  exact congrArg _ R

/-- **`buildDevices`, filled: the WebSocket frame of the reference multi-device send request.** -/
theorem buildDevices_reference (envelopes : List (List Byte)) (timestamp id : Nat) (mask frame : List Byte)
    (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (wd : ∀ i < envelopes.length, (values (2 + 2 * i)).length = 3 ∧ (values (3 + 2 * i)).length = 10)
    (hid : id < 2 ^ 70) :
    let msg := devicesMessage envelopes timestamp id official
    let request := WebSocketMessage.request
      (sendRequest (values 0) (values 1) (sendBody (devicesOf values envelopes) timestamp) id official)
    assembleHeader (total msg) mask ++ maskFrom mask 0 (render values msg) = clientFrame binary mask request.encode ∧
      decodeFrame (clientFrame binary mask request.encode) =
        some (sentFrame binary mask request.encode) := by
  intro msg request
  rw [TlsMpc.KernelSpecs.RequestFrame.buildDevices_eq] at built
  by_cases empty : envelopes.isEmpty = true
  · rw [if_pos empty] at built; cases built
  rw [if_neg empty] at built
  obtain ⟨_, hi, hm, _, _, _⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask frame _ payloadAt offsets built
  have hi' : total msg < 65536 := hi
  have len := render_length values msg (devicesMessage_fits values envelopes timestamp id official w0 w1 wd)
  have R := devicesMessage_reference values envelopes timestamp id official w0 w1 wd hid (by omega)
  have elen : request.encode.length < 65536 := by
    show (WebSocketMessage.request _).encode.length < 65536
    rw [← R, len]; exact hi
  refine ⟨?_, decode_clientFrame binary mask _ (by decide) hm elen⟩
  rw [← len, assembleHeader_frame mask _ (by omega)]
  exact congrArg _ R

/-! ## Nothing but the slots depends on the contact

The builders take no contact input at all: their frame (zero bytes in the slots) is a function of
the envelopes, timestamp, request id, WebSocket mask and profile. The theorems below say that the
frame actually encrypted (the slots filled with the contact's values) agrees with that frame at
every byte outside the slot ranges `[offset k, offset k + width k)`, whose offsets `build` /
`assemble` return; so two contacts' frames differ only inside the slots. -/

theorem body_length (mask : List Byte) : ∀ (pos : Nat) (msg : List Piece), (body mask pos msg).length = total msg
  | _, [] => rfl
  | pos, .bytes v :: rest => by
      simp [TlsMpc.KernelSpecs.RequestFrame.body, body_length mask _ rest, total_cons, Piece.width,
        TlsMpc.KernelSpecs.RequestFrame.maskFrom_length]
  | pos, .slot k w :: rest => by
      simp [TlsMpc.KernelSpecs.RequestFrame.body, body_length mask _ rest, total_cons, Piece.width]

theorem filled_outside (header mask : List Byte) (msg : List Piece) (values : Nat → List Byte) (O : Array Nat)
    (ks : List Nat) (fits : FitsAll values msg)
    (same : ∀ k, k ∈ ks ↔ k ∈ TlsMpc.KernelSpecs.RequestFrame.indicesOf msg)
    (nodup : (TlsMpc.KernelSpecs.RequestFrame.indicesOf msg).Nodup)
    (small : ∀ k ∈ TlsMpc.KernelSpecs.RequestFrame.indicesOf msg, k < O.size) (i : Nat)
    (outside : ∀ k ∈ ks,
      ¬ ((TlsMpc.KernelSpecs.RequestFrame.offsetsFold O header.length msg).toList.getD k 0 ≤ i ∧
        i < (TlsMpc.KernelSpecs.RequestFrame.offsetsFold O header.length msg).toList.getD k 0 + (values k).length)) :
    (header ++ maskFrom mask 0 (render values msg))[i]? = (header ++ body mask 0 msg)[i]? := by
  rw [← TlsMpc.KernelSpecs.RequestFrame.insertSlots_offsets header mask msg values O ks
    (TlsMpc.KernelSpecs.RequestFrame.fits_of_pairs values _ msg fits) same nodup small]
  by_cases hi : i < (header ++ body mask 0 msg).length
  · have hl : i < (TlsMpc.KernelSpecs.insertSlots ByteAuth.concrete 0 (header ++ body mask 0 msg) mask header.length
        (ks.map (fun k => ((TlsMpc.KernelSpecs.RequestFrame.offsetsFold O header.length msg).toList.getD k 0,
          values k)))).length := by
      simpa [TlsMpc.KernelSpecs.insertSlots] using hi
    rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hi,
      TlsMpc.KernelSpecs.insertSlots_outside ByteAuth.concrete 0 _ mask _ _ i hi (by
        intro slot hs
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
        exact outside k hk)]
  · rw [List.getElem?_eq_none (by simpa [TlsMpc.KernelSpecs.insertSlots] using hi),
      List.getElem?_eq_none (by omega)]

/-- **`build`: outside its four slots, the frame a contact's values are encrypted in is the public
frame `build` returned**, byte for byte (and it has the same length). -/
theorem build_public (envelope : List Byte) (timestamp id : Nat) (mask frame : List Byte) (official : Bool)
    (offsets : List Nat) (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (w2 : (values 2).length = 3) (w3 : (values 3).length = 10) (hid : id < 2 ^ 70) :
    let plain := clientFrame binary mask (WebSocketMessage.request
      (sendRequest (values 0) (values 1) (sendBody [(envelope, values 2, values 3)] timestamp) id official)).encode
    plain.length = frame.length ∧
      ∀ i, (∀ k ∈ [0, 1, 2, 3], ¬ (offsets.getD k 0 ≤ i ∧ i < offsets.getD k 0 + (values k).length)) →
        plain[i]? = frame[i]? := by
  intro plain
  have ref := (build_reference envelope timestamp id mask frame official offsets built values w0 w1 w2 w3 hid).1
  obtain ⟨_, _, hm, h8, hf, ho⟩ := TlsMpc.KernelSpecs.RequestFrame.build_ok envelope timestamp id mask frame official
    offsets built
  have fits := sendMessage_fits values envelope timestamp id official w0 w1 w2 w3
  have len := render_length values _ fits
  have ix : TlsMpc.KernelSpecs.RequestFrame.indicesOf (sendMessage envelope timestamp id official) = [0, 2, 3, 1] := by
    rw [TlsMpc.KernelSpecs.RequestFrame.indicesOf_pairs, TlsMpc.KernelSpecs.RequestFrame.sendMessage_pairs]; rfl
  have outsideEq := fun i outside => filled_outside (buildHeader (total (sendMessage envelope timestamp id official)) mask)
    mask (sendMessage envelope timestamp id official) values #[0, 0, 0, 0] [0, 1, 2, 3] fits
    (by intro k; rw [ix]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    (by rw [ix]; decide) (by rw [ix]; intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
                             show k < 4; omega) i
    (by rw [h8, ← ho]; exact outside)
  refine ⟨?_, fun i outside => ?_⟩
  · show (clientFrame binary mask _).length = frame.length
    rw [← ref, hf]
    simp only [List.length_append, TlsMpc.KernelSpecs.RequestFrame.maskFrom_length, len, body_length]
  · show (clientFrame binary mask _)[i]? = frame[i]?
    rw [← ref, hf]
    exact outsideEq i outside

/-- **`buildFetch`: outside its two slots, the encrypted frame is the public frame.** -/
theorem buildFetch_public (id : Nat) (mask frame : List Byte) (payloadAt : Nat) (offsets : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (hid : id < 2 ^ 70) :
    let plain := clientFrame binary mask (WebSocketMessage.request (keysRequest (values 0) (values 1) id)).encode
    plain.length = frame.length ∧
      ∀ i, (∀ k ∈ [0, 1], ¬ (offsets.getD k 0 ≤ i ∧ i < offsets.getD k 0 + (values k).length)) →
        plain[i]? = frame[i]? := by
  intro plain
  have ref := (buildFetch_reference id mask frame payloadAt offsets built values w0 w1 hid).1
  rw [TlsMpc.KernelSpecs.RequestFrame.buildFetch_eq] at built
  obtain ⟨_, _, _, hp, hf, ho⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask frame 2 payloadAt offsets built
  have fits := fetchMessage_fits values id w0 w1
  have len := render_length values _ fits
  have ix : TlsMpc.KernelSpecs.RequestFrame.indicesOf (fetchMessage id) = [0, 1] := by
    rw [TlsMpc.KernelSpecs.RequestFrame.indicesOf_pairs, TlsMpc.KernelSpecs.RequestFrame.fetchMessage_pairs]; rfl
  refine ⟨?_, fun i outside => ?_⟩
  · show (clientFrame binary mask _).length = frame.length
    rw [← ref, hf]
    simp only [List.length_append, TlsMpc.KernelSpecs.RequestFrame.maskFrom_length, len, body_length]
  · show (clientFrame binary mask _)[i]? = frame[i]?
    rw [← ref, hf]
    exact filled_outside (assembleHeader (total (fetchMessage id)) mask) mask (fetchMessage id) values
      (Array.replicate 2 0) [0, 1] fits
      (by intro k; rw [ix])
      (by rw [ix]; decide)
      (by rw [ix]; intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          simp only [Array.size_replicate]; omega) i
      (by rw [← hp, ← ho]; exact outside)

/-- **`buildDevices`: outside its `2 + 2n` slots, the encrypted frame is the public frame.** -/
theorem buildDevices_public (envelopes : List (List Byte)) (timestamp id : Nat) (mask frame : List Byte)
    (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (values : Nat → List Byte) (w0 : (values 0).length = 36) (w1 : (values 1).length = 24)
    (wd : ∀ i < envelopes.length, (values (2 + 2 * i)).length = 3 ∧ (values (3 + 2 * i)).length = 10)
    (hid : id < 2 ^ 70) :
    let plain := clientFrame binary mask (WebSocketMessage.request
      (sendRequest (values 0) (values 1) (sendBody (devicesOf values envelopes) timestamp) id official)).encode
    plain.length = frame.length ∧
      ∀ i, (∀ k < 2 + 2 * envelopes.length, ¬ (offsets.getD k 0 ≤ i ∧ i < offsets.getD k 0 + (values k).length)) →
        plain[i]? = frame[i]? := by
  intro plain
  have ref := (buildDevices_reference envelopes timestamp id mask frame official payloadAt offsets built values
    w0 w1 wd hid).1
  rw [TlsMpc.KernelSpecs.RequestFrame.buildDevices_eq] at built
  by_cases empty : envelopes.isEmpty = true
  · rw [if_pos empty] at built; cases built
  rw [if_neg empty] at built
  obtain ⟨_, _, _, hp, hf, ho⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask frame _ payloadAt offsets built
  have fits := devicesMessage_fits values envelopes timestamp id official w0 w1 wd
  have len := render_length values _ fits
  have pairsMsg := TlsMpc.KernelSpecs.RequestFrame.devicesMessage_pairs envelopes timestamp id official
  have ix : TlsMpc.KernelSpecs.RequestFrame.indicesOf (devicesMessage envelopes timestamp id official) =
      [0] ++ TlsMpc.KernelSpecs.RequestFrame.deviceIndices envelopes.length ++ [1] := by
    rw [TlsMpc.KernelSpecs.RequestFrame.indicesOf_pairs, pairsMsg]
    simp [TlsMpc.KernelSpecs.RequestFrame.deviceSlotPairs_fst]
  refine ⟨?_, fun i outside => ?_⟩
  · show (clientFrame binary mask _).length = frame.length
    rw [← ref, hf]
    simp only [List.length_append, TlsMpc.KernelSpecs.RequestFrame.maskFrom_length, len, body_length]
  · show (clientFrame binary mask _)[i]? = frame[i]?
    rw [← ref, hf]
    exact filled_outside (assembleHeader (total (devicesMessage envelopes timestamp id official)) mask) mask
      (devicesMessage envelopes timestamp id official) values
      (Array.replicate (2 + 2 * envelopes.length) 0) (List.range (2 + 2 * envelopes.length)) fits
      (by
        intro k
        rw [ix, List.mem_range]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          TlsMpc.KernelSpecs.RequestFrame.mem_deviceIndices]
        omega)
      (by
        rw [ix]
        have nd : (TlsMpc.KernelSpecs.RequestFrame.deviceIndices envelopes.length).Nodup := by
          rw [TlsMpc.KernelSpecs.RequestFrame.deviceIndices_eq, List.nodup_iff_pairwise_ne, List.pairwise_map]
          exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun h e => h (by omega))
        rw [List.nodup_append, List.nodup_append]
        refine ⟨⟨by simp, nd, ?_⟩, by simp, ?_⟩
        · intro a ha b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rw [TlsMpc.KernelSpecs.RequestFrame.mem_deviceIndices] at hb
          omega
        · intro a ha b hb
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha hb
          rw [TlsMpc.KernelSpecs.RequestFrame.mem_deviceIndices] at ha
          omega)
      (by
        rw [ix]; intro k hk
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          TlsMpc.KernelSpecs.RequestFrame.mem_deviceIndices] at hk
        simp only [Array.size_replicate]; omega) i
      (by rw [← hp, ← ho]; intro k hk; exact outside k (List.mem_range.mp hk))

/-- **Two contacts, the same public inputs: frames equal outside the slots.** For the same
envelope, timestamp, id, mask and profile, the frames encrypted for two contacts (any slot values
of the right widths) agree at every byte outside both contacts' slot ranges, which lie at the same
offsets. -/
theorem build_two_contacts (envelope : List Byte) (timestamp id : Nat) (mask frame : List Byte) (official : Bool)
    (offsets : List Nat) (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (values values' : Nat → List Byte)
    (w0 : (values 0).length = 36) (w1 : (values 1).length = 24) (w2 : (values 2).length = 3)
    (w3 : (values 3).length = 10)
    (w0' : (values' 0).length = 36) (w1' : (values' 1).length = 24) (w2' : (values' 2).length = 3)
    (w3' : (values' 3).length = 10) (hid : id < 2 ^ 70) (i : Nat)
    (outside : ∀ k ∈ [0, 1, 2, 3], ¬ (offsets.getD k 0 ≤ i ∧ i < offsets.getD k 0 + (values k).length)) :
    (clientFrame binary mask (WebSocketMessage.request
        (sendRequest (values 0) (values 1) (sendBody [(envelope, values 2, values 3)] timestamp) id official)).encode)[i]? =
      (clientFrame binary mask (WebSocketMessage.request
        (sendRequest (values' 0) (values' 1) (sendBody [(envelope, values' 2, values' 3)] timestamp) id official)).encode)[i]? := by
  have widths : ∀ k ∈ [0, 1, 2, 3], (values k).length = (values' k).length := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> omega
  rw [(build_public envelope timestamp id mask frame official offsets built values w0 w1 w2 w3 hid).2 i outside,
    (build_public envelope timestamp id mask frame official offsets built values' w0' w1' w2' w3' hid).2 i
      (fun k hk => by rw [← widths k hk]; exact outside k hk)]

/-! ## The layout depends only on lengths

Where the slots are and how long the frame is depends only on the envelopes' lengths (and so the
device count), the number of digits of the timestamp, the length of the request id's varint and the
profile: not on any byte of the envelopes, nor on the mask, nor on anything about the contact. -/

/-- What of a piece list the layout depends on: each piece's width, and the slot index. -/
def shape (ps : List Piece) : List (Option Nat × Nat) :=
  ps.map (fun p => match p with | .bytes v => (none, v.length) | .slot k w => (some k, w))

theorem shape_append (a b : List Piece) : shape (a ++ b) = shape a ++ shape b := by simp [shape]

def widthSum : List (Option Nat × Nat) → Nat
  | [] => 0
  | x :: xs => x.2 + widthSum xs

theorem total_of_shape (ps : List Piece) : total ps = widthSum (shape ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [total_cons, ih]
      cases p <;> rfl

theorem shape_field (tag : Nat) (ps : List Piece) :
    shape (field tag ps) = (none, 1 + (PublicRequest.varint (widthSum (shape ps))).length) :: shape ps := by
  rw [← total_of_shape]
  simp only [field, shape, List.map_cons, List.length_cons, Nat.add_comm]

theorem shape_bytes (v : List Byte) (ps : List Piece) : shape (.bytes v :: ps) = (none, v.length) :: shape ps := rfl
theorem shape_slot (k w : Nat) (ps : List Piece) : shape (.slot k w :: ps) = (some k, w) :: shape ps := rfl
theorem shape_nil : shape [] = [] := rfl

theorem offsetsFold_of_shape : ∀ (O : Array Nat) (start : Nat) (a b : List Piece), shape a = shape b →
    TlsMpc.KernelSpecs.RequestFrame.offsetsFold O start a = TlsMpc.KernelSpecs.RequestFrame.offsetsFold O start b
  | _, _, [], [], _ => rfl
  | _, _, [], _ :: _, h => by simp [shape] at h
  | _, _, _ :: _, [], h => by simp [shape] at h
  | O, start, p :: a, q :: b, h => by
      simp only [shape, List.map_cons, List.cons.injEq] at h
      obtain ⟨hpq, hab⟩ := h
      cases p <;> cases q <;> simp at hpq
      · simp only [TlsMpc.KernelSpecs.RequestFrame.offsetsFold]
        rw [hpq]; exact offsetsFold_of_shape O _ a b hab
      · obtain ⟨rfl, rfl⟩ := hpq
        simp only [TlsMpc.KernelSpecs.RequestFrame.offsetsFold]
        exact offsetsFold_of_shape _ _ a b hab

theorem base64_fast_length (e : List Byte) :
    (RelayEncoding.base64 PublicReceive.fast e).length = 4 * ((e.length + 2) / 3) :=
  TlsMpc.KernelSpecs.RequestFrame.base64_length _ _

theorem utf8_length_append (s t : String) : (utf8 (s ++ t)).length = (utf8 s).length + (utf8 t).length := by
  rw [utf8_append, List.length_append]

theorem shape_sendJson (e e' : List Byte) (t t' : Nat) (official : Bool) (he : e.length = e'.length)
    (ht : (utf8 (toString t)).length = (utf8 (toString t')).length) :
    shape (sendJson e t official) = shape (sendJson e' t' official) := by
  have ht' : (utf8 t.repr).length = (utf8 t'.repr).length := ht
  cases official
  · simp [sendJson, shape, text_eq, utf8_length_append, ht', base64_fast_length, he]
  · simp [sendJson, officialJson_eq, devicesJson, shape, text_eq, utf8_length_append, ht', he,
      itemOfficial, base64_fast_length]

/-- **`build`'s layout depends only on lengths**: two calls with envelopes of the same length,
timestamps with the same number of digits, request ids with varints of the same length and the
same profile (any envelope bytes, any masks) return frames of the same length with the slots at the
same offsets. -/
theorem build_layout (e e' : List Byte) (t t' id id' : Nat) (mask mask' frame frame' : List Byte) (official : Bool)
    (offsets offsets' : List Nat)
    (built : build e t id mask official = .ok (frame, offsets))
    (built' : build e' t' id' mask' official = .ok (frame', offsets'))
    (he : e.length = e'.length) (ht : (utf8 (toString t)).length = (utf8 (toString t')).length)
    (hid : (PublicRequest.varint id).length = (PublicRequest.varint id').length) :
    frame.length = frame'.length ∧ offsets = offsets' := by
  obtain ⟨_, _, hm, _, hf, ho⟩ := TlsMpc.KernelSpecs.RequestFrame.build_ok e t id mask frame official offsets built
  obtain ⟨_, _, hm', _, hf', ho'⟩ := TlsMpc.KernelSpecs.RequestFrame.build_ok e' t' id' mask' frame' official offsets'
    built'
  have hs : shape (sendMessage e t id official) = shape (sendMessage e' t' id' official) := by
    rw [sendMessage_eq, sendMessage_eq]
    simp only [putPieces, shape_bytes, shape_slot, shape_nil, shape_field, shape_append,
      shape_sendJson e e' t t' official he ht, List.length_cons, hid]
  have tot : total (sendMessage e t id official) = total (sendMessage e' t' id' official) := by
    rw [total_of_shape, total_of_shape, hs]
  refine ⟨?_, ?_⟩
  · rw [hf, hf']
    simp [TlsMpc.KernelSpecs.RequestFrame.buildHeader, body_length, hm, hm', tot]
  · rw [ho, ho', offsetsFold_of_shape _ _ _ _ hs]

theorem shape_items (P : List Byte × Nat → List Piece)
    (hP : ∀ e e' i, e.length = e'.length → shape (P (e, i)) = shape (P (e', i))) :
    ∀ (l l' : List (List Byte)) (k : Nat), l.map List.length = l'.map List.length →
      shape ((l.zipIdx k).map P).flatten = shape ((l'.zipIdx k).map P).flatten
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | e :: l, e' :: l', k, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons, shape_append, hP e e' k h.1,
        shape_items P hP l l' (k + 1) h.2]

theorem shape_devicesJson (l l' : List (List Byte)) (t t' : Nat) (official : Bool)
    (hl : l.map List.length = l'.map List.length)
    (ht : (utf8 (toString t)).length = (utf8 (toString t')).length) :
    shape (devicesJson l t official) = shape (devicesJson l' t' official) := by
  have ht' : (utf8 t.repr).length = (utf8 t'.repr).length := ht
  cases official
  · simp only [devicesJson, Bool.false_eq_true, if_false, shape_append]
    rw [shape_items itemSorted (fun e e' i he => by
      simp [itemSorted, shape, text_eq, utf8_length_append, base64_fast_length, he]) l l' 0 hl]
    simp [shape, text_eq, utf8_length_append, ht']
  · simp only [devicesJson, if_true, shape_append]
    rw [shape_items itemOfficial (fun e e' i he => by
      simp [itemOfficial, shape, text_eq, utf8_length_append, base64_fast_length, he]) l l' 0 hl]
    simp [shape, text_eq, utf8_length_append, ht']

/-- **`buildDevices`' layout depends only on lengths**: the same number of envelopes with the same
lengths, timestamps with the same number of digits, ids with varints of the same length and the
same profile give frames of the same length, the same payload start and the same slot offsets. -/
theorem buildDevices_layout (l l' : List (List Byte)) (t t' id id' : Nat) (mask mask' frame frame' : List Byte)
    (official : Bool) (payloadAt payloadAt' : Nat) (offsets offsets' : List Nat)
    (built : buildDevices l t id mask official = .ok (frame, payloadAt, offsets))
    (built' : buildDevices l' t' id' mask' official = .ok (frame', payloadAt', offsets'))
    (hl : l.map List.length = l'.map List.length) (ht : (utf8 (toString t)).length = (utf8 (toString t')).length)
    (hid : (PublicRequest.varint id).length = (PublicRequest.varint id').length) :
    frame.length = frame'.length ∧ payloadAt = payloadAt' ∧ offsets = offsets' := by
  have count : l.length = l'.length := by rw [← List.length_map (f := List.length), hl, List.length_map]
  rw [TlsMpc.KernelSpecs.RequestFrame.buildDevices_eq] at built built'
  by_cases empty : l.isEmpty = true
  · rw [if_pos empty] at built; cases built
  have empty' : ¬ l'.isEmpty = true := by
    intro h; apply empty; rw [List.isEmpty_iff_length_eq_zero] at h ⊢; omega
  rw [if_neg empty] at built
  rw [if_neg empty'] at built'
  obtain ⟨_, _, hm, hp, hf, ho⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask frame _ payloadAt offsets built
  obtain ⟨_, _, hm', hp', hf', ho'⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask' frame' _ payloadAt'
    offsets' built'
  have hs : shape (devicesMessage l t id official) = shape (devicesMessage l' t' id' official) := by
    rw [devicesMessage_pieces, devicesMessage_pieces]
    simp only [putPieces, shape_bytes, shape_slot, shape_nil, shape_field, shape_append,
      shape_devicesJson l l' t t' official hl ht, List.length_cons, hid]
  have tot : total (devicesMessage l t id official) = total (devicesMessage l' t' id' official) := by
    rw [total_of_shape, total_of_shape, hs]
  have header : (assembleHeader (total (devicesMessage l t id official)) mask).length =
      (assembleHeader (total (devicesMessage l' t' id' official)) mask').length := by
    rw [tot]; simp only [assembleHeader]; split <;> simp [hm, hm']
  refine ⟨?_, by rw [hp, hp', header], ?_⟩
  · rw [hf, hf', List.length_append, List.length_append, body_length, body_length, header, tot]
  · rw [ho, ho', hp, hp', header, count, offsetsFold_of_shape _ _ _ _ hs]

/-- **`buildFetch`'s layout depends only on the length of the id's varint.** -/
theorem buildFetch_layout (id id' : Nat) (mask mask' frame frame' : List Byte) (payloadAt payloadAt' : Nat)
    (offsets offsets' : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets))
    (built' : buildFetch id' mask' = .ok (frame', payloadAt', offsets'))
    (hid : (PublicRequest.varint id).length = (PublicRequest.varint id').length) :
    frame.length = frame'.length ∧ payloadAt = payloadAt' ∧ offsets = offsets' := by
  rw [TlsMpc.KernelSpecs.RequestFrame.buildFetch_eq] at built built'
  obtain ⟨_, _, hm, hp, hf, ho⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask frame _ payloadAt offsets built
  obtain ⟨_, _, hm', hp', hf', ho'⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask' frame' _ payloadAt'
    offsets' built'
  have hs : shape (fetchMessage id) = shape (fetchMessage id') := by
    rw [fetchMessage_pieces, fetchMessage_pieces]
    simp only [getPieces, shape_bytes, shape_slot, shape_nil, shape_field, shape_append, List.length_cons, hid]
  have tot : total (fetchMessage id) = total (fetchMessage id') := by rw [total_of_shape, total_of_shape, hs]
  have header : (assembleHeader (total (fetchMessage id)) mask).length =
      (assembleHeader (total (fetchMessage id')) mask').length := by
    rw [tot]; simp only [assembleHeader]; split <;> simp [hm, hm']
  refine ⟨?_, by rw [hp, hp', header], ?_⟩
  · rw [hf, hf', List.length_append, List.length_append, body_length, body_length, header, tot]
  · rw [ho, ho', hp, hp', header, offsetsFold_of_shape _ _ _ _ hs]

/-! ## What the server receives: the three request kernels, end to end

`RequestFrame.*_built` say the kernels seal the builder's frame with the slot values in place;
`*_reference` above say that frame is the reference frame. Together: the kernels' outputs are the
TLS record of exactly the RFC 6455 frame of the reference request. -/

section Kernels
open TlsMpc.KernelSpecs Std.Tactic.BVDecide
open TlsMpc.HybridKernel (lookup)

/-- **`signal-request-ctr` seals exactly the reference send request.** On a frame `build`
returned (the controller's kernel naming), the kernel's outputs are `sealedRequest` of RFC 6455's
masked binary frame of `WebSocketMessage { REQUEST, PUT /v1/messages/{uuid}[?story=false],
IncomingMessageList JSON, id, content-type and unidentified-access-key headers }`, with the
contact's UUID text, base64 access key and padded device and registration ids from the
conversation record (`RequestFrame.requestValues`). -/
theorem signalRequestCtr_reference (envelope : List Byte) (timestamp id : Nat)
    (mask frame : List Byte) (official : Bool) (offsets : List Nat)
    (built : build envelope timestamp id mask official = .ok (frame, offsets))
    (cert : Nat) (assign : BVExpr.Assignment)
    (hframe : (lookup (signalRequestInputs cert frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (signalRequestInputs cert frame.length) "mask").map (BVExpr.eval assign) = mask)
    (hid : id < 2 ^ 64) :
    let get := fun name => (lookup (signalRequestInputs cert frame.length) name).map (BVExpr.eval assign)
    let values := TlsMpc.KernelSpecs.RequestFrame.requestValues cert (get "conversation")
    (HybridKernel.signalRequestCtr cert frame.length (offsets.getD 0 0) (offsets.getD 1 0) (offsets.getD 2 0)
        (offsets.getD 3 0)).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (clientFrame binary mask (WebSocketMessage.request (sendRequest (values 0) (values 1)
          (sendBody [(envelope, values 2, values 3)] timestamp) id official)).encode)
        (signalRequestSlots cert 0 0 0 0 (get "conversation")).1 := by
  intro get values
  have convLength : (get "conversation").length = HybridKernel.conversationBytes cert 80 := by
    simp [get, lookup, HybridKernel.lookupFrom, signalRequestInputs, ByteCircuit.inputBytes]
  have ref := (build_reference envelope timestamp id mask frame official offsets built values
    (TlsMpc.KernelSpecs.RequestFrame.uuid_length _ _)
    (by
      show (RelayEncoding.base64 _ _).length = 24
      rw [TlsMpc.KernelSpecs.RequestFrame.base64_length]
      simp [convLength, HybridKernel.conversationBytes])
    (TlsMpc.KernelSpecs.RequestFrame.paddedDecimal_length _ 3 (by omega))
    (TlsMpc.KernelSpecs.RequestFrame.paddedDecimal_length _ 10 (by omega))
    (by omega)).1
  rw [TlsMpc.KernelSpecs.RequestFrame.signalRequestCtr_built envelope timestamp id mask frame official offsets built
    cert assign hframe hmask]
  exact congrArg (fun p => sealedRequest (get "clientApplication") (get "sequence") p
    (signalRequestSlots cert 0 0 0 0 (get "conversation")).1) ref

/-- **`bundle-fetch-ctr` seals exactly the reference keys request** `GET /v2/keys/{uuid}/*` with
the contact's UUID and access key from the record (`RequestFrame.fetchValues`). -/
theorem bundleFetchCtr_reference (id : Nat) (mask frame : List Byte) (payloadAt : Nat) (offsets : List Nat)
    (built : buildFetch id mask = .ok (frame, payloadAt, offsets)) (assign : BVExpr.Assignment)
    (hframe : (lookup (fetchInputs frame.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (fetchInputs frame.length) "mask").map (BVExpr.eval assign) = mask)
    (hid : id < 2 ^ 64) :
    let get := fun name => (lookup (fetchInputs frame.length) name).map (BVExpr.eval assign)
    let values := TlsMpc.KernelSpecs.RequestFrame.fetchValues (get "record")
    (BundleKernel.bundleFetchCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0)).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (clientFrame binary mask (WebSocketMessage.request (keysRequest (values 0) (values 1) id)).encode)
        (liveValue (get "record")) := by
  intro get values
  have recordLength : (get "record").length = BundleKernel.recordBytes := by
    simp [get, lookup, HybridKernel.lookupFrom, fetchInputs, BundleKernel.requestInputs, ByteCircuit.inputBytes]
  have ref := (buildFetch_reference id mask frame payloadAt offsets built values
    (TlsMpc.KernelSpecs.RequestFrame.uuid_length _ _)
    (by
      show (RelayEncoding.base64 _ _).length = 24
      rw [TlsMpc.KernelSpecs.RequestFrame.base64_length]
      simp [recordLength, BundleKernel.recordBytes])
    (by omega)).1
  rw [TlsMpc.KernelSpecs.RequestFrame.bundleFetchCtr_built id mask frame payloadAt offsets built assign hframe hmask]
  exact congrArg (fun p => sealedRequest (get "clientApplication") (get "sequence") p (liveValue (get "record"))) ref

set_option maxHeartbeats 1000000 in
/-- **`bundle-request-ctr` seals exactly the reference multi-device send request**: one
`IncomingMessage` per envelope with device `i`'s padded ids from its record
(`RequestFrame.devicesValues`), the UUID and access key of the first record. -/
theorem bundleRequestCtr_reference (envelopes : List (List Byte)) (timestamp id : Nat)
    (mask frame : List Byte) (official : Bool) (payloadAt : Nat) (offsets : List Nat)
    (built : buildDevices envelopes timestamp id mask official = .ok (frame, payloadAt, offsets))
    (devices : List (Nat × Nat)) (paired : BundleKernel.pairs (offsets.drop 2) = some devices)
    (assign : BVExpr.Assignment)
    (hframe : (lookup (requestInputsOf frame.length devices.length) "frame").map (BVExpr.eval assign) = frame)
    (hmask : (lookup (requestInputsOf frame.length devices.length) "mask").map (BVExpr.eval assign) = mask)
    (hid : id < 2 ^ 64) :
    let get := fun name => (lookup (requestInputsOf frame.length devices.length) name).map (BVExpr.eval assign)
    let values := TlsMpc.KernelSpecs.RequestFrame.devicesValues (get "records")
    (BundleKernel.bundleRequestCtr frame.length payloadAt (offsets.getD 0 0) (offsets.getD 1 0) devices).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealedRequest (get "clientApplication") (get "sequence")
        (clientFrame binary mask (WebSocketMessage.request (sendRequest (values 0) (values 1)
          (sendBody (devicesOf values envelopes) timestamp) id official)).encode)
        (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1 := by
  intro get values
  have built' := built
  rw [TlsMpc.KernelSpecs.RequestFrame.buildDevices_eq] at built'
  by_cases empty : envelopes.isEmpty = true
  · rw [if_pos empty] at built'; cases built'
  rw [if_neg empty] at built'
  obtain ⟨_, _, _, _, _, ho⟩ := TlsMpc.KernelSpecs.RequestFrame.assemble_ok _ mask frame _ payloadAt offsets built'
  have nonempty : 0 < envelopes.length := by
    cases envelopes with
    | nil => exact absurd rfl empty
    | cons _ _ => simp
  have offsetsLength : offsets.length = 2 + 2 * envelopes.length := by
    rw [ho]; simp [TlsMpc.KernelSpecs.RequestFrame.offsetsFold_size]
  have devLength : devices.length = envelopes.length := by
    rw [TlsMpc.KernelSpecs.RequestFrame.pairs_spec _ devices paired]
    simp [offsetsLength]
  have recordsLength : (get "records").length = BundleKernel.recordBytes * envelopes.length := by
    simp [get, lookup, HybridKernel.lookupFrom, requestInputsOf, BundleKernel.requestInputs, ByteCircuit.inputBytes,
      devLength]
  have ref := (buildDevices_reference envelopes timestamp id mask frame official payloadAt offsets built values
    (TlsMpc.KernelSpecs.RequestFrame.uuid_length _ _)
    (by
      show (RelayEncoding.base64 _ _).length = 24
      rw [TlsMpc.KernelSpecs.RequestFrame.base64_length]
      simp [recordsLength, BundleKernel.recordBytes]
      omega)
    (fun i _ => ⟨by
        simp only [values, TlsMpc.KernelSpecs.RequestFrame.devicesValues_device,
          TlsMpc.KernelSpecs.RequestFrame.deviceBytes, deviceValue]
        exact TlsMpc.KernelSpecs.RequestFrame.paddedDecimal_length _ 3 (by omega),
      by
        simp only [values, TlsMpc.KernelSpecs.RequestFrame.devicesValues_registration,
          TlsMpc.KernelSpecs.RequestFrame.registrationBytes, deviceValue]
        exact TlsMpc.KernelSpecs.RequestFrame.paddedDecimal_length _ 10 (by omega)⟩)
    (by omega)).1
  rw [TlsMpc.KernelSpecs.RequestFrame.bundleRequestCtr_built envelopes timestamp id mask frame official payloadAt
    offsets built devices paired assign hframe hmask]
  exact congrArg (fun p => sealedRequest (get "clientApplication") (get "sequence") p
    (bundleRequestValue (get "records") (offsets.getD 0 0) (offsets.getD 1 0) devices).1) ref

end Kernels

#print axioms varint_eq
#print axioms sendMessage_reference
#print axioms fetchMessage_reference
#print axioms devicesMessage_reference
#print axioms build_reference
#print axioms buildFetch_reference
#print axioms buildDevices_reference
#print axioms decode_clientFrame
#print axioms clientFrame_reference
#print axioms ping_reference
#print axioms ping_decode
#print axioms keepalive_reference
#print axioms keepalive_decode
#print axioms reply_reference
#print axioms reply_decode
#print axioms varintAt_lt
#print axioms signalRequestCtr_reference
#print axioms bundleFetchCtr_reference
#print axioms bundleRequestCtr_reference
#print axioms build_public
#print axioms buildFetch_public
#print axioms buildDevices_public
#print axioms build_two_contacts
#print axioms build_layout
#print axioms buildFetch_layout
#print axioms buildDevices_layout

end TlsMpc.Node.RequestProofs
