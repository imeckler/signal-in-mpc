import TlsMpc.TlsHandshake

/-! Public TLS 1.3 handshake encoding and strict parsing for the initial
certificate-authenticated X25519 / AES-128-GCM / SHA-256 client profile.
Server authentication metadata is explicitly public by the application's
policy. Application record plaintext must never be passed to these parsers.
No client certificate, PSK, early data or compressed certificate is offered.
-/
namespace TlsMpc.TlsWire
abbrev Bytes := List UInt8
abbrev Parser := StateT Bytes (Except String)

def octets (xs : List Nat) : Bytes := xs.map UInt8.ofNat
def uint (size n : Nat) : Bytes := (List.range size).map (fun i => UInt8.ofNat (n / 256 ^ (size - 1 - i)))
def number (bs : Bytes) : Nat := bs.foldl (fun n b => 256 * n + b.toNat) 0
def vector (size : Nat) (bs : Bytes) : Bytes := uint size bs.length ++ bs
def handshake (kind : Nat) (body : Bytes) : Bytes := [UInt8.ofNat kind] ++ vector 3 body
def record (kind : Nat) (body : Bytes) : Bytes := octets [kind, 3, 3] ++ vector 2 body
def hash (bytes : Bytes) : Bytes :=
  (Sha256.hash Sha256.concrete (bytes.map (fun b => BitVec.ofNat 8 b.toNat))).map (fun b => UInt8.ofNat b.toNat)

def read (size : Nat) : Parser Bytes := do
  let bytes ← get
  if size > bytes.length then throw "truncated TLS encoding"
  set (bytes.drop size)
  return bytes.take size
def readNat (size : Nat) : Parser Nat := number <$> read size
def readVector (size : Nat) : Parser Bytes := do read (← readNat size)
def require (ok : Bool) (message : String) : Parser Unit := unless ok do throw message
def exactly (p : Parser α) (bytes : Bytes) : Except String α := do
  let (value, rest) ← p.run bytes
  if !rest.isEmpty then throw "trailing TLS bytes"
  return value

abbrev Extension := Nat × Bytes
def extension (kind : Nat) (body : Bytes) : Bytes := uint 2 kind ++ vector 2 body

def extensionsAux : Nat → Bytes → Except String (List Extension)
  | 0, [] => pure []
  | 0, _ => throw "too many TLS extensions"
  | _ + 1, [] => pure []
  | fuel + 1, bytes => do
      let ((kind, body), rest) ← (do let k ← readNat 2; let b ← readVector 2; pure (k,b) : Parser Extension).run bytes
      let tail ← extensionsAux fuel rest
      if tail.any (fun x => x.1 == kind) then throw "duplicate TLS extension"
      return (kind,body) :: tail
def extensions (bytes : Bytes) : Except String (List Extension) := extensionsAux bytes.length bytes
def lookup (xs : List Extension) (kind : Nat) : Option Bytes := (xs.find? (fun x => x.1 == kind)).map Prod.snd
def optionExcept (value : Option α) (error : String) : Except String α :=
  match value with | some x => .ok x | none => .error error
def required (xs : List Extension) (kind : Nat) : Except String Bytes :=
  optionExcept (lookup xs kind) s!"missing TLS extension {kind}"

def signatureSchemes : List Nat := [0x0804, 0x0805, 0x0806, 0x0403, 0x0503, 0x0603, 0x0807, 0x0808, 0x0809, 0x080a, 0x080b]
def retryRandom : Bytes := octets
  [0xcf,0x21,0xad,0x74,0xe5,0x9a,0x61,0x11,0xbe,0x1d,0x8c,0x02,0x1e,0x65,0xb8,0x91,
   0xc2,0xa2,0x11,0x16,0x7a,0xbb,0x8c,0x5e,0x07,0x9e,0x09,0xe2,0xc8,0xa8,0x33,0x9c]

structure Config where
  hostname : String
  alpn : List String := ["http/1.1"]
  initialKeyShare : Bool := true
  maxHandshakeBytes : Nat := 1048576
  maxRecords : Nat := 4096

def Config.valid (c : Config) : Bool :=
  !c.hostname.isEmpty && c.hostname.utf8ByteSize ≤ 253 &&
    c.hostname.toUTF8.data.all (fun b => b.toNat > 32 && b.toNat < 127) &&
    c.alpn.all (fun name => !name.isEmpty && name.utf8ByteSize < 256) &&
    (c.alpn.map (fun name => name.utf8ByteSize + 1)).sum < 65536

def clientHello (cfg : Config) (random keyShare : Bytes) (cookie : Option Bytes := none)
    (includeKey : Bool := true) : Except String Bytes := do
  if !cfg.valid || random.length != 32 || keyShare.length != 32 then throw "invalid ClientHello configuration"
  let host := cfg.hostname.toUTF8.data.toList
  let sni := extension 0 (vector 2 ([0] ++ vector 2 host))
  let versions := extension 43 (octets [2,3,4])
  let groups := extension 10 (octets [0,2,0,29])
  let sigs := extension 13 (vector 2 ((signatureSchemes ++ [0x0401,0x0501,0x0601]).flatMap (uint 2)))
  let key := extension 51 (vector 2 (if includeKey then uint 2 29 ++ vector 2 keyShare else []))
  let alpn := if cfg.alpn.isEmpty then [] else extension 16
    (vector 2 (cfg.alpn.flatMap (fun name => vector 1 name.toUTF8.data.toList)))
  let cookieExt := match cookie with | none => [] | some b => extension 44 (vector 2 b)
  let body := octets [3,3] ++ random ++ octets [0,0,2,0x13,1,1,0] ++
    vector 2 (sni ++ versions ++ groups ++ sigs ++ key ++ alpn ++ cookieExt)
  return handshake 1 body

structure ServerHello where
  retry : Bool
  share : Bytes
  cookie : Option Bytes
  requestedKey : Bool

def serverHello (body : Bytes) : Except String ServerHello := exactly (do
  require ((← readNat 2) == 0x0303) "invalid ServerHello legacy version"
  let random ← read 32
  require (← readVector 1).isEmpty "ServerHello session ID does not match"
  require ((← readNat 2) == 0x1301) "server selected unoffered cipher suite"
  require ((← readNat 1) == 0) "invalid legacy compression"
  let exts ← liftM (extensions (← readVector 2))
  require ((← liftM (required exts 43)) == octets [3,4]) "server did not negotiate TLS1.3"
  let retry := random == retryRandom
  require (exts.all fun (k,_) => if retry then k == 43 || k == 51 || k == 44 else k == 43 || k == 51)
    "forbidden ServerHello extension"
  if retry then
    let key := lookup exts 51
    if let some b := key then require (b == uint 2 29) "unsupported retry group"
    let cookie ← match lookup exts 44 with
      | none => pure none
      | some b => do
          let value ← liftM (exactly (readVector 2) b)
          require (!value.isEmpty) "empty retry cookie"
          pure (some value)
    require (key.isSome || cookie.isSome) "HelloRetryRequest requested no change"
    return ⟨true, [], cookie, key.isSome⟩
  else
    let key ← liftM (required exts 51)
    let share ← liftM (exactly (do
      require ((← readNat 2) == 29) "unsupported server key share"
      let share ← readVector 2
      require (share.length == 32) "invalid X25519 key share length"
      pure share) key)
    return ⟨false, share, none, false⟩) body

def encryptedExtensions (cfg : Config) (body : Bytes) : Except String (Option String) := exactly (do
  let exts ← liftM (extensions (← readVector 2))
  require (exts.all fun (k,_) => k == 0 || k == 10 || k == 16) "unsolicited encrypted extension"
  if let some sni := lookup exts 0 then require sni.isEmpty "nonempty SNI acknowledgement"
  if let some groups := lookup exts 10 then
    let values ← liftM (exactly (readVector 2) groups)
    require (!values.isEmpty && values.length % 2 == 0) "malformed server supported groups"
  match lookup exts 16 with
  | none => return none
  | some encoded =>
      require (!cfg.alpn.isEmpty) "unsolicited ALPN"
      let name ← liftM (exactly (do
        let names ← readVector 2
        liftM (exactly (readVector 1) names)) encoded)
      let selected := cfg.alpn.find? (fun n => n.toUTF8.data.toList == name)
      let selected ← liftM (optionExcept selected "server selected unoffered ALPN")
      return some selected) body

def certificateRequest (body : Bytes) : Except String Unit := exactly (do
  require (← readVector 1).isEmpty "nonempty initial certificate request context"
  let exts ← liftM (extensions (← readVector 2))
  let schemes ← liftM (required exts 13)
  let list ← liftM (exactly (readVector 2) schemes)
  require (!list.isEmpty && list.length % 2 == 0) "malformed requested signature schemes") body

def certificateEntries : Nat → Bytes → Except String (List Bytes)
  | 0, [] => pure []
  | 0, _ => throw "too many certificates"
  | _ + 1, [] => pure []
  | fuel + 1, bytes => do
      let ((cert, extBytes), rest) ← (do let c ← readVector 3; let e ← readVector 2; pure (c,e) : Parser (Bytes × Bytes)).run bytes
      if cert.isEmpty then throw "empty certificate"
      let exts ← extensions extBytes
      -- No certificate-entry extensions are requested by this client profile.
      if !exts.isEmpty then throw "unsolicited certificate entry extension"
      return cert :: (← certificateEntries fuel rest)

def certificates (body : Bytes) : Except String (List Bytes) := exactly (do
  require (← readVector 1).isEmpty "nonempty server certificate context"
  let encoded ← readVector 3
  let chain ← liftM (certificateEntries encoded.length encoded)
  require (!chain.isEmpty) "server supplied no certificate"
  return chain) body

def certificateVerify (body : Bytes) : Except String (Nat × Bytes) := exactly (do
  let scheme ← readNat 2
  require (signatureSchemes.contains scheme) "unoffered CertificateVerify scheme"
  let signature ← readVector 2
  require (!signature.isEmpty) "empty CertificateVerify signature"
  return (scheme, signature)) body

structure Message where
  kind : Nat
  body : Bytes
  deriving Repr, Inhabited
def Message.bytes (m : Message) : Bytes := handshake m.kind m.body

/-- Split complete handshake messages; preserve an incomplete trailing message.
The bound is checked as soon as its header arrives, before waiting for its body. -/
def messages (limit : Nat) : Nat → Bytes → Except String (List Message × Bytes)
  | 0, bytes => if bytes.isEmpty then pure ([],[]) else throw "too many handshake messages"
  | fuel + 1, bytes =>
      if bytes.length < 4 then pure ([],bytes) else do
        let kind := (bytes[0]!).toNat
        let size := number ((bytes.drop 1).take 3)
        if size > limit then throw "handshake message exceeds resource limit"
        if bytes.length < size + 4 then return ([],bytes)
        let message := Message.mk kind ((bytes.drop 4).take size)
        let (tail, pending) ← messages limit fuel (bytes.drop (4 + size))
        return (message :: tail, pending)

structure Record where
  kind : Nat
  version : Nat
  body : Bytes
  deriving Repr, Inhabited
def Record.bytes (r : Record) : Bytes := [UInt8.ofNat r.kind] ++ uint 2 r.version ++ vector 2 r.body

def records : Nat → Bytes → Except String (List Record × Bytes)
  | 0, bytes => if bytes.isEmpty then pure ([],[]) else throw "too many records"
  | fuel + 1, bytes =>
      if bytes.length < 5 then pure ([],bytes) else do
        let kind := (bytes[0]!).toNat
        let version := number ((bytes.drop 1).take 2)
        let size := number ((bytes.drop 3).take 2)
        if size > 16640 then throw "TLS record overflow"
        if bytes.length < 5 + size then return ([],bytes)
        let current : Record := ⟨kind, version, (bytes.drop 5).take size⟩
        let (tail, pending) ← records fuel (bytes.drop (5 + size))
        return (current :: tail, pending)

end TlsMpc.TlsWire
