import TlsMpc.Signal.SpqrChain

/-! Actual initial A2B negotiating phase, first two sends only. Input KEM keygen
is the internally computed ML-KEM768 output status||sk2400||pk1184. The complete
KeysSampled state (including ek/dk, authenticator, header encoder, negotiation
and both chain directions) is retained. This is not an active-phase override.
No receive/epoch transition is implemented by this bounded initial profile. -/
namespace TlsMpc.Signal.PrivateInitialSpqrV1
open Std.Tactic.BVDecide

def part (xs : List B) (offset count : Nat) : List B := (xs.drop offset).take count
structure State (B : Type) where
  authKey : List B
  authRoot : List B
  authMac : List B
  ek : List B
  dk : List B
  header : List B
  chainRoot : List B
  sendChain : List B
  receiveChain : List B
  counter : B

def State.map (f : B → B') (x : State B) : State B' :=
 ⟨x.authKey.map f,x.authRoot.map f,x.authMac.map f,x.ek.map f,x.dk.map f,
  x.header.map f,x.chainRoot.map f,x.sendChain.map f,x.receiveChain.map f,f x.counter⟩
def State.bytes (x : State B) : List B :=
 x.authKey++x.authRoot++x.authMac++x.ek++x.dk++x.header++x.chainRoot++x.sendChain++x.receiveChain++[x.counter]
def State.parse (a : ByteAuth.Ops B) (raw : List B) : State B :=
 ⟨part raw 0 32,part raw 32 32,part raw 64 32,part raw 96 1152,part raw 1248 2400,
  part raw 3648 96,part raw 3744 32,part raw 3776 32,part raw 3808 32,OpenResult.get a raw 3840⟩
def State.select (a : ByteAuth.Ops B) (mask : B) (yes no : State B) : State B :=
 ⟨Unpad.choose a mask yes.authKey no.authKey,Unpad.choose a mask yes.authRoot no.authRoot,
  Unpad.choose a mask yes.authMac no.authMac,Unpad.choose a mask yes.ek no.ek,
  Unpad.choose a mask yes.dk no.dk,Unpad.choose a mask yes.header no.header,
  Unpad.choose a mask yes.chainRoot no.chainRoot,Unpad.choose a mask yes.sendChain no.sendChain,
  Unpad.choose a mask yes.receiveChain no.receiveChain,Unpad.chooseByte a mask yes.counter no.counter⟩

-- These lengths and protobuf framing are PUBLIC fixed initial-state layout.
-- Private counters have the explicit accepted domain1/2, hence canonical1byte.
def publicVarint : Nat → Nat → List Nat
 | 0,_ => []
 | fuel+1,n => if n<128 then [n] else (128+n%128)::publicVarint fuel (n/128)
def literal (a : ByteAuth.Ops B) (ns : List Nat) : List B := ns.map a.const
def field (a : ByteAuth.Ops B) (tag : Nat) (body : List B) : List B :=
 literal a ([tag]++publicVarint 4 body.length)++body

def serialize (a : ByteAuth.Ops B) (x : State B) : List B :=
 let auth := field a 10 x.authRoot ++ field a 18 x.authMac
 let uc := literal a [8,1] ++ field a 18 auth ++ field a 26 x.ek ++ field a 34 x.dk
 let points := (List.range 16).flatMap (fun i => field a 18
   (part x.header (2*i) 2 ++ part x.header (32+2*i) 2 ++ part x.header (64+2*i) 2))
 let encoder := [a.const 8,x.counter] ++ points
 let v1 := field a 18 (field a 10 uc ++ field a 18 encoder)
 let sending := [a.const 8,x.counter] ++ field a 18 x.sendChain
 let receiving := field a 18 x.receiveChain
 let links := field a 10 sending ++ field a 18 receiving
 let chain := field a 26 links ++ field a 34 x.chainRoot ++ field a 50 []
 let vn := field a 10 x.authKey ++ literal a [24,1,34,0]
 field a 10 vn ++ field a 18 chain ++ field a 26 v1

def chainStart (s : Sha256.Ops B W) (auth : List B) : List B :=
 TlsKdf.expandFast s (TlsKdf.extract s (TlsKdf.zeros s 32) auth)
  ((TlsKdf.ascii "Signal PQ Ratchet V1 Chain  Start").map s.byteConst) 96

def authenticator (s : Sha256.Ops B W) (auth : List B) : List B :=
 TlsKdf.expandFast s (TlsKdf.extract s (TlsKdf.zeros s 32) (TlsKdf.zeros s 32 ++ auth))
  ((TlsKdf.ascii "Signal_PQCKA_V1_MLKEM768:Authenticator Update").map s.byteConst ++
   (List.replicate 7 (s.byteConst 0) ++ [s.byteConst 1])) 64

def headerMac (s : Sha256.Ops B W) (key header : List B) : List B :=
 Sha256.hmac s key ((TlsKdf.ascii "Signal_PQCKA_V1_MLKEM768:ekheader").map s.byteConst ++
  (List.replicate 7 (s.byteConst 0) ++ [s.byteConst 1]) ++ header)

/-- valid||full typed state3841||actual message37||message key32. Every KEM,
DH, identity/trust/signature acceptance must also gate the OUTER bootstrap. -/
def start (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (auth generated : List B) : List B :=
 let sk := part generated 1 2400
 let pk := part generated 2401 1184
 let ok := a.and (if auth.length=32 ∧ generated.length=3585 then a.const 255 else a.const 0)
   (a.and (ByteAuth.eqMask a (OpenResult.get a generated 0) (a.const 255))
     (ByteAuth.equalMask a (part sk 1152 1184) pk))
 let keys := chainStart s auth
 let ak := authenticator s auth
 let header := part pk 1152 32 ++ part sk 2336 32
 let body := header ++ headerMac s (ak.drop 32) header
 let first := SpqrChain.materialFast s a (part keys 32 32) (List.replicate 4 (a.const 0))
 let state : State B := ⟨auth,ak.take 32,ak.drop 32,pk.take 1152,sk,body,
   keys.take 32,first.take 32,keys.drop 64,a.const 1⟩
 ok :: ByteAuth.release a ok (state.bytes ++ literal a [1,1,1,1,0] ++ body.take 32 ++ first.drop 32)

/-- Consume exact returned full state; second send has NO new KEM randomness.
A reused/exhausted phase rejects, retaining state and releasing no wire/key. -/
def second (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (old : List B) : List B :=
 let state := State.parse a (old.drop 1)
 let ok := a.and (if old.length=3842 then a.const 255 else a.const 0)
  (a.and (ByteAuth.eqMask a (OpenResult.get a old 0) (a.const 255))
   (ByteAuth.eqMask a state.counter (a.const 1)))
 let step := SpqrChain.materialFast s a state.sendChain (literal a [0,0,0,1])
 let next := {state with sendChain := step.take 32,counter := a.const 2}
 ok :: ((State.select a ok next state).bytes ++
  ByteAuth.release a ok (literal a [1,1,2,1,1] ++ part state.header 32 32 ++ step.drop 32))
end TlsMpc.Signal.PrivateInitialSpqrV1
