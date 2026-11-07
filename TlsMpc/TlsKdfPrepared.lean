import TlsMpc.TlsKdf
import TlsMpc.HmacPrepared

/-! HMAC setup sharing for TLS/HKDF. Every optimized function below is proved
equal to the direct executable specification in TlsKdf, for all inputs. -/

namespace TlsMpc.TlsKdf

open Sha256 HmacPrepared

def preparedBlocks (o : Ops B W) (key : Prepared W) (info : List B) : Nat → Nat → List B → List B
  | 0, _, _ => []
  | n + 1, counter, previous =>
      let current := run o key (previous ++ info ++ [o.byteConst counter])
      current ++ preparedBlocks o key info n (counter + 1) current

theorem preparedBlocks_correct (o : Ops B W) (prk info : List B) (n counter : Nat) (previous : List B) :
    preparedBlocks o (prepare o prk) info n counter previous =
      expandBlocks o prk info n counter previous := by
  induction n generalizing counter previous with
  | zero => rfl
  | succ n ih => simp only [preparedBlocks, expandBlocks, run_prepare, ih]

def preparedExpand (o : Ops B W) (key : Prepared W) (info : List B) (length : Nat) : List B :=
  (preparedBlocks o key info ((length + 31) / 32) 1 []).take length

theorem preparedExpand_correct (o : Ops B W) (prk info : List B) (length : Nat) :
    preparedExpand o (prepare o prk) info length = expandCore o prk info length := by
  simp only [preparedExpand, expandCore, preparedBlocks_correct]

def expandFast (o : Ops B W) (prk info : List B) (length : Nat) : List B :=
  preparedExpand o (prepare o prk) info length

theorem expandFast_correct (o : Ops B W) (prk info : List B) (length : Nat) :
    expandFast o prk info length = expandCore o prk info length := preparedExpand_correct o prk info length

def preparedLabel (o : Ops B W) (key : Prepared W) (label : String)
    (context : List B) (length : Nat) : List B :=
  preparedExpand o key (labelInfo o (ascii label) context length) length

theorem preparedLabel_correct (o : Ops B W) (secret : List B) (label : String)
    (context : List B) (length : Nat) :
    preparedLabel o (prepare o secret) label context length = expandLabelCore o secret label context length := by
  exact preparedExpand_correct o secret _ length

def expandLabelFast (o : Ops B W) (secret : List B) (label : String)
    (context : List B) (length : Nat) : List B :=
  preparedLabel o (prepare o secret) label context length

theorem expandLabelFast_correct (o : Ops B W) (secret : List B) (label : String)
    (context : List B) (length : Nat) :
    expandLabelFast o secret label context length = expandLabelCore o secret label context length :=
  preparedLabel_correct o secret label context length

def trafficKeysFast (o : Ops B W) (secret : List B) : List B × List B :=
  let key := prepare o secret
  (preparedLabel o key "key" [] 16, preparedLabel o key "iv" [] 12)

theorem trafficKeysFast_correct (o : Ops B W) (secret : List B) :
    trafficKeysFast o secret = trafficKeys o secret := by
  simp only [trafficKeysFast, trafficKeys, preparedLabel_correct]

def applicationSecretsFast (o : Ops B W) (secret transcript : List B) : List B × List B :=
  let key := prepare o secret
  (preparedLabel o key "c ap traffic" transcript 32, preparedLabel o key "s ap traffic" transcript 32)

theorem applicationSecretsFast_correct (o : Ops B W) (secret transcript : List B) :
    applicationSecretsFast o secret transcript = applicationSecrets o secret transcript := by
  simp only [applicationSecretsFast, applicationSecrets, deriveSecret, preparedLabel_correct]

def handshakeSecretsFast (o : Ops B W) (ecdhe helloHash : List B) : HandshakeSecrets B :=
  let early := extract o (zeros o 32) (zeros o 32)
  let emptyHash := Sha256.hash o []
  let handshake := extract o (deriveSecret o early "derived" emptyHash) ecdhe
  let key := prepare o handshake
  ⟨handshake, preparedLabel o key "c hs traffic" helloHash 32,
    preparedLabel o key "s hs traffic" helloHash 32,
    extract o (preparedLabel o key "derived" emptyHash 32) (zeros o 32)⟩

theorem handshakeSecretsFast_correct (o : Ops B W) (ecdhe helloHash : List B) :
    handshakeSecretsFast o ecdhe helloHash = handshakeSecrets o ecdhe helloHash := by
  simp only [handshakeSecretsFast, handshakeSecrets, deriveSecret, preparedLabel_correct]

end TlsMpc.TlsKdf
