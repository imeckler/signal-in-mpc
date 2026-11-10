import PreKeyReferenceWork.Generated.ContentModels.Funs
import TlsMpc.Signal.PreKeyBundle

namespace PreKeyReference.Proofs
open Aeneas Aeneas.Std
open state.bundle

abbrev actual := PreKeyBundle.Insts.CoreConvertTryFromPreKeyBundleContentSignalProtocolError.try_from

/-- Exact required payload, with no validation-result Boolean. -/
structure Required where
  registration : Std.U32
  device : libsignal_core.address.DeviceId
  signedId : Std.U32
  signedPublic : libsignal_core.curve.PublicKey
  signedSignature : alloc.vec.Vec Std.U8
  pqId : Std.U32
  pqPublic : kem.Key kem.Public
  pqSignature : alloc.vec.Vec Std.U8
  identity : identity_key.IdentityKey

def content (r : Required) (id : Option Std.U32)
    (key : Option libsignal_core.curve.PublicKey) : PreKeyBundleContent :=
  ⟨some r.registration, some r.device, id, key, some r.signedId,
    some r.signedPublic, some r.signedSignature, some r.identity,
    some r.pqId, some r.pqPublic, some r.pqSignature⟩

def paired {A B : Type} (a : Option A) (b : Option B) : Option (A × B) :=
  match a,b with | some x, some y => some (x,y) | _,_ => none

def bundle (r : Required) (pair : Option (Std.U32 × libsignal_core.curve.PublicKey)) : PreKeyBundle :=
  ⟨r.registration,r.device,pair.map Prod.fst,pair.map Prod.snd,
    ⟨r.signedId,r.signedPublic,r.signedSignature⟩,r.identity,
    ⟨r.pqId,r.pqPublic,r.pqSignature⟩⟩

theorem constructor_exact (r : Required) (pair : Option (Std.U32 × libsignal_core.curve.PublicKey)) :
    PreKeyBundle.new r.registration r.device pair r.signedId r.signedPublic
      r.signedSignature r.pqId r.pqPublic r.pqSignature r.identity =
      .ok (.Ok (bundle r pair)) := by
  cases pair <;> rfl

/-- Actual generated TryFrom preserves every payload. All required fields are
Some, so none of the nine modeled error closures is executed. -/
theorem try_from_present (r : Required) (id : Option Std.U32)
    (key : Option libsignal_core.curve.PublicKey) :
    actual (content r id key) = .ok (.Ok (bundle r (paired id key))) := by
  cases id <;> cases key <;> rfl

theorem optional_pair_present {A B : Type} (a : Option A) (b : Option B) :
    (paired a b).isSome = (a.isSome && b.isSome) := by
  cases a <;> cases b <;> rfl

def presence {A : Type} (a : Option A) : BitVec 8 := if a.isSome then 1 else 0

def flags (c : PreKeyBundleContent) : List (BitVec 8) :=
  [presence c.registration_id,presence c.device_id,presence c.pre_key_id,
    presence c.pre_key_public,presence c.signed_pre_key_id,presence c.signed_pre_key_public,
    presence c.signed_pre_key_signature,presence c.identity_key,presence c.kyber_pre_key_id,
    presence c.kyber_pre_key_public,presence c.kyber_pre_key_signature]

/-- The frozen shared optional mask agrees with Option::zip's presence model. -/
theorem optional_mask_refines (c : PreKeyBundleContent) :
    TlsMpc.Signal.PreKeyBundle.optionalMask TlsMpc.ByteAuth.concrete (flags c) =
      if (paired c.pre_key_id c.pre_key_public).isSome then 255 else 0 := by
  rw [TlsMpc.Signal.PreKeyBundle.optionalMask_spec]
  cases hi : c.pre_key_id <;> cases hk : c.pre_key_public <;>
    simp [flags,presence,TlsMpc.Signal.OpenResult.get,hi,hk,paired]

/-- Pure selected-source behavior relative to the explicit Option/error models. -/
def sourceSpec (c : PreKeyBundleContent) : core.result.Result PreKeyBundle error.SignalProtocolError :=
  match c.registration_id with
  | none => .Err (.InvalidArgument "registration_id is required")
  | some registration => match c.device_id with
    | none => .Err (.InvalidArgument "device_id is required")
    | some device => match c.signed_pre_key_id with
      | none => .Err (.InvalidArgument "signed_pre_key_id is required")
      | some signedId => match c.signed_pre_key_public with
        | none => .Err (.InvalidArgument "signed_pre_key_public is required")
        | some signedPublic => match c.signed_pre_key_signature with
          | none => .Err (.InvalidArgument "signed_pre_key_signature is required")
          | some signedSignature => match c.kyber_pre_key_id with
            | none => .Err (.InvalidArgument "kyber_pre_key_id is required")
            | some pqId => match c.kyber_pre_key_public with
              | none => .Err (.InvalidArgument "kyber_pre_key_public is required")
              | some pqPublic => match c.kyber_pre_key_signature with
                | none => .Err (.InvalidArgument "kyber_pre_key_signature is required")
                | some pqSignature => match c.identity_key with
                  | none => .Err (.InvalidArgument "identity_key is required")
                  | some identity => .Ok (bundle ⟨registration,device,signedId,signedPublic,
                    signedSignature,pqId,pqPublic,pqSignature,identity⟩ (paired c.pre_key_id c.pre_key_public))

/-- Error ordering is proved against the explicitly modeled error constructors.
This is not an actual Aeneas translation of those nine closures. -/
theorem try_from_source_spec (c : PreKeyBundleContent) : actual c = .ok (sourceSpec c) := by
  rcases c with ⟨reg,dev,oid,opub,sid,spub,ssig,identity,pid,ppub,psig⟩
  cases reg <;> try rfl
  cases dev <;> try rfl
  cases oid <;> cases opub <;>
    (cases sid <;> try rfl
     cases spub <;> try rfl
     cases ssig <;> try rfl
     cases pid <;> try rfl
     cases ppub <;> try rfl
     cases psig <;> try rfl
     cases identity <;> rfl)


/-- Codes coincide with the frozen constructor component; 255 is outside the
selected InvalidArgument message set. -/
def errorCode : core.result.Result PreKeyBundle error.SignalProtocolError → BitVec 8
  | .Ok _ => 0
  | .Err (.InvalidArgument message) =>
    if message = "registration_id is required" then 1 else
    if message = "device_id is required" then 2 else
    if message = "signed_pre_key_id is required" then 3 else
    if message = "signed_pre_key_public is required" then 4 else
    if message = "signed_pre_key_signature is required" then 5 else
    if message = "kyber_pre_key_id is required" then 6 else
    if message = "kyber_pre_key_public is required" then 7 else
    if message = "kyber_pre_key_signature is required" then 8 else
    if message = "identity_key is required" then 9 else
    255

theorem first_missing_refines (c : PreKeyBundleContent) :
    (do let b ← actual c; pure (errorCode b) : Result (BitVec 8)) = .ok
      (TlsMpc.Signal.PreKeyBundle.firstMissing TlsMpc.ByteAuth.concrete (flags c)
        TlsMpc.Signal.PreKeyBundle.required) := by
  rw [try_from_source_spec, TlsMpc.Signal.PreKeyBundle.firstMissing_spec]
  rcases c with ⟨reg,dev,oid,opub,sid,spub,ssig,identity,pid,ppub,psig⟩
  cases reg <;> try rfl
  cases dev <;> try rfl
  cases sid <;> try rfl
  cases spub <;> try rfl
  cases ssig <;> try rfl
  cases pid <;> try rfl
  cases ppub <;> try rfl
  cases psig <;> try rfl
  cases identity <;> rfl

/-- The modeled Option success branch is independent of the callback's behavior. -/
theorem option_some_no_callback {T E F : Type}
    (inst : core.ops.function.FnOnce F Unit E) (v : T) (f : F) :
    core.option.Option.ok_or_else inst (some v) f = .ok (.Ok v) := rfl

theorem option_zip_model_exact {T U : Type} (a : Option T) (b : Option U) :
    core.option.Option.zip a b = .ok (paired a b) := rfl

end PreKeyReference.Proofs
