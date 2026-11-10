import PreKeyReferenceWork.Generated.ContentModels.Types
open Aeneas Aeneas.Std Result
open PreKeyReference
/-! Source-reviewed external models. None is a cryptographic verifier. The
closure bodies below reproduce only the reachable InvalidArgument messages;
full Rust error-enum/string-allocation refinement is not claimed. -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or_else"]
def core.option.Option.ok_or_else {T E F : Type}
    (inst : core.ops.function.FnOnce F Unit E) (x : Option T) (f : F) :
    Result (core.result.Result T E) := do
  match x with
  | some v => ok (.Ok v)
  | none => let e ← inst.call_once f (); ok (.Err e)
@[rust_fun "core::option::{core::option::Option<@T>}::zip"]
def core.option.Option.zip {T U : Type} (x : Option T) (y : Option U) :
    Result (Option (T × U)) :=
  ok (match x, y with | some a, some b => some (a,b) | _, _ => none)
/-- Unused by all proved functions. Default feature: Kyber1024 public key bytes. -/
def kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length
    (_ : kem.KeyType) : Result Std.Usize := ok 1568#usize

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "registration_id is required")

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_1.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_1) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "device_id is required")

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_2.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_2) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "signed_pre_key_id is required")

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_3.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_3) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "signed_pre_key_public is required")

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_4.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_4) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "signed_pre_key_signature is required")

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_5.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_5) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "kyber_pre_key_id is required")

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_6.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_6) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "kyber_pre_key_public is required")

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_7.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_7) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "kyber_pre_key_signature is required")

def state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_8.Insts.CoreOpsFunctionFnOnceTupleSignalProtocolError.call_once
    (_ : state.bundle.TryFromPreKeyBundlePreKeyBundleContentSignalProtocolError.try_from.closure_8) (_ : Unit) : Result error.SignalProtocolError :=
  ok (.InvalidArgument "identity_key is required")
