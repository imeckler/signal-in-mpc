import LibSignalReference.Generated.KeyAccessors.Funs
import TlsMpc.Signal.KeyMaterial

/-!
Refinement of the actual Charon/Aeneas translation of pinned libsignal keys.rs.
These proofs cover only the nine listed constructors/accessors. No cryptographic
primitive, opaque external model or generated placeholder is used here.
-/

namespace LibSignalReference.Proofs

open Aeneas Aeneas.Std

def bytes (xs : Aeneas.Std.Array Aeneas.Std.U8 n) : TlsMpc.Signal.Bytes n.val :=
  ⟨xs.val.map (fun x => x.bv), by simp⟩

def chain (key : ratchet.keys.ChainKey) : TlsMpc.Signal.ChainKey :=
  { key := bytes key.key, index := key.index.bv }

def message (keys : ratchet.keys.MessageKeys) : TlsMpc.Signal.MessageKeys :=
  { cipherKey := bytes keys.cipher_key, macKey := bytes keys.mac_key,
    iv := bytes keys.iv, counter := keys.counter.bv }

def root (key : ratchet.keys.RootKey) : TlsMpc.Signal.RootKey :=
  { key := bytes key.key }

theorem chain_new_refines (key : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (index : Aeneas.Std.U32) :
    ∃ result, ratchet.keys.ChainKey.new key index = .ok result ∧
      chain result = { key := bytes key, index := index.bv } := by
  exact ⟨{ key, index }, rfl, rfl⟩

theorem root_new_refines (key : Aeneas.Std.Array Aeneas.Std.U8 32#usize) :
    ∃ result, ratchet.keys.RootKey.new key = .ok result ∧
      root result = { key := bytes key } := by
  exact ⟨{ key }, rfl, rfl⟩

theorem chain_key_refines_artifact (key : ratchet.keys.ChainKey) :
    ∃ result, ratchet.keys.ChainKey.impl.key key = .ok result ∧
      TlsMpc.Boolean.Artifact.evaluateProgram (TlsMpc.Signal.chainEnvironment (chain key))
        (TlsMpc.Boolean.Artifact.exportProgram TlsMpc.Signal.chainKeyCircuit) =
          some (TlsMpc.Signal.bytesBits (bytes result)) := by
  exact ⟨key.key, rfl, TlsMpc.Signal.exported_chainKey_correct (chain key)⟩

theorem chain_index_refines_artifact (key : ratchet.keys.ChainKey) :
    ∃ result, ratchet.keys.ChainKey.impl.index key = .ok result ∧
      TlsMpc.Boolean.Artifact.evaluateProgram (TlsMpc.Signal.chainEnvironment (chain key))
        (TlsMpc.Boolean.Artifact.exportProgram TlsMpc.Signal.chainIndexCircuit) =
          some (TlsMpc.Signal.counterBits result.bv) := by
  exact ⟨key.index, rfl, TlsMpc.Signal.exported_chainIndex_correct (chain key)⟩

theorem message_cipher_refines_artifact (keys : ratchet.keys.MessageKeys) :
    ∃ result, ratchet.keys.MessageKeys.impl.cipher_key keys = .ok result ∧
      TlsMpc.Boolean.Artifact.evaluateProgram (TlsMpc.Signal.messageEnvironment (message keys))
        (TlsMpc.Boolean.Artifact.exportProgram TlsMpc.Signal.messageCipherCircuit) =
          some (TlsMpc.Signal.bytesBits (bytes result)) := by
  exact ⟨keys.cipher_key, rfl, TlsMpc.Signal.exported_messageCipher_correct (message keys)⟩

theorem message_mac_refines_artifact (keys : ratchet.keys.MessageKeys) :
    ∃ result, ratchet.keys.MessageKeys.impl.mac_key keys = .ok result ∧
      TlsMpc.Boolean.Artifact.evaluateProgram (TlsMpc.Signal.messageEnvironment (message keys))
        (TlsMpc.Boolean.Artifact.exportProgram TlsMpc.Signal.messageMacCircuit) =
          some (TlsMpc.Signal.bytesBits (bytes result)) := by
  exact ⟨keys.mac_key, rfl, TlsMpc.Signal.exported_messageMac_correct (message keys)⟩

theorem message_iv_refines_artifact (keys : ratchet.keys.MessageKeys) :
    ∃ result, ratchet.keys.MessageKeys.impl.iv keys = .ok result ∧
      TlsMpc.Boolean.Artifact.evaluateProgram (TlsMpc.Signal.messageEnvironment (message keys))
        (TlsMpc.Boolean.Artifact.exportProgram TlsMpc.Signal.messageIvCircuit) =
          some (TlsMpc.Signal.bytesBits (bytes result)) := by
  exact ⟨keys.iv, rfl, TlsMpc.Signal.exported_messageIv_correct (message keys)⟩

theorem message_counter_refines_artifact (keys : ratchet.keys.MessageKeys) :
    ∃ result, ratchet.keys.MessageKeys.impl.counter keys = .ok result ∧
      TlsMpc.Boolean.Artifact.evaluateProgram (TlsMpc.Signal.messageEnvironment (message keys))
        (TlsMpc.Boolean.Artifact.exportProgram TlsMpc.Signal.messageCounterCircuit) =
          some (TlsMpc.Signal.counterBits result.bv) := by
  exact ⟨keys.counter, rfl, TlsMpc.Signal.exported_messageCounter_correct (message keys)⟩

theorem root_key_refines_artifact (key : ratchet.keys.RootKey) :
    ∃ result, ratchet.keys.RootKey.impl.key key = .ok result ∧
      TlsMpc.Boolean.Artifact.evaluateProgram (TlsMpc.Signal.rootEnvironment (root key))
        (TlsMpc.Boolean.Artifact.exportProgram TlsMpc.Signal.rootKeyCircuit) =
          some (TlsMpc.Signal.bytesBits (bytes result)) := by
  exact ⟨key.key, rfl, TlsMpc.Signal.exported_rootKey_correct (root key)⟩

end LibSignalReference.Proofs
