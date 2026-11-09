import ChatResponseReferenceWork.ParserCircuitCandidateV1.MixedFeed
open TlsMpc TlsMpc.Signal Std.Tactic.BVDecide
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

/-- Operation scheduling is public; all slot/ID/validity/data/control payloads
remain encoded circuit inputs. The two endpoint ABIs have different widths. -/
inductive EndpointKind where | byte | admit

def endpointKind : MuxInput → EndpointKind
  | .byte .. => .byte
  | .admit .. => .admit

def endpointEncodedInput (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) : MuxInput → List (BitVec 8)
  | .byte active beginning ending value => encodeCompactInput state active beginning ending value
  | .admit index id valid => encodeCompactAdmit state index id valid

def endpointOutput (d : VarintDecode.Spqr.Ops B W) (o : Word64.Ops B W) (a : ByteAuth.Ops B)
    (capacity : Nat) (kind : EndpointKind) (raw : List B) : List B :=
  match kind with
  | .byte => runByte d o a capacity raw
  | .admit => runAdmit o a raw

theorem endpoint_output_map (capacity : Nat) (kind : EndpointKind) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) :
    (endpointOutput VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity kind raw).map (BVExpr.eval assign) =
    endpointOutput VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity kind (raw.map (BVExpr.eval assign)) := by
  cases kind with
  | byte => exact runByte_map (ByteAuth.evaluationHom assign) (VarintDecode.Spqr.evaluationHom assign) (Word64.evaluationHom assign) capacity raw
  | admit => exact runAdmit_map (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign) raw

theorem endpoint_encoded_step (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (input : MuxInput) (shape : MuxCodecShape state) (safe : SafeStack state.parser) :
    endpointOutput VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
      (endpointKind input) (endpointEncodedInput state input) = mixedSourceStep capacity state input := by
  cases input with
  | byte active beginning ending value => exact encoded_byte_step capacity state shape safe _ _ _ _
  | admit index id valid => exact encoded_admit_step state shape _ _ _

theorem compiled_mixed_step (capacity : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) (input : MuxInput)
    (shape : MuxCodecShape state) (safe : SafeStack state.parser)
    (encoded : raw.map (BVExpr.eval assign) = endpointEncodedInput state input)
    (index : Nat) (bound : index < 8*(endpointOutput VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic
      capacity (endpointKind input) raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (endpointOutput VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity (endpointKind input) raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (endpointOutput VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity (endpointKind input) raw))).vec.get index bound)) =
    (ByteCircuit.joinValue (mixedSourceStep capacity state input)).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,endpoint_output_map,encoded,endpoint_encoded_step capacity state input shape safe]

/-- Every exported bit at every point of any mixed admit/feed schedule agrees
with the actual original Mux operation, with the exact proved feedback codec. -/
theorem compiled_mixed_after_prefix (capacity : Nat) (prefixInputs : List MuxInput)
    (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (input : MuxInput)
    (encoded : raw.map (BVExpr.eval assign) = endpointEncodedInput
      (muxRun capacity (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) prefixInputs) input)
    (index : Nat) (bound : index < 8*(endpointOutput VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic
      capacity (endpointKind input) raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (endpointOutput VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity (endpointKind input) raw))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (endpointOutput VarintDecode.Spqr.symbolic Word64.symbolic ByteAuth.symbolic capacity (endpointKind input) raw))).vec.get index bound)) =
    (ByteCircuit.joinValue (mixedSourceStep capacity
      (muxRun capacity (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) prefixInputs) input)).getLsbD index :=
  compiled_mixed_step capacity raw assign _ input
    (mux_run_codec_shape capacity _ prefixInputs (mux_codec_initial_shape capacity))
    (fresh_muxRun_reachable capacity prefixInputs).2 encoded index bound

#print axioms endpoint_output_map
#print axioms compiled_mixed_step
#print axioms compiled_mixed_after_prefix
end ChatResponseReference.ParserCircuitCandidateV1
