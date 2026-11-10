import TlsMpc.TlsWebSocketUpgrade
import TlsMpc.TlsWebSocketFrame
import TlsMpc.TlsWebSocketIdle
import TlsMpc.TlsWebSocketControl
import TlsMpc.TlsWebSocketActivity
import TlsMpc.TlsChatResponse
import TlsMpc.TlsProviderGate
import TlsMpc.TlsPrivateSeal
import TlsMpc.Signal.RelayUpgrade
import TlsMpc.Signal.PrivateTextNotification
import TlsMpc.Signal.PrivateConversationBackend

/-!
Shared pieces of the service-path kernels (TlsMpc/HybridKernels.lean): the
public message capacity of the WebSocket profile and the parsers' initial
states as circuit constants.
-/
namespace TlsMpc.HybridService
open Std.Tactic.BVDecide
open Signal

def capacity : Nat := 4096

def at' (bytes : List (BVExpr 8)) (index : Nat) : BVExpr 8 := bytes.getD index (.const 0)
def constants (bytes : List (BitVec 8)) : List (BVExpr 8) := bytes.map BVExpr.const

/-- Initial parser states as constants: upgrade (180), frame (26), control
(636), response (932, expected request id zero). -/
def initialStates : List (BVExpr 8) :=
  constants (TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start ByteAuth.concrete)) ++
  constants (TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start ByteAuth.concrete capacity)) ++
  constants (TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial ByteAuth.concrete)) ++
  constants (TlsChatResponse.stateBytes Word64.concrete
    (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity 0))

end TlsMpc.HybridService
