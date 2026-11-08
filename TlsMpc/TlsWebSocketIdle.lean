import TlsMpc.TlsWebSocketFrame
namespace TlsMpc.TlsWebSocketIdle
open Std.Tactic.BVDecide
/-- First integration profile has no unsolicited binary-message slot while idle.
The admission decision is public policy, not a supplied cryptographic validity
flag. Controls remain admitted, and private body/identifier bytes never open. -/
def run (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B) : List B :=
  let out := TlsWebSocketFrame.runByte a capacity raw
  let valid := a.and (TlsWebSocketUpgrade.get a out 0) (a.not (TlsWebSocketUpgrade.get a out 3))
  (List.range out.length).map (fun i =>
    if i==0 || i==13 then valid
    else if i<8 then a.and valid (TlsWebSocketUpgrade.get a out i)
    else TlsWebSocketUpgrade.get a out i)
theorem run_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} (h : ByteAuth.Hom a b f)
    (capacity : Nat) (raw : List B) : (run a capacity raw).map f = run b capacity (raw.map f) := by
  have mapped := TlsWebSocketFrame.runByte_map h capacity raw
  have len := congrArg List.length mapped
  simp only [List.length_map] at len
  simp only [run,List.map_map,Function.comp_def]
  rw [←len]
  congr 1;funext i
  split
  · simp only [h.and,h.not,TlsWebSocketUpgrade.get_map h,mapped]
  · split <;> simp only [h.and,h.not,TlsWebSocketUpgrade.get_map h,mapped]
end TlsMpc.TlsWebSocketIdle
