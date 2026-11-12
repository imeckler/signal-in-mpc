import TlsMpc.Node.Policy.Recovery

/-!
# `public_service_controller parse-bench` (measurement only)

Moved unchanged from the controller (`handshake_backend/EmpHybridWork/PublicServiceController.lean`,
which opens this namespace and calls `parseBench`) in REORGANIZATION_PLAN.md stage S2. Since S5 its
console output and clock reads are given to it (`BenchIO`, from `Channels.Real.benchIO`). No emitter
imports this module.
-/

namespace TlsMpc.Node.Bench
open TlsMpc TlsMpc.Signal

/-- What the bench needs from the process (stage S5: given by `Channels.Real.benchIO`, so this file
has no I/O primitive): a zero the compiler cannot see, a nanosecond clock, a line to stdout. -/
structure BenchIO where
  zero : IO Nat
  clock : IO Nat
  say : String → IO Unit

/-- Measurement only (`public_service_controller parse-bench`): the cost per byte of the
parsers this controller runs on revealed bytes. -/
def parseBench (io : BenchIO) : IO Unit := do
  let zero ← io.zero   -- not a compile-time constant, so nothing is evaluated ahead
  let frame := TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start PublicReceive.fast PublicReceive.capacity)
  let control := TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial PublicReceive.fast)
  let response := TlsChatResponse.stateBytes Word64.fast
    (TlsChatResponse.initial Word64.fast PublicReceive.fast PublicReceive.capacity (BitVec.ofNat 64 5))
  let upgrade := TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start PublicReceive.fast)
  let clock : IO Nat := io.clock
  let say : String → IO Unit := io.say
  let time (name : String) (rounds : Nat) (run : Nat → Nat) : IO Unit := do
    let start ← clock
    let mut sum := 0
    for i in [0:rounds] do sum := sum + run (i + zero)
    let stop ← clock
    say s!"{name}: {(stop - start) / rounds / 1000} microseconds per byte (checksum {sum})"
  time "frame parser" 200 (fun i => (TlsWebSocketFrame.runByte PublicReceive.fast PublicReceive.capacity
    (frame ++ [255, BitVec.ofNat 8 (0x82 + i % 2 * 0)])).length)
  time "control queue" 200 (fun i => (TlsWebSocketControl.run PublicReceive.fast (control ++ [0, 0, 0, BitVec.ofNat 8 i])).length)
  time "response parser" 200 (fun i => (TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast PublicReceive.fast PublicReceive.capacity
    (response ++ [255, 255, 0] ++ [BitVec.ofNat 8 i])).length)
  time "upgrade parser" 200 (fun i => (TlsWebSocketUpgrade.runByte PublicReceive.fast (upgrade ++ List.replicate 28 65 ++ [255, BitVec.ofNat 8 (72 + i % 2)])).length)
  say s!"state sizes: frame {frame.length}, control {control.length}, response {response.length}, upgrade {upgrade.length}"
  -- The pass-over of an unrevealed body through the session's own functions, at three sizes: a
  -- response's body (`stepPassed`, as for a prekey response) and a server request's (`stepSkipped`),
  -- byte by byte (before) and with the record loop's bulk step (after). The two must end in the same
  -- state (`passRun_bulk` proves it; this checks the build).
  let ascii (s : String) : List (BitVec 8) := s.toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)
  for n in [2265, 7727, 13000] do
    let body := List.replicate (n + zero) (BitVec.ofNat 8 zero)
    let inner := [0x0a, 3] ++ ascii "PUT" ++ [0x12, 9] ++ ascii "/v1/bench" ++ [0x1a] ++ PublicReceive.varint n ++
      body ++ [0x20] ++ PublicReceive.varint 9
    let payload := [0x08, 0x01, 0x12] ++ PublicReceive.varint inner.length ++ inner
    let request : List (BitVec 8) := [0x82, 126, BitVec.ofNat 8 (payload.length / 256), BitVec.ofNat 8 payload.length] ++ payload
    let cases : List (String × PublicReceive.State × List (BitVec 8)) :=
      [("response body (stepPassed)", PublicReceive.expect { PublicReceive.start [] with upgraded := true, lenient := true } 77,
         Recovery.responseFrame 77 200 "OK" body []),
       ("request body (stepSkipped)", { PublicReceive.start [] with upgraded := true }, request)]
    for (name, start, bytes) in cases do
      let t0 ← clock
      let slow := Recovery.digest (Recovery.walk false start bytes)
      let parsed := match slow with
        | some (_, (_, _, requests, _, _, complete, passed)) => passed == n && (complete || requests.length == 1)
        | none => false
      unless parsed do throw (IO.userError s!"pass-over bench: {name} not parsed")
      let t1 ← clock
      let bulk := Recovery.digest (Recovery.walk true start bytes)
      unless bulk == slow do throw (IO.userError s!"pass-over bench: {name}: bulk and byte by byte differ")
      let t2 ← clock
      say s!"pass-over {n} bytes, {name}: byte by byte {(t1 - t0) / 1000000} ms, bulk {(t2 - t1) / 1000} microseconds, same final state ({(t1 - t0) / max 1 (t2 - t1)}x)"

end TlsMpc.Node.Bench
