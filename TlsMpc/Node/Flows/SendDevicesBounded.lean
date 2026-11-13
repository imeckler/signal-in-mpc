import TlsMpc.Node.Flows.Registry

/-!
# Op 62's wires fit the pipe (S13, F54 in part)

REORGANIZATION_PLAN.md stage S13. New file; it changes no definition. No I/O; no emitter imports
this module.

`requestDevicesScript_bounded`: every instruction of op 62 (`Send.requestDevicesScript`) is
`Wire.Bounded` (ids, slice bounds and list lengths below 2^64) when the handle ids and the devices'
record offsets are. Op 61 (`devicesScript`) is not covered: unlike op 41 it has no `maxEnvelope`
check on the computed envelope lengths, so its slice bounds are bounded only through a length bound
on `bundleEnvBytes` / `sealEnvBytes` that is not proved (gap S13-12).
-/

namespace TlsMpc.Node.Flows.Registry

open TlsMpc.Node.Engine TlsMpc.Node.Flows TlsMpc.Node.Flows.Contacts

/-- **Op 62's wires fit the pipe.** -/
theorem requestDevicesScript_bounded (n : Nat) (state : BoolH) (ats : List Nat) (hn : n + ats.length < B64)
    (hs : state.id < B64) (hat : ∀ x ∈ ats, 8 * (x + Send.recordBytes) < B64) :
    Every Instr.Bounded (Send.requestDevicesScript n state ats) := by
  have hB := big_lt_B64
  refine every_seqs (Every.done _) _ ?_
  intro i hi
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (hi | rfl) | hi
  · simp only [List.mem_map] at hi
    obtain ⟨⟨j, x⟩, hjx, rfl⟩ := hi
    have hj := (List.of_mem_zip hjx).1
    have hx := hat x (List.of_mem_zip hjx).2
    simp only [List.mem_range] at hj
    simp only [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank]
    omega
  · simp only [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, List.length_map, List.length_range,
      List.mem_map, List.mem_range]
    refine ⟨by omega, by omega, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    show n + j < B64
    omega
  · simp only [frees, List.mem_map, List.mem_range] at hi
    obtain ⟨_, ⟨j, hj, rfl⟩, rfl⟩ := hi
    show n + j < B64
    omega

end TlsMpc.Node.Flows.Registry
