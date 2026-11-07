# Actual AES-256 key-schedule postprocessing

`AesKeyScheduleFinishWork.Finish` proves that the complete postprocessing of the
actual extracted key schedule equals `TlsMpc.Signal.AesKeySchedule.finish`.
The theorem covers every 120-word `Array U64`: all 7,680 input bits are
unrestricted. Offsets and loop bounds are public.

In namespace `LibSignalReference.Candidate.AesKeyScheduleFinish`:

- `finishActual` factors the exact generated suffix after the expansion loop,
  including the `step_by` constructor, actual loop1, the mutable window
  `104..112`, inverse ShiftRows1, and actual loop2. It is a proof convenience;
  the generated implementation is unchanged.
- `finishActual_spec` proves successful execution and equality of the entire
  output list, after mapping `UScalar.bv`, to root `finish concrete`.
- `restoration_loop` covers actual loop2 from any public starting round at most
  15, equaling `restoreRounds concrete (15 - round.val) round.val`.
- `phase_loop` covers all three actual inverse-shift groups. `skipRange104`
  proves the pinned StepBy model's public progression, and `phaseNext_spec`
  specializes it to a step of 32.
- The window theorems reuse the actual inverse-shift and NOT leaf bridges and
  the official array-borrow/write-back proofs. They do not assume that output
  slices preserve their length; that fact follows from the existing leaf
  equalities.

The selected reference is the unchanged `AesKeyScheduleWork.Generated.Funs`
from locked `aes 0.9.1`, used by pinned libsignal `0.106.1`. The existing
reviewed metadata preprocessing remains part of the trusted extraction
boundary, together with faithful Charon/Aeneas translation and the pinned
standard array, slice, range and StepBy models. There are no new source
substitutions or standard-library models.

The proof states the exact translated success behavior on the fixed array
shape. It does not establish the whole key-schedule entrypoint by itself;
the parent package composes initialization, expansion and this suffix. It
does not assert CBC, encryption, protocol or security properties.

Run the source/provenance and theorem-assumption audit with:

```sh
python3 SignalReference/AesKeyScheduleFinishWork/check.py \
  --packages-dir /Users/izzy/repos/eco-theorem-combined/.lake/packages
```

The audit replays the existing extraction selection, validates upstream and
official model hashes, checks cached proof-package revisions, rebuilds the
generated reference and all noncanonical proof dependencies, and checks reused
canonical proof hashes. `proof-check.json` records every workspace Lean source
dependency and all theorem assumptions. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. This package adds no runtime artifact or native
backend execution claim.
