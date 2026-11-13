# Emitter batch (branch `emitter-batch`, 2026-11-12)

Three changes that touch modules the circuit emitters import, batched so that the circuit cache
(keyed by the emitter binaries' hashes) is invalidated and re-lowered ONCE. Nothing here was
lowered or produced; the re-lowering and the manifests are for the owner to run after the merge.

## What changed, per emitter-imported module

| Module | Change | Circuits affected |
|---|---|---|
| `TlsMpc/Signal/ReceiveFirst.lean` | `text` (kernel `receive-text`): `ok` also checks the top bit of `len₁`'s second byte, the body inside the DataMessage (`len₂ + w₂ + 1 ≤ len₁`) and the DataMessage inside the content (`1 + w₁ + len₁ ≤ content length`); new gate-free helper `decodeLength` (the old length expression, named) and `incBits` (add a carry to big-endian bit masks) | every `receive-text CIPHERTEXT CAPACITY` |
| `TlsMpc/Signal/BundleSlots.lean` | `filler` (= 0) and `slotValid`: the padding must be the filler byte 0 (NUL) instead of `0` (48), the rest digits | the 8 `bundle-slot FIRST LAST ONETIME` |
| `TlsMpc/FlatLowering.lean` | printer rewritten as `printWith` (any monad; `Flat.print` = `printWith` in `IO`) from the SAME `++` chains (`appendGate`, `appendOutput`) and the same 64 kB flushes; `gateOk` (the final check of `lower`) also requires a NOT gate's unused operand to be 0, which every `lower` result satisfies (`pushGate n st 2 w 0`); parser and theorems added (not run by the emitters) | none (bytes unchanged) |
| `TlsMpc/FlatKernelLayout.lean` (new) | `selection`, `fieldName`, `layoutText`, `lowerKernel`, formerly copied verbatim in four emitters, shared; `layoutText` = the same `++` chains (`layoutText_eq_before`); `fieldName` = the same test on the characters; `lowerKernel` = the same checks in the same order with the same messages, written with explicit matches | none (bytes unchanged) |
| `handshake_backend/EmpHybridWork/Emit{Flat,BundleSlot,Ceremony,Kem}Kernel.lean` | import the shared module instead of their copies | none |

Not imported by an emitter, but it must ship with the new `bundle-slot` circuits:
`handshake_backend/EmpHybridWork/service_kernels.h` (`bundle_establish`): the C++ worker's splice
now inserts byte 0 instead of the character `0`. An old worker with the new circuits (or the
reverse) refuses every `bundle-slot` item that needs padding, i.e. almost all (the padding check
fails): no wrong value is released, but device establishment stops working until both are
current. The cache key makes a mix unlikely (the new emitter binaries miss the old cache), but a
strict run reads the manifest's own directory: produce the manifests (step 3) with the new tree
and run them with the new worker. `check_bundle_slots.py` changed
with it (filler, and tests for the former defect).

Binaries whose import closure changed (their hash, so their cache entries and every pin, change):
`flat_kernel_emitter`, `bundle_slot_emitter`, `ceremony_kernel_emitter`, `kem_kernel_emitter`,
`hybrid_kdf_emitter`, `circuit_inventory`, `public_service_controller`. Unchanged:
`word_mask_emitter` (field programs) and the `websocket_*` / `private_tls_emitter` /
`chat_*` emitters.

## What the re-lowering will produce differently

- `receive-text CIPHERTEXT CAPACITY` (every shape in the manifests): new gate list, same layout
  (same fields, bits and marks). About 190 more AND gates per shape (estimate: two 16-bit
  incrementers, one 16-bit strict comparison, two 16-bit comparisons with a constant, one AND).
- `bundle-slot FIRST LAST ONETIME` (the 8 kernels): new gate list, same layout. Roughly +120
  (no one-time prekey) to +200 (one-time prekey) AND gates on ~102.6k / ~105.5k (estimate from
  the slot positions: per position one more AND and an `= 0` comparison sharing half its gates
  with the `= '0'` one; no lowering was run, the new manifest has the exact counts).
- Everything else: byte-identical gate list (`.flat`) and layout (`.layout`), so the same
  `SHA256 LAYOUT_SHA256` in `manifest.txt`. The AND counts and gate counts too.

## Commands (repository root, after the merge; heavy jobs one at a time)

1. Save the current manifests (the production rewrites `OUT/`):

       cp real_signal/state/circuits/manifest.txt real_signal/state/manifest-before-batch.txt
       cp local_signal_server/state/circuits/manifest.txt local_signal_server/state/manifest-before-batch.txt
       cp local_signal_server/state/circuits-compact/manifest.txt local_signal_server/state/manifest-compact-before-batch.txt

2. Rebuild the emitters and the controller (`produce_circuits.py` builds `flat_kernel_emitter`,
   `bundle_slot_emitter`, `circuit_inventory` and `public_service_controller` itself, but
   `circuit_cache.py` builds the other emitters only when they are missing, so rebuild them all):

       python3 scripts/guarded.py --heavy 16 3600 lake build flat_kernel_emitter bundle_slot_emitter ceremony_kernel_emitter kem_kernel_emitter hybrid_kdf_emitter circuit_inventory public_service_controller

   and rebuild the C++ worker the usual way (`service_kernels.h` changed; e.g.
   `handshake_backend/EmpHybridWork/build_hybrid_v3.py`, or let the harness rebuild it).

3. Produce the three manifests (from an empty cache for these binaries: about 1.5 to 2 hours for
   production; the local ones share most kernels with it once production has run):

       python3 scripts/guarded.py --heavy 28 10800 python3 scripts/produce_circuits.py real_signal/deployment-production.json real_signal/state/circuits --max-gb 26
       python3 scripts/guarded.py --heavy 20 7200 python3 scripts/produce_circuits.py local_signal_server/deployment.json local_signal_server/state/circuits
       python3 scripts/guarded.py --heavy 20 7200 python3 scripts/produce_circuits.py local_signal_server/deployment-compact.json local_signal_server/state/circuits-compact

4. The byte-identity check (reads the two manifests; exit status 1 if any kernel other than
   `receive-text` / `bundle-slot` differs):

       python3 scripts/compare_manifests.py real_signal/state/manifest-before-batch.txt real_signal/state/circuits/manifest.txt --changed receive-text bundle-slot
       python3 scripts/compare_manifests.py local_signal_server/state/manifest-before-batch.txt local_signal_server/state/circuits/manifest.txt --changed receive-text bundle-slot
       python3 scripts/compare_manifests.py local_signal_server/state/manifest-compact-before-batch.txt local_signal_server/state/circuits-compact/manifest.txt --changed receive-text bundle-slot

   Expected: "N kernels byte-identical", no `DIFFERENT` line, every `receive-text …` and
   `bundle-slot …` line `changed`, nothing only in one manifest.

5. Then the usual checks: `check_bundle_slots.py` (the kernels with the new splice, and the former
   defect refused) and a local harness run with a `bundle-slot` refresh and a received text.

## Result (merged into two-party-hybrid-worker, re-lowered 2026-11-12)

Re-produced from an empty cache for the new emitters (compact 94 min, then local 16 min and
production 60 min reusing the shared kernels; peak 14.6 GB per kernel, `tls-open-typed 12288`).
`compare_manifests.py --changed receive-text bundle-slot`:

| Set | Kernels | Byte-identical | Changed by design | AND gates (total) |
|---|---|---|---|---|
| compact (`local_signal_server/state/circuits-compact`) | 413 | 403 | 8 `bundle-slot`, 2 `receive-text` | 413,364,408 (+1,434) |
| production (`real_signal/state/circuits`) | 414 | 404 | 8 `bundle-slot`, 2 `receive-text` | 412,604,527 (+1,434) |
| local (`local_signal_server/state/circuits`) | 352 (was 346) | 340 | 1 `receive-text`, +6 `bundle-slot` | 152,227,930 |

Exact AND gates, before → after (layouts unchanged): `bundle-slot F L 0` +124 (e.g. `0 0 0`:
102,574 → 102,698), `bundle-slot F L 1` +170 (`0 0 1`: 105,525 → 105,695); `receive-text 176 170`
6,277 → 6,405, `receive-text 240 234` 8,612 → 8,742 (check_receive_kernels.py's shapes: +126 to
+130). The old LOCAL manifest was older than the batch's base (made by an emitter of 11-11
afternoon): its five other differences (`signal-upgrade 22`, `signal-upgrade-shared 22`,
`receive-access-key 244 176 112..114`) equal the pre-batch emitter's own outputs (the compact and
production pins, and its cache), i.e. a stale manifest, not the batch; it also lacked six
`bundle-slot` kernels. Checked: check_axioms (483 theorems), lint_node, recovery-check 29/29,
policy-check 14/14, parse-bench, check_bundle_slots.py, check_receive_kernels.py, and the local
harness set with the C++ worker (compact signups with 2/3/4 devices, golden records equal).

## Proofs (no `sorry`, `native_decide`, new axiom or Mathlib; `check_axioms.py`: OK)

- receive-text (`TlsMpc/KernelSpecs/ReceiveAcceptText.lean`): `overlongBody_refused` (was
  `overlongBody_accepted`), `accepted_iff_reference`, `text_status_iff_reference`,
  `text_accepted_reference`; `text_eq`, `text_status`, `text_rejects`, `text_accepted`,
  `text_of_reference`, `text_reference` keep their names and statements (`Accepted` gained the
  three checks). `ReceiveFirst.text_map`, `ReceiveProofs.text_spec`, `compiled_correct` unchanged.
- bundle-slot (`TlsMpc/KernelSpecs/BundleSlotWhole.lean`): `inconsistent_width_refused` (was
  `inconsistent_width_accepts`), `zero_padding_ambiguous` (why a kernel-only fix was impossible:
  with `0` padding, `05` spliced with two digits and `5` with one are the same slot), `slotValid_width`
  without the canonical hypothesis, `deviceSlots_any_widths` / `bundleSlot_any_widths` without
  `device` accepting the item (hypothesis now: no field of the item starts with a NUL byte);
  `slotValid_pad`, `deviceSlots_splice`, `bundleSlot_device`, … restated for the filler.
- printers and marks: `FlatLowering.printWith_render`, `parseFlat_render`, `lowerExpr_loaded`,
  `header_eq_before`, `render_sample`; `FlatKernelLayout.layoutText_eq_before`,
  `parseLayout_layoutText`, `openCode_spec`, `lowerKernel_ok`, `lowerKernel_loaded`,
  `layoutText_sample`. Restated in `TlsMpc/Security.lean` section 1b.
