# Unpromoted stack32 parser circuit candidate

The isolated candidate encodes the100 group-tag stack entries in four BE bytes rather than eight. It reconstructs the original mux input with zero high32 stack bits, calls the unchanged actual `TlsChatResponseMux.runByte` at public capacity4096, and projects only those high stack halves from the output. Every other byte and control/event/ID/status/header/queue/slot field retains the same source operation. No runtime/Core/Mux/Word64/NativeWorker code changed.

`one_step_projection` records exact one-step projected observation for every compact input, including malformed masks/keys. `runByte_map` and `compiled_correct` prove the symbolic/exported numeric circuit equals that executable candidate for every assignment, using the existing proven Mux map/compiler boundary. This is deliberately NOT a full streaming-equivalence theorem: source accepted group tags fit29bits, but malformed keys can write high tag bits into rejected intermediate states. Reachable-state stack-width preservation, codec roundtrip and sticky-rejection/error-carry with private length and fragmented assembly must be proved before this can replace the existing runtime. Diagnostic/source parser trust boundaries remain unchanged.

Measured attribution (`profile-audit.json`; exact output images remain ignored Build artifacts):

| Profile | Input/output bits | Executed ANDs | Executed XORs | AND dependency depth |
| --- | --- | --- | --- | --- |
| Regenerated original mux | 7888/7880 | 65825 | 23550 | 275 |
| Compact stack input, original full output | 4688/7880 | 49229 | 14253 | 275 |
| Compact input and projected output | 4688/4680 | 40529 | 14253 | 275 |

The candidate saves38.4% executed ANDs and40.6% state-input bits, with NO dependency-depth improvement. Raw exported AND count is137444 baseline and92957 for both mapped profiles; the adapter prunes unreachable output nodes and recognizes XORs, giving the executed counts above. Export took1.27–1.47s/profile; reported child peak RSS1.387GB. These are circuit resource counts, not native MPC or network throughput measurements. No native benchmark or promotion occurred.

Focused proof check uses a separate output directory and binds unchanged current Core/Mux/Word64/ByteAuth/WebSocketFrame source/object hashes. No blanket source/native reruns. The earlier draft compiler check45532 was explicitly interrupted via its PTY (exit1) before source edits; no unresolved writer remains. The two final modules and profile exports have independent terminal receipts.
