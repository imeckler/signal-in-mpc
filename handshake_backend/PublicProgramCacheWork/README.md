# Isolated pinned public-program cache candidate

This candidate preserves the functional runtime. It is not a promoted application/recovery capability. Source overlay is in public-cache.patch; prepare_runtime.py clones only public source/build products into `.deps/tls-public-program-cache-runtime-v2/MP-SPDZ`. No Player-Data, preprocessing, memory snapshot or private archive is copied. Source replay reproduced all8changed/new runtime files.

The cache retains parsed `Program` instruction vectors, usage/register/memory requirements and public schedule metadata only. It never stores a Processor, protocol/preprocessing owner, RNG, registers, secret memory, function argument/output, socket or private I/O state. Execution still performs ordinary memory sizing/reset, collective program-hash agreement, worker initialization and checked execution. Existing epoch retirement continues to destroy cryptographic owners; public code can survive an epoch.

The internal typed `PinnedCacheAdmission` first uses canonical `PinnedPrograms` descriptor/closure validation. Runtime admission independently verifies closure identity, rechecks every SHA-pinned file even on hits, and parses misses from the exact verified owned descriptor/schedule/bytecode snapshots. A mutable pathname is a lookup location, not an identity. Identity binds descriptor argument types, complete closure digests and actual runtime type/party/field/security/options context. Changing configuration clears retained metadata. Any admitted parse/execution failure poisons future cached execution and discards retained images. The wrapper supplies no RPC/default-provider/share-import bypass.

V2 reserves one explicit producer slot up to2GiB accounted storage, independently of a256MiB/16-entry LRU for other public programs. Only the already pinned private-variable-conversation/batch function families receive this memory priority; it grants no execution capability. Parser/TLS churn cannot evict that slot. A different producer profile may replace it, and oversized images bypass retention. This is not a hard RSS limit: active image, temporary SHA-verification snapshots, allocator overhead and map metadata are separate. Program::public_storage_bytes counts instruction/operand/string capacities and usage metadata estimates. No extra deep Program copy is performed: completed public vectors move between active and retained ownership while host jobs are quiescent. The cache is per Machine, not shared across worker processes. V1's shared1GiB LRU was insufficient evidence for the real working set and remains preserved at commit fdf9b63/runtime path without v2 suffix.

Validation:

* `check_policy.py`: ASAN+UBSAN public LRU/budget/replacement/config/clear, mutation/missing-pin rejection, and stable verified snapshot/stream seek tests.
* `check_native.py`: all5parties exited0; cleanup empty; exact source/library/product integrity passed. Adjacent and interleaved private Boolean calls produce identical aggregate outputs. Four public programs initially load, then6cache hits preserve public metadata across actual epoch renewal with fresh execution owners. A public option change forces two new parses. Invalid closure identity then poisons later valid cached execution and clears retained entries. Only aggregate equality flags are opened.

Authoritative v2 native raw receipt: `benchmarks/results/raw/private-native-public-cache/cc116f8965ec9855`. A tiny pinned synthetic alias selects the producer reservation so the same actual Machine checks cover that policy. V1 final `a33ceccf0000cf66` and initial positive-only `cefabe5b5046f313` remain historical. Final receipts include core runtime source hashes omitted by the initial runner.

Limits: no malformed-MAC/protocol-failure test is claimed for this cache patch. Its base diagnostic v4 has separate caught-failure/partial-constructor gaps addressed by ExceptionWork but not yet composed here; this prevents promotion for recovery/admission. No production NativeWorker/Session/provider imports or frozen runtime files changed. Repeated real producer execution with the cache remains required before declaring the loader bottleneck solved. This cache cannot reduce the measured protocol bytes/message.

## Actual observed working-set stress (public parsing only)

`check_working_set.py` reads the frozen eight-text sequential/B2 descriptor summaries and public working directories. Each has42distinct used descriptors (84summary lines are two snapshots), totaling2202observed calls. Chronological per-call descriptor order was not logged, so this is explicitly a conservative observed-set stress: load producer, load every other41closure, then reload producer. No exact trace is invented. Boot manifest SHA matches the frozen report; runtime-generated extensions match retained receipts/manifests bound to the boot-pinned toolchain. Historical per-call extension digests were not logged, and that provenance limitation is retained in the report.

Both modes passed with producer parsed exactly once despite30small-cache evictions. Actual immutable Program metadata and hashes match after reuse. Results:

| Public-only host probe | Producer accounted bytes | First verified snapshot parse | Return after41closures inclSHA check | Total retained accounted | Actual single-process peakRSS |
|---|---:|---:|---:|---:|---:|
| Sequential service |1054260192|2.006s|0.535s|1313353492|2293760000|
| B2 service |1268574868|3.102s|0.884s|1527668168|2956705792|

These are single-host public parser/cache results, not five-party execution/RSS, fresh-state validation of the full producer, or a direct comparison with the earlier64s loader under five-party workload. Snapshot-backed parsing itself changes the file-backed parser's seek/I/O behavior. The independent tiny five-party test validates actual Machine integration/epoch/output behavior; it does not turn the public-only stress into an application pass. Actual cached producer execution is the next acceptance step. No whole-application speedup or throughput target claim follows.
