# Isolated two-party comparison

Status: source/build feasibility and adapter implementation, **not full Signal throughput**.
Bootstrap and sharing refresh remain paused. No production configuration changes.

## Plan and acceptance

1. Pin backend sources and actual checks; build locally without disabling security guards.
2. Run identical Lean-exported AES/SHA/component graphs with private XOR-share inputs. Account for live preprocessing, all channels/directions, CPU/wall/RSS and cold/warm loading. Never reuse consumed preprocessing.
3. Retain outputs as private shares across repetitions; verify public-known fixture outputs independently. Add curve work with actual private inputs before labeling any result a complete producer.
4. Compose established Signal, TLS seal/open, response parsing and updated conversation state; verify with the pinned Rust recipient. Compare equal-work sequential/batched repetitions, bounded by measured resources. Target27.78 messages/s. Loopback is not WAN.

## Source selection

EMP main README explicitly says “Heads up — AI-assisted rewrite, not yet audited.” Main inspected at a245ca0f67abaf2d48c711e3c050ce961e60ad29. Candidate is final legacy v0.3.0, **not claimed audited**:

| source | commit | official archive SHA256 |
|---|---|---|
| emp-ag2pc v0.3.0 |356cfd824772af9334ac9a994d1eec17ab5f565a|2e6073489eab9a318d63ed1e2c4b7d96b843d3a82fade5413a7be4fe79a9e9b6|
| emp-tool0.3.0 |11093a7d2160e7e7a4dcae3ffd9e6935bf2b8c1c|efa46fccf39643461078b88b82d797e7ce9f1b9357010611045b1afd0254a277|
| emp-ot0.3.0 |52b32c8371c09c1567e3d650c0f0adfbb229a270|a625ad596ec2bc3b6ba989a632407823a90b2efc2c527e64b315f89d71aac6ce|
| MP-SPDZ v0.4.4 |113c4e47dd94bca9ecab029d2f0abe649bea5c52|53cb2822dce57379f1c66647511b866e3e5db3e2f32b530a13e0c872a418ab78|

Official EMP archive URLs are https://codeload.github.com/emp-toolkit/REPOSITORY/tar.gz/COMMIT. Checked README/tag API responses are preserved here. Source trees live outside git in `.deps/two-party-comparison`.

## Security/interface boundaries under investigation

- Legacy C2PC `SSP=5` bytes (comment says40); `MASK=0xFFFFF` truncates some label comparisons to20 bits. Exact composition must be mapped, not called uniform S128. Fpre uses size-dependent buckets3/4/5 and minimum320 triples.
- `2pc.h` production label-mismatch branches print and continue. A benchmark must detect/reject these, not accept outputs after them. Legacy `LeakyDeltaOT` uses IKNP with internal malicious check disabled; outer authenticated-bit/triple protocol supplies checks. This alone does not establish either insecurity or complete security.
- Bob-only output is the default. State sharing can add fresh Alice-owned output pads to the exported graph; only Bob receives masked state. Alice retains pads, Bob retains masked state. Revealing masked outputs to Alice would reconstruct secrets and is forbidden.
- MP-SPDZ stock Tinier shuffle sacrifice caps40. Prior exact audits in `handshake_backend/BackendPackingWork/TINIER_OT_BOUNDARY.md` also identify64-bit truncations and key/OT-state lifecycle obligations. No128 claim or guard deletion.
- MP-SPDZ KOS fallback is rejected by the secure build. The isolated comparison needs supported checked SoftSpoken and exact dependency closure; canonical CCD build has no installed libOTe2. This is a build prerequisite, not permission to use insecure fallback.
- EMP has no established compatible native Fp25519 bridge here. Complete comparison requires an implemented private curve path and exact conversion accounting; Boolean-only results remain components.

## Interruption inventory

No own live bootstrap processes found by approved direct process inventory. Prior bootstrap compiler handles are terminal with preserved reports. No new native groups started at this checkpoint. Other agents may continue independent proof work; immutable graph snapshots will bind benchmark inputs.
