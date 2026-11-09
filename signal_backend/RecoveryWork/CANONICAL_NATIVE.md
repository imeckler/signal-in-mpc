# Private canonical sender component

`4e0c040` prepares the fixture; `canonical-native-report.json` records its passing
five-party execution. It uses the same immutable gate-efficient 260/80 service
closure as the throughput experiment, plus the independently compiled computed
record-binding stage. Two supported established sends execute through actual
store reserve/evaluate/preview/commit/install phases. Full canonical snapshot,
selected receive projection and service view agree with actual Rust
SessionRecord updates after both sends; only aggregate equality is opened.
The actual pinned recipient decrypts both final disposable sealed outputs,
validates the certificate and exercises its original MAC/replay rejection checks.

The input is a disposable 80-byte application-padded component payload, with
SS-bound disposable identities and genuine PQXDH-derived classical state. SPQR
is explicitly placed in the selected established no-chunk phase. This component
is separate from the already tested Content/DataMessage text service fixture.

The transaction captures actual local GF128 evaluations, encrypts and fsyncs an
immutable reservation before evaluation, then captures the computed complete
canonical/selected/service state, current typed outbox and request ID before
host installation/release. All five local stores contain four immutable blobs.
The two responses are explicit synthetic component acknowledgments.

This is **not full-account recovery**: the component archive has no quorum
certificate, restart/import, rollback/current-head protocol or epoch-retirement
binding. Registration/prekey/credentials/global-ID/account sections and older
pending outbox links must be integrated in the real account transaction. Native
helper/VM/host cleanup, checked pre-Session restore admission, snapshot roundtrip
and actual-source refinement remain required. The normal recovery/provider gate
stays closed. Final disposable wires and aggregate equality are opened; keys,
DH values and canonical/session-state shares are never opened.

The first run rejected default 64-register public constants during reservation.
Its rejection receipt and log hashes are retained; exact single-register archive
admission was not relaxed. Twelve focused local checks distinguish explicit
one-bit cells from packed64 and malformed cells. Future import/export must
preserve this representation check.

188.914 seconds measures process startup plus this two-send component with
local encrypted writes. It is not a persistent delivery throughput measurement.
