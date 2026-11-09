# Bounded restored record coherence guard

Input is `snapshot5550 || selected525 || service611`; output is one computed
private validity byte. The circuit restores the authenticated public schema,
checks the existing bounded record/service coherence, requires its selected
projection to equal the retained selected state, and requires re-flattening to
match the complete raw snapshot. No correctness/validity flag is supplied.
Wrong public dimensions reject, as do malformed private flags/lengths/padding,
selected-state disagreement and bound service-key/counter/identity disagreement.
A legitimate Tahini counter change remains valid; the final byte of this schema
is a live counter, not padding.

Three additional foundation-only endpoints prove schema mapping, full guard
Hom transport and compiled byte-circuit agreement (26 total in SendChecks).
Sixteen public model cases and fourteen exact fixed-size artifact cases pass.
The immutable first compiled candidate has input53488/output8 bits,227188 bit
triples and5432 compiler VM rounds. Build took8.442s with peakRSS753647616 bytes;
these are public compilation resources, not MPC delivery performance. The long
snapshot equality currently has linear AND depth; this is a one-time restore
check, not a per-message requirement.

`RecoveryWork/NativeRecordAdmission.h` names only that fixed pinned closure,
enforces exact single-register CCD bit cells and returns move-owned validity.
It grants no provider/Session admission. Actual Machine.run_function initializes
the VM owners needed for later retirement; a raw independent helper plus
Worker.allocate alone does not. The intended order is checked import and scoped
helper destruction, actual guard execution, completed erased host call, separate
Machine epoch retirement and completed erased host call, then fresh TLS and
account/provider phase checks. This runtime sequence has not yet been tested.

The guard is model-relative. It is not a general snapshot roundtrip theorem,
actual Rust functional refinement, arbitrary SPQR/KEM validation, private/public
DH agreement proof, fresh-session bootstrap or full-account validator. It covers
only the existing V1 bounded schema/domain. Source/certificate/head provenance,
full account/outbox sections, raw-field consistency checks, correct helper
teardown and epoch/member/sharing-domain binding remain required. Imported TLS
keys/nonces are never restored; normal recovery admission stays closed.
