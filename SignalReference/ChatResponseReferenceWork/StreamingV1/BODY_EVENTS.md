# Actual copied-body payload validity and events

`OpaqueValidity` proves actual Core validity for arbitrary byte payloads with
budget and safe child end, including exact payload completion at depth zero.
`OpaqueContext` proves field-kind/depth/remaining/inner transition facts.
`OpaquePayloadValidity` composes these over arbitrary proper/exact payload
prefixes with explicit body/child/public-budget bounds. No byte-value or UTF8
restriction is imposed on body data.

`BodyEvents` observes actual Core events as (body-data, body-reset, header-data,
byte). A successful body payload emits exactly (255,0,0,byte) for every original
byte. `native_copied_body_events` binds the trace to the exact content copied by
the actual native Bytes merger, retaining validity at the end. Source immutable
Bytes allocation/content remains its existing explicit model boundary. This is
not a redefinition or weakening of the final parser observation.

The full field/scan proof must establish the post-length opaque state, validity,
body-kind and counter/budget conditions from actual source parsing. Empty payload
control, length-prefix validity/reset, post-field scope/counters, other field/
group/private-EOF/HTTP/correlation/full compiler joins and inherited explicit
trust boundaries remain open. Existing source error/default/diagnostic/suffix and
Core malformed/underflow/overrun rejection are not replaced by this success path.

Run `check_body_events.py` for an immutable four-module combined kernel check
using verified ancestors; no unchanged native corpus is rerun.
