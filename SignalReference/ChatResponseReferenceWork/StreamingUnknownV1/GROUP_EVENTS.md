# Group event primitives candidate

Key/scalar lanes emit zero body/reset/header event masks for every byte, including malformed inputs and rejected records. Zero field-kind masks suppress every event in all lanes. Actual successful source native varint spans and actual decoded group keys have exact zero-mask traces, including their terminal byte; suffix cancellation ties this to the same consumed prefix used by state proofs. Tags and wire kinds are unrestricted within the actual accepted source-key result.

Rejected arbitrary tails have zero masks with every raw byte retained in the trace. These are event composition primitives; the complete recursive group event theorem and whole source/HTTP/correlation/compiler endpoint remain open. Existing content/UTF8/diagnostic trust boundaries are unchanged.

Run `python3 SignalReference/ChatResponseReferenceWork/StreamingUnknownV1/check_group_events.py`.
