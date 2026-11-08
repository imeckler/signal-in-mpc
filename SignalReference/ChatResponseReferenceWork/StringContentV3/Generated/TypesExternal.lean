import Aeneas
/-- The String merger discards the UTF8 diagnostic payload; only Ok/Err is
observed. This type quotient does not assert std validator correctness. -/
def core.str.error.Utf8Error := Unit
