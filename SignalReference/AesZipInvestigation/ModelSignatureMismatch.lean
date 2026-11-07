import Aeneas

open Aeneas Aeneas.Std

/- Deliberately failing diagnostic, not an accepted proof module. This is the
same type expected for `next` by the generated Iterator impl in the actual
AES add_round_key translation. It uses only pinned standard-model constants. -/
#check (core.slice.iter.IteratorIterMut.next :
  core.slice.iter.IterMut U64 → Result (Option U64 × core.slice.iter.IterMut U64))
