import Aeneas
/-- Content representation of the U16 niche; layout is outside this model. -/
def core.num.niche_types.NonZeroU16Inner := Aeneas.Std.U16
/-- Content representation. Nonzero is checked by the selected constructor;
no layout or arbitrary externally supplied NonZero value is asserted valid. -/
def core.num.nonzero.NonZero (T : Type) (_ : Type) := T
