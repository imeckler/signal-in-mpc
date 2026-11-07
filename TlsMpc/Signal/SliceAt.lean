import TlsMpc.Signal.Word64

/-! Oblivious bounded slices. Offset and actual length remain shared; public
width fixes the output size. Missing or out-of-range bytes become zero. -/
namespace TlsMpc.Signal.SliceAt

def rows (o : Word64.Ops B W) (a : ByteAuth.Ops B) (width : Nat) (offset : W) :
    Nat → List B → List B
  | start, [] => List.replicate width (a.const 0)
  | start, b :: rest =>
    Unpad.choose a (Word64.eq o a offset (o.const start))
      (((b :: rest).take width ++ List.replicate width (a.const 0)).take width)
      (rows o a width offset (start + 1) rest)

def readCore (o : Word64.Ops B W) (a : ByteAuth.Ops B) (width : Nat)
    (wire : List B) (offset length : W) : List B :=
  let selected := rows o a width offset 0 wire
  (List.range width).map (fun i => a.and (o.ule (o.const (i + 1)) length) (OpenResult.get a selected i))

section
variable {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)
include ho ha

theorem rows_map (width : Nat) (offset : W) (start : Nat) (wire : List B) :
    (rows o a width offset start wire).map f = rows o' a' width (fw offset) start (wire.map f) := by
  induction wire generalizing start with
  | nil => simp [rows, ha.const]
  | cons b rest ih =>
    simp only [rows, Unpad.choose_map ha, Word64.eq_map ho ha, ho.const,
      List.map_take, List.map_append, List.map_replicate, ha.const, List.map_cons, ih]

theorem readCore_map (width : Nat) (wire : List B) (offset length : W) :
    (readCore o a width wire offset length).map f = readCore o' a' width (wire.map f) (fw offset) (fw length) := by
  simp only [readCore, List.map_map, Function.comp_def, ha.and, ho.ule, ho.const,
    OpenResult.get_map ha, rows_map ho ha]
end

theorem readCore_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (width : Nat)
    (wire : List B) (offset length : W) : (readCore o a width wire offset length).length = width := by
  simp [readCore]

end TlsMpc.Signal.SliceAt
