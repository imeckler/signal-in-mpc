import TlsMpc.Signal.ReadAt
import TlsMpc.Signal.Word64
namespace TlsMpc.Signal.PrivateReadAtV1

/-- Bound a fixed-width oblivious read by a shared actual end. Subtract only
behind the offset<=end mask, so wrapping addition cannot authorize a read.
The rejected result keeps the original cursor and zeros every data byte. -/
def read (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W) (width : Nat)
    (bytes : List B) (offset : W) : List B :=
  let fits := a.and (o.ule offset ending) (o.ule (o.const width) (o.sub ending offset))
  let position := Word64.bytes o offset
  Unpad.choose a fits (ReadAt.readCore a width bytes position) (ReadAt.fallback a width position)

theorem read_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (ending : W) (width : Nat)
    (bytes : List B) (offset : W) : (read o a ending width bytes offset).length = 9+width := by
  simp [read,Unpad.choose,ReadAt.readCore_length,ReadAt.fallback_length,Word64.bytes_length]

theorem read_map {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
    {f : B → B'} {fw : W → W'} (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f)
    (ending : W) (width : Nat) (bytes : List B) (offset : W) :
    (read o a ending width bytes offset).map f = read o' a' (fw ending) width (bytes.map f) (fw offset) := by
  simp only [read,Unpad.choose_map ha,ReadAt.readCore_map ha,ReadAt.fallback_map ha,
    Word64.bytes_map ho,ha.and,ho.ule,ho.const,ho.sub]
end TlsMpc.Signal.PrivateReadAtV1
