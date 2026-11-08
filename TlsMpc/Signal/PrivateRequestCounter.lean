import TlsMpc.Signal.PrivateProtobuf

namespace TlsMpc.Signal.PrivateRequestCounter

def next (a : ByteAuth.Ops B) (raw : List B) : List B :=
  if raw.length=8 then
    let bits := (List.range 64).map (fun i => a.maskBit (OpenResult.get a raw (7-i/8)) (i%8))
    let sum := PrivateBuffer.addLoop a bits (a.const 255::List.replicate 63 (a.const 0)) (List.range 64) (a.const 0)
    let valid := a.not sum.2
    let bytes := (List.range 8).map (fun index => (List.range 8).foldl (fun acc bit =>
      a.xor acc (a.and (OpenResult.get a sum.1 (8*(7-index)+bit)) (a.const (2^bit)))) (a.const 0))
    valid :: ByteAuth.release a valid bytes
  else List.replicate 9 (a.const 0)

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha

theorem byteLoop_map (is : List Nat) (bits : List B) (index : Nat) (acc : B) :
    f (is.foldl (fun acc bit => a.xor acc (a.and (OpenResult.get a bits (8*(7-index)+bit)) (a.const (2^bit)))) acc) =
    is.foldl (fun acc bit => a'.xor acc (a'.and (OpenResult.get a' (bits.map f) (8*(7-index)+bit)) (a'.const (2^bit)))) (f acc) := by
  induction is generalizing acc with
  | nil => rfl
  | cons bit is ih => simp only [List.foldl_cons,ih,ha.xor,ha.and,OpenResult.get_map ha,ha.const]

theorem next_map (raw : List B) : (next a raw).map f = next a' (raw.map f) := by
  simp only [next,List.length_map]
  split
  · have sum := PrivateBuffer.addLoop_map ha
      ((List.range 64).map (fun i => a.maskBit (OpenResult.get a raw (7-i/8)) (i%8)))
      (a.const 255::List.replicate 63 (a.const 0)) (List.range 64) (a.const 0)
    simp only [List.map_map,Function.comp_def,ha.maskBit,OpenResult.get_map ha,List.map_cons,List.map_replicate,ha.const] at sum
    have words := congrArg Prod.fst sum
    have carry := congrArg Prod.snd sum
    simp only at words carry
    simp only [List.map_cons,ByteAuth.release_map ha,ha.not,carry,List.map_map,Function.comp_def,byteLoop_map ha,ha.const,words]
  · simp only [List.map_replicate,ha.const]

end Refinement
end TlsMpc.Signal.PrivateRequestCounter
