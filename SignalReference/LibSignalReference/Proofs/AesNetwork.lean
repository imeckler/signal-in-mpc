import TlsMpc.AesSbox

/-!
Proof auxiliary: the actual locked aes0.9.1 sub_bytes Boolean network,
with its four omitted NOTs restored separately. The implementation reference
remains Generated/AesSubBytes, emitted by Charon/Aeneas from unchanged Rust.
This auxiliary only helps prove that reference equals the MPC S-box.
-/

namespace LibSignalReference.Proofs.AesNetwork

open TlsMpc.AesSbox

def rawProgram : List Gate := [
  .xor 4 2,
  .xor 7 1,
  .xor 9 8,
  .xor 3 10,
  .xor 11 2,
  .and 10 12,
  .xor 12 0,
  .xor 11 6,
  .xor 7 4,
  .xor 15 16,
  .and 16 17,
  .xor 0 17,
  .xor 7 2,
  .xor 6 5,
  .xor 12 21,
  .xor 22 17,
  .and 8 23,
  .xor 24 18,
  .xor 22 20,
  .and 20 22,
  .xor 27 18,
  .xor 21 17,
  .xor 9 29,
  .and 9 29,
  .xor 7 29,
  .xor 21 0,
  .xor 33 4,
  .and 34 0,
  .xor 35 13,
  .xor 36 28,
  .xor 37 26,
  .xor 33 7,
  .and 39 19,
  .xor 40 31,
  .xor 41 28,
  .xor 42 32,
  .xor 33 1,
  .and 44 33,
  .xor 45 31,
  .xor 46 25,
  .xor 47 30,
  .xor 44 20,
  .and 49 14,
  .xor 50 13,
  .xor 51 15,
  .xor 52 25,
  .and 53 48,
  .xor 43 54,
  .xor 38 54,
  .xor 53 38,
  .and 57 55,
  .xor 58 38,
  .and 59 39,
  .and 59 19,
  .xor 48 43,
  .and 56 62,
  .xor 63 43,
  .xor 55 64,
  .and 43 65,
  .xor 55 66,
  .and 59 67,
  .xor 57 68,
  .xor 59 69,
  .and 70 29,
  .xor 71 61,
  .and 70 9,
  .and 69 44,
  .and 69 33,
  .xor 71 75,
  .xor 48 64,
  .xor 66 77,
  .xor 69 78,
  .and 79 22,
  .and 79 20,
  .xor 64 78,
  .and 82 12,
  .and 82 10,
  .and 78 49,
  .and 78 14,
  .xor 86 83,
  .xor 76 87,
  .and 64 34,
  .xor 59 64,
  .xor 90 79,
  .and 91 23,
  .xor 92 76,
  .and 91 8,
  .and 90 17,
  .xor 95 93,
  .and 90 16,
  .xor 97 96,
  .xor 97 94,
  .xor 85 99,
  .xor 100 89,
  .xor 84 100,
  .xor 102 96,
  .xor 102 88,
  .xor 104 96,
  .xor 74 99,
  .and 64 0,
  .xor 83 107,
  .xor 73 108,
  .xor 80 109,
  .xor 93 110,
  .xor 60 111,
  .xor 101 112,
  .xor 112 98,
  .xor 114 81,
  .xor 108 72,
  .xor 106 116,
  .xor 111 117,
  .xor 73 117,
  .xor 116 104]

def rawIndices : List Nat := [119, 118, 113, 120, 104, 115, 105, 103]

def program : List Gate := rawProgram ++ [
  .not 119,
  .not 118,
  .not 115,
  .not 105]

def indices : List Nat := [121, 122, 113, 120, 104, 123, 124, 103]

def run (o : Ops B) (input : List B) : List B :=
  let values := TlsMpc.AesSbox.run o program input
  indices.map (fun i => values[i]?.getD o.zero)

theorem run_map {B B' : Type} {a : Ops B} {b : Ops B'} {f : B → B'}
    (h : Hom a b f) (input : List B) :
    (run a input).map f = run b (input.map f) := by
  simp only [run, ← TlsMpc.AesSbox.run_map h, List.map_map, Function.comp_def,
    ← h.zero, TlsMpc.AesSbox.get_map]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem packed_correct : run packedOps packedInputs = packedOutputs := by decide +kernel

theorem byte_correct (x : BitVec 8) :
    packValue (run concrete ((List.range 8).map (fun i => x.extractLsb' i 1))) = value x := by
  rw [← inputs_at_lane x, ← run_map (laneHom x.toNat x.isLt), packed_correct,
    outputs_at_lane, value_eq_spec]

end LibSignalReference.Proofs.AesNetwork
