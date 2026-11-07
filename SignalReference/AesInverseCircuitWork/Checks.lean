import TlsMpc.AesInverse

#print axioms TlsMpc.AesInverse.inverseAffineExpr_refines
#print axioms TlsMpc.AesInverse.invSboxExpr_refines
#print axioms TlsMpc.AesInverse.invSbox_forward
#print axioms TlsMpc.AesInverse.forward_invSbox
#print axioms TlsMpc.AesInverse.evaluationHom
#print axioms TlsMpc.AesInverse.invSubBytes_map
#print axioms TlsMpc.AesInverse.invShiftRows_map
#print axioms TlsMpc.AesInverse.invMixColumn_map
#print axioms TlsMpc.AesInverse.invMixColumns_map
#print axioms TlsMpc.AesInverse.round_map
#print axioms TlsMpc.AesInverse.middleRounds_map
#print axioms TlsMpc.AesInverse.decryptExpanded_map
#print axioms TlsMpc.AesInverse.decryptCore_map
#print axioms TlsMpc.AesInverse.decrypt_map
#print axioms TlsMpc.AesInverse.invMixColumns_length
#print axioms TlsMpc.AesInverse.decryptExpanded_length
#print axioms TlsMpc.AesInverse.decryptCore_length
#print axioms TlsMpc.AesInverse.decrypt_result_length
#print axioms TlsMpc.AesInverse.compiled_decryptExpanded_correct
#print axioms TlsMpc.AesInverse.compiled_decryptCore_correct

example (o : TlsMpc.AesInverse.Ops B) (key block : List B)
    (h : block.length ≠ 16) : TlsMpc.AesInverse.decrypt o key block = none := by
  simp [TlsMpc.AesInverse.decrypt, h]

example (o : TlsMpc.AesInverse.Ops B) (key block : List B)
    (h16 : key.length ≠ 16) (h32 : key.length ≠ 32) :
    TlsMpc.AesInverse.decrypt o key block = none := by
  simp [TlsMpc.AesInverse.decrypt, h16, h32]
