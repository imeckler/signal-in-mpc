# Private-length hash candidate

The public capacity determines a maximum SHA256 block count. Padding marker,
BE64 bitlength and the final digest are selected from shared length bits;
HMAC includes the64-byte key prefix in that bitlength. No length is opened.
One compression is performed per maximum block, rather than hashing every
possible prefix. Invalid status or lengths reject to35 zero output bytes.

Three standard-axiom kernel endpoints prove homomorphism and compiler
agreement with this concrete byte model. The general integer padding,
final-state selection and SHA/HMAC prefix semantic refinements remain
unproved, as do the underlying buffer arithmetic specifications. Differential
tests against hashlib/HMAC exercise152 cases over ten profiles; they do not
replace those proofs. No native MPC or persistent service integration claim.
