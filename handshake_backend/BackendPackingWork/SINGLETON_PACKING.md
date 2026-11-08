# One-lane packing correction

MP-SPDZ sbits.bit_compose([sbit]) constructs default40-bit sbits. A singleton
in aig_packed.execute_mpc now returns the existing one-bit value. The branch
inspects public batch size; downstream bit width remains1, and logical values
are unchanged. Mixed batches retain the original packing path.

192 exact-width public model cases pass across12 sizes including tail singles
at65/129 and inversion masks; old/new outputs agree and new consumed triples
match logical AND count. Existing13348 packed/scalar public evaluations pass.
Fresh actual compiler closures confirm five-term carry-save sum2456→272 triples
with unchanged60 VM rounds, and complete compression59798→59759 (original) /
51984→51945 (carry-save), with unchanged3212 rounds. Prior closures are preserved.
This fixes padding waste; it is not bit-packed network transmission or a claim
of application throughput. No native MPC/application rerun occurred here.
